// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Aggregation trace builder for ZlAggAir.
//!
//! This module constructs a minimal aggregation trace over
//! `AggColumns` from a batch of `ZlChildCompact` instances
//! and public inputs. The initial implementation focuses on
//! enforcing a global work accumulator consistent with
//! `AggAirPublicInputs::v_units_total`.

use crate::agg_air::AggAirPublicInputs;
use crate::agg_child::{ZlChildCompact, children_root_from_compact, merkle_root_from_leaf};
use crate::agg_layout::AggColumns;
use crate::utils;

use winterfell::TraceTable;
use winterfell::crypto::Digest as CryptoDigest;
use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;
use zk_lisp_proof::error;

/// Helper structure bundling an aggregation trace with
/// its column layout.
#[derive(Debug)]
pub struct AggTrace {
    pub trace: TraceTable<BE>,
    pub cols: AggColumns,
}

impl AggTrace {
    #[inline]
    pub fn new(trace: TraceTable<BE>, cols: AggColumns) -> Self {
        Self { trace, cols }
    }
}

/// Build an aggregation trace from compact child proofs
/// and aggregation public inputs.
///
/// Invariants enforced here:
/// - `children` must be non-empty;
/// - `agg_pi.children_count == children.len()`;
/// - `agg_pi.children_ms.len() == children.len()`;
/// - for all `i`, `agg_pi.children_ms[i] == children[i].meta.m`;
/// - `agg_pi.v_units_total` equals the sum of `children[i].meta.v_units`.
///
/// The trace layout:
/// - child segments are concatenated in order;
/// - each child `j` with base trace length `m_j` occupies `m_j` rows;
/// - on the first row of each child segment we set `seg_first = 1`
///   and `v_units_child = meta.v_units`;
/// - on all other rows `seg_first = 0` and `v_units_child = 0`;
/// - the global accumulator `v_units_acc` is updated only on
///   rows where `seg_first == 1` and remains constant elsewhere.
pub fn build_agg_trace(
    agg_pi: &AggAirPublicInputs,
    children: &[ZlChildCompact],
) -> error::Result<AggTrace> {
    if children.is_empty() {
        return Err(error::Error::InvalidInput(
            "AggTrace requires at least one child proof",
        ));
    }

    let cols = AggColumns::baseline();
    let n_children = children.len();

    // Basic shape checks against public inputs.
    if agg_pi.children_count != n_children as u32 {
        return Err(error::Error::InvalidInput(
            "AggAirPublicInputs.children_count must match number of children",
        ));
    }
    if agg_pi.children_ms.len() != n_children {
        return Err(error::Error::InvalidInput(
            "AggAirPublicInputs.children_ms length must match number of children",
        ));
    }

    // Enforce suite_id consistency
    // across children and public inputs.
    for child in children {
        if child.suite_id != agg_pi.suite_id {
            return Err(error::Error::InvalidInput(
                "AggAirPublicInputs.suite_id must match suite_id of all children",
            ));
        }
    }

    // Enforce that all children share the same
    // global STARK profile as advertised in
    // AggAirPublicInputs.profile_meta and
    // AggAirPublicInputs.profile_queries. We
    // deliberately do not constrain per-child
    // quantities such as base trace length `m`
    // or `v_units` here; those are handled via
    // `children_ms` and the work accumulator.
    let pm = &agg_pi.profile_meta;
    let pq = &agg_pi.profile_queries;

    for child in children {
        if child.meta.rho != pm.rho
            || child.meta.o != pm.o
            || child.meta.lambda != pm.lambda
            || child.meta.pi_len != pm.pi_len
        {
            return Err(error::Error::InvalidInput(
                "AggAirPublicInputs.profile_meta is inconsistent with child StepMeta",
            ));
        }

        if child.meta.q != pq.num_queries {
            return Err(error::Error::InvalidInput(
                "AggAirPublicInputs.profile_queries.num_queries is inconsistent with child meta.q",
            ));
        }
    }

    // Enforce canonical children_root
    let children_root_expected = children_root_from_compact(&agg_pi.suite_id, children);
    if children_root_expected != agg_pi.children_root {
        return Err(error::Error::InvalidInput(
            "AggAirPublicInputs.children_root is inconsistent with child commitments",
        ));
    }

    // Enforce per-child m and aggregate v_units.
    let mut base_rows: usize = 0;
    let mut v_units_sum: u64 = 0;

    for (i, child) in children.iter().enumerate() {
        let m = agg_pi.children_ms[i];
        if m == 0 {
            return Err(error::Error::InvalidInput(
                "AggAirPublicInputs.children_ms entries must be non-zero",
            ));
        }

        if m != child.meta.m {
            return Err(error::Error::InvalidInput(
                "AggAirPublicInputs.children_ms entry does not match child meta.m",
            ));
        }

        base_rows = base_rows
            .checked_add(m as usize)
            .ok_or(error::Error::InvalidInput(
                "AggTrace length overflow when summing children_ms",
            ))?;

        v_units_sum =
            v_units_sum
                .checked_add(child.meta.v_units)
                .ok_or(error::Error::InvalidInput(
                    "AggAirPublicInputs.v_units_total overflow when summing child meta.v_units",
                ))?;
    }

    if agg_pi.v_units_total != v_units_sum {
        return Err(error::Error::InvalidInput(
            "AggAirPublicInputs.v_units_total must equal sum of child meta.v_units",
        ));
    }

    if base_rows == 0 {
        return Err(error::Error::InvalidInput(
            "AggTrace requires a positive total number of rows",
        ));
    }

    let n_rows = base_rows.next_power_of_two();

    let mut trace = TraceTable::new(cols.width(), n_rows);

    let mut row = 0usize;
    let mut v_acc = BE::from(0u64);
    let mut child_count_acc = BE::from(0u64);

    // Global FRI layer-0 accumulators.
    // In the current skeleton they stay
    // at zero, but the layout and transition
    // constraints are wired so that future
    // child-level contributions can be added at
    // segment boundaries.
    let fri_v0_sum = BE::ZERO;
    let fri_v1_sum = BE::ZERO;
    let fri_vnext_sum = BE::ZERO;

    for (i, child) in children.iter().enumerate() {
        let m = agg_pi.children_ms[i] as usize;
        let v_child_fe = BE::from(child.meta.v_units);

        // Aggregate Merkle root errors for trace and constraint
        // commitments for this child. When Fiat–Shamir challenges
        // or Merkle proofs are missing (e.g. for synthetic children
        // in tests or zero-query profiles), we keep the errors at
        // zero so that the AIR does not enforce Merkle binding.
        let mut trace_root_err_fe = BE::ZERO;
        let mut constraint_root_err_fe = BE::ZERO;

        if let (Some(fs), Some(merkle)) = (&child.fs_challenges, &child.merkle_proofs) {
            let num_q = fs.query_positions.len();

            if num_q != merkle.trace_paths.len() || num_q != merkle.constraint_paths.len() {
                return Err(error::Error::InvalidInput(
                    "ZlChildCompact.merkle_proofs path lengths are inconsistent with fs_challenges",
                ));
            }

            if num_q > 0 {
                if child.trace_roots.is_empty() {
                    return Err(error::Error::InvalidInput(
                        "ZlChildCompact.trace_roots must be non-empty when Merkle proofs are present",
                    ));
                }

                let trace_root_expected_fe = utils::fold_bytes32_to_fe(&child.trace_roots[0]);
                let constraint_root_expected_fe = utils::fold_bytes32_to_fe(&child.constraint_root);

                let lde_domain_size = (child.meta.m as usize)
                    .checked_mul(child.meta.rho as usize)
                    .ok_or(error::Error::InvalidInput(
                        "AggTrace LDE domain size overflow when checking Merkle paths",
                    ))?;

                for (k, &pos) in fs.query_positions.iter().enumerate() {
                    let idx = pos as usize;
                    if idx >= lde_domain_size {
                        return Err(error::Error::InvalidInput(
                            "AggTrace encountered an FS query position outside LDE domain",
                        ));
                    }

                    let t_path = &merkle.trace_paths[k];
                    let c_path = &merkle.constraint_paths[k];

                    let t_root = merkle_root_from_leaf(&t_path.leaf, idx, &t_path.siblings);
                    let c_root = merkle_root_from_leaf(&c_path.leaf, idx, &c_path.siblings);

                    let t_root_fe = utils::fold_bytes32_to_fe(&t_root.as_bytes());
                    let c_root_fe = utils::fold_bytes32_to_fe(&c_root.as_bytes());

                    trace_root_err_fe += t_root_fe - trace_root_expected_fe;
                    constraint_root_err_fe += c_root_fe - constraint_root_expected_fe;
                }
            }
        }

        for r in 0..m {
            let cur_row = row + r;
            let is_first = r == 0;

            // seg_first flag
            trace.set(
                cols.seg_first,
                cur_row,
                if is_first { BE::ONE } else { BE::ZERO },
            );

            // v_units_child: only on the
            // first row of the segment.
            if is_first {
                trace.set(cols.v_units_child, cur_row, v_child_fe);
                trace.set(cols.v_units_acc, cur_row, v_acc);
                trace.set(cols.child_count_acc, cur_row, child_count_acc);
                trace.set(cols.trace_root_err, cur_row, trace_root_err_fe);
                trace.set(cols.constraint_root_err, cur_row, constraint_root_err_fe);

                // Skeleton: no per-child FRI contributions
                // yet, keep child-level deltas at zero.
                trace.set(cols.fri_v0_child, cur_row, BE::ZERO);
                trace.set(cols.fri_v1_child, cur_row, BE::ZERO);
                trace.set(cols.fri_vnext_child, cur_row, BE::ZERO);

                // Global FRI accumulators currently stay
                // constant at zero.
                trace.set(cols.v0_sum, cur_row, fri_v0_sum);
                trace.set(cols.v1_sum, cur_row, fri_v1_sum);
                trace.set(cols.vnext_sum, cur_row, fri_vnext_sum);

                v_acc += v_child_fe;
                child_count_acc += BE::ONE;
            } else {
                trace.set(cols.v_units_child, cur_row, BE::ZERO);
                trace.set(cols.v_units_acc, cur_row, v_acc);
                trace.set(cols.child_count_acc, cur_row, child_count_acc);
                trace.set(cols.trace_root_err, cur_row, BE::ZERO);
                trace.set(cols.constraint_root_err, cur_row, BE::ZERO);

                trace.set(cols.fri_v0_child, cur_row, BE::ZERO);
                trace.set(cols.fri_v1_child, cur_row, BE::ZERO);
                trace.set(cols.fri_vnext_child, cur_row, BE::ZERO);

                trace.set(cols.v0_sum, cur_row, fri_v0_sum);
                trace.set(cols.v1_sum, cur_row, fri_v1_sum);
                trace.set(cols.vnext_sum, cur_row, fri_vnext_sum);
            }

            // ok and other composition-related columns
            // remain at their default zero values.
        }

        row += m;
    }

    // Padding rows (if any):
    // keep accumulator constant and
    // disable seg_first, v_units_child
    // and trace_root_err / fri_root_err.
    for cur_row in row..n_rows {
        trace.set(cols.seg_first, cur_row, BE::ZERO);
        trace.set(cols.v_units_child, cur_row, BE::ZERO);
        trace.set(cols.v_units_acc, cur_row, v_acc);
        trace.set(cols.child_count_acc, cur_row, child_count_acc);
        trace.set(cols.trace_root_err, cur_row, BE::ZERO);
        trace.set(cols.constraint_root_err, cur_row, BE::ZERO);

        trace.set(cols.fri_v0_child, cur_row, BE::ZERO);
        trace.set(cols.fri_v1_child, cur_row, BE::ZERO);
        trace.set(cols.fri_vnext_child, cur_row, BE::ZERO);

        trace.set(cols.v0_sum, cur_row, fri_v0_sum);
        trace.set(cols.v1_sum, cur_row, fri_v1_sum);
        trace.set(cols.vnext_sum, cur_row, fri_vnext_sum);
    }

    Ok(AggTrace::new(trace, cols))
}

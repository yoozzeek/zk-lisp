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

use crate::agg_air::{AggAirPublicInputs, AggFriProfile};
use crate::agg_child::{
    ZlChildCompact, ZlChildTranscript, children_root_from_compact, fold_positions_usize,
    merkle_root_from_leaf,
};
use crate::agg_layout::AggColumns;
use crate::utils;

#[derive(Clone, Copy, Debug)]
struct FriDeepSample {
    v0: BE,
    v1: BE,
    vnext: BE,
    alpha: BE,
    x0: BE,
    x1: BE,
    q1: BE,
    deep_err: BE,
}

use winterfell::TraceTable;
use winterfell::crypto::Digest as CryptoHashDigest;
use winterfell::math::FieldElement;
use winterfell::math::StarkField;
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

    // Global FRI accumulators over all children.
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

                trace.set(cols.fri_v0_child, cur_row, BE::ZERO);
                trace.set(cols.fri_v1_child, cur_row, BE::ZERO);
                trace.set(cols.fri_vnext_child, cur_row, BE::ZERO);
                trace.set(cols.fri_alpha_child, cur_row, BE::ZERO);
                trace.set(cols.fri_x0_child, cur_row, BE::ZERO);
                trace.set(cols.fri_x1_child, cur_row, BE::ZERO);
                trace.set(cols.fri_q1_child, cur_row, BE::ZERO);

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
                trace.set(cols.fri_alpha_child, cur_row, BE::ZERO);
                trace.set(cols.fri_x0_child, cur_row, BE::ZERO);
                trace.set(cols.fri_x1_child, cur_row, BE::ZERO);
                trace.set(cols.fri_q1_child, cur_row, BE::ZERO);

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
        trace.set(cols.fri_alpha_child, cur_row, BE::ZERO);
        trace.set(cols.fri_x0_child, cur_row, BE::ZERO);
        trace.set(cols.fri_x1_child, cur_row, BE::ZERO);
        trace.set(cols.fri_q1_child, cur_row, BE::ZERO);

        trace.set(cols.v0_sum, cur_row, fri_v0_sum);
        trace.set(cols.v1_sum, cur_row, fri_v1_sum);
        trace.set(cols.vnext_sum, cur_row, fri_vnext_sum);
    }

    Ok(AggTrace::new(trace, cols))
}

/// Build an aggregation trace from full child transcripts
/// (ZlChildTranscript) and aggregation public inputs.
///
/// This builder mirrors `build_agg_trace` but also
/// wires a minimal binary FRI-folding sample per child
/// into dedicated columns so that `ZlAggAir` can enforce
/// an on-circuit FRI-folding relation.
pub fn build_agg_trace_from_transcripts(
    agg_pi: &AggAirPublicInputs,
    transcripts: &[ZlChildTranscript],
) -> error::Result<AggTrace> {
    if transcripts.is_empty() {
        return Err(error::Error::InvalidInput(
            "AggTrace requires at least one child transcript",
        ));
    }

    let cols = AggColumns::baseline();
    let n_children = transcripts.len();

    // Basic shape checks against public inputs.
    if agg_pi.children_count != n_children as u32 {
        return Err(error::Error::InvalidInput(
            "AggAirPublicInputs.children_count must match number of transcripts",
        ));
    }
    if agg_pi.children_ms.len() != n_children {
        return Err(error::Error::InvalidInput(
            "AggAirPublicInputs.children_ms length must match number of transcripts",
        ));
    }

    // Enforce suite_id consistency across children and public inputs.
    for tx in transcripts {
        if tx.compact.suite_id != agg_pi.suite_id {
            return Err(error::Error::InvalidInput(
                "AggAirPublicInputs.suite_id must match suite_id of all transcripts",
            ));
        }
    }

    // Enforce that all children share the same global STARK profile
    // as advertised in AggAirPublicInputs.profile_meta and
    // AggAirPublicInputs.profile_queries.
    let pm = &agg_pi.profile_meta;
    let pq = &agg_pi.profile_queries;

    for tx in transcripts {
        let meta = &tx.compact.meta;
        if meta.rho != pm.rho
            || meta.o != pm.o
            || meta.lambda != pm.lambda
            || meta.pi_len != pm.pi_len
        {
            return Err(error::Error::InvalidInput(
                "AggAirPublicInputs.profile_meta is inconsistent with transcript StepMeta",
            ));
        }

        if meta.q != pq.num_queries {
            return Err(error::Error::InvalidInput(
                "AggAirPublicInputs.profile_queries.num_queries is inconsistent with transcript meta.q",
            ));
        }
    }

    // Enforce canonical children_root via compact views.
    let children: Vec<ZlChildCompact> = transcripts.iter().map(|tx| tx.compact.clone()).collect();
    let children_root_expected = children_root_from_compact(&agg_pi.suite_id, &children);
    if children_root_expected != agg_pi.children_root {
        return Err(error::Error::InvalidInput(
            "AggAirPublicInputs.children_root is inconsistent with transcript commitments",
        ));
    }

    // Enforce per-child m and aggregate v_units.
    let mut base_rows: usize = 0;
    let mut v_units_sum: u64 = 0;

    for (i, tx) in transcripts.iter().enumerate() {
        let child = &tx.compact;
        let m = agg_pi.children_ms[i];
        if m == 0 {
            return Err(error::Error::InvalidInput(
                "AggAirPublicInputs.children_ms entries must be non-zero",
            ));
        }

        if m != child.meta.m {
            return Err(error::Error::InvalidInput(
                "AggAirPublicInputs.children_ms entry does not match transcript meta.m",
            ));
        }

        base_rows = base_rows
            .checked_add(m as usize)
            .ok_or(error::Error::InvalidInput(
                "AggTrace length overflow when summing children_ms (transcripts)",
            ))?;

        v_units_sum = v_units_sum.checked_add(child.meta.v_units).ok_or(
            error::Error::InvalidInput(
                "AggAirPublicInputs.v_units_total overflow when summing transcript meta.v_units",
            ),
        )?;
    }

    if agg_pi.v_units_total != v_units_sum {
        return Err(error::Error::InvalidInput(
            "AggAirPublicInputs.v_units_total must equal sum of transcript meta.v_units",
        ));
    }

    if base_rows == 0 {
        return Err(error::Error::InvalidInput(
            "AggTrace requires a positive total number of rows (transcripts)",
        ));
    }

    let n_rows = base_rows.next_power_of_two();

    let mut trace = TraceTable::new(cols.width(), n_rows);

    let mut row = 0usize;
    let mut v_acc = BE::from(0u64);
    let mut child_count_acc = BE::from(0u64);

    let fri_v0_sum = BE::ZERO;
    let fri_v1_sum = BE::ZERO;
    let fri_vnext_sum = BE::ZERO;

    for (i, tx) in transcripts.iter().enumerate() {
        let child = &tx.compact;
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

        // Minimal per-child FRI-folding sample: we pick a
        // single binary FRI coset from the first layer and
        // compute (v0, v1, vnext, alpha, x0, x1) for it. These
        // values are wired into dedicated columns so that the
        // AIR can enforce the binary folding relation. When FRI
        // data or query positions are unavailable, we fall back
        // to zeros so that the constraint becomes vacuous.
        let FriDeepSample {
            v0: fri_v0_child_fe,
            v1: fri_v1_child_fe,
            vnext: fri_vnext_child_fe,
            alpha: fri_alpha_child_fe,
            x0: fri_x0_child_fe,
            x1: fri_x1_child_fe,
            q1: fri_q1_child_fe,
            deep_err: _fri_deep_err_fe,
        } = sample_fri_fold_child(tx, &agg_pi.profile_fri)?;

        // Aggregate DEEP vs FRI layer-0 errors across all
        // query positions for this child using a simple
        // geometric weighting beta^k. For now we use a fixed
        // beta; in future revisions this can be derived from
        // the aggregator's own Fiat–Shamir transcript.
        let deep_agg = compute_deep_agg_over_queries(tx, BE::from(3u64))?;

        // Aggregate FRI layer-1 evaluations == query_values
        // errors across all query positions for this child.
        // We use a separate geometric weighting beta_fri^k
        // so that DEEP and FRI aggregates remain
        // statistically independent.
        let fri_layer1_agg =
            compute_fri_layer1_agg_over_queries(tx, &agg_pi.profile_fri, BE::from(5u64))?;

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

                trace.set(cols.fri_v0_child, cur_row, fri_v0_child_fe);
                trace.set(cols.fri_v1_child, cur_row, fri_v1_child_fe);
                trace.set(cols.fri_vnext_child, cur_row, fri_vnext_child_fe);
                trace.set(cols.fri_alpha_child, cur_row, fri_alpha_child_fe);
                trace.set(cols.fri_x0_child, cur_row, fri_x0_child_fe);
                trace.set(cols.fri_x1_child, cur_row, fri_x1_child_fe);
                trace.set(cols.fri_q1_child, cur_row, fri_q1_child_fe);
                trace.set(cols.comp_sum, cur_row, deep_agg);
                trace.set(cols.alpha_div_zm_sum, cur_row, fri_layer1_agg);

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
                trace.set(cols.fri_alpha_child, cur_row, BE::ZERO);
                trace.set(cols.fri_x0_child, cur_row, BE::ZERO);
                trace.set(cols.fri_x1_child, cur_row, BE::ZERO);
                trace.set(cols.fri_q1_child, cur_row, BE::ZERO);

                trace.set(cols.v0_sum, cur_row, fri_v0_sum);
                trace.set(cols.v1_sum, cur_row, fri_v1_sum);
                trace.set(cols.vnext_sum, cur_row, fri_vnext_sum);
                trace.set(cols.alpha_div_zm_sum, cur_row, BE::ZERO);
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
        trace.set(cols.fri_alpha_child, cur_row, BE::ZERO);
        trace.set(cols.fri_x0_child, cur_row, BE::ZERO);
        trace.set(cols.fri_x1_child, cur_row, BE::ZERO);
        trace.set(cols.fri_q1_child, cur_row, BE::ZERO);

        trace.set(cols.v0_sum, cur_row, fri_v0_sum);
        trace.set(cols.v1_sum, cur_row, fri_v1_sum);
        trace.set(cols.vnext_sum, cur_row, fri_vnext_sum);
        trace.set(cols.alpha_div_zm_sum, cur_row, BE::ZERO);
    }

    Ok(AggTrace::new(trace, cols))
}

/// Aggregate DEEP vs FRI layer-0 errors over all FS query
/// positions for a single child transcript.
///
/// For each query position x_k this function reconstructs
/// a DEEP-composed value Y(x_k) using fs.ood_points and
/// fs.deep_coeffs and matches it against the FRI layer-0
/// query value q0_k obtained via `get_query_values`-style
/// indexing into `fri_layers[0]`. It then computes a
/// weighted sum
///
///     deep_agg = Σ_{k=0..num_q-1} beta^k * (Y(x_k) - q0_k)
///
/// and returns deep_agg. When FRI/DEEP data is missing we
/// fall back to zero so that the AIR constraint over
/// `comp_sum` becomes vacuous.
fn compute_deep_agg_over_queries(tx: &ZlChildTranscript, beta: BE) -> error::Result<BE> {
    let num_layers = tx.fri_layers.len();
    let num_queries = tx.num_queries as usize;

    if num_layers == 0 || num_queries == 0 {
        return Ok(BE::ZERO);
    }

    let folding = 2usize;

    let child = &tx.compact;
    let fs = match &child.fs_challenges {
        Some(fs) => fs,
        None => {
            // Without FS challenges we cannot reconstruct
            // the FRI / DEEP domain geometry; fall back to
            // zero so that AIR constraints become vacuous.
            return Ok(BE::ZERO);
        }
    };

    if fs.query_positions.len() != num_queries {
        return Err(error::Error::InvalidInput(
            "FS query_positions length is inconsistent with child transcript num_queries in compute_deep_agg_over_queries",
        ));
    }

    if fs.ood_points.len() != 1 {
        return Err(error::Error::InvalidInput(
            "AggTrace expects exactly one OOD point in compute_deep_agg_over_queries",
        ));
    }

    if fs.deep_coeffs.is_empty() {
        return Err(error::Error::InvalidInput(
            "AggTrace requires non-empty DEEP coefficients in compute_deep_agg_over_queries",
        ));
    }

    let trace_width = tx.main_trace_width as usize;
    let constraint_width = tx.constraint_frame_width as usize;

    if trace_width == 0 && constraint_width == 0 {
        return Err(error::Error::InvalidInput(
            "ZlChildTranscript must have non-zero trace or constraint width in compute_deep_agg_over_queries",
        ));
    }

    if fs.deep_coeffs.len() != trace_width + constraint_width {
        return Err(error::Error::InvalidInput(
            "FS deep_coeffs length is inconsistent with trace/constraint widths in compute_deep_agg_over_queries",
        ));
    }

    if tx.trace_main_openings.len() != num_queries {
        return Err(error::Error::InvalidInput(
            "ZlChildTranscript.trace_main_openings length is inconsistent with num_queries in compute_deep_agg_over_queries",
        ));
    }

    if constraint_width > 0
        && !tx.constraint_openings.is_empty()
        && tx.constraint_openings.len() != num_queries
    {
        return Err(error::Error::InvalidInput(
            "ZlChildTranscript.constraint_openings length is inconsistent with num_queries in compute_deep_agg_over_queries",
        ));
    }

    if tx.ood_main_current.len() != trace_width
        || tx.ood_main_next.len() != trace_width
        || tx.ood_quotient_current.len() != constraint_width
        || tx.ood_quotient_next.len() != constraint_width
    {
        return Err(error::Error::InvalidInput(
            "ZlChildTranscript OOD row lengths are inconsistent with trace/constraint widths in compute_deep_agg_over_queries",
        ));
    }

    // Reconstruct the LDE / FRI domain size as m * rho.
    let lde_domain_size = (child.meta.m as usize)
        .checked_mul(child.meta.rho as usize)
        .ok_or(error::Error::InvalidInput(
            "AggTrace LDE domain size overflow in compute_deep_agg_over_queries",
        ))?;

    if lde_domain_size == 0 || !lde_domain_size.is_power_of_two() {
        return Err(error::Error::InvalidInput(
            "AggTrace LDE domain size must be a non-zero power of two in compute_deep_agg_over_queries",
        ));
    }

    let positions: Vec<usize> = fs.query_positions.iter().map(|&p| p as usize).collect();
    let folded_positions = fold_positions_usize(&positions, lde_domain_size, folding)?;

    let layer0_vals = tx.fri_layers.first().ok_or(error::Error::InvalidInput(
        "ZlChildTranscript.fri_layers must contain at least one layer when num_queries > 0 in compute_deep_agg_over_queries",
    ))?;

    if folded_positions.is_empty() || layer0_vals.is_empty() {
        return Ok(BE::ZERO);
    }

    let q_count = layer0_vals.len();
    if q_count != folded_positions.len() {
        return Err(error::Error::InvalidInput(
            "FRI folded positions count is inconsistent with transcript layer 0 values in compute_deep_agg_over_queries",
        ));
    }

    let base_g = BE::get_root_of_unity(lde_domain_size.ilog2());
    let offset = BE::GENERATOR;

    let z = fs.ood_points[0];
    let m = child.meta.m as usize;
    if m == 0 || !m.is_power_of_two() {
        return Err(error::Error::InvalidInput(
            "child.meta.m must be a non-zero power of two in compute_deep_agg_over_queries",
        ));
    }

    let g_trace = BE::get_root_of_unity(m.ilog2());
    let z_g = z * g_trace;

    let (deep_trace_coeffs, deep_constraint_coeffs) = fs.deep_coeffs.split_at(trace_width);

    let mut deep_agg = BE::ZERO;
    let mut beta_pow = BE::ONE;

    let domain_size_0 = lde_domain_size;
    let row_length_0 = domain_size_0 / folding;
    if row_length_0 == 0 {
        return Err(error::Error::InvalidInput(
            "FRI row length at depth 0 must be non-zero in compute_deep_agg_over_queries",
        ));
    }

    for (k, &pos_k) in positions.iter().enumerate() {
        if pos_k >= lde_domain_size {
            return Err(error::Error::InvalidInput(
                "FRI sample position exceeds LDE domain size in compute_deep_agg_over_queries",
            ));
        }

        let x = base_g.exp_vartime((pos_k as u64).into()) * offset;

        let x_minus_z = x - z;
        let x_minus_zg = x - z_g;

        if x_minus_z == BE::ZERO || x_minus_zg == BE::ZERO {
            return Err(error::Error::InvalidInput(
                "evaluation point x collides with OOD point in compute_deep_agg_over_queries",
            ));
        }

        let inv_x_minus_z = x_minus_z.inv();
        let inv_x_minus_zg = x_minus_zg.inv();

        // Trace contribution
        let mut y_trace = BE::ZERO;
        let row_x = &tx.trace_main_openings[k];
        if row_x.len() != trace_width {
            return Err(error::Error::InvalidInput(
                "ZlChildTranscript.trace_main_openings row width is inconsistent with main_trace_width in compute_deep_agg_over_queries",
            ));
        }

        for i in 0..trace_width {
            let coeff = deep_trace_coeffs[i];
            let t_x = row_x[i];
            let t_z = tx.ood_main_current[i];
            let t_zg = tx.ood_main_next[i];

            let term_z = (t_x - t_z) * inv_x_minus_z;
            let term_zg = (t_x - t_zg) * inv_x_minus_zg;
            y_trace += coeff * (term_z + term_zg);
        }

        // Constraint composition contribution (if present)
        let mut y_constraints = BE::ZERO;
        if constraint_width > 0 && !tx.constraint_openings.is_empty() {
            let row_c = &tx.constraint_openings[k];
            if row_c.len() != constraint_width {
                return Err(error::Error::InvalidInput(
                    "ZlChildTranscript.constraint_openings row width is inconsistent with constraint_frame_width in compute_deep_agg_over_queries",
                ));
            }

            for j in 0..constraint_width {
                let coeff = deep_constraint_coeffs[j];
                let c_x = row_c[j];
                let c_z = tx.ood_quotient_current[j];
                let c_zg = tx.ood_quotient_next[j];

                let term_c_z = (c_x - c_z) * inv_x_minus_z;
                let term_c_zg = (c_x - c_zg) * inv_x_minus_zg;
                y_constraints += coeff * (term_c_z + term_c_zg);
            }
        }

        let y_k = y_trace + y_constraints;

        // FRI layer-0 query value q0_k via get_query_values geometry.
        let coset_idx_0 = pos_k % row_length_0;
        let elem_idx_0 = pos_k / row_length_0;
        if elem_idx_0 >= folding {
            return Err(error::Error::InvalidInput(
                "FRI element index exceeds folding factor at depth 0 in compute_deep_agg_over_queries",
            ));
        }

        let folded_idx_0 = folded_positions
            .iter()
            .position(|&p| p == coset_idx_0)
            .ok_or(error::Error::InvalidInput(
                "FRI sample coset index not found in folded positions at depth 0 in compute_deep_agg_over_queries",
            ))?;

        let pair_0 = layer0_vals[folded_idx_0];
        let q0_k = pair_0[elem_idx_0];

        let e_k = y_k - q0_k;
        deep_agg += beta_pow * e_k;
        beta_pow *= beta;
    }

    Ok(deep_agg)
}

/// Aggregate FRI layer-1 evaluations == query_values
/// errors over all FS query positions for a single
/// child transcript.
///
/// For folding factor 2 this function reconstructs
/// per-query folding results v_next,k from layer-0
/// pairs (v0_k, v1_k) using the first FRI alpha and
/// matches them against layer-1 query values q1_k
/// obtained via `get_query_values` geometry. It then
/// computes a weighted sum
///
///     fri_agg = Σ_{k=0..num_q-1} beta^k * (v_next,k - q1_k)
///
/// and returns fri_agg. When FRI data is missing we
/// fall back to zero so that the AIR constraint over
/// `alpha_div_zm_sum` becomes vacuous.
fn compute_fri_layer1_agg_over_queries(
    tx: &ZlChildTranscript,
    fri_profile: &AggFriProfile,
    beta: BE,
) -> error::Result<BE> {
    let num_layers = tx.fri_layers.len();
    let num_queries = tx.num_queries as usize;

    if num_layers < 2 || num_queries == 0 {
        return Ok(BE::ZERO);
    }

    let folding = fri_profile.folding_factor as usize;
    if folding != 2 {
        return Err(error::Error::InvalidInput(
            "AggTrace currently supports only FRI folding factor 2 in compute_fri_layer1_agg_over_queries",
        ));
    }

    let child = &tx.compact;
    let fs = match &child.fs_challenges {
        Some(fs) => fs,
        None => {
            // Without FS challenges we cannot reconstruct
            // the FRI domain geometry; fall back to zero
            // so that AIR constraints become vacuous.
            return Ok(BE::ZERO);
        }
    };

    if fs.query_positions.len() != num_queries {
        return Err(error::Error::InvalidInput(
            "FS query_positions length is inconsistent with child transcript num_queries in compute_fri_layer1_agg_over_queries",
        ));
    }

    // Reconstruct the LDE / FRI domain size as m * rho.
    let lde_domain_size = (child.meta.m as usize)
        .checked_mul(child.meta.rho as usize)
        .ok_or(error::Error::InvalidInput(
            "AggTrace LDE domain size overflow in compute_fri_layer1_agg_over_queries",
        ))?;

    if lde_domain_size == 0 || !lde_domain_size.is_power_of_two() {
        return Err(error::Error::InvalidInput(
            "AggTrace LDE domain size must be a non-zero power of two in compute_fri_layer1_agg_over_queries",
        ));
    }

    let positions: Vec<usize> = fs.query_positions.iter().map(|&p| p as usize).collect();
    let folded_positions0 = fold_positions_usize(&positions, lde_domain_size, folding)?;

    let layer0_vals = tx.fri_layers.first().ok_or(error::Error::InvalidInput(
        "ZlChildTranscript.fri_layers must contain at least one layer when num_queries > 0 in compute_fri_layer1_agg_over_queries",
    ))?;
    let layer1_vals = tx.fri_layers.get(1).ok_or(error::Error::InvalidInput(
        "ZlChildTranscript.fri_layers must contain at least two layers in compute_fri_layer1_agg_over_queries",
    ))?;

    if folded_positions0.is_empty() || layer0_vals.is_empty() || layer1_vals.is_empty() {
        return Ok(BE::ZERO);
    }

    let q_count0 = layer0_vals.len();

    let domain_size_1 = lde_domain_size
        .checked_div(folding)
        .ok_or(error::Error::InvalidInput(
            "AggTrace domain size underflow at FRI depth 1 in compute_fri_layer1_agg_over_queries",
        ))?;

    if domain_size_1 == 0 || domain_size_1 % folding != 0 {
        return Err(error::Error::InvalidInput(
            "AggTrace FRI domain size at depth 1 must be a positive multiple of folding in compute_fri_layer1_agg_over_queries",
        ));
    }

    let positions_1 = folded_positions0.clone();
    let folded_positions_1 = fold_positions_usize(&positions_1, domain_size_1, folding)?;

    let q_count1 = layer1_vals.len();
    if q_count1 != folded_positions_1.len() {
        return Err(error::Error::InvalidInput(
            "FRI folded positions count is inconsistent with transcript layer 1 values in compute_fri_layer1_agg_over_queries",
        ));
    }

    let base_g = BE::get_root_of_unity(lde_domain_size.ilog2());
    let folding_root = base_g.exp_vartime(((lde_domain_size / folding) as u64).into());
    let folding_roots = [BE::ONE, folding_root];
    let offset = BE::GENERATOR;

    let alpha0 = fs
        .fri_alphas
        .first()
        .copied()
        .ok_or(error::Error::InvalidInput(
            "AggTrace requires at least one FRI alpha in compute_fri_layer1_agg_over_queries",
        ))?;

    let mut fri_agg = BE::ZERO;
    let mut beta_pow = BE::ONE;

    let row_length_1 = domain_size_1 / folding;
    if row_length_1 == 0 {
        return Err(error::Error::InvalidInput(
            "FRI row length at depth 1 must be non-zero in compute_fri_layer1_agg_over_queries",
        ));
    }

    let num_k = core::cmp::min(q_count0, positions.len());

    for k in 0..num_k {
        // Layer-0 folding result v_next,k for this query.
        let coset_pos0 = folded_positions0[k] as u64;
        let xe = base_g.exp_vartime(coset_pos0.into()) * offset;
        let x0 = xe * folding_roots[0];
        let x1 = xe * folding_roots[1];

        let pair0 = layer0_vals[k];
        let v0 = pair0[0];
        let v1 = pair0[1];

        let den = x1 - x0;
        if den == BE::ZERO {
            return Err(error::Error::InvalidInput(
                "FRI coset has zero denominator in compute_fri_layer1_agg_over_queries",
            ));
        }

        let num = v1 * (alpha0 - x0) - v0 * (alpha0 - x1);
        let vnext_k = num * den.inv();

        // Layer-1 query value q1_k via get_query_values
        // geometry at depth 1.
        let pos1_k = positions_1[k];
        if pos1_k >= domain_size_1 {
            return Err(error::Error::InvalidInput(
                "FRI sample position exceeds domain size at depth 1 in compute_fri_layer1_agg_over_queries",
            ));
        }

        let coset_idx_1 = pos1_k % row_length_1;
        let elem_idx_1 = pos1_k / row_length_1;
        if elem_idx_1 >= folding {
            return Err(error::Error::InvalidInput(
                "FRI element index exceeds folding factor at depth 1 in compute_fri_layer1_agg_over_queries",
            ));
        }

        let folded_idx_1 = folded_positions_1
            .iter()
            .position(|&p| p == coset_idx_1)
            .ok_or(error::Error::InvalidInput(
                "FRI sample coset index not found in folded positions at depth 1 in compute_fri_layer1_agg_over_queries",
            ))?;

        if folded_idx_1 >= q_count1 {
            return Err(error::Error::InvalidInput(
                "FRI layer 1 values length is inconsistent with folded positions in compute_fri_layer1_agg_over_queries",
            ));
        }

        let pair1 = layer1_vals[folded_idx_1];
        let q1_k = pair1[elem_idx_1];

        let e_k = vnext_k - q1_k;
        fri_agg += beta_pow * e_k;
        beta_pow *= beta;
    }

    Ok(fri_agg)
}

/// Compute a minimal per-child binary FRI-folding
/// and DEEP-composition sample from a child transcript.
///
/// We pick the first FRI layer and the first coset
/// in that layer and derive (v0, v1, vnext, alpha,
/// x0, x1) for a binary FRI step. We also compute a
/// layer-1 FRI query value `q1` matching `vnext` via
/// `get_query_values` semantics and a DEEP composition
/// error `deep_err = Y(x_0) - q0`, where `Y(x_0)` is
/// reconstructed from trace / constraint openings and
/// OOD frames and `q0` is the FRI layer-0 query value
/// at the same query position.
///
/// When FRI data or query positions are unavailable,
/// we return all zeros so that the corresponding AIR
/// constraints become vacuous.
fn sample_fri_fold_child(
    tx: &ZlChildTranscript,
    fri_profile: &AggFriProfile,
) -> error::Result<FriDeepSample> {
    let num_layers = tx.fri_layers.len();
    let num_queries = tx.num_queries as usize;

    if num_layers == 0 || num_queries == 0 {
        return Ok(FriDeepSample {
            v0: BE::ZERO,
            v1: BE::ZERO,
            vnext: BE::ZERO,
            alpha: BE::ZERO,
            x0: BE::ZERO,
            x1: BE::ZERO,
            q1: BE::ZERO,
            deep_err: BE::ZERO,
        });
    }

    let folding = fri_profile.folding_factor as usize;
    if folding != 2 {
        return Err(error::Error::InvalidInput(
            "AggTrace currently supports only FRI folding factor 2 in sample_fri_fold_child",
        ));
    }

    if num_layers < 2 {
        return Err(error::Error::InvalidInput(
            "AggTrace requires at least two FRI layers in sample_fri_fold_child when num_queries > 0",
        ));
    }

    let child = &tx.compact;
    let fs = match &child.fs_challenges {
        Some(fs) => fs,
        None => {
            // Without FS challenges we cannot reconstruct
            // the FRI / DEEP domain geometry; fall back to
            // zeros so that AIR constraints become vacuous.
            return Ok(FriDeepSample {
                v0: BE::ZERO,
                v1: BE::ZERO,
                vnext: BE::ZERO,
                alpha: BE::ZERO,
                x0: BE::ZERO,
                x1: BE::ZERO,
                q1: BE::ZERO,
                deep_err: BE::ZERO,
            });
        }
    };

    if fs.query_positions.len() != num_queries {
        return Err(error::Error::InvalidInput(
            "FS query_positions length is inconsistent with child transcript num_queries",
        ));
    }

    if fs.ood_points.len() != 1 {
        return Err(error::Error::InvalidInput(
            "AggTrace expects exactly one OOD point in sample_fri_fold_child",
        ));
    }

    if fs.deep_coeffs.is_empty() {
        return Err(error::Error::InvalidInput(
            "AggTrace requires non-empty DEEP coefficients in sample_fri_fold_child",
        ));
    }

    // Reconstruct the LDE / FRI domain size as m * rho.
    let lde_domain_size = (child.meta.m as usize)
        .checked_mul(child.meta.rho as usize)
        .ok_or(error::Error::InvalidInput(
            "AggTrace LDE domain size overflow in sample_fri_fold_child",
        ))?;

    if lde_domain_size == 0 || !lde_domain_size.is_power_of_two() {
        return Err(error::Error::InvalidInput(
            "AggTrace LDE domain size must be a non-zero power of two in sample_fri_fold_child",
        ));
    }

    // FRI domain generator and coset roots as in FriVerifier.
    let base_g = BE::get_root_of_unity(lde_domain_size.ilog2());
    let folding_root = base_g.exp_vartime(((lde_domain_size / folding) as u64).into());
    let folding_roots = [BE::ONE, folding_root];
    let offset = BE::GENERATOR;

    // Start from query positions in the base domain and fold
    // them once to obtain coset indexes for layer 0.
    let positions: Vec<usize> = fs.query_positions.iter().map(|&p| p as usize).collect();
    let folded_positions = fold_positions_usize(&positions, lde_domain_size, folding)?;

    let layer0_vals = tx.fri_layers.first().ok_or(error::Error::InvalidInput(
        "ZlChildTranscript.fri_layers must contain at least one layer when num_queries > 0",
    ))?;

    if folded_positions.is_empty() || layer0_vals.is_empty() {
        return Ok(FriDeepSample {
            v0: BE::ZERO,
            v1: BE::ZERO,
            vnext: BE::ZERO,
            alpha: BE::ZERO,
            x0: BE::ZERO,
            x1: BE::ZERO,
            q1: BE::ZERO,
            deep_err: BE::ZERO,
        });
    }

    let q_count = layer0_vals.len();
    if q_count != folded_positions.len() {
        return Err(error::Error::InvalidInput(
            "FRI folded positions count is inconsistent with transcript layer 0 values in sample_fri_fold_child",
        ));
    }

    // Pick the first coset as our sample.
    let sample_idx = 0usize;
    let coset_pos = folded_positions[sample_idx] as u64;
    let pair = layer0_vals[sample_idx];

    let xe = base_g.exp_vartime(coset_pos.into()) * offset;
    let x0 = xe * folding_roots[0];
    let x1 = xe * folding_roots[1];

    let v0 = pair[0];
    let v1 = pair[1];

    let alpha = match fs.fri_alphas.first().copied() {
        Some(a) => a,
        None => {
            // Without a layer-0 FRI alpha we cannot form
            // the folding sample; fall back to zeros.
            return Ok(FriDeepSample {
                v0: BE::ZERO,
                v1: BE::ZERO,
                vnext: BE::ZERO,
                alpha: BE::ZERO,
                x0: BE::ZERO,
                x1: BE::ZERO,
                q1: BE::ZERO,
                deep_err: BE::ZERO,
            });
        }
    };

    let den = x1 - x0;
    if den == BE::ZERO {
        return Err(error::Error::InvalidInput(
            "FRI coset has zero denominator in sample_fri_fold_child",
        ));
    }

    let num = v1 * (alpha - x0) - v0 * (alpha - x1);
    let vnext = num * den.inv();

    // --- FRI layer-1 evaluations == query_values sample ---
    // Reconstruct layer-1 query value for the same path
    // using `get_query_values` geometry.
    let layer1_vals = tx.fri_layers.get(1).ok_or(error::Error::InvalidInput(
        "ZlChildTranscript.fri_layers must contain at least two layers in sample_fri_fold_child",
    ))?;

    let domain_size_1 = lde_domain_size
        .checked_div(folding)
        .ok_or(error::Error::InvalidInput(
            "AggTrace domain size underflow at FRI depth 1 in sample_fri_fold_child",
        ))?;

    if domain_size_1 == 0 || domain_size_1 % folding != 0 {
        return Err(error::Error::InvalidInput(
            "AggTrace FRI domain size at depth 1 must be a positive multiple of folding in sample_fri_fold_child",
        ));
    }

    let positions_1 = folded_positions.clone();
    let folded_positions_1 = fold_positions_usize(&positions_1, domain_size_1, folding)?;

    let q_count_1 = layer1_vals.len();
    if q_count_1 != folded_positions_1.len() {
        return Err(error::Error::InvalidInput(
            "FRI folded positions count is inconsistent with transcript layer 1 values in sample_fri_fold_child",
        ));
    }

    let pos_1 = positions_1[sample_idx];
    if pos_1 >= domain_size_1 {
        return Err(error::Error::InvalidInput(
            "FRI sample position exceeds domain size at depth 1 in sample_fri_fold_child",
        ));
    }

    let row_length_1 = domain_size_1 / folding;
    if row_length_1 == 0 {
        return Err(error::Error::InvalidInput(
            "FRI row length at depth 1 must be non-zero in sample_fri_fold_child",
        ));
    }

    let coset_idx_1 = pos_1 % row_length_1;
    let elem_idx_1 = pos_1 / row_length_1;
    if elem_idx_1 >= folding {
        return Err(error::Error::InvalidInput(
            "FRI element index exceeds folding factor at depth 1 in sample_fri_fold_child",
        ));
    }

    let folded_idx_1 = folded_positions_1
        .iter()
        .position(|&p| p == coset_idx_1)
        .ok_or(error::Error::InvalidInput(
            "FRI sample coset index not found in folded positions at depth 1 in sample_fri_fold_child",
        ))?;

    let pair_1 = layer1_vals[folded_idx_1];
    let q1 = pair_1[elem_idx_1];

    // --- DEEP composition vs FRI layer-0 sample ---
    // Reconstruct a single DEEP composition value Y(x_0)
    // for the same query position and compare it to the
    // corresponding FRI layer-0 query value q0.
    let trace_width = tx.main_trace_width as usize;
    let constraint_width = tx.constraint_frame_width as usize;

    if trace_width == 0 && constraint_width == 0 {
        return Err(error::Error::InvalidInput(
            "ZlChildTranscript must have non-zero trace or constraint width in sample_fri_fold_child",
        ));
    }

    if fs.deep_coeffs.len() != trace_width + constraint_width {
        return Err(error::Error::InvalidInput(
            "FS deep_coeffs length is inconsistent with trace/constraint widths in sample_fri_fold_child",
        ));
    }

    if tx.trace_main_openings.len() != num_queries {
        return Err(error::Error::InvalidInput(
            "ZlChildTranscript.trace_main_openings length is inconsistent with num_queries in sample_fri_fold_child",
        ));
    }

    if !tx.constraint_openings.is_empty() && tx.constraint_openings.len() != num_queries {
        return Err(error::Error::InvalidInput(
            "ZlChildTranscript.constraint_openings length is inconsistent with num_queries in sample_fri_fold_child",
        ));
    }

    if tx.ood_main_current.len() != trace_width
        || tx.ood_main_next.len() != trace_width
        || tx.ood_quotient_current.len() != constraint_width
    {
        return Err(error::Error::InvalidInput(
            "ZlChildTranscript OOD row lengths are inconsistent with trace/constraint widths in sample_fri_fold_child",
        ));
    }

    if trace_width > 0 && tx.trace_main_openings[sample_idx].len() != trace_width {
        return Err(error::Error::InvalidInput(
            "ZlChildTranscript.trace_main_openings row width is inconsistent with main_trace_width in sample_fri_fold_child",
        ));
    }

    if constraint_width > 0
        && !tx.constraint_openings.is_empty()
        && tx.constraint_openings[sample_idx].len() != constraint_width
    {
        return Err(error::Error::InvalidInput(
            "ZlChildTranscript.constraint_openings row width is inconsistent with constraint_frame_width in sample_fri_fold_child",
        ));
    }

    let z = fs.ood_points[0];

    // Reconstruct the evaluation point x_0 in the LDE domain
    // matching the sample query position.
    let pos_0 = positions[sample_idx];
    if pos_0 >= lde_domain_size {
        return Err(error::Error::InvalidInput(
            "FRI sample position exceeds LDE domain size in sample_fri_fold_child",
        ));
    }

    let x = base_g.exp_vartime((pos_0 as u64).into()) * offset;

    // Reconstruct the trace-domain generator and z * g for
    // the OOD "next" row. We require m to be a power of two
    // so that get_root_of_unity(m.ilog2()) is well-defined.
    let m = child.meta.m as usize;
    if m == 0 || !m.is_power_of_two() {
        return Err(error::Error::InvalidInput(
            "child.meta.m must be a non-zero power of two in sample_fri_fold_child",
        ));
    }

    let g_trace = BE::get_root_of_unity(m.ilog2());
    let z_g = z * g_trace;

    let x_minus_z = x - z;
    let x_minus_zg = x - z_g;

    if x_minus_z == BE::ZERO || x_minus_zg == BE::ZERO {
        return Err(error::Error::InvalidInput(
            "evaluation point x collides with OOD point in sample_fri_fold_child",
        ));
    }

    let inv_x_minus_z = x_minus_z.inv();
    let inv_x_minus_zg = x_minus_zg.inv();

    let (deep_trace_coeffs, deep_constraint_coeffs) = fs.deep_coeffs.split_at(trace_width);

    let mut deep_val = BE::ZERO;

    // Trace contribution: use both current and next OOD
    // rows with a single coefficient per column, mirroring
    // DeepComposer semantics.
    if trace_width > 0 {
        let row_x = &tx.trace_main_openings[sample_idx];
        for i in 0..trace_width {
            let coeff = deep_trace_coeffs[i];
            let t_x = row_x[i];
            let t_z = tx.ood_main_current[i];
            let t_zg = tx.ood_main_next[i];

            let term_z = (t_x - t_z) * inv_x_minus_z;
            let term_zg = (t_x - t_zg) * inv_x_minus_zg;
            deep_val += coeff * (term_z + term_zg);
        }
    }

    // Constraint composition contribution: use both
    // current and next OOD rows with the same common
    // denominator as for trace columns, mirroring
    // DeepComposer semantics.
    if constraint_width > 0 && !tx.constraint_openings.is_empty() {
        let row_c = &tx.constraint_openings[sample_idx];
        for j in 0..constraint_width {
            let coeff = deep_constraint_coeffs[j];
            let c_x = row_c[j];
            let c_z = tx.ood_quotient_current[j];
            let c_zg = tx.ood_quotient_next[j];

            let term_c_z = (c_x - c_z) * inv_x_minus_z;
            let term_c_zg = (c_x - c_zg) * inv_x_minus_zg;
            deep_val += coeff * (term_c_z + term_c_zg);
        }
    }

    // FRI layer-0 query value q0 for the same sample
    // path, computed via get_query_values geometry.
    let domain_size_0 = lde_domain_size;
    let row_length_0 = domain_size_0 / folding;
    if row_length_0 == 0 {
        return Err(error::Error::InvalidInput(
            "FRI row length at depth 0 must be non-zero in sample_fri_fold_child",
        ));
    }

    let pos_0_fe = positions[sample_idx];
    if pos_0_fe >= domain_size_0 {
        return Err(error::Error::InvalidInput(
            "FRI sample position exceeds domain size at depth 0 in sample_fri_fold_child",
        ));
    }

    let coset_idx_0 = pos_0_fe % row_length_0;
    let elem_idx_0 = pos_0_fe / row_length_0;
    if elem_idx_0 >= folding {
        return Err(error::Error::InvalidInput(
            "FRI element index exceeds folding factor at depth 0 in sample_fri_fold_child",
        ));
    }

    let folded_idx_0 = folded_positions
        .iter()
        .position(|&p| p == coset_idx_0)
        .ok_or(error::Error::InvalidInput(
            "FRI sample coset index not found in folded positions at depth 0 in sample_fri_fold_child",
        ))?;

    let pair_0 = layer0_vals[folded_idx_0];
    let q0 = pair_0[elem_idx_0];

    let deep_err = deep_val - q0;

    Ok(FriDeepSample {
        v0,
        v1,
        vnext,
        alpha,
        x0,
        x1,
        q1,
        deep_err,
    })
}

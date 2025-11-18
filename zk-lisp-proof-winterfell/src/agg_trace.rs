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
use crate::poseidon_hasher::PoseidonHasher;
use crate::utils;

use winterfell::TraceTable;
use winterfell::crypto::{DefaultRandomCoin, Digest as CryptoHashDigest, RandomCoin};
use winterfell::math::FieldElement;
use winterfell::math::StarkField;
use winterfell::math::ToElements;
use winterfell::math::fields::f128::BaseElement as BE;
use zk_lisp_proof::error;

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

#[derive(Clone, Copy, Debug)]
struct AggFsWeights {
    beta_deep: BE,
    beta_fri_layer1: BE,
    delta_depth: BE,
    beta_paths: BE,
}

fn derive_agg_fs_weights(agg_pi: &AggAirPublicInputs) -> error::Result<AggFsWeights> {
    // Derive aggregation weights from AggAirPublicInputs via a
    // dedicated Fiat–Shamir coin so that DEEP / FRI aggregates use
    // unpredictable challenges rather than fixed constants.
    let mut seed_elems = agg_pi.to_elements();
    // Simple domain separator to make aggregation FS distinct from
    // other transcripts using the same hasher.
    seed_elems.push(BE::from(0xA9u64));

    let mut coin = DefaultRandomCoin::<PoseidonHasher<BE>>::new(&seed_elems);

    let beta_deep: BE = coin
        .draw()
        .map_err(|_| error::Error::InvalidInput("failed to draw beta_deep in aggregation FS"))?;
    let beta_fri_layer1: BE = coin.draw().map_err(|_| {
        error::Error::InvalidInput("failed to draw beta_fri_layer1 in aggregation FS")
    })?;
    let delta_depth: BE = coin
        .draw()
        .map_err(|_| error::Error::InvalidInput("failed to draw delta_depth in aggregation FS"))?;
    let beta_paths: BE = coin
        .draw()
        .map_err(|_| error::Error::InvalidInput("failed to draw beta_paths in aggregation FS"))?;

    Ok(AggFsWeights {
        beta_deep,
        beta_fri_layer1,
        delta_depth,
        beta_paths,
    })
}

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

    // Derive aggregation Fiat–Shamir weights once per aggregation
    // instance and reuse them across all children so that DEEP and
    // FRI aggregates are driven by unpredictable challenges.
    let AggFsWeights {
        beta_deep,
        beta_fri_layer1,
        delta_depth,
        beta_paths,
    } = derive_agg_fs_weights(agg_pi)?;

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
        // geometric weighting beta^k drawn from the aggregation
        // Fiat–Shamir transcript.
        let deep_agg = compute_deep_agg_over_queries(tx, beta_deep)?;

        // Aggregate FRI layer-1 evaluations == query_values
        // errors across all query positions for this child.
        // We use a separate geometric weighting beta_fri^k so
        // that DEEP and FRI aggregates remain statistically
        // independent.
        let fri_layer1_agg =
            compute_fri_layer1_agg_over_queries(tx, &agg_pi.profile_fri, beta_fri_layer1)?;

        // Aggregate local FRI folding errors along a single
        // path across all layers, including the remainder
        // polynomial. We use an independent delta challenge
        // so that this aggregate stays statistically
        // independent from beta-based aggregates.
        let fri_path_agg =
            compute_fri_path_agg_over_layers(tx, &agg_pi.profile_fri, delta_depth, 0usize)?;

        // Aggregate FRI folding and remainder errors over all query
        // paths using a separate geometric weighting beta_paths^k so
        // that depth and path aggregates remain statistically
        // independent.
        let fri_paths_agg =
            compute_fri_paths_agg_over_layers(tx, &agg_pi.profile_fri, delta_depth, beta_paths)?;

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
                trace.set(cols.map_l0_sum, cur_row, fri_path_agg);
                trace.set(cols.final_llast_sum, cur_row, fri_paths_agg);

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
        trace.set(cols.map_l0_sum, cur_row, BE::ZERO);
        trace.set(cols.final_llast_sum, cur_row, BE::ZERO);
    }

    Ok(AggTrace::new(trace, cols))
}

/// Aggregate local FRI folding errors along a single FRI query path
/// across all FRI layers and the remainder polynomial for a child
/// transcript.
///
/// This function mirrors the structure of FriVerifier::verify_generic
/// for folding factor 2 but restricts to a single query path. For each
/// FRI depth d it:
/// - recovers the coset index for the path via fold_positions_usize;
/// - reconstructs x-coordinates for the two points in the coset using
///   the same domain generator and offset as Winterfell FRI;
/// - computes the folded value v_{d+1} at alpha_d via the binary
///   degree-respecting projection;
/// - for all but the last layer, checks that v_{d+1} matches the
///   committed evaluation in the next FRI layer for the same path;
/// - on the last layer, treats v_{L} as the evaluation of the final
///   folded polynomial on the smallest domain and compares it against
///   the remainder polynomial at the corresponding point.
///
/// All errors for a single path indexed by `sample_idx` are accumulated
/// into a scalar using a geometric weighting delta^d so that a non-zero
/// result flags any inconsistency along that path. When FRI data or FS
/// challenges are missing, or when num_layers < 2, the function falls
/// back to zero so that the AIR constraint becomes vacuous.
fn compute_fri_path_agg_over_layers(
    tx: &ZlChildTranscript,
    fri_profile: &AggFriProfile,
    delta: BE,
    sample_idx: usize,
) -> error::Result<BE> {
    let num_layers = tx.fri_layers.len();
    let num_queries = tx.num_queries as usize;

    if num_layers < 2 || num_queries == 0 {
        return Ok(BE::ZERO);
    }

    let folding = fri_profile.folding_factor as usize;
    if folding != 2 {
        return Err(error::Error::InvalidInput(
            "AggTrace currently supports only FRI folding factor 2 in compute_fri_path_agg_over_layers",
        ));
    }

    let child = &tx.compact;
    let fs = match &child.fs_challenges {
        Some(fs) => fs,
        None => {
            // Without FS challenges we cannot reconstruct the FRI
            // domain geometry or alphas; fall back to zero so that
            // AIR constraints become vacuous.
            return Ok(BE::ZERO);
        }
    };

    if fs.query_positions.len() != num_queries {
        return Err(error::Error::InvalidInput(
            "FS query_positions length is inconsistent with child transcript num_queries in compute_fri_path_agg_over_layers",
        ));
    }

    if fs.fri_alphas.len() < num_layers {
        return Err(error::Error::InvalidInput(
            "FS fri_alphas length is inconsistent with transcript fri_layers in compute_fri_path_agg_over_layers",
        ));
    }

    // Reconstruct the LDE / FRI domain size as m * rho.
    let lde_domain_size = (child.meta.m as usize)
        .checked_mul(child.meta.rho as usize)
        .ok_or(error::Error::InvalidInput(
            "AggTrace LDE domain size overflow in compute_fri_path_agg_over_layers",
        ))?;

    if lde_domain_size == 0 || !lde_domain_size.is_power_of_two() {
        return Err(error::Error::InvalidInput(
            "AggTrace LDE domain size must be a non-zero power of two in compute_fri_path_agg_over_layers",
        ));
    }

    let positions0: Vec<usize> = fs.query_positions.iter().map(|&p| p as usize).collect();
    let mut positions_d = positions0.clone();
    let mut domain_size_d = lde_domain_size;

    // Domain generator at depth 0 matches Winterfell FRI domain
    // generator used by the verifier; we update it by powering
    // with folding_factor at each subsequent depth.
    let mut domain_generator_d = BE::get_root_of_unity(lde_domain_size.ilog2());

    // Folding roots are computed once from the base domain and
    // reused across depths, mirroring FriVerifier::verify_generic.
    let folding_root = domain_generator_d.exp_vartime(((lde_domain_size / folding) as u64).into());
    let folding_roots = [BE::ONE, folding_root];
    let offset = BE::GENERATOR;

    let mut agg = BE::ZERO;
    let mut delta_pow = BE::ONE;

    // We track the final folded evaluation at the remainder domain
    // for the chosen path so that we can compare it against
    // fri_final at the end.
    let mut v_remainder_path = BE::ZERO;
    let mut pos_remainder = 0usize;

    for depth in 0..num_layers {
        let layer_vals = &tx.fri_layers[depth];

        if layer_vals.is_empty() {
            return Err(error::Error::InvalidInput(
                "ZlChildTranscript.fri_layers[depth] must be non-empty in compute_fri_path_agg_over_layers",
            ));
        }

        // Fold positions for this depth to obtain coset indexes and
        // next-layer positions.
        let folded_positions = fold_positions_usize(&positions_d, domain_size_d, folding)?;

        let q_count = layer_vals.len();
        if q_count != folded_positions.len() {
            return Err(error::Error::InvalidInput(
                "FRI folded positions count is inconsistent with transcript layer values in compute_fri_path_agg_over_layers",
            ));
        }

        if sample_idx >= q_count {
            return Err(error::Error::InvalidInput(
                "sample index out of bounds for FRI layer in compute_fri_path_agg_over_layers",
            ));
        }

        let coset_pos = folded_positions[sample_idx] as u64;
        let pair = layer_vals[sample_idx];

        let xe = domain_generator_d.exp_vartime(coset_pos.into()) * offset;
        let x0 = xe * folding_roots[0];
        let x1 = xe * folding_roots[1];

        let v0 = pair[0];
        let v1 = pair[1];

        let alpha_d = fs.fri_alphas[depth];

        let den = x1 - x0;
        if den == BE::ZERO {
            return Err(error::Error::InvalidInput(
                "FRI coset has zero denominator in compute_fri_path_agg_over_layers",
            ));
        }

        let num = v1 * (alpha_d - x0) - v0 * (alpha_d - x1);
        let vnext = num * den.inv();

        // Prepare geometry for the next domain (after folding this
        // layer) regardless of whether there is another FRI layer or
        // we are at the remainder step.
        let domain_size_next =
            domain_size_d
                .checked_div(folding)
                .ok_or(error::Error::InvalidInput(
                    "AggTrace domain size underflow in compute_fri_path_agg_over_layers",
                ))?;

        if domain_size_next == 0 || domain_size_next % folding != 0 {
            return Err(error::Error::InvalidInput(
                "AggTrace FRI domain size at next depth must be a positive multiple of folding in compute_fri_path_agg_over_layers",
            ));
        }

        let positions_next = folded_positions.clone();

        if depth + 1 < num_layers {
            // There is a next FRI layer; check that the value obtained
            // by folding this layer matches the committed
            // evaluation in the next layer for the same path.
            let layer_next_vals = &tx.fri_layers[depth + 1];

            let folded_positions_next =
                fold_positions_usize(&positions_next, domain_size_next, folding)?;

            if layer_next_vals.is_empty() {
                return Err(error::Error::InvalidInput(
                    "ZlChildTranscript next FRI layer must be non-empty in compute_fri_path_agg_over_layers",
                ));
            }

            if layer_next_vals.len() != folded_positions_next.len() {
                return Err(error::Error::InvalidInput(
                    "FRI folded positions count is inconsistent with next layer values in compute_fri_path_agg_over_layers",
                ));
            }

            if sample_idx >= positions_next.len() {
                return Err(error::Error::InvalidInput(
                    "sample index out of bounds for positions_next in compute_fri_path_agg_over_layers",
                ));
            }

            let pos_next = positions_next[sample_idx];
            if pos_next >= domain_size_next {
                return Err(error::Error::InvalidInput(
                    "FRI sample position exceeds domain size at next depth in compute_fri_path_agg_over_layers",
                ));
            }

            let row_length_next = domain_size_next / folding;
            if row_length_next == 0 {
                return Err(error::Error::InvalidInput(
                    "FRI row length at next depth must be non-zero in compute_fri_path_agg_over_layers",
                ));
            }

            let coset_idx_next = pos_next % row_length_next;
            let elem_idx_next = pos_next / row_length_next;
            if elem_idx_next >= folding {
                return Err(error::Error::InvalidInput(
                    "FRI element index exceeds folding factor at next depth in compute_fri_path_agg_over_layers",
                ));
            }

            let folded_idx_next = folded_positions_next
                .iter()
                .position(|&p| p == coset_idx_next)
                .ok_or(error::Error::InvalidInput(
                    "FRI sample coset index not found in folded positions at next depth in compute_fri_path_agg_over_layers",
                ))?;

            if folded_idx_next >= layer_next_vals.len() {
                return Err(error::Error::InvalidInput(
                    "FRI layer values length is inconsistent with folded positions at next depth in compute_fri_path_agg_over_layers",
                ));
            }

            let pair_next = layer_next_vals[folded_idx_next];
            let q_next = pair_next[elem_idx_next];

            let e_d = vnext - q_next;
            agg += delta_pow * e_d;
            delta_pow *= delta;
        } else {
            // Last FRI layer: vnext is the evaluation of the final
            // folded polynomial (remainder) at the corresponding
            // position in the smallest domain.
            if sample_idx >= positions_next.len() {
                return Err(error::Error::InvalidInput(
                    "sample index out of bounds for remainder positions in compute_fri_path_agg_over_layers",
                ));
            }

            v_remainder_path = vnext;
            pos_remainder = positions_next[sample_idx];
        }

        // Advance domain geometry for the next depth (or remainder).
        domain_generator_d = domain_generator_d.exp_vartime((folding as u32).into());
        domain_size_d = domain_size_next;
        positions_d = positions_next;
    }

    // Final remainder check using Horner evaluation over
    // tx.fri_final.coeffs in the same reverse-coefficient convention
    // as winter-fri's eval_horner_rev.
    if tx.fri_final.coeffs.is_empty() {
        return Err(error::Error::InvalidInput(
            "ZlChildTranscript.fri_final.coeffs must be non-empty in compute_fri_path_agg_over_layers",
        ));
    }

    if pos_remainder >= domain_size_d {
        return Err(error::Error::InvalidInput(
            "FRI sample position exceeds remainder domain size in compute_fri_path_agg_over_layers",
        ));
    }

    let x_l = BE::GENERATOR * domain_generator_d.exp_vartime((pos_remainder as u64).into());

    let rem_val = tx
        .fri_final
        .coeffs
        .iter()
        .fold(BE::ZERO, |acc, &coeff| acc * x_l + coeff);

    let e_final = v_remainder_path - rem_val;
    agg += delta_pow * e_final;

    Ok(agg)
}

/// Aggregate FRI folding and remainder errors over all query paths and
/// all FRI layers for a child transcript.
///
/// For each FRI path index `k` (coset index shared across all layers)
/// this function computes the single-path aggregate
/// `path_err_k = compute_fri_path_agg_over_layers` with depth challenge
/// `delta`, and then folds all such paths into a single scalar
///
///     agg = sum_{k} beta^k * path_err_k
///
/// using an independent path-weighting challenge `beta`. When FRI data
/// or FS challenges are missing, or when there are fewer than two FRI
/// layers or no non-empty layers, the aggregate falls back to zero so
/// that the corresponding AIR constraint becomes vacuous.
fn compute_fri_paths_agg_over_layers(
    tx: &ZlChildTranscript,
    fri_profile: &AggFriProfile,
    delta: BE,
    beta: BE,
) -> error::Result<BE> {
    let num_layers = tx.fri_layers.len();
    let num_queries = tx.num_queries as usize;

    if num_layers < 2 || num_queries == 0 {
        return Ok(BE::ZERO);
    }

    // Use the minimum non-empty layer length as the number of FRI paths
    // that can be followed consistently across all depths without
    // running out of samples.
    let min_paths = tx
        .fri_layers
        .iter()
        .map(|layer| layer.len())
        .filter(|&len| len > 0)
        .min()
        .unwrap_or(0usize);

    if min_paths == 0 {
        return Ok(BE::ZERO);
    }

    let mut agg = BE::ZERO;
    let mut beta_pow = BE::ONE;

    for k in 0..min_paths {
        let path_err = compute_fri_path_agg_over_layers(tx, fri_profile, delta, k)?;
        agg += beta_pow * path_err;
        beta_pow *= beta;
    }

    Ok(agg)
}
/// fs.deep_coeffs and matches it against the FRI layer-0
/// query value q0_k obtained via `get_query_values`-style
/// indexing into `fri_layers[0]`. It then computes a
/// weighted sum
///
///     deep_agg = sum_{k=0..num_q-1} beta^k * (Y(x_k) - q0_k)
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
///     fri_agg = sum_{k=0..num_q-1} beta^k * (v_next,k - q1_k)
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

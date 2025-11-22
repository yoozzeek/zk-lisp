// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
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

use crate::agg::air::{AggAirPublicInputs, AggFriProfile};
use crate::agg::child::{
    ZlChildCompact, ZlChildTranscript, ZlFsChallenges, children_root_from_compact,
    fold_positions_usize, merkle_root_from_leaf,
};
use crate::agg::layout::AggColumns;
use crate::poseidon::hasher::PoseidonHasher;
use crate::utils;

use winterfell::TraceTable;
use winterfell::crypto::{DefaultRandomCoin, Digest as CryptoHashDigest, RandomCoin};
use winterfell::math::FieldElement;
use winterfell::math::StarkField;
use winterfell::math::ToElements;
use winterfell::math::fields::f128::BaseElement as BE;
use zk_lisp_proof::error;

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

/// Shared context for DEEP aggregation over all query positions
/// for a single child transcript. This bundles together domain
struct DeepContext<'a> {
    _child: &'a ZlChildCompact,
    trace_width: usize,
    constraint_width: usize,
    lde_domain_size: usize,
    positions: Vec<usize>,
    folded_positions: Vec<usize>,
    layer0_vals: &'a Vec<[BE; 2]>,
    base_g: BE,
    offset: BE,
    z: BE,
    z_g: BE,
    deep_trace_coeffs: &'a [BE],
    deep_constraint_coeffs: &'a [BE],
    row_length_0: usize,
    trace_rows: &'a Vec<Vec<BE>>,
    constraint_rows: &'a Vec<Vec<BE>>,
    ood_main_current: &'a [BE],
    ood_main_next: &'a [BE],
    ood_quotient_current: &'a [BE],
    ood_quotient_next: &'a [BE],
}

fn derive_agg_fs_weights(agg_pi: &AggAirPublicInputs) -> error::Result<AggFsWeights> {
    // Derive aggregation weights from AggAirPublicInputs via a
    // dedicated Fiat–Shamir coin so that DEEP / FRI aggregates use
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
    let (agg_trace, _child_start_rows) = build_agg_trace_core(agg_pi, children)?;
    Ok(agg_trace)
}

/// Build an aggregation trace from full child transcripts
/// (ZlChildTranscript) and aggregation public inputs.
pub fn build_agg_trace_from_transcripts(
    agg_pi: &AggAirPublicInputs,
    transcripts: &[ZlChildTranscript],
) -> error::Result<AggTrace> {
    if transcripts.is_empty() {
        return Err(error::Error::InvalidInput(
            "AggTrace requires at least one child transcript",
        ));
    }

    let children: Vec<ZlChildCompact> = transcripts.iter().map(|tx| tx.compact.clone()).collect();

    let (mut agg_trace, child_start_rows) = build_agg_trace_core(agg_pi, &children)?;

    if child_start_rows.len() != transcripts.len() {
        return Err(error::Error::InvalidInput(
            "AggTrace internal error: child_start_rows length mismatch in build_agg_trace_from_transcripts",
        ));
    }

    // Derive aggregation Fiat–Shamir weights once per aggregation
    // instance and reuse them across all children so that DEEP and
    let AggFsWeights {
        beta_deep,
        beta_fri_layer1,
        delta_depth,
        beta_paths,
    } = derive_agg_fs_weights(agg_pi)?;

    let cols = agg_trace.cols;
    let trace = &mut agg_trace.trace;

    for (i, tx) in transcripts.iter().enumerate() {
        let start_row = child_start_rows[i];

        // Minimal per-child FRI-folding sample: we pick a
        // single binary FRI coset from the first layer and
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
        let deep_agg = compute_deep_agg_over_queries(tx, beta_deep)?;

        // Aggregate FRI layer-1 evaluations == query_values
        // errors across all query positions for this child.
        let fri_layer1_agg =
            compute_fri_layer1_agg_over_queries(tx, &agg_pi.profile_fri, beta_fri_layer1)?;

        // Aggregate local FRI folding errors along a single
        // path across all layers, including the remainder
        let fri_path_agg =
            compute_fri_path_agg_over_layers(tx, &agg_pi.profile_fri, delta_depth, 0usize)?;

        // Aggregate FRI folding and remainder errors over all query
        // paths using a separate geometric weighting beta_paths^k so
        let fri_paths_agg =
            compute_fri_paths_agg_over_layers(tx, &agg_pi.profile_fri, delta_depth, beta_paths)?;

        // Overlay FRI/DEEP aggregates on the first row of the
        // corresponding child segment. All other rows and padding
        trace.set(cols.fri_v0_child, start_row, fri_v0_child_fe);
        trace.set(cols.fri_v1_child, start_row, fri_v1_child_fe);
        trace.set(cols.fri_vnext_child, start_row, fri_vnext_child_fe);
        trace.set(cols.fri_alpha_child, start_row, fri_alpha_child_fe);
        trace.set(cols.fri_x0_child, start_row, fri_x0_child_fe);
        trace.set(cols.fri_x1_child, start_row, fri_x1_child_fe);
        trace.set(cols.fri_q1_child, start_row, fri_q1_child_fe);
        trace.set(cols.comp_sum, start_row, deep_agg);
        trace.set(cols.alpha_div_zm_sum, start_row, fri_layer1_agg);
        trace.set(cols.map_l0_sum, start_row, fri_path_agg);
        trace.set(cols.final_llast_sum, start_row, fri_paths_agg);
    }

    Ok(agg_trace)
}

/// Core builder shared by both compact and transcript-based
/// aggregation trace constructors. This function performs all
/// shape checks against `AggAirPublicInputs`, enforces the
/// canonical `children_root` and constructs the base layout
/// over `AggColumns` with Merkle root error accumulators.
///
/// It returns the constructed `AggTrace` together with the
/// starting row index for each child segment so that callers
/// can overlay additional per-child data (e.g. FRI/DEEP
/// aggregates) only on `seg_first` rows.
fn build_agg_trace_core(
    agg_pi: &AggAirPublicInputs,
    children: &[ZlChildCompact],
) -> error::Result<(AggTrace, Vec<usize>)> {
    if children.is_empty() {
        return Err(error::Error::InvalidInput(
            "AggTrace requires at least one child proof",
        ));
    }

    let cols = AggColumns::baseline();
    let n_children = children.len();

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

    // Enforce suite_id consistency across children and public inputs.
    for child in children {
        if child.suite_id != agg_pi.suite_id {
            return Err(error::Error::InvalidInput(
                "AggAirPublicInputs.suite_id must match suite_id of all children",
            ));
        }
    }

    // Segment sanity first: make chain errors surface before profile shape errors.
    // All children must advertise valid segment indices and form a contiguous chain
    let mut totals: Option<u32> = None;
    let mut indices: Vec<u32> = Vec::with_capacity(n_children);

    for child in children {
        if child.segments_total == 0 {
            return Err(error::Error::InvalidInput(
                "AggTrace requires child.segments_total > 0",
            ));
        }
        if child.segment_index >= child.segments_total {
            return Err(error::Error::InvalidInput(
                "AggTrace segment_index must satisfy 0 <= idx < segments_total",
            ));
        }

        match totals {
            None => totals = Some(child.segments_total),
            Some(t) => {
                if child.segments_total != t {
                    return Err(error::Error::InvalidInput(
                        "AggTrace requires a uniform segments_total across children",
                    ));
                }
            }
        }

        indices.push(child.segment_index);
    }

    if let Some(t) = totals {
        if t > 1 {
            if t as usize != n_children {
                return Err(error::Error::InvalidInput(
                    "AggTrace requires a complete contiguous segment chain in batch",
                ));
            }

            indices.sort_unstable();

            for (i, idx) in indices.iter().enumerate() {
                if *idx != i as u32 {
                    return Err(error::Error::InvalidInput(
                        "AggTrace segment indices must form [0..children_count) without gaps",
                    ));
                }
            }
        }
    }

    // Enforce that all children share the same global STARK profile
    // as advertised in AggAirPublicInputs.profile_meta and
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

    // Enforce per-child m and aggregate v_units
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

    for r in 0..n_rows {
        trace.set(cols.ok, r, BE::ZERO);
        trace.set(cols.comp_sum, r, BE::ZERO);
        trace.set(cols.alpha_div_zm_sum, r, BE::ZERO);
        trace.set(cols.map_l0_sum, r, BE::ZERO);
        trace.set(cols.final_llast_sum, r, BE::ZERO);
    }

    let mut row = 0usize;
    let mut v_acc = BE::from(0u64);
    let mut child_count_acc = BE::from(0u64);

    // Global FRI accumulators over all children remain zero in the
    // current aggregator; we keep them explicit for clarity.
    let fri_v0_sum = BE::ZERO;
    let fri_v1_sum = BE::ZERO;
    let fri_vnext_sum = BE::ZERO;

    // Decode global boundary state from AggAirPublicInputs once
    // so that VM / RAM / ROM chain checks can be expressed as
    let vm_initial_fe = utils::fold_bytes32_to_fe(&agg_pi.vm_state_initial);
    let vm_final_fe = utils::fold_bytes32_to_fe(&agg_pi.vm_state_final);
    let ram_u_initial_fe = utils::fold_bytes32_to_fe(&agg_pi.ram_gp_unsorted_initial);
    let ram_u_final_fe = utils::fold_bytes32_to_fe(&agg_pi.ram_gp_unsorted_final);
    let ram_s_initial_fe = utils::fold_bytes32_to_fe(&agg_pi.ram_gp_sorted_initial);
    let ram_s_final_fe = utils::fold_bytes32_to_fe(&agg_pi.ram_gp_sorted_final);

    let rom_initial_fe: [BE; 3] = [
        utils::fold_bytes32_to_fe(&agg_pi.rom_s_initial[0]),
        utils::fold_bytes32_to_fe(&agg_pi.rom_s_initial[1]),
        utils::fold_bytes32_to_fe(&agg_pi.rom_s_initial[2]),
    ];
    let rom_final_fe: [BE; 3] = [
        utils::fold_bytes32_to_fe(&agg_pi.rom_s_final[0]),
        utils::fold_bytes32_to_fe(&agg_pi.rom_s_final[1]),
        utils::fold_bytes32_to_fe(&agg_pi.rom_s_final[2]),
    ];

    let mut prev_vm_out: Option<BE> = None;
    let mut prev_ram_u_out: Option<BE> = None;
    let mut prev_ram_s_out: Option<BE> = None;
    let mut prev_rom_out: Option<[BE; 3]> = None;

    let mut child_start_rows = Vec::with_capacity(n_children);

    for (i, child) in children.iter().enumerate() {
        let m = agg_pi.children_ms[i] as usize;
        let v_child_fe = BE::from(child.meta.v_units);

        // Decode per-child boundary state from ZlChildCompact.
        let vm_in_fe = utils::fold_bytes32_to_fe(&child.state_in_hash);
        let vm_out_fe = utils::fold_bytes32_to_fe(&child.state_out_hash);

        let ram_u_in_fe = utils::fold_bytes32_to_fe(&child.ram_gp_unsorted_in);
        let ram_u_out_fe = utils::fold_bytes32_to_fe(&child.ram_gp_unsorted_out);
        let ram_s_in_fe = utils::fold_bytes32_to_fe(&child.ram_gp_sorted_in);
        let ram_s_out_fe = utils::fold_bytes32_to_fe(&child.ram_gp_sorted_out);

        let rom_in_fe: [BE; 3] = [
            utils::fold_bytes32_to_fe(&child.rom_s_in[0]),
            utils::fold_bytes32_to_fe(&child.rom_s_in[1]),
            utils::fold_bytes32_to_fe(&child.rom_s_in[2]),
        ];
        let rom_out_fe: [BE; 3] = [
            utils::fold_bytes32_to_fe(&child.rom_s_out[0]),
            utils::fold_bytes32_to_fe(&child.rom_s_out[1]),
            utils::fold_bytes32_to_fe(&child.rom_s_out[2]),
        ];

        // Compute chain errors for this child relative to the
        // global boundary state and previous children. These
        let is_first_child = i == 0;
        let is_last_child = i + 1 == n_children;

        let mut vm_err = if is_first_child {
            vm_in_fe - vm_initial_fe
        } else {
            match prev_vm_out {
                Some(prev) => vm_in_fe - prev,
                None => vm_in_fe - vm_initial_fe,
            }
        };

        let mut ram_u_err = if is_first_child {
            ram_u_in_fe - ram_u_initial_fe
        } else {
            match prev_ram_u_out {
                Some(prev) => ram_u_in_fe - prev,
                None => ram_u_in_fe - ram_u_initial_fe,
            }
        };

        let mut ram_s_err = if is_first_child {
            ram_s_in_fe - ram_s_initial_fe
        } else {
            match prev_ram_s_out {
                Some(prev) => ram_s_in_fe - prev,
                None => ram_s_in_fe - ram_s_initial_fe,
            }
        };

        let mut rom_err: [BE; 3] = if is_first_child {
            [
                rom_in_fe[0] - rom_initial_fe[0],
                rom_in_fe[1] - rom_initial_fe[1],
                rom_in_fe[2] - rom_initial_fe[2],
            ]
        } else {
            match prev_rom_out {
                Some(prev) => [
                    rom_in_fe[0] - prev[0],
                    rom_in_fe[1] - prev[1],
                    rom_in_fe[2] - prev[2],
                ],
                None => [
                    rom_in_fe[0] - rom_initial_fe[0],
                    rom_in_fe[1] - rom_initial_fe[1],
                    rom_in_fe[2] - rom_initial_fe[2],
                ],
            }
        };

        if is_last_child {
            vm_err += vm_out_fe - vm_final_fe;
            ram_u_err += ram_u_out_fe - ram_u_final_fe;
            ram_s_err += ram_s_out_fe - ram_s_final_fe;
            rom_err[0] += rom_out_fe[0] - rom_final_fe[0];
            rom_err[1] += rom_out_fe[1] - rom_final_fe[1];
            rom_err[2] += rom_out_fe[2] - rom_final_fe[2];
        }

        // Aggregate Merkle root errors for trace and constraint
        // commitments for this child. When Fiat–Shamir challenges
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

        let child_start_row = row;
        child_start_rows.push(child_start_row);

        for r in 0..m {
            let cur_row = row + r;
            let is_first = r == 0;

            // seg_first flag
            trace.set(
                cols.seg_first,
                cur_row,
                if is_first { BE::ONE } else { BE::ZERO },
            );

            // v_units_child: only on the first row of the segment.
            if is_first {
                trace.set(cols.v_units_child, cur_row, v_child_fe);
                trace.set(cols.v_units_acc, cur_row, v_acc);
                trace.set(cols.child_count_acc, cur_row, child_count_acc);
                trace.set(cols.trace_root_err, cur_row, trace_root_err_fe);
                trace.set(cols.constraint_root_err, cur_row, constraint_root_err_fe);
                trace.set(cols.vm_chain_err, cur_row, vm_err);
                trace.set(cols.ram_u_chain_err, cur_row, ram_u_err);
                trace.set(cols.ram_s_chain_err, cur_row, ram_s_err);
                trace.set(cols.rom_chain_err_0, cur_row, rom_err[0]);
                trace.set(cols.rom_chain_err_1, cur_row, rom_err[1]);
                trace.set(cols.rom_chain_err_2, cur_row, rom_err[2]);

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
                trace.set(cols.vm_chain_err, cur_row, vm_err);
                trace.set(cols.ram_u_chain_err, cur_row, ram_u_err);
                trace.set(cols.ram_s_chain_err, cur_row, ram_s_err);
                trace.set(cols.rom_chain_err_0, cur_row, rom_err[0]);
                trace.set(cols.rom_chain_err_1, cur_row, rom_err[1]);
                trace.set(cols.rom_chain_err_2, cur_row, rom_err[2]);

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

        // Update previous-boundary trackers for the next child.
        prev_vm_out = Some(vm_out_fe);
        prev_ram_u_out = Some(ram_u_out_fe);
        prev_ram_s_out = Some(ram_s_out_fe);
        prev_rom_out = Some(rom_out_fe);
    }

    // Padding rows (if any): keep accumulator and chain error
    // scalars constant and disable seg_first, v_units_child and
    let pad_vm_err = BE::ZERO;
    let pad_ram_u_err = BE::ZERO;
    let pad_ram_s_err = BE::ZERO;
    let pad_rom_err_0 = BE::ZERO;
    let pad_rom_err_1 = BE::ZERO;
    let pad_rom_err_2 = BE::ZERO;

    for cur_row in row..n_rows {
        trace.set(cols.seg_first, cur_row, BE::ZERO);
        trace.set(cols.v_units_child, cur_row, BE::ZERO);
        trace.set(cols.v_units_acc, cur_row, v_acc);
        trace.set(cols.child_count_acc, cur_row, child_count_acc);
        trace.set(cols.trace_root_err, cur_row, BE::ZERO);
        trace.set(cols.constraint_root_err, cur_row, BE::ZERO);
        trace.set(cols.vm_chain_err, cur_row, pad_vm_err);
        trace.set(cols.ram_u_chain_err, cur_row, pad_ram_u_err);
        trace.set(cols.ram_s_chain_err, cur_row, pad_ram_s_err);
        trace.set(cols.rom_chain_err_0, cur_row, pad_rom_err_0);
        trace.set(cols.rom_chain_err_1, cur_row, pad_rom_err_1);
        trace.set(cols.rom_chain_err_2, cur_row, pad_rom_err_2);

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

    Ok((AggTrace::new(trace, cols), child_start_rows))
}

/// Aggregate local FRI folding errors along a single FRI query path
/// across all FRI layers and the remainder polynomial for a child
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
            if sample_idx >= positions_next.len() {
                return Err(error::Error::InvalidInput(
                    "sample index out of bounds for remainder positions in compute_fri_path_agg_over_layers",
                ));
            }

            v_remainder_path = vnext;
            pos_remainder = positions_next[sample_idx];
        }

        // Advance domain geometry for
        // the next depth (or remainder).
        domain_generator_d = domain_generator_d.exp_vartime((folding as u32).into());
        domain_size_d = domain_size_next;
        positions_d = positions_next;
    }

    // Final remainder check using Horner evaluation
    // over tx.fri_final.coeffs in the same
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
fn prepare_deep_context<'a>(
    tx: &'a ZlChildTranscript,
    fs: &'a ZlFsChallenges,
) -> error::Result<Option<DeepContext<'a>>> {
    let num_queries = tx.num_queries as usize;
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

    let child = &tx.compact;

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

    let folding = 2usize;

    let positions: Vec<usize> = fs.query_positions.iter().map(|&p| p as usize).collect();
    let folded_positions = fold_positions_usize(&positions, lde_domain_size, folding)?;

    let layer0_vals = tx.fri_layers.first().ok_or(error::Error::InvalidInput(
        "ZlChildTranscript.fri_layers must contain at least one layer when num_queries > 0 in compute_deep_agg_over_queries",
    ))?;

    if folded_positions.is_empty() || layer0_vals.is_empty() {
        return Ok(None);
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

    let domain_size_0 = lde_domain_size;
    let row_length_0 = domain_size_0 / folding;

    if row_length_0 == 0 {
        return Err(error::Error::InvalidInput(
            "FRI row length at depth 0 must be non-zero in compute_deep_agg_over_queries",
        ));
    }

    Ok(Some(DeepContext {
        _child: child,
        trace_width,
        constraint_width,
        lde_domain_size,
        positions,
        folded_positions,
        layer0_vals,
        base_g,
        offset,
        z,
        z_g,
        deep_trace_coeffs,
        deep_constraint_coeffs,
        row_length_0,
        trace_rows: &tx.trace_main_openings,
        constraint_rows: &tx.constraint_openings,
        ood_main_current: &tx.ood_main_current,
        ood_main_next: &tx.ood_main_next,
        ood_quotient_current: &tx.ood_quotient_current,
        ood_quotient_next: &tx.ood_quotient_next,
    }))
}

fn deep_eval_at_position(ctx: &DeepContext<'_>, k: usize) -> error::Result<(BE, BE)> {
    let pos_k = ctx.positions[k];
    if pos_k >= ctx.lde_domain_size {
        return Err(error::Error::InvalidInput(
            "FRI sample position exceeds LDE domain size in compute_deep_agg_over_queries",
        ));
    }

    let x = ctx.base_g.exp_vartime((pos_k as u64).into()) * ctx.offset;

    let x_minus_z = x - ctx.z;
    let x_minus_zg = x - ctx.z_g;

    if x_minus_z == BE::ZERO || x_minus_zg == BE::ZERO {
        return Err(error::Error::InvalidInput(
            "evaluation point x collides with OOD point in compute_deep_agg_over_queries",
        ));
    }

    let inv_x_minus_z = x_minus_z.inv();
    let inv_x_minus_zg = x_minus_zg.inv();

    // Trace contribution
    let mut y_trace = BE::ZERO;
    let row_x = &ctx.trace_rows[k];

    if row_x.len() != ctx.trace_width {
        return Err(error::Error::InvalidInput(
            "ZlChildTranscript.trace_main_openings row width is inconsistent with main_trace_width in compute_deep_agg_over_queries",
        ));
    }

    for (i, &t_x) in row_x.iter().enumerate().take(ctx.trace_width) {
        let coeff = ctx.deep_trace_coeffs[i];
        let t_z = ctx.ood_main_current[i];
        let t_zg = ctx.ood_main_next[i];

        let term_z = (t_x - t_z) * inv_x_minus_z;
        let term_zg = (t_x - t_zg) * inv_x_minus_zg;

        y_trace += coeff * (term_z + term_zg);
    }

    // Constraint composition
    // contribution (if present)
    let mut y_constraints = BE::ZERO;

    if ctx.constraint_width > 0 && !ctx.constraint_rows.is_empty() {
        let row_c = &ctx.constraint_rows[k];
        if row_c.len() != ctx.constraint_width {
            return Err(error::Error::InvalidInput(
                "ZlChildTranscript.constraint_openings row width is inconsistent with constraint_frame_width in compute_deep_agg_over_queries",
            ));
        }

        for (j, &c_x) in row_c.iter().enumerate().take(ctx.constraint_width) {
            let coeff = ctx.deep_constraint_coeffs[j];
            let c_z = ctx.ood_quotient_current[j];
            let c_zg = ctx.ood_quotient_next[j];

            let term_c_z = (c_x - c_z) * inv_x_minus_z;
            let term_c_zg = (c_x - c_zg) * inv_x_minus_zg;

            y_constraints += coeff * (term_c_z + term_c_zg);
        }
    }

    let y_k = y_trace + y_constraints;

    // FRI layer-0 query value q0_k
    // via get_query_values geometry.
    let coset_idx_0 = pos_k % ctx.row_length_0;
    let elem_idx_0 = pos_k / ctx.row_length_0;
    let folding = 2usize;

    if elem_idx_0 >= folding {
        return Err(error::Error::InvalidInput(
            "FRI element index exceeds folding factor at depth 0 in compute_deep_agg_over_queries",
        ));
    }

    let folded_idx_0 = ctx
        .folded_positions
        .iter()
        .position(|&p| p == coset_idx_0)
        .ok_or(error::Error::InvalidInput(
            "FRI sample coset index not found in folded positions at depth 0 in compute_deep_agg_over_queries",
        ))?;

    let pair_0 = ctx.layer0_vals[folded_idx_0];
    let q0_k = pair_0[elem_idx_0];

    Ok((y_k, q0_k))
}

fn compute_deep_agg_over_queries(tx: &ZlChildTranscript, beta: BE) -> error::Result<BE> {
    let num_layers = tx.fri_layers.len();
    let num_queries = tx.num_queries as usize;

    if num_layers == 0 || num_queries == 0 {
        return Ok(BE::ZERO);
    }

    let child = &tx.compact;
    let fs = match &child.fs_challenges {
        Some(fs) => fs,
        None => {
            // Without FS challenges we cannot reconstruct
            // the FRI / DEEP domain geometry; fall back to
            return Ok(BE::ZERO);
        }
    };

    // Prepare shared DEEP context;
    // when folded positions or layer-0
    let ctx = match prepare_deep_context(tx, fs)? {
        Some(ctx) => ctx,
        None => return Ok(BE::ZERO),
    };

    let mut deep_agg = BE::ZERO;
    let mut beta_pow = BE::ONE;

    for k in 0..ctx.positions.len() {
        let (y_k, q0_k) = deep_eval_at_position(&ctx, k)?;
        let e_k = y_k - q0_k;
        deep_agg += beta_pow * e_k;
        beta_pow *= beta;
    }

    Ok(deep_agg)
}

/// Aggregate FRI layer-1 evaluations == query_values
/// errors over all FS query positions for a single
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
    let ctx = match prepare_deep_context(tx, fs)? {
        Some(ctx) => ctx,
        None => {
            return Ok(FriDeepSample {
                v0,
                v1,
                vnext,
                alpha,
                x0,
                x1,
                q1,
                deep_err: BE::ZERO,
            });
        }
    };

    let (deep_val, q0) = deep_eval_at_position(&ctx, sample_idx)?;
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

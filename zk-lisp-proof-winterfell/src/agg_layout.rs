// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Column layout for the STARK-in-STARK aggregation trace.
//!
//! `AggColumns` defines indices for all columns used by the
//! ZlAggAir aggregator. The initial implementation focuses
//! on per-child work aggregation and reserves slots for
//! future Merkle/FRI and composition accumulators.

#[derive(Clone, Copy, Debug)]
pub struct AggColumns {
    /// Aggregated composition error. This column
    /// must be identically zero for a valid trace.
    pub ok: usize,

    /// Accumulator of FRI layer-0 v0 values.
    pub v0_sum: usize,
    /// Accumulator of FRI layer-0 v1 values.
    pub v1_sum: usize,
    /// Accumulator of v_next = v0 + r * v1.
    pub vnext_sum: usize,

    /// Per-child FRI layer-0 v0 contribution,
    /// non-zero only on rows where `seg_first == 1`.
    pub fri_v0_child: usize,
    /// Per-child FRI layer-0 v1 contribution,
    /// non-zero only on rows where `seg_first == 1`.
    pub fri_v1_child: usize,
    /// Per-child FRI layer-0 v_next contribution,
    /// non-zero only on rows where `seg_first == 1`.
    pub fri_vnext_child: usize,

    /// Aggregated AIR composition value.
    pub comp_sum: usize,
    /// Aggregated alpha-part divided by Z_m.
    pub alpha_div_zm_sum: usize,
    /// Aggregated map * L0 component.
    pub map_l0_sum: usize,
    /// Aggregated final * L_last component.
    pub final_llast_sum: usize,

    /// Fiat–Shamir challenges, constant per child
    /// segment. The initial aggregator skeleton does
    /// not yet enforce their consistency.
    pub r: usize,
    pub alpha: usize,
    pub beta: usize,
    pub gamma: usize,

    /// Segment-first flag: 1 at the first row of each
    /// child segment, 0 elsewhere.
    pub seg_first: usize,

    /// Trace Merkle root mismatch accumulator.
    pub trace_root_err: usize,
    /// FRI Merkle root mismatch accumulator.
    pub fri_root_err: usize,

    /// Global accumulator over per-child work units.
    pub v_units_acc: usize,
    /// Per-child work units, constant on rows where
    /// `seg_first == 1`, zero elsewhere.
    pub v_units_child: usize,

    width: usize,
}

impl AggColumns {
    /// Baseline layout for the aggregator trace.
    #[inline]
    pub const fn baseline() -> Self {
        // Keep columns densely packed starting
        // from zero to simplify reasoning about
        // width and offsets.
        let ok = 0;
        let v0_sum = ok + 1;
        let v1_sum = v0_sum + 1;
        let vnext_sum = v1_sum + 1;

        let fri_v0_child = vnext_sum + 1;
        let fri_v1_child = fri_v0_child + 1;
        let fri_vnext_child = fri_v1_child + 1;

        let comp_sum = fri_vnext_child + 1;
        let alpha_div_zm_sum = comp_sum + 1;
        let map_l0_sum = alpha_div_zm_sum + 1;
        let final_llast_sum = map_l0_sum + 1;

        let r = final_llast_sum + 1;
        let alpha = r + 1;
        let beta = alpha + 1;
        let gamma = beta + 1;

        let seg_first = gamma + 1;

        let trace_root_err = seg_first + 1;
        let fri_root_err = trace_root_err + 1;

        let v_units_acc = fri_root_err + 1;
        let v_units_child = v_units_acc + 1;

        let width = v_units_child + 1;

        Self {
            ok,
            v0_sum,
            v1_sum,
            vnext_sum,
            fri_v0_child,
            fri_v1_child,
            fri_vnext_child,
            comp_sum,
            alpha_div_zm_sum,
            map_l0_sum,
            final_llast_sum,
            r,
            alpha,
            beta,
            gamma,
            seg_first,
            trace_root_err,
            fri_root_err,
            v_units_acc,
            v_units_child,
            width,
        }
    }

    #[inline]
    pub const fn width(&self) -> usize {
        self.width
    }
}

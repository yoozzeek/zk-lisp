// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Aggregation AIR for STARK-in-STARK recursion.
//!
//! The initial `ZlAggAir` implementation focuses on a minimal,
//! well-typed skeleton: it defines a column layout and enforces a
//! global accumulator over per-child work units (`v_units`). Further
//! iterations will extend this AIR with full composition, Merkle and
//! FRI checks over compact child proofs.

use crate::agg_layout::AggColumns;
use crate::utils;

use winterfell::math::fft;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::math::{FieldElement, ToElements};
use winterfell::{
    Air, AirContext, Assertion, EvaluationFrame, ProofOptions, TraceInfo,
    TransitionConstraintDegree,
};

/// Public inputs for the aggregation AIR.
///
/// At the logical level these inputs expose the
/// children aggregation root and a global STARK
/// profile shared by all children (see AGG_SPEC.md
/// for the high-level protocol). In the current
/// implementation we also keep a few helper fields
/// (`suite_id`, `children_ms`) used by the trace
/// builder; these may be removed or folded into
/// `batch_id` in future revisions.
#[derive(Clone, Debug)]
pub struct AggAirPublicInputs {
    /// Canonical aggregation root over compact
    /// children as defined in AGG_SPEC §2.1.
    pub children_root: [u8; 32],

    /// Global sum of child work units; the
    /// aggregator AIR enforces that the work
    /// accumulator equals this value on the
    /// last row.
    pub v_units_total: u64,

    /// Number of children in the batch.
    pub children_count: u32,

    /// Aggregation batch identifier (optional
    /// from protocol perspective). This can
    /// be used to tie the aggregation instance
    /// to a particular higher-level protocol
    /// state or program set.
    pub batch_id: [u8; 32],

    /// Global zk-lisp STARK profile that all
    /// children are expected to share.
    pub profile_meta: AggProfileMeta,

    /// Global FRI profile shared by all children.
    pub profile_fri: AggFriProfile,

    /// Global FS query / PoW profile.
    pub profile_queries: AggQueryProfile,

    /// Helper field used by the current
    /// aggregation trace builder to check
    /// suite-id consistency and recompute
    /// `children_root`. This is not encoded
    /// directly into the public elements and
    /// may be removed once batch_id fully
    /// covers protocol binding.
    pub suite_id: [u8; 32],

    /// Helper field used by the trace builder
    /// to enforce shape invariants between
    /// public inputs and individual children.
    /// This will likely be phased out once
    /// the global profile constraints are in
    /// place.
    pub children_ms: Vec<u32>,
}

/// Global zk-lisp STARK profile shared by all
/// children in a batch. For now this simply
/// mirrors `StepMeta` but is not yet enforced
/// by `ZlAggAir`; the enforcement logic will
/// be added incrementally.
#[derive(Clone, Debug, Default)]
pub struct AggProfileMeta {
    pub m: u32,
    pub rho: u16,
    pub q: u16,
    pub o: u16,
    pub lambda: u16,
    pub pi_len: u32,
    pub v_units: u64,
}

/// Global FRI profile used by all
/// children in the aggregation.
#[derive(Clone, Debug, Default)]
pub struct AggFriProfile {
    pub lde_blowup: u32,
    pub folding_factor: u8,
    pub redundancy: u8,
    pub num_layers: u8,
}

/// Global query / PoW profile
/// shared by all children.
#[derive(Clone, Debug, Default)]
pub struct AggQueryProfile {
    pub num_queries: u16,
    pub grinding_factor: u32,
}

impl ToElements<BE> for AggAirPublicInputs {
    fn to_elements(&self) -> Vec<BE> {
        let mut out = Vec::new();
        out.push(utils::fold_bytes32_to_fe(&self.children_root));
        out.push(utils::fold_bytes32_to_fe(&self.batch_id));

        out.push(BE::from(self.profile_meta.m));
        out.push(BE::from(self.profile_meta.rho as u64));
        out.push(BE::from(self.profile_meta.q as u64));
        out.push(BE::from(self.profile_meta.o as u64));
        out.push(BE::from(self.profile_meta.lambda as u64));
        out.push(BE::from(self.profile_meta.pi_len));
        out.push(BE::from(self.profile_meta.v_units));

        out.push(BE::from(self.profile_fri.lde_blowup));
        out.push(BE::from(self.profile_fri.folding_factor as u64));
        out.push(BE::from(self.profile_fri.redundancy as u64));
        out.push(BE::from(self.profile_fri.num_layers as u64));

        out.push(BE::from(self.profile_queries.num_queries as u64));
        out.push(BE::from(self.profile_queries.grinding_factor));

        out.push(BE::from(self.children_count as u64));
        out.push(BE::from(self.v_units_total));

        out
    }
}

#[derive(Clone)]
pub struct ZlAggAir {
    ctx: AirContext<BE>,
    cols: AggColumns,
    v_units_total_fe: BE,
    children_count_fe: BE,
}

impl Air for ZlAggAir {
    type BaseField = BE;
    type PublicInputs = AggAirPublicInputs;

    fn new(info: TraceInfo, pub_inputs: Self::PublicInputs, options: ProofOptions) -> Self {
        let cols = AggColumns::baseline();
        assert_eq!(
            info.width(),
            cols.width(),
            "AggTrace width must match AggColumns layout",
        );

        let trace_len = info.length();
        assert!(trace_len > 0, "AggTrace must contain at least one row");

        // We currently expose twelve constraints:
        // C0: ok == 0 on all rows;
        // C1: work accumulator chain gated to non-last rows.
        // C2: trace_root_err must be zero on all rows.
        // C3: fri_root_err must be zero on all rows.
        // C4–C7: FS challenges (r, alpha, beta, gamma) are constant
        //        across the trace (and thus per segment).
        // C8–C10: FRI layer-0 accumulators v0_sum, v1_sum and
        //         vnext_sum form a gated chain over child segments.
        // C11: child_count_acc chain gated to non-last rows.
        let degrees = vec![
            TransitionConstraintDegree::new(1),
            TransitionConstraintDegree::with_cycles(2, vec![trace_len]),
            TransitionConstraintDegree::new(1),
            TransitionConstraintDegree::new(1),
            TransitionConstraintDegree::new(1),
            TransitionConstraintDegree::new(1),
            TransitionConstraintDegree::new(1),
            TransitionConstraintDegree::new(1),
            TransitionConstraintDegree::new(1),
            TransitionConstraintDegree::new(1),
            TransitionConstraintDegree::new(1),
            TransitionConstraintDegree::with_cycles(1, vec![trace_len]),
        ];

        // ok[0], v_units_acc[0], v_units_acc[last],
        // child_count_acc[0], child_count_acc[last].
        let num_assertions = 5;
        let v_units_total_fe = BE::from(pub_inputs.v_units_total);
        let children_count_fe = BE::from(pub_inputs.children_count as u64);
        let ctx = AirContext::new(info, degrees, num_assertions, options);

        Self {
            ctx,
            cols,
            v_units_total_fe,
            children_count_fe,
        }
    }

    fn context(&self) -> &AirContext<Self::BaseField> {
        &self.ctx
    }

    fn evaluate_transition<E>(
        &self,
        frame: &EvaluationFrame<E>,
        periodic_values: &[E],
        result: &mut [E],
    ) where
        E: FieldElement<BaseField = Self::BaseField> + From<Self::BaseField>,
    {
        debug_assert_eq!(result.len(), 12);
        debug_assert_eq!(periodic_values.len(), 1);

        let cols = &self.cols;
        let current = frame.current();
        let next = frame.next();

        let ok = current[cols.ok];
        let v_acc = current[cols.v_units_acc];
        let v_acc_next = next[cols.v_units_acc];
        let v_child = current[cols.v_units_child];
        let seg_first = current[cols.seg_first];
        let trace_root_err = current[cols.trace_root_err];
        let fri_root_err = current[cols.fri_root_err];
        let child_count_acc = current[cols.child_count_acc];
        let child_count_acc_next = next[cols.child_count_acc];

        let r = current[cols.r];
        let r_next = next[cols.r];
        let alpha = current[cols.alpha];
        let alpha_next = next[cols.alpha];
        let beta = current[cols.beta];
        let beta_next = next[cols.beta];
        let gamma = current[cols.gamma];
        let gamma_next = next[cols.gamma];

        let v0_sum = current[cols.v0_sum];
        let v0_sum_next = next[cols.v0_sum];
        let v1_sum = current[cols.v1_sum];
        let v1_sum_next = next[cols.v1_sum];
        let vnext_sum = current[cols.vnext_sum];
        let vnext_sum_next = next[cols.vnext_sum];

        let fri_v0_child = current[cols.fri_v0_child];
        let fri_v1_child = current[cols.fri_v1_child];
        let fri_vnext_child = current[cols.fri_vnext_child];

        let is_last = periodic_values[0];
        let not_last = E::ONE - is_last;

        // C0: ok must stay zero on all rows.
        result[0] = ok;

        // C1: work accumulator chain gated to non-last rows.
        // When seg_first == 1 (first row of a child segment),
        // v_units_acc is incremented by v_units_child; otherwise
        // it stays constant. We do not enforce the relation on
        // the last row to avoid an artificial wrap-around to
        // the first row induced by the evaluation domain.
        result[1] = not_last * (v_acc_next - (v_acc + v_child * seg_first));

        // C2: trace-root error column must be identically zero.
        // The trace builder populates this column with
        // `expected_root - actual_root` on the first row of
        // each child segment and zeros elsewhere.
        result[2] = trace_root_err;

        // C3: FRI-root error column must also be identically
        // zero. Once FRI Merkle paths are wired, the trace
        // builder will populate this column with
        // `expected_root - actual_root` on segment boundaries.
        result[3] = fri_root_err;

        // C4–C7: FS challenges must be constant across the
        // trace (and thus per child segment).
        result[4] = not_last * (r_next - r);
        result[5] = not_last * (alpha_next - alpha);
        result[6] = not_last * (beta_next - beta);
        result[7] = not_last * (gamma_next - gamma);

        // C8–C10: FRI layer-0 accumulators follow a gated
        // chain over child segments. In the current skeleton
        // fri_v*_child are zero, so the sums stay constant.
        result[8] = not_last * (v0_sum_next - (v0_sum + fri_v0_child * seg_first));
        result[9] = not_last * (v1_sum_next - (v1_sum + fri_v1_child * seg_first));
        result[10] = not_last * (vnext_sum_next - (vnext_sum + fri_vnext_child * seg_first));

        // C11: child_count_acc increments by 1 on
        // segment starts and stays constant otherwise.
        result[11] = not_last * (child_count_acc_next - (child_count_acc + seg_first));
    }

    fn get_assertions(&self) -> Vec<Assertion<Self::BaseField>> {
        let mut out = Vec::with_capacity(5);
        let last = self.ctx.trace_len().saturating_sub(1);

        // ok[0] == 0
        out.push(Assertion::single(self.cols.ok, 0, BE::ZERO));

        // v_units_acc[0] == 0
        out.push(Assertion::single(self.cols.v_units_acc, 0, BE::ZERO));

        // v_units_acc[last] == v_units_total
        out.push(Assertion::single(
            self.cols.v_units_acc,
            last,
            self.v_units_total_fe,
        ));

        // child_count_acc[0] == 0
        out.push(Assertion::single(self.cols.child_count_acc, 0, BE::ZERO));

        // child_count_acc[last] == children_count
        out.push(Assertion::single(
            self.cols.child_count_acc,
            last,
            self.children_count_fe,
        ));

        out
    }

    fn get_periodic_column_values(&self) -> Vec<Vec<Self::BaseField>> {
        let n = self.ctx.trace_len();
        let mut p_last = vec![BE::ZERO; n];

        if n > 0 {
            p_last[n - 1] = BE::ONE;
        }

        vec![p_last]
    }

    fn get_periodic_column_polys(&self) -> Vec<Vec<Self::BaseField>> {
        let n = self.ctx.trace_len();
        let mut p_last = vec![BE::ZERO; n];

        if n > 0 {
            p_last[n - 1] = BE::ONE;
        }

        if n > 0 {
            let inv_twiddles = fft::get_inv_twiddles::<BE>(n);
            fft::interpolate_poly(&mut p_last, &inv_twiddles);
        }

        vec![p_last]
    }
}

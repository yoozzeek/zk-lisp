// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Aggregation AIR for STARK-in-STARK recursion.

use crate::agg::layout::AggColumns;
use crate::agg::pi::AggAirPublicInputs;

use winterfell::math::FieldElement;
use winterfell::math::fft;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::{
    Air, AirContext, Assertion, EvaluationFrame, ProofOptions, TraceInfo,
    TransitionConstraintDegree,
};

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

        // We currently expose 23 constraints:
        // C0: ok == 0 on all rows;
        // C1: work accumulator chain gated to non-last rows.
        // C2: trace_root_err must be zero on all rows.
        // C3: constraint_root_err must be zero on all rows.
        // C4–C7: FS challenges (r, alpha, beta, gamma) are constant
        //        across the trace (and thus per segment).
        // C8–C10: FRI layer-0 accumulators v0_sum, v1_sum and
        //         vnext_sum form a gated chain over child segments.
        // C11: child_count_acc chain gated to non-last rows.
        // C12: minimal on-circuit FRI-folding check for a
        //      per-child binary FRI sample.
        // C13: FRI layer-1 evaluations == query_values sample.
        // C14: DEEP composition vs FRI layer-0 sample.
        // C15: aggregated FRI layer-1 evaluations == query_values
        //      error over all query positions.
        // C16: local FRI path folding and remainder consistency
        //      across all layers for a single query path.
        // C17: global FRI paths folding and remainder consistency
        //      aggregated over all query paths.
        // ...
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
            TransitionConstraintDegree::new(1), // C12
            TransitionConstraintDegree::new(1), // C13
            TransitionConstraintDegree::new(1), // C14
            TransitionConstraintDegree::new(1), // C15
            TransitionConstraintDegree::new(1), // C16
            TransitionConstraintDegree::new(1), // C17
            TransitionConstraintDegree::new(1), // C18
            TransitionConstraintDegree::new(1), // C19
            TransitionConstraintDegree::new(1), // C20
            TransitionConstraintDegree::new(1), // C21
            TransitionConstraintDegree::new(1), // C22
            TransitionConstraintDegree::new(1), // C23
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
        debug_assert_eq!(result.len(), 24);
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
        let constraint_root_err = current[cols.constraint_root_err];
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
        let fri_alpha_child = current[cols.fri_alpha_child];
        let fri_x0_child = current[cols.fri_x0_child];
        let fri_x1_child = current[cols.fri_x1_child];
        let fri_q1_child = current[cols.fri_q1_child];

        let comp_sum = current[cols.comp_sum];
        let fri_layer1_agg = current[cols.alpha_div_zm_sum];
        let fri_path_agg = current[cols.map_l0_sum];
        let fri_paths_agg = current[cols.final_llast_sum];

        let vm_chain_err = current[cols.vm_chain_err];
        let ram_u_chain_err = current[cols.ram_u_chain_err];
        let ram_s_chain_err = current[cols.ram_s_chain_err];
        let rom_chain_err_0 = current[cols.rom_chain_err_0];
        let rom_chain_err_1 = current[cols.rom_chain_err_1];
        let rom_chain_err_2 = current[cols.rom_chain_err_2];

        let is_last = periodic_values[0];
        let not_last = E::ONE - is_last;

        // C0: ok must stay zero on all rows.
        result[0] = ok;

        // C1: work accumulator chain gated to non-last rows.
        // When seg_first == 1 (first row of a child segment),
        // v_units_acc is incremented by v_units_child; otherwise
        // it stays constant.
        result[1] = not_last * (v_acc_next - (v_acc + v_child * seg_first));

        // C2: trace-root error column must be identically zero.
        // The trace builder populates this column with
        // `expected_root - actual_root` on the first row of
        // each child segment and zeros elsewhere.
        result[2] = trace_root_err;

        // C3: constraint-root error column must also be
        // identically zero. The trace builder populates this
        // column with an aggregated difference between the
        // advertised constraint commitment root and roots
        // reconstructed from Merkle paths at all query
        // positions.
        result[3] = constraint_root_err;

        // C4–C7: FS challenges must be constant across the
        // trace (and thus per child segment).
        result[4] = not_last * (r_next - r);
        result[5] = not_last * (alpha_next - alpha);
        result[6] = not_last * (beta_next - beta);
        result[7] = not_last * (gamma_next - gamma);

        // C8–C10: FRI accumulators are currently kept constant
        // across the trace; they are reserved for future use in
        // DEEP/FRI composition checks. For now enforce
        // that v*_sum do not change between consecutive rows.
        result[8] = not_last * (v0_sum_next - v0_sum);
        result[9] = not_last * (v1_sum_next - v1_sum);
        result[10] = not_last * (vnext_sum_next - vnext_sum);

        // C11: child_count_acc increments by 1 on
        // segment starts and stays constant otherwise.
        result[11] = not_last * (child_count_acc_next - (child_count_acc + seg_first));

        // C12: minimal on-circuit FRI-folding constraint
        // for a single binary FRI sample per child. On
        // rows where fri_*_child are zero this vanishes
        // automatically; on segment-first rows the trace
        // builder populates (v0, v1, vnext, alpha, x0, x1)
        // so that they satisfy the binary folding relation:
        // (x1 - x0) * vnext == v1 * (alpha - x0) - v0 * (alpha - x1).
        let x_diff = fri_x1_child - fri_x0_child;
        let lhs = fri_vnext_child * x_diff;
        let rhs = fri_v1_child * (fri_alpha_child - fri_x0_child)
            - fri_v0_child * (fri_alpha_child - fri_x1_child);
        result[12] = lhs - rhs;

        // C13: FRI layer-1 evaluations == query_values
        // sample. The trace builder wires vnext_child
        // as the evaluation obtained by folding the
        // first-layer coset, and fri_q1_child as the
        // corresponding value read from fri_layers[1]
        // via get_query_values semantics.
        result[13] = fri_vnext_child - fri_q1_child;

        // C14: DEEP composition vs FRI layer-0 sample.
        // We aggregate DEEP vs FRI layer-0 errors across all
        // query positions for each child and wire the result
        // into comp_sum on segment-first rows. This must be
        // identically zero across the trace.
        result[14] = comp_sum;

        // C15: aggregated FRI layer-1 evaluations == query_values
        // error over all query positions. The trace builder populates
        // alpha_div_zm_sum with this aggregate on segment-first rows
        // and zeros elsewhere; must be zero across the trace.
        result[15] = fri_layer1_agg;

        // C16: local FRI path folding and remainder consistency
        // across all FRI layers for a single query path. The
        // trace builder wires the aggregate error into map_l0_sum
        // on segment-first rows and zeros elsewhere;
        // must be identically zero across the trace.
        result[16] = fri_path_agg;

        // C17: global FRI paths folding and remainder consistency
        // aggregated over all query paths. The trace builder wires
        // this scalar into final_llast_sum on segment-first rows and
        // zeros elsewhere; must be identically zero across the trace.
        result[17] = fri_paths_agg;

        // C18–C23: global VM / RAM / ROM boundary chain
        // errors are wired directly into dedicated columns
        result[18] = vm_chain_err;
        result[19] = ram_u_chain_err;
        result[20] = ram_s_chain_err;
        result[21] = rom_chain_err_0;
        result[22] = rom_chain_err_1;
        result[23] = rom_chain_err_2;
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

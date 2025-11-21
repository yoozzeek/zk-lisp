// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Aggregation AIR for STARK-in-STARK recursion.

use crate::agg::child::{ZlChildCompact, ZlChildTranscript, children_root_from_compact};
use crate::agg::layout::AggColumns;
use crate::proof::step::StepProof;
use crate::utils;

use winterfell::math::fft;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::math::{FieldElement, ToElements};
use winterfell::{
    Air, AirContext, Assertion, EvaluationFrame, ProofOptions, TraceInfo,
    TransitionConstraintDegree,
};
use zk_lisp_proof::error;

/// Public inputs for the aggregation AIR.
///
#[derive(Clone, Debug)]
pub struct AggAirPublicInputs {
    /// Program identity and public-input digest
    /// (program + public main args) proved by the
    /// underlying step proofs.
    pub program_id: [u8; 32],
    pub program_commitment: [u8; 32],
    pub pi_digest: [u8; 32],

    /// Canonical aggregation root over compact
    /// children as defined in AGG_SPEC §2.1.
    pub children_root: [u8; 32],

    /// Global sum of child work units; the
    /// aggregator AIR enforces that the work
    pub v_units_total: u64,

    /// Number of children in the batch.
    pub children_count: u32,

    /// Aggregation batch identifier (optional
    /// from protocol perspective). This can
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
    pub suite_id: [u8; 32],

    /// Helper field used by the trace builder
    /// to enforce shape invariants between
    /// public inputs and individual children.
    /// This will likely be phased out once
    /// the global profile constraints are in
    /// place.
    pub children_ms: Vec<u32>,

    /// Global VM state at the beginning and end
    /// of the aggregated prefix (including all
    pub vm_state_initial: [u8; 32],
    pub vm_state_final: [u8; 32],

    /// Global RAM grand-product accumulators for
    /// unsorted and sorted RAM tables at the
    pub ram_gp_unsorted_initial: [u8; 32],
    pub ram_gp_unsorted_final: [u8; 32],
    pub ram_gp_sorted_initial: [u8; 32],
    pub ram_gp_sorted_final: [u8; 32],

    /// Global ROM t=3 accumulator state at the
    /// beginning and end of the aggregated prefix.
    pub rom_s_initial: [[u8; 32]; 3],
    pub rom_s_final: [[u8; 32]; 3],
}

/// Global zk-lisp STARK profile shared by all
/// children in a batch. For now this simply
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

impl AggAirPublicInputs {
    /// Build aggregation public inputs for a single zk-lisp
    /// step proof by deriving a compact child view and child
    pub fn from_step_proof(step: &StepProof) -> error::Result<Self> {
        let compact = ZlChildCompact::from_step(step)?;
        let transcript = ZlChildTranscript::from_step(step)?;

        let core_pi = &compact.pi_core;
        let pi_digest = core_pi.digest();

        let children = vec![compact.clone()];
        let children_root = children_root_from_compact(&compact.suite_id, &children);

        let profile_meta = AggProfileMeta {
            m: compact.meta.m,
            rho: compact.meta.rho,
            q: compact.meta.q,
            o: compact.meta.o,
            lambda: compact.meta.lambda,
            pi_len: compact.meta.pi_len,
            v_units: compact.meta.v_units,
        };

        let profile_fri = AggFriProfile {
            lde_blowup: compact.meta.rho as u32,
            folding_factor: 2,
            redundancy: 1,
            num_layers: transcript.fri_layers.len() as u8,
        };

        let profile_queries = AggQueryProfile {
            num_queries: compact.meta.q,
            grinding_factor: 0,
        };

        Ok(AggAirPublicInputs {
            program_id: core_pi.program_id,
            program_commitment: core_pi.program_commitment,
            pi_digest,
            children_root,
            v_units_total: compact.meta.v_units,
            children_count: 1,
            batch_id: [0u8; 32],
            profile_meta,
            profile_fri,
            profile_queries,
            suite_id: compact.suite_id,
            children_ms: vec![compact.meta.m],
            vm_state_initial: compact.state_in_hash,
            vm_state_final: compact.state_out_hash,
            ram_gp_unsorted_initial: compact.ram_gp_unsorted_in,
            ram_gp_unsorted_final: compact.ram_gp_unsorted_out,
            ram_gp_sorted_initial: compact.ram_gp_sorted_in,
            ram_gp_sorted_final: compact.ram_gp_sorted_out,
            rom_s_initial: compact.rom_s_in,
            rom_s_final: compact.rom_s_out,
        })
    }
}

impl ToElements<BE> for AggAirPublicInputs {
    fn to_elements(&self) -> Vec<BE> {
        let mut out = Vec::with_capacity(32);

        out.push(utils::fold_bytes32_to_fe(&self.program_id));
        out.push(utils::fold_bytes32_to_fe(&self.program_commitment));
        out.push(utils::fold_bytes32_to_fe(&self.pi_digest));
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

        // Fold global boundary bytes into field elements as
        // part of the aggregation FS seed so that any change
        out.push(utils::fold_bytes32_to_fe(&self.vm_state_initial));
        out.push(utils::fold_bytes32_to_fe(&self.vm_state_final));
        out.push(utils::fold_bytes32_to_fe(&self.ram_gp_unsorted_initial));
        out.push(utils::fold_bytes32_to_fe(&self.ram_gp_unsorted_final));
        out.push(utils::fold_bytes32_to_fe(&self.ram_gp_sorted_initial));
        out.push(utils::fold_bytes32_to_fe(&self.ram_gp_sorted_final));

        for lane in &self.rom_s_initial {
            out.push(utils::fold_bytes32_to_fe(lane));
        }
        for lane in &self.rom_s_final {
            out.push(utils::fold_bytes32_to_fe(lane));
        }

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

        // We currently expose twenty-four constraints:
        // C0: ok == 0 on all rows;
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
        result[1] = not_last * (v_acc_next - (v_acc + v_child * seg_first));

        // C2: trace-root error column must be identically zero.
        // The trace builder populates this column with
        result[2] = trace_root_err;

        // C3: constraint-root error column must also be
        // identically zero. The trace builder populates this
        result[3] = constraint_root_err;

        // C4–C7: FS challenges must be constant across the
        // trace (and thus per child segment).
        result[4] = not_last * (r_next - r);
        result[5] = not_last * (alpha_next - alpha);
        result[6] = not_last * (beta_next - beta);
        result[7] = not_last * (gamma_next - gamma);

        // C8–C10: FRI accumulators are currently kept constant
        // across the trace; they are reserved for future use in
        result[8] = not_last * (v0_sum_next - v0_sum);
        result[9] = not_last * (v1_sum_next - v1_sum);
        result[10] = not_last * (vnext_sum_next - vnext_sum);

        // C11: child_count_acc increments by 1 on
        // segment starts and stays constant otherwise.
        result[11] = not_last * (child_count_acc_next - (child_count_acc + seg_first));

        // C12: minimal on-circuit FRI-folding constraint
        // for a single binary FRI sample per child. On
        let x_diff = fri_x1_child - fri_x0_child;
        let lhs = fri_vnext_child * x_diff;
        let rhs = fri_v1_child * (fri_alpha_child - fri_x0_child)
            - fri_v0_child * (fri_alpha_child - fri_x1_child);
        result[12] = lhs - rhs;

        // C13: FRI layer-1 evaluations == query_values
        // sample. The trace builder wires vnext_child
        result[13] = fri_vnext_child - fri_q1_child;

        // C14: DEEP composition vs FRI layer-0 sample.
        // We aggregate DEEP vs FRI layer-0 errors across all
        result[14] = comp_sum;

        // C15: aggregated FRI layer-1 evaluations == query_values
        // error over all query positions. The trace builder populates
        result[15] = fri_layer1_agg;

        // C16: local FRI path folding and remainder consistency
        // across all FRI layers for a single query path. The
        result[16] = fri_path_agg;

        // C17: global FRI paths folding and remainder consistency
        // aggregated over all query paths. The trace builder wires
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

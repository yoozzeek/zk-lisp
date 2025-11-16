// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! AIR for the IVC aggregation layer.
//!
//! This AIR enforces a chain over hashed VM
//! states and an execution-root binding:
//! - the first row's `state_in` matches `state_initial`;
//! - for all non-last rows, `state_in(next) == state_out`;
//! - the last row's `state_out` matches `state_final`;
//! - the execution root is constant across the trace;
//! - aggregated work units match `v_units_total`.
//!
//! The actual hashing of step proofs into digests and
//! advanced recursion logic are handled outside and will
//! be wired in future iterations.

use crate::ivc_layout::IvColumns;
use crate::utils;

use winterfell::math::fft;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::math::{FieldElement, ToElements};
use winterfell::{
    Air, AirContext, Assertion, EvaluationFrame, ProofOptions, TraceInfo,
    TransitionConstraintDegree,
};
use zk_lisp_proof::ivc::{ExecRoot, IvPublic};

/// Public inputs visible to the IVC AIR.
#[derive(Clone, Debug)]
pub struct IvAirPublicInputs {
    pub suite_id: [u8; 32],
    pub prev_iv_digest: [u8; 32],
    pub state_initial: [u8; 32],
    pub state_final: [u8; 32],
    pub exec_root: ExecRoot,
    pub v_units_total: u64,
    /// Number of child step proofs aggregated
    /// in this IVC step. This is used to model
    /// the effective degree of the state-chain
    /// constraint.
    pub steps_count: u32,
}

impl ToElements<BE> for IvAirPublicInputs {
    fn to_elements(&self) -> Vec<BE> {
        vec![
            utils::be_from_le8(&self.suite_id),
            utils::fold_bytes32_to_fe(&self.prev_iv_digest),
            utils::fold_bytes32_to_fe(&self.state_initial),
            utils::fold_bytes32_to_fe(&self.state_final),
            utils::fold_bytes32_to_fe(&self.exec_root),
            BE::from(self.v_units_total),
            BE::from(self.steps_count),
        ]
    }
}

impl From<&IvPublic> for IvAirPublicInputs {
    fn from(p: &IvPublic) -> Self {
        Self {
            suite_id: p.suite_id,
            prev_iv_digest: p.prev_iv_digest,
            state_initial: p.state_initial,
            state_final: p.state_final,
            exec_root: p.exec_root,
            v_units_total: p.v_units_total,
            steps_count: p.steps_count,
        }
    }
}

#[derive(Clone)]
pub struct ZlIvAir {
    ctx: AirContext<BE>,
    cols: IvColumns,
    state_initial_fe: BE,
    state_final_fe: BE,
    exec_root_fe: BE,
    v_units_total_fe: BE,
}

impl Air for ZlIvAir {
    type BaseField = BE;
    type PublicInputs = IvAirPublicInputs;

    fn new(info: TraceInfo, pub_inputs: Self::PublicInputs, options: ProofOptions) -> Self {
        let cols = IvColumns::baseline();
        assert_eq!(
            info.width(),
            cols.width(),
            "IvTrace width must match IvColumns layout",
        );

        let trace_len = info.length();
        assert!(trace_len > 0, "IvTrace must contain at least one row");

        // State-chain constraint behaves differently
        // in degenerate cases where the aggregated segment
        // is a single child step and the initial and final
        // VM states are identical. In this case, the constraint
        // polynomial collapses to a constant (zero) after
        // dividing by the transition divisor, and Winterfell
        // will observe degree 0 even though we gate it with
        // a periodic last-row selector.
        let trivial_state_chain =
            pub_inputs.steps_count == 1 && pub_inputs.state_initial == pub_inputs.state_final;
        let deg_state_chain = if trivial_state_chain {
            TransitionConstraintDegree::new(1)
        } else {
            TransitionConstraintDegree::with_cycles(1, vec![trace_len])
        };

        let degrees = vec![
            // C0: per-row root consistency
            TransitionConstraintDegree::new(1),
            // C1: VM state chain
            deg_state_chain,
            // C2: execution-root chain
            TransitionConstraintDegree::new(1),
            // C3: work accumulator chain
            TransitionConstraintDegree::with_cycles(1, vec![trace_len]),
        ];

        let num_assertions = 5;

        let state_initial_fe = utils::fold_bytes32_to_fe(&pub_inputs.state_initial);
        let state_final_fe = utils::fold_bytes32_to_fe(&pub_inputs.state_final);
        let exec_root_fe = utils::fold_bytes32_to_fe(&pub_inputs.exec_root);
        let v_units_total_fe = BE::from(pub_inputs.v_units_total);

        let ctx = AirContext::new(info, degrees, num_assertions, options);

        Self {
            ctx,
            cols,
            state_initial_fe,
            state_final_fe,
            exec_root_fe,
            v_units_total_fe,
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
        debug_assert_eq!(result.len(), 4);

        let cols = &self.cols;
        let current = frame.current();
        let next = frame.next();

        let state_out = current[cols.state_out];
        let root_in = current[cols.root_in];
        let root_out = current[cols.root_out];
        let v_acc = current[cols.v_units_acc];
        let v_units = current[cols.v_units];

        let state_in_next = next[cols.state_in];
        let root_in_next = next[cols.root_in];
        let v_acc_next = next[cols.v_units_acc];

        let is_last = periodic_values[0];
        let not_last = E::ONE - is_last;

        // C0: per-row root consistency.
        result[0] = root_out - root_in;
        // C1: VM state chain across rows.
        result[1] = not_last * (state_in_next - state_out);
        // C2: execution-root chain across rows.
        result[2] = not_last * (root_in_next - root_in);
        // C3: work accumulator chain across rows.
        result[3] = not_last * (v_acc_next - (v_acc + v_units));
    }

    fn get_assertions(&self) -> Vec<Assertion<Self::BaseField>> {
        let mut out = Vec::with_capacity(5);
        let last = self.ctx.trace_len().saturating_sub(1);

        out.push(Assertion::single(
            self.cols.state_in,
            0,
            self.state_initial_fe,
        ));
        out.push(Assertion::single(self.cols.root_in, 0, self.exec_root_fe));
        out.push(Assertion::single(self.cols.v_units_acc, 0, BE::ZERO));

        out.push(Assertion::single(
            self.cols.state_out,
            last,
            self.state_final_fe,
        ));
        out.push(Assertion::single(
            self.cols.v_units_acc,
            last,
            self.v_units_total_fe,
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

// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Trace builder for the IVC aggregation AIR.
//!
//! The current trace keeps a minimal set of columns
//! needed to express a simple chain from `state_initial`
//! to `state_final` over folded step digests and to
//! bind them to a public execution root.

use crate::ivc_layout::IvColumns;
use crate::utils;
use crate::zl_ivc;
use crate::zl_step::ZlStepProof;

use rayon::prelude::*;
use winterfell::TraceTable;
use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;
use zk_lisp_proof::error;
use zk_lisp_proof::ivc::{ExecRoot, IvPublic, StepDigest};

/// Helper structure bundling an IVC trace with its layout.
#[derive(Debug)]
pub struct IvTrace {
    pub trace: TraceTable<BE>,
    pub cols: IvColumns,
}

impl IvTrace {
    #[inline]
    pub fn new(trace: TraceTable<BE>, cols: IvColumns) -> Self {
        Self { trace, cols }
    }
}

/// Build an IVC aggregation trace from a
/// list of step proofs and public inputs.
///
/// This performs basic consistency checks
/// against `IvPublic` (step count, work
/// units and execution root) before
/// constructing the trace.
pub fn build_iv_trace(iv_pi: &IvPublic, steps: &[ZlStepProof]) -> error::Result<IvTrace> {
    if steps.is_empty() {
        return Err(error::Error::InvalidInput(
            "IvTrace requires at least one step proof",
        ));
    }

    let cols = IvColumns::baseline();
    let n_steps = steps.len();

    // Winterfell requires trace length to be at least 8
    // and a power of two. Pad the IVC trace accordingly,
    // keeping state/root accumulators constant on padding
    // rows and setting digest to zero there.
    let n_rows = n_steps.next_power_of_two().max(8);

    // Basic arity checks against IvPublic
    if iv_pi.steps_count != n_steps as u32 {
        return Err(error::Error::InvalidInput(
            "IvPublic.steps_count must match number of step proofs",
        ));
    }
    if iv_pi.steps_ms.len() != n_steps {
        return Err(error::Error::InvalidInput(
            "IvPublic.steps_ms length must match number of step proofs",
        ));
    }

    // Compute step digests in parallel and
    // fold them into base-field elements.
    let step_digests: Vec<StepDigest> = steps.par_iter().map(ZlStepProof::digest).collect();

    let digest_fes: Vec<BE> = step_digests
        .par_iter()
        .map(utils::fold_bytes32_to_fe)
        .collect();

    // Execution root as a base-field element; kept
    // constant across the trace and tied to IvPublic.
    let exec_root_fe = utils::fold_bytes32_to_fe(&iv_pi.exec_root);

    // Verify ExecRoot consistency with the canonical
    // multiset of digests and the optional previous
    // IVC digest.
    let exec_root_expected: ExecRoot =
        zl_ivc::exec_root_from_digests(&iv_pi.suite_id, &iv_pi.prev_iv_digest, &step_digests);
    if exec_root_expected != iv_pi.exec_root {
        return Err(error::Error::InvalidInput(
            "IvPublic.exec_root is inconsistent with step digests",
        ));
    }

    // Verify aggregated work units and per-step lengths.
    let mut v_units_sum: u64 = 0;
    for (i, step) in steps.iter().enumerate() {
        let meta = &step.proof.meta;
        if iv_pi.steps_ms[i] != meta.m {
            return Err(error::Error::InvalidInput(
                "IvPublic.steps_ms entry does not match step meta",
            ));
        }

        v_units_sum = v_units_sum
            .checked_add(meta.v_units)
            .ok_or(error::Error::InvalidInput(
                "IvPublic.v_units_total overflow when summing step meta v_units",
            ))?;
    }

    if iv_pi.v_units_total != v_units_sum {
        return Err(error::Error::InvalidInput(
            "IvPublic.v_units_total must equal sum of step meta v_units",
        ));
    }

    // Derive per-step VM state hashes from the step
    // proofs and enforce that IvPublic describes the
    // same segment of the global state chain.
    let state_initial_expected = steps[0].state_in_hash();
    if iv_pi.state_initial != state_initial_expected {
        return Err(error::Error::InvalidInput(
            "IvPublic.state_initial must match first step state_in_hash",
        ));
    }

    let state_final_expected = steps
        .last()
        .map(ZlStepProof::state_out_hash)
        .expect("steps is non-empty by earlier check");
    if iv_pi.state_final != state_final_expected {
        return Err(error::Error::InvalidInput(
            "IvPublic.state_final must match last step state_out_hash",
        ));
    }

    let state_initial_fe = utils::fold_bytes32_to_fe(&iv_pi.state_initial);
    let state_final_fe = utils::fold_bytes32_to_fe(&iv_pi.state_final);

    let state_in_fes: Vec<BE> = steps
        .par_iter()
        .map(|s| utils::fold_bytes32_to_fe(&s.state_in_hash()))
        .collect();
    let state_out_fes: Vec<BE> = steps
        .par_iter()
        .map(|s| utils::fold_bytes32_to_fe(&s.state_out_hash()))
        .collect();

    // First/last rows of the trace must agree with
    // the public initial/final states once folded.
    if state_in_fes.first().copied().unwrap_or(state_initial_fe) != state_initial_fe {
        return Err(error::Error::InvalidInput(
            "IvTrace first state_in row is inconsistent with IvPublic.state_initial",
        ));
    }
    if state_out_fes.last().copied().unwrap_or(state_final_fe) != state_final_fe {
        return Err(error::Error::InvalidInput(
            "IvTrace last state_out row is inconsistent with IvPublic.state_final",
        ));
    }

    let mut trace = TraceTable::new(cols.width(), n_rows);

    let mut v_acc = BE::from(0u64);

    for (row, ((d_fe, state_in), state_out)) in digest_fes
        .iter()
        .zip(state_in_fes.iter())
        .zip(state_out_fes.iter())
        .enumerate()
    {
        let meta = &steps[row].proof.meta;

        trace.set(cols.state_in, row, *state_in);
        trace.set(cols.root_in, row, exec_root_fe);
        trace.set(cols.digest, row, *d_fe);
        trace.set(cols.step_m, row, BE::from(meta.m as u64));
        trace.set(cols.v_units, row, BE::from(meta.v_units));
        trace.set(cols.v_units_acc, row, v_acc);
        trace.set(cols.state_out, row, *state_out);
        trace.set(cols.root_out, row, exec_root_fe);

        v_acc += BE::from(meta.v_units);
    }

    // Pad remaining rows (if any) with a stationary state
    // equal to the final state's hash and zero digest/work;
    // v_units_acc is kept constant on padding rows.
    let pad_state = state_final_fe;
    for row in digest_fes.len()..n_rows {
        trace.set(cols.state_in, row, pad_state);
        trace.set(cols.root_in, row, exec_root_fe);
        trace.set(cols.digest, row, BE::ZERO);
        trace.set(cols.step_m, row, BE::ZERO);
        trace.set(cols.v_units, row, BE::ZERO);
        trace.set(cols.v_units_acc, row, v_acc);
        trace.set(cols.state_out, row, pad_state);
        trace.set(cols.root_out, row, exec_root_fe);
    }

    Ok(IvTrace::new(trace, cols))
}

/// Select partitioning parameters for IVC proving.
pub fn ivc_partition_options(trace_width: usize, trace_length: usize) -> (usize, usize) {
    crate::trace::select_partitions_for_trace(trace_width, trace_length)
}

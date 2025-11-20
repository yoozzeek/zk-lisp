// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Winterfell-based STARK backend for zk-lisp.
//!
//! This crate implements [`ZkBackend`] and frontend extension
//! traits for the Winterfell prover, wiring zk-lisp programs,
//! backend-agnostic public inputs and Winterfell's AIR/trace
//! into a concrete proof system.

pub mod agg_air;
pub mod agg_child;
pub mod agg_layout;
pub mod agg_trace;
pub mod air;
pub mod commit;
pub mod fs;
pub mod layout;
pub mod poseidon;
pub mod poseidon_hasher;
pub mod preflight;
pub mod prove;
pub mod romacc;
pub mod schedule;
pub mod segment_planner;
pub mod trace;
pub mod utils;
pub mod zl1;
pub mod zl_step;

use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::math::{FieldElement, StarkField, ToElements};
use winterfell::{BatchingMethod, FieldExtension, Proof, ProofOptions, Trace};
use zk_lisp_compiler::Program;
use zk_lisp_proof::frontend::{
    PreflightBackend, PreflightMode, ProofCodec, VmBackend, VmRunResult,
};
use zk_lisp_proof::pi::PublicInputs as CorePublicInputs;
use zk_lisp_proof::recursion::{RecursionBackend, RecursionDigest};
use zk_lisp_proof::{ProverOptions, ZkBackend, ZkField};

use crate::agg_air::AggAirPublicInputs;
use crate::agg_child::{ZlChildTranscript, verify_child_transcript};
use crate::trace::build_trace;

/// Newtype wrapper for the Winterfell
/// base field implementing the
/// backend-agnostic `ZkField` trait.
#[derive(Clone, Debug)]
pub struct WinterfellField(pub BE);

impl ZkField for WinterfellField {
    fn zero() -> Self {
        WinterfellField(BE::ZERO)
    }

    fn one() -> Self {
        WinterfellField(BE::ONE)
    }

    fn from_u64(x: u64) -> Self {
        WinterfellField(BE::from(x))
    }

    fn to_u128(&self) -> u128 {
        self.0.as_int()
    }
}

/// Public inputs visible to the Winterfell AIR.
///
/// `core` wraps backend-agnostic public inputs used
/// across backends. `rom_acc` carries the offline ROM
/// accumulator state lanes (t=3 sponge) computed from
/// the program; it is currently kept for backwards
/// compatibility and debugging. Segment-local boundary
/// state (PC, RAM GPs, ROM lanes) is provided via
/// dedicated fields below and derived directly from the
/// concrete execution trace for each proof.
#[derive(Clone, Debug)]
pub struct AirPublicInputs {
    pub core: CorePublicInputs,

    /// Offline ROM accumulator derived from the program
    /// commitment. Not used directly by the AIR for
    /// segment-local ROM binding but preserved for
    /// backwards compatibility and potential cross-checks.
    pub rom_acc: [BE; 3],

    /// Program counter value at the first map row of the
    /// trace segment proved by this AIR instance.
    pub pc_init: BE,

    /// RAM grand-product accumulators for the unsorted and
    /// sorted RAM tables at the first and last rows of the
    /// trace segment.
    pub ram_gp_unsorted_in: BE,
    pub ram_gp_unsorted_out: BE,
    pub ram_gp_sorted_in: BE,
    pub ram_gp_sorted_out: BE,

    /// ROM t=3 accumulator state at the logical beginning
    /// and end of the trace segment. `rom_s_in` is taken at
    /// the map row of the first level; `rom_s_out` at the
    /// final row of the last level.
    pub rom_s_in: [BE; 3],
    pub rom_s_out: [BE; 3],
}

impl Default for AirPublicInputs {
    fn default() -> Self {
        Self {
            core: CorePublicInputs::default(),
            rom_acc: [BE::ZERO; 3],
            pc_init: BE::ZERO,
            ram_gp_unsorted_in: BE::ZERO,
            ram_gp_unsorted_out: BE::ZERO,
            ram_gp_sorted_in: BE::ZERO,
            ram_gp_sorted_out: BE::ZERO,
            rom_s_in: [BE::ZERO; 3],
            rom_s_out: [BE::ZERO; 3],
        }
    }
}

impl ToElements<BE> for AirPublicInputs {
    fn to_elements(&self) -> Vec<BE> {
        // Encode feature mask + commitments first
        let mut out = Vec::with_capacity(16);

        out.push(BE::from(self.core.feature_mask));
        out.push(utils::be_from_le8(&self.core.program_commitment));
        out.push(utils::be_from_le8(&self.core.merkle_root));

        if self.core.program_commitment.iter().any(|b| *b != 0) {
            let fc = commit::program_field_commitment(&self.core.program_commitment);
            out.push(fc[0]);
            out.push(fc[1]);
        } else {
            out.push(BE::ZERO);
            out.push(BE::ZERO);
        }

        // Encode main_args as a flattened sequence of
        // base-field elements using the same layout as
        // VM registers / AIR assertions.
        let main_slots = utils::encode_main_args_to_slots(&self.core.main_args);
        out.reserve(main_slots.len() + 16);
        out.extend_from_slice(&main_slots);

        // Include segment-local boundary state into the
        // public-element vector so that Fiat–Shamir
        // challenges depend on these values.
        out.push(self.pc_init);
        out.push(self.ram_gp_unsorted_in);
        out.push(self.ram_gp_unsorted_out);
        out.push(self.ram_gp_sorted_in);
        out.push(self.ram_gp_sorted_out);

        for lane in &self.rom_s_in {
            out.push(*lane);
        }
        for lane in &self.rom_s_out {
            out.push(*lane);
        }

        out
    }
}

pub struct WinterfellBackend;

impl ZkBackend for WinterfellBackend {
    type Field = WinterfellField;
    type Program = Program;
    type PublicInputs = CorePublicInputs;
    type Proof = Proof;
    type Error = crate::prove::Error;
    type ProverOptions = ProverOptions;

    fn prove(
        program: &Self::Program,
        pub_inputs: &Self::PublicInputs,
        opts: &Self::ProverOptions,
    ) -> Result<Self::Proof, Self::Error> {
        let base_opts = ProofOptions::new(
            opts.queries as usize,
            opts.blowup as usize,
            opts.grind,
            FieldExtension::Quadratic,
            2,
            1,
            BatchingMethod::Linear,
            BatchingMethod::Linear,
        );

        // Build trace first so we can size partition options.
        let trace = build_trace(program, pub_inputs)?;
        let trace_width = trace.width();
        let trace_length = trace.length();
        let (num_partitions, hash_rate) =
            trace::select_partitions_for_trace(trace_width, trace_length);

        let wf_opts = base_opts.with_partitions(num_partitions, hash_rate);

        // Offline ROM accumulator from program
        let rom_acc = if pub_inputs.program_commitment.iter().any(|b| *b != 0) {
            romacc::rom_acc_from_program(program)
        } else {
            [BE::ZERO; 3]
        };

        let prover = prove::ZkProver::new(wf_opts, pub_inputs.clone(), rom_acc);

        prover.prove(trace)
    }

    fn verify(
        proof: Self::Proof,
        program: &Self::Program,
        pub_inputs: &Self::PublicInputs,
        opts: &Self::ProverOptions,
    ) -> Result<(), Self::Error> {
        let min_bits = opts.min_security_bits;
        let wf_opts = ProofOptions::new(
            opts.queries as usize,
            opts.blowup as usize,
            opts.grind,
            FieldExtension::Quadratic,
            2,
            1,
            BatchingMethod::Linear,
            BatchingMethod::Linear,
        );

        prove::verify_proof(proof, program, pub_inputs.clone(), &wf_opts, min_bits)
    }
}

impl VmBackend for WinterfellBackend {
    fn eval_vm(
        program: &Self::Program,
        pub_inputs: &Self::PublicInputs,
    ) -> Result<VmRunResult<Self::Field>, Self::Error> {
        let trace = build_trace(program, pub_inputs)?;
        let (out_reg, out_row) = utils::vm_output_from_trace(&trace);
        let cols = layout::Columns::baseline();
        let val = trace.get(cols.r_index(out_reg as usize), out_row as usize);

        Ok(VmRunResult {
            out_reg,
            out_row,
            value: WinterfellField(val),
            trace_len: trace.length(),
        })
    }
}

impl PreflightBackend for WinterfellBackend {
    fn run_preflight(
        mode: PreflightMode,
        opts: &Self::ProverOptions,
        program: &Self::Program,
        pub_inputs: &Self::PublicInputs,
    ) -> Result<(), Self::Error> {
        let base_opts = ProofOptions::new(
            opts.queries as usize,
            opts.blowup as usize,
            opts.grind,
            FieldExtension::None,
            2,
            1,
            BatchingMethod::Linear,
            BatchingMethod::Linear,
        );

        let trace = build_trace(program, pub_inputs)?;

        let (num_partitions, hash_rate) =
            trace::select_partitions_for_trace(trace.width(), trace.length());
        let wf_opts = base_opts.with_partitions(num_partitions, hash_rate);

        preflight::run(mode, &wf_opts, pub_inputs, &trace)
    }
}

impl ProofCodec for WinterfellBackend {
    type CodecError = crate::prove::Error;

    fn proof_to_bytes(proof: &Self::Proof) -> Result<Vec<u8>, Self::CodecError> {
        Ok(proof.to_bytes())
    }

    fn proof_from_bytes(bytes: &[u8]) -> Result<Self::Proof, Self::CodecError> {
        Proof::from_bytes(bytes).map_err(|e| prove::Error::BackendSource(Box::new(e)))
    }
}

impl RecursionBackend for WinterfellBackend {
    type StepProof = zl_step::ZlStepProof;
    type RecursionProof = Proof;
    type RecursionPublic = AggAirPublicInputs;

    fn recursion_prove(
        steps: &[Self::StepProof],
        rc_pi: &Self::RecursionPublic,
        opts: &Self::ProverOptions,
    ) -> Result<(Self::RecursionProof, RecursionDigest), Self::Error> {
        if steps.is_empty() {
            return Err(prove::Error::RecursionInvalid(
                "RecursionBackend::recursion_prove requires at least one step proof",
            ));
        }

        // Basic shape validation for aggregation public inputs relative to
        // the number of step proofs supplied. Callers may either leave
        // children_count/children_ms unset (0/empty) or provide values
        // consistent with `steps.len()`; any other configuration is
        // rejected early to avoid surprising aggregation profiles.
        let expected_children = steps.len() as u32;
        if rc_pi.children_count != 0 && rc_pi.children_count != expected_children {
            return Err(prove::Error::RecursionInvalid(
                "RecursionBackend::recursion_prove requires AggAirPublicInputs.children_count to be 0 or match number of step proofs",
            ));
        }

        if !rc_pi.children_ms.is_empty() && rc_pi.children_ms.len() != steps.len() {
            return Err(prove::Error::RecursionInvalid(
                "RecursionBackend::recursion_prove requires AggAirPublicInputs.children_ms length to be 0 or match number of step proofs",
            ));
        }

        let mut transcripts = Vec::with_capacity(steps.len());
        for step in steps {
            let tx = ZlChildTranscript::from_step(step)?;
            verify_child_transcript(&tx)?;
            transcripts.push(tx);
        }

        // Derive helper fields of AggAirPublicInputs from
        // steps so callers do not need to supply them manually.
        let mut agg_pi = rc_pi.clone();

        // Suite id must be consistent across all children;
        // derive it from the first step and enforce equality.
        let suite_id = steps[0].proof.header.suite_id;
        for step in steps.iter().skip(1) {
            if step.proof.header.suite_id != suite_id {
                return Err(prove::Error::RecursionInvalid(
                    "RecursionBackend::recursion_prove requires all steps to share the same suite_id",
                ));
            }
        }

        agg_pi.suite_id = suite_id;
        agg_pi.children_count = steps.len() as u32;
        agg_pi.children_ms = steps.iter().map(|s| s.proof.meta.m).collect();

        let proof = prove::prove_agg_air(&agg_pi, &transcripts, opts)?;

        // Compute a recursion digest from the effective
        // aggregation public inputs; this binds the proof
        // to its batch config.
        let digest = prove::recursion_digest_from_agg_pi(&agg_pi);

        Ok((proof, digest))
    }

    fn recursion_verify(
        proof: Self::RecursionProof,
        rc_pi: &Self::RecursionPublic,
        opts: &Self::ProverOptions,
    ) -> Result<(), Self::Error> {
        let min_bits = opts.min_security_bits;

        // Use at least 16 queries for the aggregation AIR.
        let agg_queries = core::cmp::max(opts.queries as usize, 16usize);

        let wf_opts = ProofOptions::new(
            agg_queries,
            opts.blowup as usize,
            opts.grind,
            FieldExtension::Quadratic,
            2,
            1,
            BatchingMethod::Linear,
            BatchingMethod::Linear,
        );

        prove::verify_agg_air(proof, rc_pi, &wf_opts, min_bits)
    }
}

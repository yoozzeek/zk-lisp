// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp.
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

pub mod air;
pub mod commit;
pub mod layout;
pub mod poseidon;
pub mod preflight;
pub mod prove;
pub mod romacc;
pub mod schedule;
pub mod trace;
pub mod utils;

use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::math::{FieldElement, StarkField, ToElements};
use winterfell::{BatchingMethod, FieldExtension, Proof, ProofOptions, Trace};
use zk_lisp_compiler::Program;
use zk_lisp_proof::frontend::{
    PreflightBackend, PreflightMode, ProofCodec, VmBackend, VmRunResult,
};
use zk_lisp_proof::pi::PublicInputs as CorePublicInputs;
use zk_lisp_proof::{ProverOptions, ZkBackend, ZkField};

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
/// across backends. `rom_acc` carries the final ROM
/// accumulator state lanes (t=3 sponge) and is used
/// only internally by this backend's AIR; it is not
/// currently exposed in the public input encoding.
#[derive(Clone, Debug)]
pub struct AirPublicInputs {
    pub core: CorePublicInputs,
    pub rom_acc: [BE; 3],
}

impl Default for AirPublicInputs {
    fn default() -> Self {
        Self {
            core: CorePublicInputs::default(),
            rom_acc: [BE::ZERO; 3],
        }
    }
}

impl ToElements<BE> for AirPublicInputs {
    fn to_elements(&self) -> Vec<BE> {
        let mut out = Vec::with_capacity(5);

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
        let wf_opts = ProofOptions::new(
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

        // Offline ROM accumulator
        // from program.
        let rom_acc = if pub_inputs.program_commitment.iter().any(|b| *b != 0) {
            crate::romacc::rom_acc_from_program(program)
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
        let wf_opts = ProofOptions::new(
            opts.queries as usize,
            opts.blowup as usize,
            opts.grind,
            FieldExtension::None,
            2,
            1,
            BatchingMethod::Linear,
            BatchingMethod::Linear,
        );

        prove::verify_proof(proof, program, pub_inputs.clone(), &wf_opts)
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
        let wf_opts = ProofOptions::new(
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
        crate::preflight::run(mode, &wf_opts, pub_inputs, &trace)
    }
}

impl ProofCodec for WinterfellBackend {
    type CodecError = crate::prove::Error;

    fn proof_to_bytes(proof: &Self::Proof) -> Result<Vec<u8>, Self::CodecError> {
        Ok(proof.to_bytes())
    }

    fn proof_from_bytes(bytes: &[u8]) -> Result<Self::Proof, Self::CodecError> {
        Proof::from_bytes(bytes).map_err(|e| crate::prove::Error::BackendSource(Box::new(e)))
    }
}

// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
//
// Backend abstraction traits and Winterfell implementation.
//
// Future multi-crate layout:
// - Traits (`ZkField`, `ZkBackend`, `ProverOptions`) move to crate `zk-lisp-proof`.
// - `WinterfellBackend` impl moves to crate `zk-lisp-proof-winterfell`.

use crate::compiler;
use crate::pi;
use crate::prove;
use crate::build_trace;

use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::math::FieldElement;
use winterfell::{BatchingMethod, FieldExtension, Proof, ProofOptions};

/// Minimal backend-agnostic proving options.
/// These are enough to construct concrete backend options
/// (e.g. Winterfell `ProofOptions`).
#[allow(dead_code)]
#[derive(Clone, Copy, Debug)]
pub struct ProverOptions {
    pub queries: u8,
    pub blowup: u8,
    pub grind: u32,
}

impl Default for ProverOptions {
    fn default() -> Self {
        Self {
            queries: 64,
            blowup: 8,
            grind: 0,
        }
    }
}

/// Minimal field abstraction for zk backends.
#[allow(dead_code)]
pub trait ZkField: Sized + Clone + 'static {
    fn zero() -> Self;
    fn one() -> Self;
    fn from_u64(x: u64) -> Self;
}

impl ZkField for BE {
    fn zero() -> Self {
        BE::ZERO
    }

    fn one() -> Self {
        BE::ONE
    }

    fn from_u64(x: u64) -> Self {
        BE::from(x)
    }
}

/// Generic backend interface.
/// Future GPU / alternative STARK backends should implement this trait.
#[allow(dead_code)]
pub trait ZkBackend {
    type Field: ZkField;
    type Program;
    type PublicInputs;
    type Proof;
    type Error;
    type ProverOptions;

    fn prove(
        program: &Self::Program,
        pub_inputs: &Self::PublicInputs,
        opts: &Self::ProverOptions,
    ) -> Result<Self::Proof, Self::Error>;

    fn verify(
        proof: Self::Proof,
        pub_inputs: &Self::PublicInputs,
        opts: &Self::ProverOptions,
    ) -> Result<(), Self::Error>;
}

/// Concrete backend implementation using Winterfell.
/// This will eventually live in `zk-lisp-proof-winterfell`.
#[allow(dead_code)]
pub struct WinterfellBackend;

impl ZkBackend for WinterfellBackend {
    type Field = BE;
    type Program = compiler::Program;
    type PublicInputs = pi::PublicInputs;
    type Proof = Proof;
    type Error = prove::Error;
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
        let prover = prove::ZkProver::new(wf_opts, pub_inputs.clone());
        prover.prove(trace)
    }

    fn verify(
        proof: Self::Proof,
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

        prove::verify_proof(proof, pub_inputs.clone(), &wf_opts)
    }
}

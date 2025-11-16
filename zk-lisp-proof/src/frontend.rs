// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Thin, backend-agnostic frontend helpers.
//!
//! This module provides small wrappers and extension traits
//! on top of the generic [`ZkBackend`] interface so that
//! frontends (CLI, services, etc.) can work with different
//! backends through a stable API.

use crate::ZkBackend;
use crate::ivc::{IvBackend, IvDigest, IvPublic, StepDigest};

/// Backend-provided proof serialization.
///
/// This trait is implemented by concrete backends to expose
/// encoding/decoding of opaque proof types into raw bytes.
pub trait ProofCodec: ZkBackend {
    type CodecError;

    fn proof_to_bytes(proof: &Self::Proof) -> Result<Vec<u8>, Self::CodecError>;
    fn proof_from_bytes(bytes: &[u8]) -> Result<Self::Proof, Self::CodecError>;
}

/// Generic preflight reporting mode.
///
/// Backends may interpret these modes as they see fit,
/// e.g. printing human-readable diagnostics, emitting
/// structured JSON, or doing nothing in release builds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PreflightMode {
    Off,
    Console,
    Json,
}

/// Result of running a VM program without proof generation.
#[derive(Clone, Debug)]
pub struct VmRunResult<F> {
    pub out_reg: u8,
    pub out_row: u32,
    pub value: F,
    pub trace_len: usize,
}

/// Backend extension: ability to execute the VM and locate
/// its output cell in the execution trace.
pub trait VmBackend: ZkBackend {
    fn eval_vm(
        program: &Self::Program,
        pub_inputs: &Self::PublicInputs,
    ) -> Result<VmRunResult<Self::Field>, Self::Error>;
}

/// Backend extension: ability to run preflight checks over
/// the execution trace and AIR constraints.
pub trait PreflightBackend: ZkBackend {
    fn run_preflight(
        mode: PreflightMode,
        opts: &Self::ProverOptions,
        program: &Self::Program,
        pub_inputs: &Self::PublicInputs,
    ) -> Result<(), Self::Error>;
}

/// Thin wrapper over [`ZkBackend::prove`] for ergonomic use
/// from frontends.
pub fn prove<B: ZkBackend>(
    program: &B::Program,
    pub_inputs: &B::PublicInputs,
    opts: &B::ProverOptions,
) -> Result<B::Proof, B::Error> {
    B::prove(program, pub_inputs, opts)
}

/// Thin wrapper over [`ZkBackend::verify`].
pub fn verify<B: ZkBackend>(
    proof: B::Proof,
    program: &B::Program,
    pub_inputs: &B::PublicInputs,
    opts: &B::ProverOptions,
) -> Result<(), B::Error> {
    B::verify(proof, program, pub_inputs, opts)
}

/// Execute a program and obtain its VM output cell and
/// trace length via a backend implementing [`VmBackend`].
pub fn run_vm<B: VmBackend>(
    program: &B::Program,
    pub_inputs: &B::PublicInputs,
) -> Result<VmRunResult<B::Field>, B::Error> {
    B::eval_vm(program, pub_inputs)
}

/// Run backend-specific preflight checks using a backend
/// implementing [`PreflightBackend`].
pub fn preflight<B: PreflightBackend>(
    mode: PreflightMode,
    opts: &B::ProverOptions,
    program: &B::Program,
    pub_inputs: &B::PublicInputs,
) -> Result<(), B::Error> {
    B::run_preflight(mode, opts, program, pub_inputs)
}

/// Encode a backend proof into raw bytes.
pub fn encode_proof<B: ProofCodec>(proof: &B::Proof) -> Result<Vec<u8>, B::CodecError> {
    B::proof_to_bytes(proof)
}

/// Decode a backend proof from raw bytes.
pub fn decode_proof<B: ProofCodec>(bytes: &[u8]) -> Result<B::Proof, B::CodecError> {
    B::proof_from_bytes(bytes)
}

/// Thin wrapper over [`IvBackend::step_digest`].
pub fn step_digest<B: IvBackend>(step: &B::StepProof) -> StepDigest {
    B::step_digest(step)
}

/// Thin wrapper over [`IvBackend::exec_root`]
/// with explicit suite identifier.
pub fn exec_root<B: IvBackend>(
    suite_id: &[u8; 32],
    prev_iv_digest: &[u8; 32],
    digests_sorted: &[StepDigest],
) -> crate::ivc::ExecRoot {
    B::exec_root(suite_id, prev_iv_digest, digests_sorted)
}

/// Produce a new IVC aggregation step.
pub fn prove_ivc<B: IvBackend>(
    prev: Option<B::IvProof>,
    steps: &[B::StepProof],
    iv_pi: &IvPublic,
    opts: &B::ProverOptions,
) -> Result<(B::IvProof, IvDigest), B::Error> {
    B::prove_ivc(prev, steps, iv_pi, opts)
}

/// Verify an IVC aggregation step.
pub fn verify_ivc<B: IvBackend>(
    iv_proof: B::IvProof,
    iv_pi: &IvPublic,
    opts: &B::ProverOptions,
) -> Result<(), B::Error> {
    B::verify_ivc(iv_proof, iv_pi, opts)
}

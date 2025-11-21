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
use crate::recursion::{RecursionBackend, RecursionDigest};

/// Generic preflight reporting mode.
///
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

/// Produce a new recursion aggregation step over a batch
/// of step proofs using a backend implementing
pub fn recursion_prove<B: RecursionBackend>(
    steps: &[B::StepProof],
    rc_pi: &B::RecursionPublic,
    opts: &B::ProverOptions,
) -> Result<(B::RecursionProof, RecursionDigest), B::Error> {
    B::recursion_prove(steps, rc_pi, opts)
}

/// Verify a recursion aggregation step against backend-specific
/// recursion public inputs.
pub fn recursion_verify<B: RecursionBackend>(
    proof: B::RecursionProof,
    rc_pi: &B::RecursionPublic,
    opts: &B::ProverOptions,
) -> Result<(), B::Error> {
    B::recursion_verify(proof, rc_pi, opts)
}

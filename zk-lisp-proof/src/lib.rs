// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Backend-agnostic proof interfaces for zk-lisp.
//!
//! This crate defines the core [`ZkBackend`] and [`ZkField`]
//! traits plus minimal [`ProverOptions`], so concrete proving
//! backends can plug in while frontends stay generic.

pub mod error;
pub mod frontend;
pub mod pi;

/// Minimal backend-agnostic proving options.
/// These are enough to construct concrete
/// backend options (e.g. backend-specific `ProofOptions`).
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
pub trait ZkField: Sized + Clone + 'static {
    fn zero() -> Self;
    fn one() -> Self;
    fn from_u64(x: u64) -> Self;
    fn to_u128(&self) -> u128;
}

/// Generic backend interface.
/// Future GPU / alternative STARK
/// backends should implement this trait.
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

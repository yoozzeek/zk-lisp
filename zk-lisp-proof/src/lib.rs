// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Backend-agnostic proof interfaces for zk-lisp.

pub mod error;
pub mod frontend;
pub mod pi;
pub mod recursion;
pub mod segment;

/// Field abstraction for zk backends.
pub trait ZkField: Sized + Clone + 'static {
    fn zero() -> Self;
    fn one() -> Self;
    fn from_u64(x: u64) -> Self;
    fn to_u128(&self) -> u128;
}

/// Generic backend type-bag.
pub trait ZkBackend {
    type Field: ZkField;
    type Program;
    type PublicInputs;
    type Error;
    type ProverOptions;
}

/// Backend-agnostic proving options.
/// These are enough to construct concrete
#[derive(Clone, Copy, Debug)]
pub struct ProverOptions {
    pub queries: u8,
    pub blowup: u8,
    pub grind: u32,

    /// Minimum conjectured security in bits.
    pub min_security_bits: u32,

    /// Optional override for the maximum number of base-trace
    /// rows per execution segment. When `None`, the backend's
    /// default policy is used.
    pub max_segment_rows: Option<usize>,

    /// Optional upper bound on the number of child proofs
    /// (segments) that may be constructed in parallel.
    /// None means no parallelism.
    pub max_concurrent_segments: Option<usize>,
}

impl Default for ProverOptions {
    fn default() -> Self {
        let min_security_bits = if cfg!(debug_assertions) { 64 } else { 128 };
        Self {
            queries: 32,
            blowup: 16,
            grind: 0,
            min_security_bits,
            max_segment_rows: None,
            max_concurrent_segments: None,
        }
    }
}

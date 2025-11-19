// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Step-level metadata and digest for zk-lisp STARK proofs.
//!
//! This module defines a minimal echo of per-proof
//! parameters (`StepMeta`) and a Poseidon-based
//! digest function (`step_digest`) used by the
//! STARK-in-STARK recursion layer, along with a
//! concrete step proof wrapper (`ZlStepProof`).

use crate::zl1;

use winterfell::ProofOptions;
use winterfell::math::fields::f128::BaseElement as BE;

/// Minimal per-proof echo used for digest computation.
///
/// These fields are chosen to capture the essential
/// shape of the proof (trace length, blowup, queries)
/// and a coarse "work" estimate without pulling the
/// entire public input vector into the digest.
#[derive(Clone, Copy, Debug, Default)]
pub struct StepMeta {
    /// Base trace length m (number of rows before blowup).
    pub m: u32,

    /// Blowup factor rho used for this proof.
    pub rho: u16,

    /// Number of FRI queries q.
    pub q: u16,

    /// Number of committed oracles (trace + composition).
    pub o: u16,

    /// Target security level in bits.
    pub lambda: u16,

    /// Length of encoded public inputs vector
    /// (in field elements) as seen by the AIR.
    pub pi_len: u32,

    /// Coarse estimate of verifier work units.
    pub v_units: u64,
}

/// Concrete step-proof wrapper used as the
/// backend-specific `StepProof` type for
/// the recursion layer.
///
/// This structure carries the zl1 step proof container
/// which in turn encapsulates profile metadata, public
/// inputs echo, commitment echo and the underlying
/// Winterfell proof.
#[derive(Clone, Debug)]
pub struct ZlStepProof {
    pub proof: zl1::format::Proof,
    /// Backend-agnostic public inputs used when building
    /// this step trace.
    pub pi_core: zk_lisp_proof::pi::PublicInputs,
    /// Final ROM accumulator lanes for this step.
    pub rom_acc: [BE; 3],
}

impl ZlStepProof {
    /// Compute the step digest for this proof using
    /// the zl1 format and digest construction.
    pub fn digest(&self) -> [u8; 32] {
        zl1::digest::step_digest(&self.proof)
    }

    /// Return the VM state hash at the beginning
    /// of this segment as recorded in the zl1
    /// step public inputs.
    pub fn state_in_hash(&self) -> [u8; 32] {
        self.proof.pi.state_in_hash
    }

    /// Return the VM state hash at the end of
    /// this segment as recorded in the zl1
    /// step public inputs.
    pub fn state_out_hash(&self) -> [u8; 32] {
        self.proof.pi.state_out_hash
    }
}

impl StepMeta {
    /// Construct a `StepMeta` from basic profile numbers.
    pub fn new(m: u32, rho: u16, q: u16, o: u16, lambda: u16, pi_len: u32) -> Self {
        let v_units = (m as u64).saturating_mul(q as u64);

        Self {
            m,
            rho,
            q,
            o,
            lambda,
            pi_len,
            v_units,
        }
    }

    /// Convenience constructor for building
    /// step metadata from runtime proof
    /// options and trace shape.
    pub fn from_env(
        trace_len: usize,
        wf_opts: &ProofOptions,
        lambda_bits: u32,
        pi_len: u32,
    ) -> Self {
        let m = trace_len as u32;
        let rho = wf_opts.blowup_factor() as u16;
        let q = wf_opts.num_queries() as u16;

        // current backend commits the
        // main trace and a single
        // composition column;
        let o: u16 = 2;

        let lambda = lambda_bits.min(u16::MAX as u32) as u16;

        StepMeta::new(m, rho, q, o, lambda, pi_len)
    }
}

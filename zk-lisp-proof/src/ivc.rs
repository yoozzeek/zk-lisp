// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Backend-agnostic IVC abstractions for zk-lisp.
//!
//! This module defines shared types and traits for
//! incrementally verifiable proofs built on top of
//! a base [`ZkBackend`]. Concrete backends wire
//! their own step and IVC proof formats into these
//! traits while frontends stay generic.

use crate::ZkBackend;

/// Digest of a single execution step proof.
///
/// This is a 32-byte value computed from the
/// step proof and its commitments using a
/// backend-specific construction with fixed
/// string domains.
pub type StepDigest = [u8; 32];

/// Digest of an IVC aggregation step.
pub type IvDigest = [u8; 32];

/// Merkle-style root over a multiset of
/// step digests aggregated in an IVC step.
pub type ExecRoot = [u8; 32];

/// Public inputs for an IVC aggregation step
/// in a backend-agnostic form.
///
/// Concrete backends map this structure into
/// their AIR public-input vector.
#[derive(Clone, Debug, Default)]
pub struct IvPublic {
    pub suite_id: [u8; 32],

    pub program_id: [u8; 32],
    pub program_commitment: [u8; 32],

    /// Global VM state at the beginning of
    /// the aggregated prefix.
    pub state_initial: [u8; 32],

    /// Global VM state at the end of the aggregated
    /// prefix (including any previous IVC steps).
    pub state_final: [u8; 32],

    /// Digest of the previous IVC step in the chain.
    ///
    /// When this value is all zeros, the current
    /// IVC step is treated as the first step in
    /// the chain. When non-zero, it is included
    /// into `exec_root` and `IvDigest` as an
    /// additional child element.
    pub prev_iv_digest: [u8; 32],

    /// Merkle root over the sorted list of
    /// child step digests aggregated in this
    /// IVC step (including `prev_iv_digest`
    /// when it is non-zero).
    pub exec_root: ExecRoot,

    /// Number of children in this step.
    pub steps_count: u32,

    /// Base trace lengths `m_i` for each
    /// child segment.
    pub steps_ms: Vec<u32>,

    /// Aggregated work units across children.
    pub v_units_total: u64,
}

/// Backend extension for IVC.
///
/// This trait is implemented by backends that support
/// step-level proofs and recursive aggregation on top
/// of the base [`ZkBackend`] interface.
pub trait IvBackend: ZkBackend {
    /// Proof type for a single execution step (segment).
    /// The exact format is backend-specific.
    type StepProof;

    /// Proof type for an IVC aggregation step.
    type IvProof;

    /// Compute a digest for a step proof.
    fn step_digest(step: &Self::StepProof) -> StepDigest;

    /// Compute a Merkle-style execution root from an
    /// optional previous IVC digest and a sorted list
    /// of child step digests.
    ///
    /// `prev_iv_digest` is the digest of the previous
    /// IVC step in the chain. When all bytes are zero,
    /// no previous step is included. `suite_id` selects
    /// the Poseidon suite used for hashing child digests
    /// in this IVC step.
    fn exec_root(
        suite_id: &[u8; 32],
        prev_iv_digest: &[u8; 32],
        digests_sorted: &[StepDigest],
    ) -> ExecRoot;

    /// Produce a new IVC aggregation step.
    ///
    /// `prev` is the previous IVC proof in the chain,
    /// or `None` for the first step. `steps` is the
    /// list of newly aggregated step proofs. `iv_pi`
    /// carries the public inputs for this IVC step.
    fn prove_ivc(
        prev: Option<Self::IvProof>,
        steps: &[Self::StepProof],
        iv_pi: &IvPublic,
        opts: &Self::ProverOptions,
    ) -> Result<(Self::IvProof, IvDigest), Self::Error>;

    /// Verify an IVC aggregation proof against its
    /// public inputs.
    fn verify_ivc(
        iv_proof: Self::IvProof,
        iv_pi: &IvPublic,
        opts: &Self::ProverOptions,
    ) -> Result<(), Self::Error>;
}

/// Error type for high-level IVC chain verification.
///
/// This is intentionally small and backend-agnostic:
/// backend errors are wrapped into [`IvChainError::Backend`],
/// while chain-shape violations are reported as
/// [`IvChainError::Invalid`].
#[derive(Debug)]
pub enum IvChainError<E> {
    Backend(E),
    Invalid(&'static str),
}

/// Verify a sequence of IVC steps as a single chain.
///
/// This function enforces the following invariants:
/// - every step verifies under [`IvBackend::verify_ivc`];
/// - the first step must have `prev_iv_digest == 0`;
/// - for every k > 0, `iv_k.prev_iv_digest == digest_{k-1}`;
/// - for every k > 0, `iv_k.state_initial == iv_{k-1}.state_final`;
/// - all steps share the same `suite_id`, `program_id`
///   and `program_commitment`.
pub fn verify_ivc_chain<B, I>(
    chain: I,
    opts: &B::ProverOptions,
) -> Result<(), IvChainError<B::Error>>
where
    B: IvBackend,
    I: IntoIterator<Item = (B::IvProof, IvDigest, IvPublic)>,
{
    let mut prev_pi: Option<IvPublic> = None;
    let mut prev_digest: Option<IvDigest> = None;
    let mut suite_id: Option<[u8; 32]> = None;
    let mut program_id: Option<[u8; 32]> = None;
    let mut program_commitment: Option<[u8; 32]> = None;

    for (iv_proof, iv_digest, iv_pi) in chain.into_iter() {
        // First, delegate to backend-level verifier.
        B::verify_ivc(iv_proof, &iv_pi, opts).map_err(IvChainError::Backend)?;

        // Enforce per-chain static fields.
        match suite_id {
            None => {
                suite_id = Some(iv_pi.suite_id);
                program_id = Some(iv_pi.program_id);
                program_commitment = Some(iv_pi.program_commitment);
            }
            Some(sid) => {
                if iv_pi.suite_id != sid {
                    return Err(IvChainError::Invalid(
                        "IvPublic.suite_id must be constant across IVC chain",
                    ));
                }
                if let Some(pid) = program_id {
                    if iv_pi.program_id != pid {
                        return Err(IvChainError::Invalid(
                            "IvPublic.program_id must be constant across IVC chain",
                        ));
                    }
                }
                if let Some(pc) = program_commitment {
                    if iv_pi.program_commitment != pc {
                        return Err(IvChainError::Invalid(
                            "IvPublic.program_commitment must be constant across IVC chain",
                        ));
                    }
                }
            }
        }

        match (&prev_pi, &prev_digest) {
            (None, None) => {
                // First step: prev_iv_digest must be zeroed.
                if iv_pi.prev_iv_digest.iter().any(|b| *b != 0) {
                    return Err(IvChainError::Invalid(
                        "first IvPublic.prev_iv_digest must be zero",
                    ));
                }
            }
            (Some(prev_pi), Some(prev_d)) => {
                if iv_pi.prev_iv_digest != *prev_d {
                    return Err(IvChainError::Invalid(
                        "IvPublic.prev_iv_digest must match previous IvDigest",
                    ));
                }
                if iv_pi.state_initial != prev_pi.state_final {
                    return Err(IvChainError::Invalid(
                        "IvPublic.state_initial must match previous state_final",
                    ));
                }
            }
            _ => unreachable!(),
        }

        prev_digest = Some(iv_digest);
        prev_pi = Some(iv_pi);
    }

    Ok(())
}

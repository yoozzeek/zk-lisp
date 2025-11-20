// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Backend-agnostic recursion interfaces for zk-lisp.
//!
//! This module defines a minimal trait for STARK-in-STARK
//! style recursion over step proofs. Concrete backends
//! implement [`RecursionBackend`] to expose their own
//! aggregation proof format, while frontends can remain
//! generic over the recursion layer.

use crate::ZkBackend;

/// Backend extension for recursive aggregation.
///
/// Backends implementing this trait can produce and verify
/// aggregation proofs over a batch of step proofs using a
/// backend-specific recursion AIR (e.g. an aggregation AIR
/// over compact child proofs).
pub trait RecursionBackend: ZkBackend {
    /// Proof type for a single execution step (segment).
    type StepProof;

    /// Proof type for a recursion aggregation step.
    type RecursionProof;

    /// Backend-specific public inputs used to drive the
    /// recursion AIR. This may refine or extend the
    /// backend-agnostic [`RecursionPublic`] with
    /// implementation details.
    type RecursionPublic;

    /// Produce a new recursion aggregation step from a batch
    /// of step proofs and backend-specific recursion public
    /// inputs. Returns the aggregation proof and its 32-byte
    /// digest.
    fn recursion_prove(
        steps: &[Self::StepProof],
        rc_pi: &Self::RecursionPublic,
        opts: &Self::ProverOptions,
    ) -> Result<(Self::RecursionProof, RecursionDigest), Self::Error>;

    /// Verify a recursion aggregation proof against its
    /// backend-specific recursion public inputs.
    fn recursion_verify(
        proof: Self::RecursionProof,
        rc_pi: &Self::RecursionPublic,
        opts: &Self::ProverOptions,
    ) -> Result<(), Self::Error>;
}

/// Digest of a recursion aggregation step.
///
/// This is a 32-byte value computed from backend-specific
/// public inputs and the list of child step proofs. The
/// exact construction is left to the backend.
pub type RecursionDigest = [u8; 32];

/// Error type for high-level recursion chain verification.
///
/// Backend-specific errors are wrapped into
/// [`RecursionChainError::Backend`], while violations of
/// chain-shape invariants are reported as
/// [`RecursionChainError::Invalid`].
#[derive(Debug)]
pub enum RecursionChainError<E> {
    Backend(E),
    Invalid(&'static str),
}

/// Public inputs for a recursion aggregation step in a
/// backend-agnostic form.
///
/// This structure captures the high-level semantics of a
/// recursion step as seen by frontends and chain-level
/// verification, leaving backend-specific details (such as
/// AIR layouts or FRI profiles) to concrete backends.
#[derive(Clone, Debug, Default)]
pub struct RecursionPublic {
    pub suite_id: [u8; 32],

    pub program_id: [u8; 32],
    pub program_commitment: [u8; 32],

    /// Global VM state at the beginning of the aggregated
    /// prefix (including any previous recursion steps).
    pub state_initial: [u8; 32],

    /// Global VM state at the end of the aggregated prefix.
    pub state_final: [u8; 32],

    /// Global RAM grand-product accumulators for the
    /// unsorted and sorted RAM tables at the beginning
    /// and end of the aggregated prefix.
    pub ram_gp_unsorted_initial: [u8; 32],
    pub ram_gp_unsorted_final: [u8; 32],
    pub ram_gp_sorted_initial: [u8; 32],
    pub ram_gp_sorted_final: [u8; 32],

    /// Global ROM t=3 accumulator state at the beginning
    /// and end of the aggregated prefix.
    pub rom_s_initial: [[u8; 32]; 3],
    pub rom_s_final: [[u8; 32]; 3],

    /// Digest of the previous recursion step in the chain.
    ///
    /// When this value is all zeros, the current recursion
    /// step is treated as the first element in the chain.
    /// When non-zero, it is included into the chain-level
    /// invariants enforced by [`verify_recursion_chain`].
    pub prev_digest: RecursionDigest,

    /// Backend-agnostic commitment to the batch of children
    /// aggregated in this step (e.g. a Merkle root over
    /// child descriptors).
    pub children_root: [u8; 32],

    /// Number of children aggregated in this recursion step.
    pub children_count: u32,

    /// Base trace lengths `m_i` for each child segment.
    pub children_ms: Vec<u32>,

    /// Aggregated work units across children.
    pub v_units_total: u64,
}

/// Verify a sequence of recursion steps as a single chain.
///
/// This function enforces the following invariants:
/// - every step verifies under [`RecursionBackend::recursion_verify`];
/// - the first step must have `prev_digest == 0`;
/// - for every k > 0, `rc_k.prev_digest == digest_{k-1}`;
/// - for every k > 0, `rc_k.state_initial == rc_{k-1}.state_final`;
/// - for every k > 0, RAM and ROM global boundary values
///   chain across steps:
///   - `rc_k.ram_gp_unsorted_initial == rc_{k-1}.ram_gp_unsorted_final`;
///   - `rc_k.ram_gp_sorted_initial == rc_{k-1}.ram_gp_sorted_final`;
///   - `rc_k.rom_s_initial == rc_{k-1}.rom_s_final`;
/// - all steps share the same `suite_id`, `program_id` and
///   `program_commitment`.
pub fn verify_recursion_chain<B, I>(
    chain: I,
    opts: &B::ProverOptions,
) -> Result<(), RecursionChainError<B::Error>>
where
    B: RecursionBackend,
    I: IntoIterator<
        Item = (
            B::RecursionProof,
            RecursionDigest,
            B::RecursionPublic,
            RecursionPublic,
        ),
    >,
{
    let mut prev_pi: Option<RecursionPublic> = None;
    let mut prev_digest: Option<RecursionDigest> = None;
    let mut suite_id: Option<[u8; 32]> = None;
    let mut program_id: Option<[u8; 32]> = None;
    let mut program_commitment: Option<[u8; 32]> = None;
    let mut saw_step = false;

    for (rc_proof, rc_digest, backend_pi, rc_pi) in chain.into_iter() {
        B::recursion_verify(rc_proof, &backend_pi, opts).map_err(RecursionChainError::Backend)?;

        saw_step = true;

        match suite_id {
            None => {
                suite_id = Some(rc_pi.suite_id);
                program_id = Some(rc_pi.program_id);
                program_commitment = Some(rc_pi.program_commitment);
            }
            Some(sid) => {
                if rc_pi.suite_id != sid {
                    return Err(RecursionChainError::Invalid(
                        "RecursionPublic.suite_id must be constant across recursion chain",
                    ));
                }

                if let Some(pid) = program_id {
                    if rc_pi.program_id != pid {
                        return Err(RecursionChainError::Invalid(
                            "RecursionPublic.program_id must be constant across recursion chain",
                        ));
                    }
                }

                if let Some(pc) = program_commitment {
                    if rc_pi.program_commitment != pc {
                        return Err(RecursionChainError::Invalid(
                            "RecursionPublic.program_commitment must be constant across recursion chain",
                        ));
                    }
                }
            }
        }

        match (&prev_pi, &prev_digest) {
            (None, None) => {
                // First step: prev_digest must be zeroed.
                if rc_pi.prev_digest.iter().any(|b| *b != 0) {
                    return Err(RecursionChainError::Invalid(
                        "first RecursionPublic.prev_digest must be zero",
                    ));
                }
            }
            (Some(prev_pi), Some(prev_d)) => {
                if rc_pi.prev_digest != *prev_d {
                    return Err(RecursionChainError::Invalid(
                        "RecursionPublic.prev_digest must match previous RecursionDigest",
                    ));
                }

                if rc_pi.state_initial != prev_pi.state_final {
                    return Err(RecursionChainError::Invalid(
                        "RecursionPublic.state_initial must match previous state_final",
                    ));
                }

                if rc_pi.ram_gp_unsorted_initial != prev_pi.ram_gp_unsorted_final {
                    return Err(RecursionChainError::Invalid(
                        "RecursionPublic.ram_gp_unsorted_initial must match previous ram_gp_unsorted_final",
                    ));
                }

                if rc_pi.ram_gp_sorted_initial != prev_pi.ram_gp_sorted_final {
                    return Err(RecursionChainError::Invalid(
                        "RecursionPublic.ram_gp_sorted_initial must match previous ram_gp_sorted_final",
                    ));
                }

                if rc_pi.rom_s_initial != prev_pi.rom_s_final {
                    return Err(RecursionChainError::Invalid(
                        "RecursionPublic.rom_s_initial must match previous rom_s_final",
                    ));
                }
            }
            _ => unreachable!(),
        }

        prev_digest = Some(rc_digest);
        prev_pi = Some(rc_pi);
    }

    if !saw_step {
        return Err(RecursionChainError::Invalid(
            "recursion chain must contain at least one step",
        ));
    }

    Ok(())
}

// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Backend-agnostic recursion interfaces for zk-lisp.

use crate::ZkBackend;

pub trait RecursionBackend: ZkBackend {
    type StepProof;
    type RecursionProof;
    type RecursionPublic;

    fn prove(
        steps: &[Self::StepProof],
        rc_pi: &Self::RecursionPublic,
        opts: &Self::ProverOptions,
    ) -> Result<(Self::RecursionProof, RecursionDigest), Self::Error>;

    fn verify(
        proof: Self::RecursionProof,
        rc_pi: &Self::RecursionPublic,
        opts: &Self::ProverOptions,
    ) -> Result<(), Self::Error>;
}

pub trait RecursionStepProver: RecursionBackend {
    fn prove_all_steps(
        program: &Self::Program,
        pub_inputs: &Self::PublicInputs,
        opts: &Self::ProverOptions,
    ) -> Result<Vec<Self::StepProof>, Self::Error>;
}

pub trait RecursionPublicBuilder: RecursionBackend {
    fn build_public(
        program: &Self::Program,
        pub_inputs: &Self::PublicInputs,
        steps: &[Self::StepProof],
        opts: &Self::ProverOptions,
    ) -> Result<Self::RecursionPublic, Self::Error>;
}

pub trait RecursionArtifactCodec: RecursionBackend {
    type CodecError;

    fn encode(
        proof: &Self::RecursionProof,
        rc_pi: &Self::RecursionPublic,
    ) -> Result<Vec<u8>, Self::CodecError>;

    fn decode(
        bytes: &[u8],
    ) -> Result<(Self::RecursionProof, Self::RecursionPublic), Self::CodecError>;
}

pub type RecursionDigest = [u8; 32];

#[derive(Debug)]
pub enum RecursionChainError<E> {
    Backend(E),
    Invalid(&'static str),
}

#[derive(Clone, Debug, Default)]
pub struct RecursionPublic {
    pub suite_id: [u8; 32],
    pub program_id: [u8; 32],
    pub program_commitment: [u8; 32],
    pub state_initial: [u8; 32],
    pub state_final: [u8; 32],
    pub ram_gp_unsorted_initial: [u8; 32],
    pub ram_gp_unsorted_final: [u8; 32],
    pub ram_gp_sorted_initial: [u8; 32],
    pub ram_gp_sorted_final: [u8; 32],
    pub rom_s_initial: [[u8; 32]; 3],
    pub rom_s_final: [[u8; 32]; 3],
    pub prev_digest: RecursionDigest,
    pub children_root: [u8; 32],
    pub children_count: u32,
    pub children_ms: Vec<u32>,
    pub v_units_total: u64,
}

pub fn verify_chain<B, I>(
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
        B::verify(rc_proof, &backend_pi, opts).map_err(RecursionChainError::Backend)?;

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

pub fn prove_chain<B: RecursionBackend + RecursionStepProver + RecursionPublicBuilder>(
    program: &B::Program,
    pub_inputs: &B::PublicInputs,
    opts: &B::ProverOptions,
) -> Result<(B::RecursionProof, RecursionDigest, B::RecursionPublic), B::Error> {
    let steps = B::prove_all_steps(program, pub_inputs, opts)?;
    let rc_pi = B::build_public(program, pub_inputs, &steps, opts)?;
    let (proof, digest) = B::prove(&steps, &rc_pi, opts)?;

    Ok((proof, digest, rc_pi))
}

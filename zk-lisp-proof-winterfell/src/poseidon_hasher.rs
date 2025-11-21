// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Poseidon-based hasher for Winterfell
//! commitments and random coin.

use core::fmt::Debug;
use core::marker::PhantomData;

use crate::poseidon;
use crate::utils;
use winter_utils::{ByteReader, ByteWriter, Deserializable, DeserializationError, Serializable};
use winterfell::crypto::Digest as CryptoDigest;
use winterfell::crypto::{ElementHasher, Hasher};
use winterfell::math::FieldElement;
use winterfell::math::StarkField;
use winterfell::math::fields::f128::BaseElement as BE;

const POSEIDON_SUITE_ID: [u8; 32] = [0u8; 32];

#[derive(Copy, Clone, Eq, PartialEq, Default)]
pub struct PoseidonDigest([u8; 32]);

impl Debug for PoseidonDigest {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "PoseidonDigest([{} bytes])", self.0.len())
    }
}

impl Serializable for PoseidonDigest {
    fn write_into<W: ByteWriter>(&self, target: &mut W) {
        target.write_bytes(&self.0);
    }
}

impl Deserializable for PoseidonDigest {
    fn read_from<R: ByteReader>(source: &mut R) -> Result<Self, DeserializationError> {
        Ok(Self(source.read_array()?))
    }
}

impl CryptoDigest for PoseidonDigest {
    fn as_bytes(&self) -> [u8; 32] {
        self.0
    }
}

/// Poseidon-based hasher for Winterfell commitments over f128.
///
/// Note: this hasher is used only for Merkle/coin commitments
/// inside Winterfell and is not parameterised by per-proof suite
/// ids; protocol-level binders continue to use zk-lisp Poseidon
/// digests derived from program-level suite ids.
#[derive(Debug, PartialEq, Eq)]
pub struct PoseidonHasher<B: StarkField>(PhantomData<B>);

impl Hasher for PoseidonHasher<BE> {
    type Digest = PoseidonDigest;

    const COLLISION_RESISTANCE: u32 = 128;

    fn hash(bytes_in: &[u8]) -> Self::Digest {
        let fe = ro_bytes_sponge_custom_rounds(
            &POSEIDON_SUITE_ID,
            "zkl/winter/hash/bytes",
            bytes_in,
            hasher_rounds(),
        );
        PoseidonDigest(utils::fe_to_bytes_fold(fe))
    }

    fn merge(values: &[Self::Digest; 2]) -> Self::Digest {
        let mut buf = [0u8; 64];
        buf[0..32].copy_from_slice(&values[0].0);
        buf[32..64].copy_from_slice(&values[1].0);

        let fe = ro_bytes_sponge_custom_rounds(
            &POSEIDON_SUITE_ID,
            "zkl/winter/hash/merge",
            &buf,
            hasher_rounds(),
        );

        PoseidonDigest(utils::fe_to_bytes_fold(fe))
    }

    fn merge_many(values: &[Self::Digest]) -> Self::Digest {
        if values.is_empty() {
            return PoseidonDigest([0u8; 32]);
        }

        let mut buf = Vec::with_capacity(values.len() * 32);
        for d in values {
            buf.extend_from_slice(&d.0);
        }

        let fe = ro_bytes_sponge_custom_rounds(
            &POSEIDON_SUITE_ID,
            "zkl/winter/hash/merge_many",
            &buf,
            hasher_rounds(),
        );

        PoseidonDigest(utils::fe_to_bytes_fold(fe))
    }

    fn merge_with_int(seed: Self::Digest, value: u64) -> Self::Digest {
        let mut buf = [0u8; 40];
        buf[0..32].copy_from_slice(&seed.0);
        buf[32..40].copy_from_slice(&value.to_le_bytes());

        let fe = ro_bytes_sponge_custom_rounds(
            &POSEIDON_SUITE_ID,
            "zkl/winter/hash/merge_with_int",
            &buf,
            hasher_rounds(),
        );

        PoseidonDigest(utils::fe_to_bytes_fold(fe))
    }
}

impl ElementHasher for PoseidonHasher<BE> {
    type BaseField = BE;

    fn hash_elements<E>(elements: &[E]) -> Self::Digest
    where
        E: FieldElement<BaseField = Self::BaseField>,
    {
        let bytes_in = E::elements_as_bytes(elements);
        let fe = ro_bytes_sponge_custom_rounds(
            &POSEIDON_SUITE_ID,
            "winter/hash/elements",
            bytes_in,
            hasher_rounds(),
        );

        PoseidonDigest(utils::fe_to_bytes_fold(fe))
    }
}

/// Local RO→field helper using a
/// tunable number of Poseidon rounds.
fn ro_bytes_sponge_custom_rounds(
    suite_id: &[u8; 32],
    domain: &str,
    data: &[u8],
    rounds: usize,
) -> BE {
    // Build suite with the requested number
    // of rounds, keeping MDS/DOM derived from
    // the suite id consistent with other contexts.
    let ps = crate::poseidon::get_poseidon_suite_with_rounds(suite_id, rounds);

    // Domain element
    let mut dbuf = [0u8; 32];
    let dbytes = domain.as_bytes();
    let copy_len = core::cmp::min(32, dbytes.len());
    dbuf[..copy_len].copy_from_slice(&dbytes[..copy_len]);
    
    let dom_fe = crate::utils::fold_bytes32_to_fe(&dbuf);

    // Sponge state: lanes 0..10 are the
    // rate/capacity pool, lanes 10..11 carry tags.
    let mut state = [BE::ZERO; 12];
    state[10] = ps.dom[0];
    state[11] = ps.dom[1];

    const RATE: usize = 10;
    let mut lane = 0usize;

    // One full permutation
    // with precomputed MDS/RC.
    let permute = |state: &mut [BE; 12]| {
        for rc_r in ps.rc.iter() {
            for v in state.iter_mut() {
                *v = *v * *v * *v;
            }
            
            let mut new_state = [BE::ZERO; 12];
            for (i, row) in ps.mds.iter().enumerate() {
                let acc = row
                    .iter()
                    .zip(state.iter())
                    .fold(BE::ZERO, |acc, (m, s)| acc + (*m) * (*s));
                new_state[i] = acc + rc_r[i];
            }
    
            *state = new_state;
        }
    };

    // Absorb helper
    let absorb = |msg: BE, state: &mut [BE; 12], lane: &mut usize| {
        state[*lane] += msg;
        *lane += 1;
            
        if *lane == RATE {
            permute(state);
            *lane = 0;
        }
    };

    absorb(dom_fe, &mut state, &mut lane);

    // Absorb input as 32-byte chunks folded into field elements.
    let mut chunk = [0u8; 32];
    let mut i = 0usize;
            
    while i < data.len() {
        let end = core::cmp::min(i + 32, data.len());
        let len = end - i;
        chunk[..len].copy_from_slice(&data[i..end]);
                
        if len < 32 {
            for b in &mut chunk[len..] {
                *b = 0;
            }
        }
        
        let fe = crate::utils::fold_bytes32_to_fe(&chunk);
        absorb(fe, &mut state, &mut lane);
    
        i = end;
    }

    if lane != 0 {
        permute(&mut state);
    }

    state[0]
}

/// Select Poseidon rounds for the commitment/coin hasher.
/// Default is 27 (matches ROM/trace). Can be lowered for
/// local testing via env var ZKL_POSEIDON_HASHER_ROUNDS.
fn hasher_rounds() -> usize {
    std::env::var("ZKL_POSEIDON_HASHER_ROUNDS")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .filter(|&v| v > 0)
        .unwrap_or(27)
}


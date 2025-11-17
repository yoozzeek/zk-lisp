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
        let fe = poseidon::poseidon_ro_bytes_sponge(
            &POSEIDON_SUITE_ID,
            "zkl/winter/hash/bytes",
            bytes_in,
        );
        PoseidonDigest(utils::fe_to_bytes_fold(fe))
    }

    fn merge(values: &[Self::Digest; 2]) -> Self::Digest {
        let mut buf = [0u8; 64];
        buf[0..32].copy_from_slice(&values[0].0);
        buf[32..64].copy_from_slice(&values[1].0);

        let fe =
            poseidon::poseidon_ro_bytes_sponge(&POSEIDON_SUITE_ID, "zkl/winter/hash/merge", &buf);

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

        let fe = poseidon::poseidon_ro_bytes_sponge(
            &POSEIDON_SUITE_ID,
            "zkl/winter/hash/merge_many",
            &buf,
        );

        PoseidonDigest(utils::fe_to_bytes_fold(fe))
    }

    fn merge_with_int(seed: Self::Digest, value: u64) -> Self::Digest {
        let mut buf = [0u8; 40];
        buf[0..32].copy_from_slice(&seed.0);
        buf[32..40].copy_from_slice(&value.to_le_bytes());

        let fe = poseidon::poseidon_ro_bytes_sponge(
            &POSEIDON_SUITE_ID,
            "zkl/winter/hash/merge_with_int",
            &buf,
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
        let fe = poseidon::poseidon_ro_bytes_sponge(
            &POSEIDON_SUITE_ID,
            "winter/hash/elements",
            bytes_in,
        );

        PoseidonDigest(utils::fe_to_bytes_fold(fe))
    }
}

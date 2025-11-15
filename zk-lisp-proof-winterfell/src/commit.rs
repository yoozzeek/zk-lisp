// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Program commitment utilities.
//!
//! Computes the Blake3 byte-level program commitment and a
//! field-level Poseidon commitment derived from it, used to
//! bind VM execution, RAM randomizers and ROM encodings.

use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;

pub fn program_commitment(bytes: &[u8]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(bytes);

    let mut out = [0u8; 32];
    out.copy_from_slice(hasher.finalize().as_bytes());

    out
}

/// Compute a field-friendly (internal)
/// program commitment using Poseidon2
/// absorbing the 32-byte Blake3 digest
/// as two field elements and returning
/// two field elements (≈256-bit). This
/// is intended for in-circuit binding.
pub fn program_field_commitment(blake32: &[u8; 32]) -> [BE; 2] {
    let sid = blake32;
    let suite = crate::poseidon::get_poseidon_suite(sid);

    // Map 32 bytes into two field
    // elements (little-endian halves).
    let mut le16a = [0u8; 16];
    let mut le16b = [0u8; 16];
    le16a.copy_from_slice(&blake32[0..16]);
    le16b.copy_from_slice(&blake32[16..32]);

    let fe_from_le16 = |b: [u8; 16]| -> BE {
        let val = u128::from_le_bytes(b);
        let lo = (val & 0xFFFF_FFFF_FFFF_FFFFu128) as u64;
        let hi = (val >> 64) as u64;

        BE::from(lo) + BE::from(hi) * crate::utils::pow2_64()
    };

    let a = fe_from_le16(le16a);
    let b = fe_from_le16(le16b);

    // Initialize 12-lane state: (a,b) in
    // lanes 0..1, domain tags in lanes 10..11
    let mut s = [BE::ZERO; 12];
    s[0] = a;
    s[1] = b;
    s[10] = suite.dom[0];
    s[11] = suite.dom[1];

    for rc in suite.rc.iter() {
        for x in &mut s {
            *x = *x * *x * *x;
        }

        let mut y = [BE::ZERO; 12];
        for (i, row) in suite.mds.iter().enumerate() {
            let acc = row
                .iter()
                .zip(s.iter())
                .fold(BE::ZERO, |acc, (m, v)| acc + (*m) * (*v));
            y[i] = acc + rc[i];
        }

        s = y;
    }

    [s[0], s[1]]
}

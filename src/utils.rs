// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use std::sync::OnceLock;
use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;

// Cached 2^64 in BaseElement
static POW2_64_BE: OnceLock<BE> = OnceLock::new();

#[inline]
pub fn pow2_64() -> BE {
    *POW2_64_BE.get_or_init(|| {
        let mut acc = BE::ONE;
        let two = BE::from(2u64);

        for _ in 0..64 {
            acc *= two;
        }

        acc
    })
}

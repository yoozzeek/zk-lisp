// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! High-degree mixers used to randomize grouped constraints.
//!
//! Provides small helpers for combining periodic schedule
//! selectors and program commitments into mixing scalars
//! with controlled algebraic degree.

use crate::layout::POSEIDON_ROUNDS;
use winterfell::math::FieldElement;

pub(super) fn low<E: FieldElement>(periodic: &[E]) -> E {
    // s_low = p_last * p_map
    let p_map = periodic[0];
    let p_last = periodic[1 + POSEIDON_ROUNDS + 3];

    p_last * p_map
}

#[inline]
pub(super) fn pi1<E: FieldElement>(periodic: &[E], pi: E) -> E {
    low(periodic) * pi
}

#[inline]
pub(super) fn pi4<E: FieldElement>(periodic: &[E], pi: E) -> E {
    let pi2 = pi * pi;
    let pi4 = pi2 * pi2;

    low(periodic) * pi4
}

#[inline]
pub(super) fn pi6<E: FieldElement>(periodic: &[E], pi: E) -> E {
    // pi^6 = (pi^2)^3
    let pi2 = pi * pi;
    let pi4 = pi2 * pi2;
    let pi6 = pi4 * pi2;

    low(periodic) * pi6
}

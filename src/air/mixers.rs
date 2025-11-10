use crate::layout::POSEIDON_ROUNDS;
use winterfell::math::FieldElement;

// Constraint mixing helpers for AIR blocks.
// These are NOT cryptographic; they shape CE degrees and
// gate contributions to the last-row exemption and map rows.

pub(crate) fn low<E: FieldElement>(periodic: &[E]) -> E {
    // s_low = p_last * p_map
    let p_map = periodic[0];
    let p_last = periodic[1 + POSEIDON_ROUNDS + 3];

    p_last * p_map
}

#[inline]
pub(crate) fn pi1<E: FieldElement>(periodic: &[E], pi: E) -> E {
    low(periodic) * pi
}

#[inline]
pub(crate) fn pi2<E: FieldElement>(periodic: &[E], pi: E) -> E {
    let pi2 = pi * pi;
    low(periodic) * pi2
}

#[inline]
pub(crate) fn pi4<E: FieldElement>(periodic: &[E], pi: E) -> E {
    let pi2 = pi * pi;
    let pi4 = pi2 * pi2;

    low(periodic) * pi4
}

#[inline]
pub(crate) fn pi5<E: FieldElement>(periodic: &[E], pi: E) -> E {
    pi4(periodic, pi) * pi
}

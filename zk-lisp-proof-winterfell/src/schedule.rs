// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Periodic schedule for one level and utilities.
//!
//! Exposes helpers for mapping row positions inside a level
//! (map, round, final, pad) and building periodic selector
//! columns used by AIR constraints.

use crate::layout::{POSEIDON_ROUNDS, STEPS_PER_LEVEL_P2};

#[inline]
pub fn pos_map() -> usize {
    0
}

#[inline]
pub fn is_round_pos(pos: usize) -> bool {
    (1..=POSEIDON_ROUNDS).contains(&pos)
}

#[inline]
pub fn pos_final() -> usize {
    1 + POSEIDON_ROUNDS
}

// Build periodic selectors
// over the full trace length n.
// Columns: p_map, p_r[0..R-1],
// p_final, p_pad, p_pad_last, p_last
pub fn build_periodic_selectors(n: usize) -> Vec<Vec<u8>> {
    let cycle = STEPS_PER_LEVEL_P2;
    let cols_len = 1 + POSEIDON_ROUNDS + 1 + 1 + 1 + 1;
    let mut out: Vec<Vec<u8>> = (0..cols_len).map(|_| vec![0u8; n]).collect();

    if n == 0 {
        return out;
    }

    for row in 0..n {
        let pos = row % cycle;

        // map
        if pos == pos_map() {
            out[0][row] = 1;
        }

        // rounds
        for j in 0..POSEIDON_ROUNDS {
            if pos == 1 + j {
                out[1 + j][row] = 1;
            }
        }

        // final
        if pos == pos_final() {
            out[1 + POSEIDON_ROUNDS][row] = 1;
        }

        // pad
        let is_pad = pos != pos_map() && pos != pos_final() && !is_round_pos(pos);
        if is_pad {
            out[1 + POSEIDON_ROUNDS + 1][row] = 1;
        }

        // last pad in level
        if pos == (cycle - 1) {
            out[1 + POSEIDON_ROUNDS + 2][row] = 1;
        }
    }

    // last row in full trace
    out[1 + POSEIDON_ROUNDS + 3][n - 1] = 1;

    out
}

#[cfg(test)]
mod tests {
    use crate::schedule;

    #[test]
    fn schedule_shapes() {
        let n = 32;
        let cols = schedule::build_periodic_selectors(n);

        assert!(!cols.is_empty());

        for c in cols.iter() {
            assert_eq!(c.len(), n);
        }
    }
}

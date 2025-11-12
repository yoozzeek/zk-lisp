// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

//! Trace builder orchestrator

pub mod poseidon;
pub mod vm;

use winterfell::TraceTable;
use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;

use crate::layout::{Columns, POSEIDON_ROUNDS, STEPS_PER_LEVEL_P2};
use crate::schedule;

pub struct TraceBuilder;

impl TraceBuilder {
    pub fn build_empty_levels(levels: usize) -> TraceTable<BE> {
        let cols = Columns::baseline();
        let width = cols.width(0);
        let n_rows = levels * STEPS_PER_LEVEL_P2;

        let mut trace = TraceTable::new(width, n_rows);

        Self::zero_all(&mut trace, width, n_rows);
        Self::tie_schedule_gates_for_rows(&mut trace, n_rows);

        trace
    }

    pub fn zero_all(trace: &mut TraceTable<BE>, width: usize, n_rows: usize) {
        trace.fill(
            |state| {
                state.fill(BE::ZERO);
            },
            |_, state| {
                state.fill(BE::ZERO);
            },
        );

        let _ = (width, n_rows);
    }

    pub fn tie_schedule_gates_for_rows(trace: &mut TraceTable<BE>, n_rows: usize) {
        let cols = Columns::baseline();
        let steps = STEPS_PER_LEVEL_P2;

        for row in 0..n_rows {
            let pos = row % steps;
            if pos == schedule::pos_map() {
                trace.set(cols.g_map, row, BE::ONE);
            }

            if pos == schedule::pos_final() {
                trace.set(cols.g_final, row, BE::ONE);
            }

            for j in 0..POSEIDON_ROUNDS {
                let rj = 1 + j;
                if pos == rj {
                    trace.set(cols.g_r_index(j), row, BE::ONE);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use winterfell::Trace;

    #[test]
    fn empty_levels_schedule() {
        let levels = 2;
        let trace = TraceBuilder::build_empty_levels(levels);
        let cols = Columns::baseline();
        let steps = STEPS_PER_LEVEL_P2;
        let n_rows = levels * steps;

        for lvl in 0..levels {
            let base = lvl * steps;

            assert_eq!(trace.get(cols.g_map, base + schedule::pos_map()), BE::ONE);
            assert_eq!(
                trace.get(cols.g_final, base + schedule::pos_final()),
                BE::ONE
            );

            for j in 0..POSEIDON_ROUNDS {
                assert_eq!(trace.get(cols.g_r_index(j), base + 1 + j), BE::ONE);
            }
        }

        assert_eq!(trace.length(), n_rows);
    }
}

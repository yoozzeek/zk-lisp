// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! High-level trace builder for the Winterfell backend.
//!
//! Constructs the unified execution trace from a compiled
//! [`Program`] and [`pi::PublicInputs`], delegating to VM,
//! RAM and ROM modules and seeding VM arguments when present.

mod poseidon;
mod ram;
mod rom;
mod vm;

use crate::layout::{Columns, NR, POSEIDON_ROUNDS, STEPS_PER_LEVEL_P2};
use crate::poseidon::get_poseidon_suite;
use crate::schedule;
use crate::trace::ram::{RamEvent, RamTraceBuilder};
use crate::trace::rom::RomTraceBuilder;
use crate::trace::vm::VmTraceBuilder;

use std::collections::BTreeMap;
use winterfell::TraceTable;
use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;
use zk_lisp_compiler::Program;
use zk_lisp_proof::error;
use zk_lisp_proof::pi;

trait TraceModule {
    fn fill_table(
        &mut self,
        ctx: &TraceBuilderContext,
        trace: &mut TraceTable<BE>,
    ) -> error::Result<()>;
}

pub struct TraceBuilderContext<'a> {
    pub(crate) prog: &'a Program,
    pub(crate) cols: Columns,
    pub(crate) levels: usize,
    pub(crate) steps: usize,
}

/// Initialize trace builder
/// from program and public inputs.
#[tracing::instrument(level = "info", skip(pi))]
pub fn build_trace(prog: &Program, pi: &pi::PublicInputs) -> error::Result<TraceTable<BE>> {
    let levels = prog.ops.len();
    let cols = Columns::baseline();
    let steps = STEPS_PER_LEVEL_P2;
    let total_levels = levels.next_power_of_two();

    let mut trace = build_empty_trace(total_levels);

    // PC is set consistently across levels
    for lvl in 0..total_levels {
        let base = lvl * steps;
        for r in base..(base + steps) {
            trace.set(cols.pc, r, BE::from(lvl as u64));
        }
    }

    // Ensure Poseidon domain tags are
    // present on map rows for all levels.
    let dom_all = get_poseidon_suite(&prog.commitment).dom;
    for lvl in 0..total_levels {
        let base = lvl * steps;
        let row_map = base + schedule::pos_map();
        trace.set(cols.lane_c0, row_map, dom_all[0]);
        trace.set(cols.lane_c1, row_map, dom_all[1]);
    }

    // RAM: host-side memory map
    // and event log (addr, clk, val, is_write)
    let mut ram_events: Vec<RamEvent> = Vec::new();
    let mut mem: BTreeMap<u128, BE> = BTreeMap::new();

    let ctx = &TraceBuilderContext {
        prog,
        cols,
        levels,
        steps,
    };

    // Init VM trace core, seeding secret VM args
    // and main_args into the initial register file.
    VmTraceBuilder::new(&mut mem, &mut ram_events, &pi.secret_args, &pi.main_args)
        .fill_table(ctx, &mut trace)?;

    // Populate sorted RAM table across pad rows
    RamTraceBuilder::new(&ctx.prog.commitment, ram_events.as_mut_slice())
        .fill_table(ctx, &mut trace)?;

    // Populate ROM accumulator t=3 across all levels
    RomTraceBuilder::new().fill_table(ctx, &mut trace)?;

    Ok(trace)
}

pub(super) fn build_empty_trace(total_levels: usize) -> TraceTable<BE> {
    let cols = Columns::baseline();
    let width = cols.width(0);
    let n_rows = total_levels * STEPS_PER_LEVEL_P2;

    let mut trace = TraceTable::new(width, n_rows);

    // Zero all
    trace.fill(
        |state| {
            state.fill(BE::ZERO);
        },
        |_, state| {
            state.fill(BE::ZERO);
        },
    );

    // Schedule gates
    for row in 0..n_rows {
        let pos = row % STEPS_PER_LEVEL_P2;
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

    trace
}

/// Select partitioning parameters for
/// a trace of given width and length.
pub fn select_partitions_for_trace(trace_width: usize, trace_length: usize) -> (usize, usize) {
    let hash_rate = trace_width.clamp(1, 256);
    if trace_length <= (1 << 14) || trace_width <= 16 {
        return (1, hash_rate);
    }

    let num_partitions = if trace_length >= (1 << 20) {
        8
    } else if trace_length >= (1 << 18) {
        4
    } else if trace_length >= (1 << 16) {
        2
    } else {
        1
    };

    (num_partitions, hash_rate)
}

#[inline]
pub(super) fn set_sel(trace: &mut TraceTable<BE>, row: usize, sel_start: usize, idx: u8) {
    for i in 0..NR {
        trace.set(sel_start + i, row, BE::ZERO);
    }

    trace.set(sel_start + (idx as usize), row, BE::ONE);
}

#[cfg(test)]
mod tests {
    use super::*;
    use winterfell::Trace;

    #[test]
    fn empty_levels_schedule() {
        let levels = 2;
        let trace = build_empty_trace(levels);
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

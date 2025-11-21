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

use crate::poseidon::get_poseidon_suite;
use crate::utils;
use crate::vm::layout::{Columns, NR, POSEIDON_ROUNDS, STEPS_PER_LEVEL_P2};
use crate::vm::schedule;
use crate::vm::trace::ram::{RamEvent, RamTraceBuilder};
use crate::vm::trace::rom::RomTraceBuilder;
use crate::vm::trace::vm::VmTraceBuilder;

use std::collections::BTreeMap;
use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::{Trace, TraceTable};
use zk_lisp_compiler::Program;
use zk_lisp_proof::error;
use zk_lisp_proof::pi;
use zk_lisp_proof::segment::Segment;

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

/// Minimal previous-state handle used when constructing
/// segment traces for step-level proofs. For now this
/// carries only the VM state_out hash of the previous
/// segment; additional fields can be added later without
/// affecting callers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrevState {
    pub state_out_hash: [u8; 32],
}

/// Initialize trace builder
/// from program and public inputs.
#[tracing::instrument(level = "info", skip(pi))]
pub fn build_trace(prog: &Program, pi: &pi::PublicInputs) -> error::Result<TraceTable<BE>> {
    build_full_trace(prog, pi)
}

/// Build an execution trace for a specific row segment
/// `[segment.r_start, segment.r_end)`.
#[tracing::instrument(level = "info", skip(pi, segment))]
pub fn build_segment_trace(
    prog: &Program,
    pi: &pi::PublicInputs,
    segment: &Segment,
) -> error::Result<TraceTable<BE>> {
    if segment.r_start >= segment.r_end {
        return Err(error::Error::InvalidInput(
            "build_segment_trace requires r_start < r_end",
        ));
    }

    // Compute the full-trace length implied by the
    // program so we can validate the requested
    // segment against it.
    let levels = prog.ops.len();
    let total_levels = levels.next_power_of_two();
    let full_len = total_levels * STEPS_PER_LEVEL_P2;

    if segment.r_end > full_len {
        return Err(error::Error::InvalidInput(
            "build_segment_trace segment out of bounds for trace length",
        ));
    }

    // Enforce level alignment so that segment boundaries
    // always coincide with full VM levels.
    if segment.r_start % STEPS_PER_LEVEL_P2 != 0 || segment.r_end % STEPS_PER_LEVEL_P2 != 0 {
        return Err(error::Error::InvalidInput(
            "build_segment_trace requires segments aligned to full levels",
        ));
    }

    let full = build_full_trace(prog, pi)?;
    Ok(slice_trace_segment(&full, segment))
}

/// Build a segment trace together with VM state hashes at
/// the segment boundaries. This is the primary entrypoint
/// for step-level proof construction.
#[tracing::instrument(level = "info", skip(pi, prev_state, segment))]
pub fn build_segment_trace_with_state(
    prog: &Program,
    pi: &pi::PublicInputs,
    segment: &Segment,
    prev_state: Option<&PrevState>,
) -> error::Result<(TraceTable<BE>, [u8; 32], [u8; 32])> {
    if segment.r_start >= segment.r_end {
        return Err(error::Error::InvalidInput(
            "build_segment_trace_with_state requires r_start < r_end",
        ));
    }

    let levels = prog.ops.len();
    let total_levels = levels.next_power_of_two();
    let full_len = total_levels * STEPS_PER_LEVEL_P2;

    if segment.r_end > full_len {
        return Err(error::Error::InvalidInput(
            "build_segment_trace_with_state segment out of bounds for trace length",
        ));
    }

    if segment.r_start % STEPS_PER_LEVEL_P2 != 0 || segment.r_end % STEPS_PER_LEVEL_P2 != 0 {
        return Err(error::Error::InvalidInput(
            "build_segment_trace_with_state requires segments aligned to full levels",
        ));
    }

    let full = build_full_trace(prog, pi)?;

    build_segment_trace_with_state_without_full(&full, segment, prev_state)
}

/// Slice an already built full trace into a segment trace and compute
/// segment-local VM state hashes. This avoids rebuilding the full trace.
#[tracing::instrument(level = "info", skip(full, prev_state, segment))]
pub fn build_segment_trace_with_state_without_full(
    full: &TraceTable<BE>,
    segment: &Segment,
    prev_state: Option<&PrevState>,
) -> error::Result<(TraceTable<BE>, [u8; 32], [u8; 32])> {
    if segment.r_start >= segment.r_end {
        return Err(error::Error::InvalidInput(
            "build_segment_trace_with_state_without_full requires r_start < r_end",
        ));
    }

    let n_rows_full = full.length();
    if segment.r_end > n_rows_full {
        return Err(error::Error::InvalidInput(
            "segment out of bounds for provided full trace",
        ));
    }

    if segment.r_start % STEPS_PER_LEVEL_P2 != 0 || segment.r_end % STEPS_PER_LEVEL_P2 != 0 {
        return Err(error::Error::InvalidInput(
            "segment must be aligned to full levels",
        ));
    }

    let trace = slice_trace_segment(full, segment);
    let trace_len = trace.length();

    let row0_map = schedule::pos_map();
    let state_in_hash = utils::vm_state_hash_row(&trace, row0_map);

    // For segment chaining we want the VM state at the end of this
    // segment, not the program-level output row. The last row of the
    // segment carries the post-final register file for the last level.
    let last_row = trace_len.saturating_sub(1);
    let state_out_hash = utils::vm_state_hash_row(&trace, last_row);

    if let Some(prev) = prev_state {
        if prev.state_out_hash != state_in_hash {
            return Err(error::Error::InvalidInput(
                "prev_state.state_out_hash must match segment state_in_hash",
            ));
        }
    }

    Ok((trace, state_in_hash, state_out_hash))
}

/// Public helper to slice an already built full trace without computing
/// state hashes. Provided for callers that only need the segment trace.
#[tracing::instrument(level = "info", skip(full, segment))]
pub fn build_segment_trace_without_full(
    full: &TraceTable<BE>,
    segment: &Segment,
) -> error::Result<TraceTable<BE>> {
    if segment.r_start >= segment.r_end {
        return Err(error::Error::InvalidInput(
            "build_segment_trace_without_full requires r_start < r_end",
        ));
    }

    if segment.r_end > full.length() {
        return Err(error::Error::InvalidInput(
            "segment out of bounds for provided full trace",
        ));
    }

    if segment.r_start % STEPS_PER_LEVEL_P2 != 0 || segment.r_end % STEPS_PER_LEVEL_P2 != 0 {
        return Err(error::Error::InvalidInput(
            "segment must be aligned to full levels",
        ));
    }

    Ok(slice_trace_segment(full, segment))
}

fn build_full_trace(prog: &Program, pi: &pi::PublicInputs) -> error::Result<TraceTable<BE>> {
    let t_all = std::time::Instant::now();
    let levels = prog.ops.len();
    let cols = Columns::baseline();
    let steps = STEPS_PER_LEVEL_P2;
    let total_levels = levels.next_power_of_two();

    let t_empty = std::time::Instant::now();
    let mut trace = build_empty_trace(total_levels);

    tracing::debug!(
        target="trace.build",
        total_levels=%total_levels,
        steps=%steps,
        elapsed_ms=%t_empty.elapsed().as_millis(),
        "empty trace ready",
    );

    // PC is set consistently across levels
    let t_pc = std::time::Instant::now();
    for lvl in 0..total_levels {
        let base = lvl * steps;
        for r in base..(base + steps) {
            trace.set(cols.pc, r, BE::from(lvl as u64));
        }
    }

    tracing::debug!(target="trace.build", elapsed_ms=%t_pc.elapsed().as_millis(), "pc lanes filled");

    // Ensure Poseidon domain tags are
    // present on map rows for all levels.
    let dom_all = get_poseidon_suite(&prog.commitment).dom;
    let t_tags = std::time::Instant::now();
    for lvl in 0..total_levels {
        let base = lvl * steps;
        let row_map = base + schedule::pos_map();
        trace.set(cols.lane_c0, row_map, dom_all[0]);
        trace.set(cols.lane_c1, row_map, dom_all[1]);
    }

    tracing::debug!(target="trace.build", elapsed_ms=%t_tags.elapsed().as_millis(), "poseidon tags filled");

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
    let t_vm = std::time::Instant::now();
    VmTraceBuilder::new(&mut mem, &mut ram_events, &pi.secret_args, &pi.main_args)
        .fill_table(ctx, &mut trace)?;

    tracing::debug!(
        target="trace.build",
        elapsed_ms=%t_vm.elapsed().as_millis(),
        "vm filled",
    );

    // Populate sorted RAM table across pad rows
    let t_ram = std::time::Instant::now();
    RamTraceBuilder::new(&ctx.prog.commitment, ram_events.as_mut_slice())
        .fill_table(ctx, &mut trace)?;

    tracing::debug!(
        target="trace.build",
        elapsed_ms=%t_ram.elapsed().as_millis(),
        "ram filled",
    );

    // Populate ROM accumulator t=3 across all levels
    let t_rom = std::time::Instant::now();
    RomTraceBuilder::new().fill_table(ctx, &mut trace)?;

    tracing::debug!(
        target="trace.build",
        elapsed_ms=%t_rom.elapsed().as_millis(),
        total_ms=%t_all.elapsed().as_millis(),
        "rom filled, trace build done",
    );

    Ok(trace)
}

fn slice_trace_segment(full: &TraceTable<BE>, segment: &Segment) -> TraceTable<BE> {
    let width = full.width();
    let seg_len = segment.r_end - segment.r_start;
    let mut out = TraceTable::new(width, seg_len);

    for col in 0..width {
        for row in 0..seg_len {
            let src_row = segment.r_start + row;
            out.set(col, row, full.get(col, src_row));
        }
    }

    out
}

pub(crate) fn build_empty_trace(total_levels: usize) -> TraceTable<BE> {
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
    let hash_rate = if trace_width <= 32 { 8 } else { 16 };
    if trace_length <= (1 << 14) || trace_width <= 16 {
        return (1, hash_rate);
    }

    let num_partitions = if trace_length >= (1 << 20) {
        16
    } else if trace_length >= (1 << 18) {
        8
    } else if trace_length >= (1 << 16) {
        4
    } else {
        1
    };

    (num_partitions, hash_rate)
}

#[inline]
pub(crate) fn set_sel(trace: &mut TraceTable<BE>, row: usize, sel_start: usize, idx: u8) {
    for i in 0..NR {
        trace.set(sel_start + i, row, BE::ZERO);
    }

    trace.set(sel_start + (idx as usize), row, BE::ONE);
}

#[cfg(test)]
mod tests {
    use super::*;
    use winterfell::Trace;
    use zk_lisp_compiler::CompilerMetrics;
    use zk_lisp_compiler::builder::{self, Op};
    use zk_lisp_proof::pi::PublicInputs;

    #[test]
    fn build_segment_trace_with_state_matches_legacy_state_hashes() {
        let metrics = CompilerMetrics::default();
        let mut b = builder::ProgramBuilder::new();

        b.push(Op::Const { dst: 0, imm: 7 });
        b.push(Op::Const { dst: 1, imm: 9 });
        b.push(Op::Add { dst: 2, a: 0, b: 1 });
        b.push(Op::End);

        let p = b.finalize(metrics).expect("finalize must succeed");
        let pi = PublicInputs::default();

        let full = build_trace(&p, &pi).expect("build_trace must succeed");
        let seg = Segment::new(0, full.length()).expect("segment must be valid");

        // Legacy computation of state hashes used by prove_step.
        let row0_map = schedule::pos_map();
        let legacy_state_in = crate::utils::vm_state_hash_row(&full, row0_map);
        let (_out_reg, out_row) = crate::utils::vm_output_from_trace(&full);
        let out_row_usize = (out_row as usize).min(full.length().saturating_sub(1));
        let legacy_state_out = crate::utils::vm_state_hash_row(&full, out_row_usize);

        let (seg_trace, state_in, state_out) = build_segment_trace_with_state(&p, &pi, &seg, None)
            .expect("build_segment_trace_with_state must succeed");

        assert_eq!(seg_trace.width(), full.width());
        assert_eq!(seg_trace.length(), full.length());

        for row in 0..full.length() {
            for col in 0..full.width() {
                assert_eq!(seg_trace.get(col, row), full.get(col, row));
            }
        }

        assert_eq!(state_in, legacy_state_in);
        assert_eq!(state_out, legacy_state_out);
    }

    #[test]
    fn build_segment_trace_with_state_rejects_prev_state_mismatch() {
        let metrics = CompilerMetrics::default();
        let mut b = builder::ProgramBuilder::new();

        b.push(Op::Const { dst: 0, imm: 1 });
        b.push(Op::End);

        let p = b.finalize(metrics).expect("finalize must succeed");
        let pi = PublicInputs::default();

        let full = build_trace(&p, &pi).expect("build_trace must succeed");
        let seg = Segment::new(0, full.length()).expect("segment must be valid");

        let bogus_prev = PrevState {
            state_out_hash: [1u8; 32],
        };

        let err = build_segment_trace_with_state(&p, &pi, &seg, Some(&bogus_prev))
            .expect_err("prev_state mismatch must be rejected");
        match err {
            error::Error::InvalidInput(msg) => {
                assert!(msg.contains("prev_state.state_out_hash"));
            }
        }
    }

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

    #[test]
    fn segment_trace_matches_full_trace_for_single_segment() {
        let metrics = CompilerMetrics::default();
        let mut b = builder::ProgramBuilder::new();

        b.push(Op::Const { dst: 0, imm: 7 });
        b.push(Op::Const { dst: 1, imm: 9 });
        b.push(Op::Add { dst: 2, a: 0, b: 1 });
        b.push(Op::End);

        let p = b.finalize(metrics).expect("finalize must succeed");
        let pi = PublicInputs::default();

        let full = build_trace(&p, &pi).expect("build_trace must succeed");
        let seg = Segment::new(0, full.length()).expect("segment must be valid");
        let sliced = build_segment_trace(&p, &pi, &seg).expect("build_segment_trace must succeed");

        assert_eq!(sliced.width(), full.width());
        assert_eq!(sliced.length(), full.length());

        for row in 0..full.length() {
            for col in 0..full.width() {
                assert_eq!(sliced.get(col, row), full.get(col, row));
            }
        }
    }

    #[test]
    fn segment_trace_rejects_out_of_bounds_segment() {
        let metrics = CompilerMetrics::default();
        let mut b = builder::ProgramBuilder::new();

        b.push(Op::Const { dst: 0, imm: 1 });
        b.push(Op::End);

        let p = b.finalize(metrics).expect("finalize must succeed");
        let pi = PublicInputs::default();

        let full = build_trace(&p, &pi).expect("build_trace must succeed");
        let out_of_bounds =
            Segment::new(0, full.length() + 1).expect("segment struct allows construction");

        let err =
            build_segment_trace(&p, &pi, &out_of_bounds).expect_err("must fail for oob segment");
        match err {
            error::Error::InvalidInput(msg) => {
                assert!(msg.contains("segment out of bounds"));
            }
        }
    }
}

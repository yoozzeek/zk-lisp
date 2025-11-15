// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! RAM trace construction for sorted and unsorted tables.
//!
//! Builds the sorted RAM view, last-write witnesses,
//! delta_clk gadget bits and random-compressor accumulators
//! consistent with the RAM AIR constraints.

use crate::commit::program_field_commitment;
use crate::layout::{NR, STEPS_PER_LEVEL_P2};
use crate::schedule;
use crate::trace::{TraceBuilderContext, TraceModule};

use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::math::{FieldElement, StarkField};
use winterfell::{Trace, TraceTable};
use zk_lisp_proof::error;

/// RamEvent(addr, clk, val, is_write)
pub(super) type RamEvent = (BE, BE, BE, BE);

pub(super) struct RamTraceBuilder<'a> {
    commitment: &'a [u8; 32],
    ram_events: &'a mut [RamEvent],
}

impl<'a> RamTraceBuilder<'a> {
    pub fn new(commitment: &'a [u8; 32], ram_events: &'a mut [RamEvent]) -> Self {
        Self {
            commitment,
            ram_events,
        }
    }
}

impl<'a> TraceModule for RamTraceBuilder<'a> {
    fn fill_table(
        &mut self,
        ctx: &TraceBuilderContext,
        trace: &mut TraceTable<BE>,
    ) -> error::Result<()> {
        // Place sorted events by (addr, clk)
        self.ram_events.sort_by(|a, b| {
            let (aa, ac) = (a.0.as_int(), a.1.as_int());
            let (ba, bc) = (b.0.as_int(), b.1.as_int());

            aa.cmp(&ba).then(ac.cmp(&bc))
        });

        let mut it = self.ram_events.iter();
        for row in 0..trace.length() {
            // decide if row is a pad row
            let pos = row % STEPS_PER_LEVEL_P2;
            let is_pad = pos != schedule::pos_map()
                && pos != schedule::pos_final()
                && !schedule::is_round_pos(pos);

            if is_pad {
                if let Some(ev) = it.next() {
                    trace.set(ctx.cols.ram_sorted, row, BE::ONE);
                    trace.set(ctx.cols.ram_s_addr, row, ev.0);
                    trace.set(ctx.cols.ram_s_clk, row, ev.1);
                    trace.set(ctx.cols.ram_s_val, row, ev.2);
                    trace.set(ctx.cols.ram_s_is_write, row, ev.3);
                } else {
                    trace.set(ctx.cols.ram_sorted, row, BE::ZERO);
                }
            } else {
                trace.set(ctx.cols.ram_sorted, row, BE::ZERO);
            }
        }

        // Randomized compressor
        // coefficients (match AIR).
        let fc = program_field_commitment(self.commitment);
        let pi_be = fc[0];
        let pi2 = pi_be * pi_be;
        let pi3 = pi2 * pi_be;
        let pi4 = pi2 * pi2;
        let pi5 = pi4 * pi_be;
        let r1 = pi2 + BE::ONE;
        let r2 = pi3 + pi_be;
        let r3 = pi5 + BE::from(7u64);

        let mut gp_sorted_vals = vec![BE::ZERO; trace.length()];
        let mut last_write_vals = vec![BE::ZERO; trace.length()];

        for row in 0..trace.length() {
            // Carry gp_sorted from
            // previous row by default
            let mut gp_sorted_cur = if row > 0 {
                gp_sorted_vals[row - 1]
            } else {
                BE::ZERO
            };

            // Apply previous row's
            // sorted update into this row.
            if row > 0 && trace.get(ctx.cols.ram_sorted, row - 1) == BE::ONE {
                let prev = row - 1;
                let cur_addr = trace.get(ctx.cols.ram_s_addr, prev);
                let clk = trace.get(ctx.cols.ram_s_clk, prev);
                let val = trace.get(ctx.cols.ram_s_val, prev);
                let w = trace.get(ctx.cols.ram_s_is_write, prev);

                let comp = cur_addr + r1 * clk + r2 * val + r3 * w;
                gp_sorted_cur += comp;
            }

            gp_sorted_vals[row] = gp_sorted_cur;
            trace.set(ctx.cols.ram_gp_sorted, row, gp_sorted_cur);

            // Build last_write as next-state
            // of previous sorted row.
            let mut last_cur = if row > 0 {
                last_write_vals[row - 1]
            } else {
                BE::ZERO
            };

            if row > 0 && trace.get(ctx.cols.ram_sorted, row - 1) == BE::ONE {
                let prev = row - 1;
                let s_addr = trace.get(ctx.cols.ram_s_addr, prev);
                let s_w = trace.get(ctx.cols.ram_s_is_write, prev);
                let s_val = trace.get(ctx.cols.ram_s_val, prev);
                let s_addr_n = trace.get(ctx.cols.ram_s_addr, row);
                let same = (s_addr_n == s_addr) as u8; // 1 if same, 0 otherwise

                if same == 1 {
                    // same group:
                    // (1 - w) * last + w * val
                    last_cur = (BE::ONE - s_w) * last_cur + s_w * s_val;
                } else {
                    // new addr:
                    // must be write to seed;
                    // last_next = w * val
                    last_cur = s_w * s_val;
                }
            }

            last_write_vals[row] = last_cur;
            trace.set(ctx.cols.ram_s_last_write, row, last_cur);
        }

        // Populate RAM delta_clk gadget
        // bits on sorted rows for same-addr pairs.
        for row in 0..(trace.length().saturating_sub(1)) {
            if trace.get(ctx.cols.ram_sorted, row) == BE::ONE {
                let s_addr = trace.get(ctx.cols.ram_s_addr, row);
                let s_addr_n = trace.get(ctx.cols.ram_s_addr, row + 1);

                // Set inv witness for same_addr
                // check (always from next row addr).
                let d_addr = s_addr_n - s_addr;
                let inv = if d_addr != BE::ZERO {
                    d_addr.inv()
                } else {
                    BE::ZERO
                };

                trace.set(ctx.cols.eq_inv, row, inv);

                if trace.get(ctx.cols.ram_sorted, row + 1) == BE::ONE && s_addr_n == s_addr {
                    // same-addr:
                    // set gadget bits for delta_clk
                    let clk = trace.get(ctx.cols.ram_s_clk, row).as_int();
                    let clk_n = trace.get(ctx.cols.ram_s_clk, row + 1).as_int();

                    let mut delta = clk_n.saturating_sub(clk);
                    for i in 0..32 {
                        let bit = (delta & 1) as u64;
                        let v = BE::from(bit);

                        trace.set(ctx.cols.gadget_b_index(i), row, v);
                        delta >>= 1;
                    }
                }
            }
        }

        // Build gp_unsorted across
        // all rows (carry), update
        // at final rows with events.
        let mut gp_uns_vals = vec![BE::ZERO; trace.length()];

        for row in 0..trace.length() {
            // carry from previous row by default
            let mut gp_uns_cur = if row > 0 {
                gp_uns_vals[row - 1]
            } else {
                BE::ZERO
            };

            // If previous row was an event (final row),
            // apply its update into this row.
            if row > 0 {
                let prev = row - 1;
                let pos_prev = prev % STEPS_PER_LEVEL_P2;
                if pos_prev == schedule::pos_final() {
                    let is_load = trace.get(ctx.cols.op_load, prev) == BE::ONE;
                    let is_store = trace.get(ctx.cols.op_store, prev) == BE::ONE;

                    if is_load || is_store {
                        let mut a_ev = BE::ZERO;
                        let mut b_ev = BE::ZERO;

                        for i in 0..NR {
                            let ri = trace.get(ctx.cols.r_index(i), prev);
                            a_ev += trace.get(ctx.cols.sel_a_index(i), prev) * ri;
                            b_ev += trace.get(ctx.cols.sel_b_index(i), prev) * ri;
                        }

                        let w_ev = if is_store { BE::ONE } else { BE::ZERO };
                        let val_ev = w_ev * b_ev + (BE::ONE - w_ev) * trace.get(ctx.cols.imm, prev);
                        let clk_ev = trace.get(ctx.cols.pc, prev);
                        let addr_ev = a_ev;

                        let comp = addr_ev + r1 * clk_ev + r2 * val_ev + r3 * w_ev;
                        gp_uns_cur += comp;
                    }
                }
            }

            gp_uns_vals[row] = gp_uns_cur;
            trace.set(ctx.cols.ram_gp_unsorted, row, gp_uns_cur);
        }

        Ok(())
    }
}

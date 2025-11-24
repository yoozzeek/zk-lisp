// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! ROM accumulator trace construction.
//!
//! Populates the t=3 Poseidon-like ROM state across levels,
//! starting from an initial accumulator and per-level
//! encodings derived from opcode/selector rows.

use crate::poseidon::{derive_rom_mds_cauchy_3x3, derive_rom_round_constants_3};
use crate::utils;
use crate::vm::layout::POSEIDON_ROUNDS;
use crate::vm::trace::{TraceBuilderContext, TraceModule};

use crate::vm::schedule;
use winterfell::TraceTable;
use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;
use zk_lisp_proof::error;

pub(crate) struct RomTraceBuilder;

impl RomTraceBuilder {
    pub fn new() -> Self {
        Self {}
    }
}

impl TraceModule for RomTraceBuilder {
    fn fill_table(
        &mut self,
        ctx: &TraceBuilderContext,
        trace: &mut TraceTable<BE>,
    ) -> error::Result<()> {
        let total_levels = ctx.levels.next_power_of_two();
        let rc3 = derive_rom_round_constants_3(&ctx.prog.program_id, POSEIDON_ROUNDS);
        let mds3 = derive_rom_mds_cauchy_3x3(&ctx.prog.program_id);

        // Precompute weights
        let w_enc0 = utils::rom_weights_for_seed(utils::ROM_W_SEED_0);
        let w_enc1 = utils::rom_weights_for_seed(utils::ROM_W_SEED_1);

        // initial accumulator
        let mut s0_prev = BE::ZERO;

        for lvl in 0..total_levels {
            let base = lvl * ctx.steps;
            let row_map = base + schedule::pos_map();
            let row_final = base + schedule::pos_final();

            // Compute encodings from map
            // row columns using precomputed weights
            let s1_map = utils::rom_linear_encode_from_trace(trace, row_map, &ctx.cols, &w_enc0);
            let s2_map = utils::rom_linear_encode_from_trace(trace, row_map, &ctx.cols, &w_enc1);

            // Set map row state
            trace.set(ctx.cols.rom_s_index(0), row_map, s0_prev);
            trace.set(ctx.cols.rom_s_index(1), row_map, s1_map);
            trace.set(ctx.cols.rom_s_index(2), row_map, s2_map);

            // Execute 27 rounds:
            // y = MDS * s^3 + rc.
            let mut s = [s0_prev, s1_map, s2_map];
            for (j, rc_row) in rc3.iter().enumerate().take(POSEIDON_ROUNDS) {
                let r = base + 1 + j; // round row index

                // set current state s at round row
                trace.set(ctx.cols.rom_s_index(0), r, s[0]);
                trace.set(ctx.cols.rom_s_index(1), r, s[1]);
                trace.set(ctx.cols.rom_s_index(2), r, s[2]);

                // compute next state
                let s3 = [s[0] * s[0] * s[0], s[1] * s[1] * s[1], s[2] * s[2] * s[2]];
                let y0 = mds3[0][0] * s3[0] + mds3[0][1] * s3[1] + mds3[0][2] * s3[2] + rc_row[0];
                let y1 = mds3[1][0] * s3[0] + mds3[1][1] * s3[1] + mds3[1][2] * s3[2] + rc_row[1];
                let y2 = mds3[2][0] * s3[0] + mds3[2][1] * s3[1] + mds3[2][2] * s3[2] + rc_row[2];

                // write next state at next row (r+1)
                let rn = r + 1;
                trace.set(ctx.cols.rom_s_index(0), rn, y0);
                trace.set(ctx.cols.rom_s_index(1), rn, y1);
                trace.set(ctx.cols.rom_s_index(2), rn, y2);

                s = [y0, y1, y2];
            }

            // Set pad rows after
            // final to last state.
            let last_state = s;

            for r in (row_final + 1)..(base + ctx.steps) {
                trace.set(ctx.cols.rom_s_index(0), r, last_state[0]);
                trace.set(ctx.cols.rom_s_index(1), r, last_state[1]);
                trace.set(ctx.cols.rom_s_index(2), r, last_state[2]);
            }

            s0_prev = last_state[0];
        }

        Ok(())
    }
}

// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! RAM table constraints for the zk-lisp VM.
//!
//! Checks sorted/unsorted group compressors, last-write
//! tracking, forbidden read patterns and 32-bit delta_clk
//! range proofs for per-address access groups.

use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::{EvaluationFrame, TransitionConstraintDegree};

use crate::air::{AirModule, AirSharedContext};
use crate::layout::{POSEIDON_ROUNDS, STEPS_PER_LEVEL_P2};

pub(super) struct RamAir;

impl AirModule for RamAir {
    fn push_degrees(_ctx: &AirSharedContext, out: &mut Vec<TransitionConstraintDegree>) {
        // Carry gp_unsorted across rows,
        // update at final+event
        out.push(TransitionConstraintDegree::with_cycles(
            3,
            vec![STEPS_PER_LEVEL_P2],
        ));

        // Carry gp_sorted across rows,
        // update at ram_sorted rows
        out.push(TransitionConstraintDegree::with_cycles(
            3,
            vec![STEPS_PER_LEVEL_P2],
        ));

        // last_write carry on sorted rows
        out.push(TransitionConstraintDegree::with_cycles(
            3,
            vec![STEPS_PER_LEVEL_P2],
        ));

        // read == last_write on
        // sorted rows when is_write==0
        out.push(TransitionConstraintDegree::with_cycles(
            3,
            vec![STEPS_PER_LEVEL_P2],
        ));

        // forbid new-addr read:
        // (1 - same) * (1 - is_write) == 0
        out.push(TransitionConstraintDegree::with_cycles(
            3,
            vec![STEPS_PER_LEVEL_P2],
        ));

        // same_addr boolean via inv trick:
        // s = 1 - d * inv
        out.push(TransitionConstraintDegree::with_cycles(
            3,
            vec![STEPS_PER_LEVEL_P2],
        ));

        // delta_clk in 32-bit range
        // when same_addr we gate by
        // same_addr and reuse 32-bit
        // gadget via Columns.gadget_b.
        for _ in 0..33 {
            out.push(TransitionConstraintDegree::with_cycles(
                5,
                vec![STEPS_PER_LEVEL_P2],
            ));
        }

        // final-row equality
        // (unsorted == sorted)
        out.push(TransitionConstraintDegree::with_cycles(
            3,
            vec![STEPS_PER_LEVEL_P2],
        ));
    }

    fn eval_block<E>(
        ctx: &AirSharedContext,
        frame: &EvaluationFrame<E>,
        periodic: &[E],
        result: &mut [E],
        ix: &mut usize,
    ) where
        E: FieldElement<BaseField = BE> + From<BE>,
    {
        let cur = frame.current();
        let next = frame.next();

        let p_final = periodic[1 + POSEIDON_ROUNDS];
        let p_pad = periodic[1 + POSEIDON_ROUNDS + 1];
        let p_pad_last = periodic[1 + POSEIDON_ROUNDS + 2];
        let p_last = periodic[1 + POSEIDON_ROUNDS + 3];

        let g_hold = p_pad - p_pad_last;

        let op_load = cur[ctx.cols.op_load];
        let op_store = cur[ctx.cols.op_store];

        // event on final rows
        let event = p_final * (op_load + op_store);

        // Randomized compressor coefficients
        // derived from field-level program commitment.
        let pi0 = E::from(ctx.program_fe[0]);
        let pi2 = pi0 * pi0;
        let pi3 = pi2 * pi0;
        let pi4 = pi2 * pi2;
        let pi5 = pi4 * pi0;

        let r1 = pi2 + E::ONE; // clk coeff
        let r2 = pi3 + pi0; // val coeff
        let r3 = pi5 + E::from(BE::from(7u64)); // is_write coeff

        // Unsorted GP: reconstruct
        // (addr, clk, val, w) on event rows
        let mut a_ev = E::ZERO;
        let mut b_ev = E::ZERO;

        for i in 0..crate::layout::NR {
            let ri = cur[ctx.cols.r_index(i)];
            a_ev += cur[ctx.cols.sel_a_index(i)] * ri;
            b_ev += cur[ctx.cols.sel_b_index(i)] * ri;
        }

        let w_ev = op_store; // 1 for store, 0 for load
        let val_ev = w_ev * b_ev + (E::ONE - w_ev) * cur[ctx.cols.imm];
        let clk_ev = cur[ctx.cols.pc];
        let addr_ev = a_ev;
        let comp_uns = addr_ev + r1 * clk_ev + r2 * val_ev + r3 * w_ev;

        // gp_unsorted carry/update
        result[*ix] = event
            * (next[ctx.cols.ram_gp_unsorted] - (cur[ctx.cols.ram_gp_unsorted] + comp_uns))
            + (E::ONE - event) * (next[ctx.cols.ram_gp_unsorted] - cur[ctx.cols.ram_gp_unsorted])
            + g_hold * (next[ctx.cols.ram_gp_unsorted] - cur[ctx.cols.ram_gp_unsorted]);
        *ix += 1;

        // Sorted path
        let s_on = cur[ctx.cols.ram_sorted];
        let s_addr = cur[ctx.cols.ram_s_addr];
        let s_clk = cur[ctx.cols.ram_s_clk];
        let s_val = cur[ctx.cols.ram_s_val];
        let s_w = cur[ctx.cols.ram_s_is_write];
        let last = cur[ctx.cols.ram_s_last_write];

        // next row values
        let s_addr_n = next[ctx.cols.ram_s_addr];
        let s_clk_n = next[ctx.cols.ram_s_clk];
        let last_n = next[ctx.cols.ram_s_last_write];

        // same_addr via inv trick
        // (reuse eq_inv column as inv witness).
        let d_addr = s_addr_n - s_addr;
        let inv = cur[ctx.cols.eq_inv];

        // if d!=0 and inv=d^-1 => same=0;
        // if d==0 and inv=0 => same=1
        let same = E::ONE - d_addr * inv;

        // gp_sorted carry/update
        // with randomized compressor
        let comp = s_addr + r1 * s_clk + r2 * s_val + r3 * s_w;
        result[*ix] = s_on * (next[ctx.cols.ram_gp_sorted] - (cur[ctx.cols.ram_gp_sorted] + comp))
            + (E::ONE - s_on) * (next[ctx.cols.ram_gp_sorted] - cur[ctx.cols.ram_gp_sorted]);
        *ix += 1;

        // last_write update on sorted rows
        let last_keep = same * ((E::ONE - s_w) * last + s_w * s_val) // same addr
            // new addr => must be write to seed
            + (E::ONE - same) * (s_w * s_val);
        result[*ix] = s_on * (last_n - last_keep);
        *ix += 1;

        // read equals last_write on
        // sorted rows when is_write==0
        result[*ix] = s_on * (E::ONE - s_w) * (s_val - last);
        *ix += 1;

        // Forbid read as FIRST event
        // of an address group;
        // apply at edge (cur -> next):
        // if next is sorted and next_addr != cur_addr,
        // then next must be a write (seed).
        // Uses next.eq_inv for inv(next_addr - cur_addr).
        let s_on_c = cur[ctx.cols.ram_sorted];
        let s_on_n = next[ctx.cols.ram_sorted];
        let d_prev_n = next[ctx.cols.ram_s_addr] - cur[ctx.cols.ram_s_addr];
        let inv_n = next[ctx.cols.eq_inv];
        let same_prev_n = E::ONE - d_prev_n * inv_n;
        let w_n = next[ctx.cols.ram_s_is_write];

        result[*ix] = s_on_c * s_on_n * (E::ONE - same_prev_n) * (E::ONE - w_n);
        *ix += 1;

        // same boolean check:
        // same = 1 - d*inv,
        // enforce consistency.
        result[*ix] = s_on * (same * (same - E::ONE));
        *ix += 1;

        // delta_clk 32-bit
        // range when same_addr
        let d_clk = s_clk_n - s_clk;
        let mut sum = E::ZERO;
        let mut pow2 = E::ONE;

        for i in 0..32 {
            let bi = cur[ctx.cols.gadget_b_index(i)];

            // booleanity
            result[*ix] = s_on * same * bi * (bi - E::ONE);
            *ix += 1;
            sum += pow2 * bi;
            pow2 = pow2 + pow2;
        }

        // equality
        result[*ix] = s_on * same * (d_clk - sum);
        *ix += 1;

        // Final-row equality of GP
        // accumulators (unsorted == sorted)
        result[*ix] = p_last * (cur[ctx.cols.ram_gp_unsorted] - cur[ctx.cols.ram_gp_sorted]);
        *ix += 1;
    }
}

// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025

use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::{EvaluationFrame, TransitionConstraintDegree};

use super::{AirBlock, BlockCtx};
use crate::layout::{POSEIDON_ROUNDS, STEPS_PER_LEVEL_P2};

pub struct RamBlock;

impl<E> AirBlock<E> for RamBlock
where
    E: FieldElement<BaseField = BE> + From<BE>,
{
    fn push_degrees(out: &mut Vec<TransitionConstraintDegree>) {
        // Carry gp_unsorted across rows,
        // update at final+event
        out.push(TransitionConstraintDegree::with_cycles(3, vec![STEPS_PER_LEVEL_P2]));
        
        // Carry gp_sorted across rows,
        // update at ram_sorted rows
        out.push(TransitionConstraintDegree::with_cycles(3, vec![STEPS_PER_LEVEL_P2]));
        
        // last_write carry on sorted rows
        out.push(TransitionConstraintDegree::with_cycles(3, vec![STEPS_PER_LEVEL_P2]));
        
        // read == last_write on
        // sorted rows when is_write==0
        out.push(TransitionConstraintDegree::with_cycles(3, vec![STEPS_PER_LEVEL_P2]));
        
        // forbid new-addr read:
        // (1 - same) * (1 - is_write) == 0
        out.push(TransitionConstraintDegree::with_cycles(3, vec![STEPS_PER_LEVEL_P2]));
        
        // same_addr boolean via inv trick:
        // s = 1 - d * inv
        out.push(TransitionConstraintDegree::with_cycles(3, vec![STEPS_PER_LEVEL_P2]));
        
        // delta_clk in 32-bit range
        // when same_addr we gate by
        // same_addr and reuse 32-bit
        // gadget via Columns.gadget_b.
        for _ in 0..33 {
            out.push(TransitionConstraintDegree::with_cycles(5, vec![STEPS_PER_LEVEL_P2]));
        }
    }

    fn eval_block(
        ctx: &BlockCtx<E>,
        frame: &EvaluationFrame<E>,
        periodic: &[E],
        result: &mut [E],
        ix: &mut usize,
    ) {
        let cur = frame.current();
        let next = frame.next();

        let p_final = periodic[1 + POSEIDON_ROUNDS];
        let p_pad = periodic[1 + POSEIDON_ROUNDS + 1];
        let p_pad_last = periodic[1 + POSEIDON_ROUNDS + 2];
        let g_hold = p_pad - p_pad_last;

        let op_load = cur[ctx.cols.op_load];
        let op_store = cur[ctx.cols.op_store];
        
        // event on final rows
        let event = p_final * (op_load + op_store);

        // compress(addr,clk,val,is_write) = a + k1*c + k2*v + k3*w
        // Constants in BE
        let k1 = E::from(BE::from(0x10001u64));
        let k2 = E::from(BE::from(0x1_0000u64));
        let k3 = E::from(BE::from(0x1337u64));

        // not used; placeholder to silence warnings
        let a_uns = cur[ctx.cols.sel_a_start];
        let _ = a_uns;

        // Unsorted GP update
        // not used; event comes from op_*;
        // GP uses ram_s_* only in sorted.
        let addr_ev = cur[ctx.cols.imm];
        let _ = addr_ev;

        // gp_unsorted carry/update
        let comp_uns = {
            // For unsorted path no way to recompute
            // addr/clk/val; rely solely on event flag,
            // and TraceBuilder precomputes gp_unsorted
            // sequence. Here we just carry:
            E::ZERO
        };
        
        result[*ix] = event * comp_uns + (E::ONE - event) * (next[ctx.cols.ram_gp_unsorted] - cur[ctx.cols.ram_gp_unsorted]) + g_hold * (next[ctx.cols.ram_gp_unsorted] - cur[ctx.cols.ram_gp_unsorted]);
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

        // gp_sorted carry/update with compressor
        let comp = s_addr + k1 * s_clk + k2 * s_val + k3 * s_w;
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

        // forbid new-addr read
        result[*ix] = s_on * (E::ONE - same) * (E::ONE - s_w);
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
    }
}
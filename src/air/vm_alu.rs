// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::{EvaluationFrame, TransitionConstraintDegree};

use super::{AirBlock, BlockCtx};
use crate::air::mixers;
use crate::layout::{NR, POSEIDON_ROUNDS, STEPS_PER_LEVEL_P2};

pub struct VmAluBlock;

impl<E> AirBlock<E> for VmAluBlock
where
    E: FieldElement<BaseField = BE> + From<BE>,
{
    fn push_degrees(out: &mut Vec<TransitionConstraintDegree>) {
        // carry registers on non-final rows
        for _ in 0..NR {
            out.push(TransitionConstraintDegree::with_cycles(
                1,
                vec![STEPS_PER_LEVEL_P2],
            ));
        }

        // write registers at final (op-gated)
        for _ in 0..NR {
            out.push(TransitionConstraintDegree::with_cycles(
                6,
                vec![STEPS_PER_LEVEL_P2],
            ));
        }

        // equality ties (dst reflects [a==b])
        for _ in 0..2 {
            out.push(TransitionConstraintDegree::with_cycles(
                5,
                vec![STEPS_PER_LEVEL_P2],
            ));
        }

        // assert enforcer (c==1 at final)
        out.push(TransitionConstraintDegree::with_cycles(
            5,
            vec![STEPS_PER_LEVEL_P2],
        ));

        // AssertBit:
        // booleanity r(r-1)=0 at final
        out.push(TransitionConstraintDegree::with_cycles(
            5,
            vec![STEPS_PER_LEVEL_P2],
        ));

        // AssertRange (32-bit): 
        // 32 bit booleanities + equality r - sum(2^i b_i) = 0
        for _ in 0..32 {
            out.push(TransitionConstraintDegree::with_cycles(
                5,
                vec![STEPS_PER_LEVEL_P2],
            ));
        }

        out.push(TransitionConstraintDegree::with_cycles(
            5,
            vec![STEPS_PER_LEVEL_P2],
        ));
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

        let p_map = periodic[0];
        let p_final = periodic[1 + POSEIDON_ROUNDS];
        let p_pad = periodic[1 + POSEIDON_ROUNDS + 1];
        let p_pad_last = periodic[1 + POSEIDON_ROUNDS + 2];

        // mixers
        let pi = cur[ctx.cols.pi_prog];
        let s_low = mixers::low(periodic);
        let s_write = mixers::pi5(periodic, pi); // pi^5
        // keep eq mixer degree lower than writes
        let s_eq = mixers::pi4(periodic, pi);

        // carry when next row is not final within the level
        let mut g_carry = p_map + (p_pad - p_pad_last);
        for gr in (0..(POSEIDON_ROUNDS - 1)).map(|j| periodic[1 + j]) {
            g_carry += gr;
        }

        // reconstruct a/b/c from
        // role selectors and regs.
        let mut a_val = E::ZERO;
        let mut b_val = E::ZERO;
        let mut c_val = E::ZERO;

        for i in 0..NR {
            let r = cur[ctx.cols.r_index(i)];
            a_val += cur[ctx.cols.sel_a_index(i)] * r;
            b_val += cur[ctx.cols.sel_b_index(i)] * r;
            c_val += cur[ctx.cols.sel_c_index(i)] * r;
        }

        // carry r[i] across rows where next is not final
        for i in 0..NR {
            result[*ix] = g_carry * (next[ctx.cols.r_index(i)] - cur[ctx.cols.r_index(i)]) + s_low;
            *ix += 1;
        }

        // compute op result (excluding Eq),
        // including Hash2 via lane_l.
        let imm = cur[ctx.cols.imm];
        let b_const = cur[ctx.cols.op_const];
        let b_mov = cur[ctx.cols.op_mov];
        let b_add = cur[ctx.cols.op_add];
        let b_sub = cur[ctx.cols.op_sub];
        let b_mul = cur[ctx.cols.op_mul];
        let b_neg = cur[ctx.cols.op_neg];
        let b_eq = cur[ctx.cols.op_eq];
        let b_sel = cur[ctx.cols.op_select];
        let b_sponge = cur[ctx.cols.op_sponge];
        let b_assert = cur[ctx.cols.op_assert];
        let b_assert_bit = cur[ctx.cols.op_assert_bit];
        let b_assert_range = cur[ctx.cols.op_assert_range];

        // include Eq via dst_next so
        // generic write can be uniform.
        let mut dst_next = E::ZERO; // sum dst_i * r_i_next
        for i in 0..NR {
            dst_next += cur[ctx.cols.sel_dst_index(i)] * next[ctx.cols.r_index(i)];
        }

        let res = b_const * imm
            + b_mov * a_val
            + b_add * (a_val + b_val)
            + b_sub * (a_val - b_val)
            + b_mul * (a_val * b_val)
            + b_neg * (E::ZERO - a_val)
            + b_sel * (c_val * a_val + (E::ONE - c_val) * b_val)
            + b_sponge * cur[ctx.cols.lane_l]
            + b_eq * dst_next
            + b_assert * E::ONE
            + b_assert_bit * E::ONE
            + b_assert_range * E::ONE;

        // write at final: r' = (1-dst)*r + dst*res (uniform for all ops)
        for i in 0..NR {
            let dsti = cur[ctx.cols.sel_dst_index(i)];
            result[*ix] = p_final
                * (next[ctx.cols.r_index(i)]
                    - ((E::ONE - dsti) * cur[ctx.cols.r_index(i)] + dsti * res))
                + s_write;
            *ix += 1;
        }

        let diff = a_val - b_val;
        let inv = cur[ctx.cols.eq_inv];

        // if dst_next==1 => diff==0
        result[*ix] = p_final * b_eq * (dst_next * diff) + s_eq;
        *ix += 1;

        // if diff!=0 => dst_next==0
        // via (1 - dst_next) - diff*inv == 0
        result[*ix] = p_final * b_eq * ((E::ONE - dst_next) - diff * inv) + s_eq;
        *ix += 1;

        // assert: require c_val == 1 at final
        // and enforce c booleanity for SELECT at final
        result[*ix] =
            p_final * (b_assert * (c_val - E::ONE) + b_sel * (c_val * (c_val - E::ONE))) + s_eq;
        *ix += 1;

        // AssertBit: c_val in {0,1}
        result[*ix] = p_final * b_assert_bit * (c_val * (c_val - E::ONE)) + s_eq;
        *ix += 1;

        // AssertRange: booleanity for witness
        // bits and reconstruction equality
        let mut sum = E::ZERO;
        let mut pow2 = E::ONE;
        for i in 0..32 {
            let bi = cur[ctx.cols.rng_b_index(i)];
            // booleanity for each bi
            result[*ix] = p_final * b_assert_range * (bi * (bi - E::ONE)) + s_eq;
            *ix += 1;

            sum += pow2 * bi;
            // multiply by 2 via addition
            // to avoid constants table.
            pow2 = pow2 + pow2;
        }

        // reconstruction:
        // c_val == sum(2^i * b_i)
        result[*ix] = p_final * b_assert_range * (c_val - sum) + s_eq;
        *ix += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::layout::Columns;
    use winterfell::EvaluationFrame;

    #[test]
    fn assert_enforcer_violates_when_false() {
        let cols = Columns::baseline();
        let mut frame = EvaluationFrame::<BE>::new(cols.width(0));
        let mut periodic = vec![BE::ZERO; 1 + POSEIDON_ROUNDS + 1 + 1 + 1 + 1];

        // final row
        periodic[1 + POSEIDON_ROUNDS] = BE::ONE;

        // Select c from r0, set r0 = 0 => c_val = 0 -> violation
        frame.current_mut()[cols.op_assert] = BE::ONE;
        frame.current_mut()[cols.sel_c_index(0)] = BE::ONE;
        frame.current_mut()[cols.r_index(0)] = BE::ZERO;

        // next row copies registers
        // (not used for assert constraint besides dst)
        // Allocate a sufficiently large buffer
        // for all constraints in this block.
        let mut res = vec![BE::ZERO; 1024];
        let mut ix = 0usize;

        let rc_box = Box::new([[BE::ZERO; 12]; POSEIDON_ROUNDS]);
        let mds_box = Box::new({
            let mut m = [[BE::ZERO; 12]; 12];
            for (i, row) in m.iter_mut().enumerate() {
                row[i] = BE::ONE;
            }

            m
        });

        VmAluBlock::eval_block(
            &BlockCtx::new(
                &cols,
                &Default::default(),
                &rc_box,
                &mds_box,
                &Box::new([BE::ZERO; 2]),
            ),
            &frame,
            &periodic,
            &mut res,
            &mut ix,
        );

        assert!(res.iter().any(|v| *v != BE::ZERO));
    }
}

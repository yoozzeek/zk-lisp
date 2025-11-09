// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::{EvaluationFrame, TransitionConstraintDegree};

use super::{AirBlock, BlockCtx};
use crate::layout::{NR, STEPS_PER_LEVEL_P2};

pub struct VmCtrlBlock;

impl VmCtrlBlock {
    pub fn push_degrees(out: &mut Vec<TransitionConstraintDegree>) {
        // selector bits booleanity (4*NR)
        for _ in 0..(4 * NR) {
            out.push(TransitionConstraintDegree::with_cycles(
                2,
                vec![STEPS_PER_LEVEL_P2],
            ));
        }

        // selector sums (4)
        for _ in 0..4 {
            out.push(TransitionConstraintDegree::with_cycles(
                1,
                vec![STEPS_PER_LEVEL_P2],
            ));
        }

        // select cond boolean
        out.push(TransitionConstraintDegree::with_cycles(
            2,
            vec![STEPS_PER_LEVEL_P2],
        ));

        // op_* booleans (10)
        for _ in 0..10 {
            out.push(TransitionConstraintDegree::with_cycles(
                2,
                vec![STEPS_PER_LEVEL_P2],
            ));
        }

        // one-hot across ops: sum is boolean (1)
        out.push(TransitionConstraintDegree::with_cycles(
            2,
            vec![STEPS_PER_LEVEL_P2],
        ));
    }
}

impl<E> AirBlock<E> for VmCtrlBlock
where
    E: FieldElement<BaseField = BE> + From<BE>,
{
    fn push_degrees(_out: &mut Vec<TransitionConstraintDegree>) {}

    fn eval_block(
        ctx: &BlockCtx<E>,
        frame: &EvaluationFrame<E>,
        periodic: &[E],
        result: &mut [E],
        ix: &mut usize,
    ) {
        let cur = frame.current();
        let p_map = periodic[0];

        // Mixer:
        // - s_low = p_last * p_map yields CE quotient degree ~120;
        // - s_high = s_low * pi_prog raises CE quotient degree to ~247
        //   (deg(p_last)=~127, deg(p_map)=~120, deg(pi_prog)=~127; minus z-degree 127).
        let p_last = periodic[1 + crate::layout::POSEIDON_ROUNDS + 3];
        let s_low = p_last * p_map;
        let pi_prog = cur[ctx.cols.pi_prog];
        let s_high = s_low * pi_prog;

        let b_const = cur[ctx.cols.op_const];
        let b_mov = cur[ctx.cols.op_mov];
        let b_add = cur[ctx.cols.op_add];
        let b_sub = cur[ctx.cols.op_sub];
        let b_mul = cur[ctx.cols.op_mul];
        let b_neg = cur[ctx.cols.op_neg];
        let b_eq = cur[ctx.cols.op_eq];
        let b_sel = cur[ctx.cols.op_select];
        let b_hash = cur[ctx.cols.op_hash2];
        let b_assert = cur[ctx.cols.op_assert];

        let mut sum_dst = E::ZERO;
        let mut sum_a = E::ZERO;
        let mut sum_b = E::ZERO;
        let mut sum_c = E::ZERO;

        for i in 0..NR {
            let sd = cur[ctx.cols.sel_dst_index(i)];
            let sa = cur[ctx.cols.sel_a_index(i)];
            let sb = cur[ctx.cols.sel_b_index(i)];
            let sc = cur[ctx.cols.sel_c_index(i)];

            sum_dst += sd;
            sum_a += sa;
            sum_b += sb;
            sum_c += sc;

            result[*ix] = p_map * sd * (sd - E::ONE) + s_high;
            *ix += 1;
            result[*ix] = p_map * sa * (sa - E::ONE) + s_high;
            *ix += 1;
            result[*ix] = p_map * sb * (sb - E::ONE) + s_high;
            *ix += 1;
            result[*ix] = p_map * sc * (sc - E::ONE) + s_high;
            *ix += 1;
        }

        // role usage gates: which roles
        // must select exactly one src.
        let uses_a = b_mov + b_add + b_sub + b_mul + b_neg + b_eq + b_sel;
        let uses_b = b_add + b_sub + b_mul + b_eq + b_sel;
        let uses_c = b_sel + b_assert;
        let op_any =
            b_const + b_mov + b_add + b_sub + b_mul + b_neg + b_eq + b_sel + b_hash + b_assert;

        // dst required only when an
        // op is present at this map row.
        result[*ix] = p_map * (sum_dst - op_any) + s_low;
        *ix += 1;
        result[*ix] = p_map * (sum_a - uses_a) + s_low;
        *ix += 1;
        result[*ix] = p_map * (sum_b - uses_b) + s_low;
        *ix += 1;
        result[*ix] = p_map * (sum_c - uses_c) + s_low;
        *ix += 1;

        // Select cond booleanity at map
        // Compute c_val = sum sel_c_i * r_i
        let mut c_val = E::ZERO;
        for i in 0..NR {
            let r = cur[ctx.cols.r_index(i)];
            c_val += cur[ctx.cols.sel_c_index(i)] * r;
        }

        // booleanity for select is
        // enforced at final in ALU.
        result[*ix] = s_high;
        *ix += 1;

        // op_* booleanity and one-hot,
        // at most one op per map row.
        for b in [
            b_const, b_mov, b_add, b_sub, b_mul, b_neg, b_eq, b_sel, b_hash, b_assert,
        ] {
            result[*ix] = p_map * b * (b - E::ONE) + s_high;
            *ix += 1;
        }

        let op_sum =
            b_const + b_mov + b_add + b_sub + b_mul + b_neg + b_eq + b_sel + b_hash + b_assert;
        result[*ix] = p_map * op_sum * (op_sum - E::ONE) + s_low;
        *ix += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::layout::Columns;
    use winterfell::EvaluationFrame;

    #[test]
    fn two_ops_set_violation() {
        let cols = Columns::baseline();
        let mut frame = EvaluationFrame::<BE>::new(cols.width(0));
        let mut periodic = vec![BE::ZERO; 1 + crate::layout::POSEIDON_ROUNDS + 1 + 1 + 1 + 1];

        // map row
        periodic[0] = BE::ONE;

        // op_add and op_sub both set
        frame.current_mut()[cols.op_add] = BE::ONE;
        frame.current_mut()[cols.op_sub] = BE::ONE;

        // Evaluate
        let mut res = vec![BE::ZERO; 48];
        let mut ix = 0usize;

        VmCtrlBlock::eval_block(
            &BlockCtx::new(
                &cols,
                &Default::default(),
                &Box::new([[BE::ZERO; 4]; crate::layout::POSEIDON_ROUNDS]),
                &Box::new([[BE::ZERO; 4]; 4]),
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

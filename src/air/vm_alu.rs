use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::{EvaluationFrame, TransitionConstraintDegree};

use super::{AirBlock, BlockCtx};
use crate::layout::{NR, POSEIDON_ROUNDS, STEPS_PER_LEVEL_P2};

pub struct VmAluBlock;

impl VmAluBlock {
    pub fn push_degrees(out: &mut Vec<TransitionConstraintDegree>) {
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
                4,
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
    }
}

impl<E> AirBlock<E> for VmAluBlock
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
        let next = frame.next();

        let p_map = periodic[0];
        let p_final = periodic[1 + POSEIDON_ROUNDS];
        let p_pad = periodic[1 + POSEIDON_ROUNDS + 1];
        let p_last = periodic[1 + POSEIDON_ROUNDS + 3];

        // mixers
        let s_low = p_last * p_map;
        let pi = cur[ctx.cols.pi_prog];
        let s_write = s_low * pi * pi * pi;
        let s_eq = s_write * pi;

        // carry when next row is not final within the level:
        // map rows, rounds 0..R-2, and all pad rows
        let mut g_carry = p_map + p_pad;
        for j in 0..(POSEIDON_ROUNDS - 1) {
            g_carry += periodic[1 + j];
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
        let b_hash = cur[ctx.cols.op_hash2];
        let b_assert = cur[ctx.cols.op_assert];

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
            + b_hash * cur[ctx.cols.lane_l]
            + b_eq * dst_next
            + b_assert * E::ONE;

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
        result[*ix] = p_final * b_assert * (c_val - E::ONE) + s_eq;
        *ix += 1;
    }
}

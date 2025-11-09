// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::{EvaluationFrame, TransitionConstraintDegree};

use super::{AirBlock, BlockCtx};
use crate::layout::{NR, POSEIDON_ROUNDS, STEPS_PER_LEVEL_P2};

pub struct PoseidonBlock;

impl PoseidonBlock {
    pub fn push_degrees(out: &mut Vec<TransitionConstraintDegree>) {
        // Per-round Poseidon
        // transitions (4 lanes per round)
        for _ in 0..POSEIDON_ROUNDS {
            for _ in 0..4 {
                out.push(TransitionConstraintDegree::with_cycles(
                    3,
                    vec![STEPS_PER_LEVEL_P2],
                ));
            }
        }

        // Hold constraints on non-round rows:
        // pad rows except last pad)
        // base=1 (linear), cycles=1
        for _ in 0..4 {
            out.push(TransitionConstraintDegree::with_cycles(
                1,
                vec![STEPS_PER_LEVEL_P2],
            ));
        }
    }

    pub fn push_degrees_vm_bind(out: &mut Vec<TransitionConstraintDegree>) {
        // VM->lane binding at map row for
        // Hash2 (lane_l and lane_r).
        // base=3 (b_hash * (lane - sum sel*reg)),
        // cycles=1 (p_map)
        for _ in 0..2 {
            out.push(TransitionConstraintDegree::with_cycles(
                3,
                vec![STEPS_PER_LEVEL_P2],
            ));
        }
    }
}

impl<E> AirBlock<E> for PoseidonBlock
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
        let mm = ctx.poseidon_mds;

        // Gate for map-row constraints
        let p_map = periodic[0];

        for j in 0..POSEIDON_ROUNDS {
            let gr = periodic[1 + j];

            let sl = cur[ctx.cols.lane_l];
            let sr = cur[ctx.cols.lane_r];
            let sc0 = cur[ctx.cols.lane_c0];
            let sc1 = cur[ctx.cols.lane_c1];

            let sl3 = sl * sl * sl;
            let sr3 = sr * sr * sr;
            let sc03 = sc0 * sc0 * sc0;
            let sc13 = sc1 * sc1 * sc1;

            let rc = &ctx.poseidon_rc[j];
            let yl = E::from(mm[0][0]) * sl3
                + E::from(mm[0][1]) * sr3
                + E::from(mm[0][2]) * sc03
                + E::from(mm[0][3]) * sc13
                + E::from(rc[0]);
            let yr = E::from(mm[1][0]) * sl3
                + E::from(mm[1][1]) * sr3
                + E::from(mm[1][2]) * sc03
                + E::from(mm[1][3]) * sc13
                + E::from(rc[1]);
            let yc0 = E::from(mm[2][0]) * sl3
                + E::from(mm[2][1]) * sr3
                + E::from(mm[2][2]) * sc03
                + E::from(mm[2][3]) * sc13
                + E::from(rc[2]);
            let yc1 = E::from(mm[3][0]) * sl3
                + E::from(mm[3][1]) * sr3
                + E::from(mm[3][2]) * sc03
                + E::from(mm[3][3]) * sc13
                + E::from(rc[3]);

            result[*ix] = gr * (next[ctx.cols.lane_l] - yl);
            *ix += 1;
            result[*ix] = gr * (next[ctx.cols.lane_r] - yr);
            *ix += 1;
            result[*ix] = gr * (next[ctx.cols.lane_c0] - yc0);
            *ix += 1;
            result[*ix] = gr * (next[ctx.cols.lane_c1] - yc1);
            *ix += 1;
        }

        // Hold lanes on non-round rows:
        // final and pad rows except last pad.
        let p_pad = periodic[1 + POSEIDON_ROUNDS + 1];
        let p_pad_last = periodic[1 + POSEIDON_ROUNDS + 2];
        let g_hold = p_pad - p_pad_last;

        result[*ix] = g_hold * (next[ctx.cols.lane_l] - cur[ctx.cols.lane_l]);
        *ix += 1;
        result[*ix] = g_hold * (next[ctx.cols.lane_r] - cur[ctx.cols.lane_r]);
        *ix += 1;
        result[*ix] = g_hold * (next[ctx.cols.lane_c0] - cur[ctx.cols.lane_c0]);
        *ix += 1;
        result[*ix] = g_hold * (next[ctx.cols.lane_c1] - cur[ctx.cols.lane_c1]);
        *ix += 1;

        // Bind map-row lanes to VM-selected
        // inputs when sponge ops are enabled;
        // gated by op_hash2 at map row.
        if ctx.pub_inputs.get_features().vm && ctx.pub_inputs.get_features().sponge {
            let b_hash = cur[ctx.cols.op_hash2];

            let mut a_val = E::ZERO;
            let mut b_val = E::ZERO;

            for i in 0..NR {
                a_val += cur[ctx.cols.sel_a_index(i)] * cur[ctx.cols.r_index(i)];
                b_val += cur[ctx.cols.sel_b_index(i)] * cur[ctx.cols.r_index(i)];
            }

            result[*ix] = p_map * b_hash * (cur[ctx.cols.lane_l] - a_val);
            *ix += 1;
            result[*ix] = p_map * b_hash * (cur[ctx.cols.lane_r] - b_val);
            *ix += 1;
        }
    }
}

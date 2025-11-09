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
        // map/final/pad except last pad;
        // base=3 to cover x^3 terms and s_pos; 
        // cycles=2 to conservatively account for 
        // two periodic factors (e.g. p_map and p_last)
        // in mixers.
        for _ in 0..4 {
            out.push(TransitionConstraintDegree::with_cycles(
                3,
                vec![STEPS_PER_LEVEL_P2],
            ));
        }

        // VM->lane binding at map row for
        // Hash2 (lane_l and lane_r).
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
        let ver = cur[ctx.cols.kv_version];

        // mixers for Poseidon constraints:
        // use deg~(1 + 1) after dividing by z
        // s_pos = p_last * p_map * kv_version
        let p_map = periodic[0];
        let p_last = periodic[1 + POSEIDON_ROUNDS + 3];
        let s_pos = p_last * p_map * ver * ver;

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

            result[*ix] = gr * (next[ctx.cols.lane_l] - yl) + s_pos;
            *ix += 1;
            result[*ix] = gr * (next[ctx.cols.lane_r] - yr) + s_pos;
            *ix += 1;
            result[*ix] = gr * (next[ctx.cols.lane_c0] - yc0) + s_pos;
            *ix += 1;
            result[*ix] = gr * (next[ctx.cols.lane_c1] - yc1) + s_pos;
            *ix += 1;
        }

        // Hold lanes on non-round rows:
        // final and pad rows except last pad.
        let p_pad = periodic[1 + POSEIDON_ROUNDS + 1];
        let p_pad_last = periodic[1 + POSEIDON_ROUNDS + 2];
        let g_hold = p_pad - p_pad_last;

        result[*ix] = g_hold * (next[ctx.cols.lane_l] - cur[ctx.cols.lane_l]) + s_pos;
        *ix += 1;
        result[*ix] = g_hold * (next[ctx.cols.lane_r] - cur[ctx.cols.lane_r]) + s_pos;
        *ix += 1;
        result[*ix] = g_hold * (next[ctx.cols.lane_c0] - cur[ctx.cols.lane_c0]) + s_pos;
        *ix += 1;
        result[*ix] = g_hold * (next[ctx.cols.lane_c1] - cur[ctx.cols.lane_c1]) + s_pos;
        *ix += 1;

        // Bind map-row lanes to
        // VM-selected inputs for Hash2
        let b_hash = cur[ctx.cols.op_hash2];

        let mut a_val = E::ZERO;
        let mut b_val = E::ZERO;

        for i in 0..NR {
            a_val += cur[ctx.cols.sel_a_index(i)] * cur[ctx.cols.r_index(i)];
            b_val += cur[ctx.cols.sel_b_index(i)] * cur[ctx.cols.r_index(i)];
        }

        result[*ix] = p_map * b_hash * (cur[ctx.cols.lane_l] - a_val) + s_pos;
        *ix += 1;
        result[*ix] = p_map * b_hash * (cur[ctx.cols.lane_r] - b_val) + s_pos;
        *ix += 1;
    }
}

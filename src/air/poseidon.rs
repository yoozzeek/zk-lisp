// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::{EvaluationFrame, TransitionConstraintDegree};

use super::{AirBlock, BlockCtx};
use crate::layout::{POSEIDON_ROUNDS, STEPS_PER_LEVEL_P2};

pub struct PoseidonBlock;

impl PoseidonBlock {
    pub fn push_degrees(out: &mut Vec<TransitionConstraintDegree>) {
        for _ in 0..POSEIDON_ROUNDS {
            for _ in 0..4 {
                out.push(TransitionConstraintDegree::with_cycles(
                    3,
                    vec![STEPS_PER_LEVEL_P2],
                ));
            }
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
    }
}

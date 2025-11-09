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
        // Per-round Poseidon transitions
        for _ in 0..POSEIDON_ROUNDS {
            for _ in 0..12 {
                out.push(TransitionConstraintDegree::with_cycles(
                    4,
                    vec![STEPS_PER_LEVEL_P2],
                ));
            }
        }

        // Hold constraints on non-round rows:
        // pad rows except last pad)
        // base=1 (linear), cycles=1
        for _ in 0..12 {
            out.push(TransitionConstraintDegree::with_cycles(
                1,
                vec![STEPS_PER_LEVEL_P2],
            ));
        }
    }

    pub fn push_degrees_vm_bind(out: &mut Vec<TransitionConstraintDegree>) {
        // VM->lane binding at map row
        // for sponge absorb lanes (0..9).
        // base=3 (pa * b_sponge * (lane - sum sel_s*reg)),
        // cycles=1 (p_map)
        for _ in 0..10 {
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

        // Gates
        let p_map = periodic[0];

        // Per-round transitions
        for j in 0..POSEIDON_ROUNDS {
            let gr = periodic[1 + j];
            let pa = cur[ctx.cols.pose_active];

            let s: [E; 12] = core::array::from_fn(|i| cur[ctx.cols.lane_index(i)]);
            let s3 = s.map(|v| {
                let v2 = v * v;
                v2 * v
            });

            // y = MDS * s^3 + rc
            let rc = &ctx.poseidon_rc[j];
            let y: [E; 12] = core::array::from_fn(|i| {
                let acc = (0..12).fold(E::ZERO, |acc, k| acc + E::from(mm[i][k]) * s3[k]);
                acc + E::from(rc[i])
            });

            for (i, yi) in y.iter().enumerate() {
                result[*ix] = pa * gr * (next[ctx.cols.lane_index(i)] - *yi);
                *ix += 1;
            }
        }

        // Hold lanes on non-round rows:
        // final and pad rows except last pad.
        let p_pad = periodic[1 + POSEIDON_ROUNDS + 1];
        let p_pad_last = periodic[1 + POSEIDON_ROUNDS + 2];
        let g_hold = p_pad - p_pad_last;

        for i in 0..12 {
            result[*ix] = g_hold * (next[ctx.cols.lane_index(i)] - cur[ctx.cols.lane_index(i)]);
            *ix += 1;
        }

        // Bind map-row absorb lanes
        // (0..9) to VM-selected inputs
        // when sponge ops are enabled;
        // gate by p_map, b_sponge and pose_active.
        if ctx.pub_inputs.get_features().vm && ctx.pub_inputs.get_features().sponge {
            let b_sponge = cur[ctx.cols.op_sponge];
            let pa = cur[ctx.cols.pose_active];

            for lane in 0..10 {
                let mut sel_val = E::ZERO;
                for r in 0..NR {
                    sel_val += cur[ctx.cols.sel_s_index(lane, r)] * cur[ctx.cols.r_index(r)];
                }

                result[*ix] = p_map * pa * b_sponge * (cur[ctx.cols.lane_index(lane)] - sel_val);
                *ix += 1;
            }
        }
    }
}

// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Merkle path constraints for zk-lisp proofs.
//!
//! Binds Merkle leaves and roots to the trace, enforcing
//! correct direction bits, Poseidon lane routing and
//! cross-level accumulator transport.

use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::{EvaluationFrame, TransitionConstraintDegree};

use crate::utils;
use crate::vm::layout::{POSEIDON_ROUNDS, STEPS_PER_LEVEL_P2};

use super::{AirModule, AirSharedContext};

pub(crate) struct MerkleAir;

impl AirModule for MerkleAir {
    fn push_degrees(_ctx: &AirSharedContext, out: &mut Vec<TransitionConstraintDegree>) {
        // dir boolean at map
        out.push(TransitionConstraintDegree::new(1));
        // lane selections at map:
        // use two trace columns (g and lane/acc/sib)
        out.push(TransitionConstraintDegree::with_cycles(
            2,
            vec![STEPS_PER_LEVEL_P2],
        ));
        out.push(TransitionConstraintDegree::with_cycles(
            2,
            vec![STEPS_PER_LEVEL_P2],
        ));
        // carry acc across non-final rows
        out.push(TransitionConstraintDegree::with_cycles(
            2,
            vec![STEPS_PER_LEVEL_P2],
        ));
        // first-level leaf binding at map
        out.push(TransitionConstraintDegree::with_cycles(
            3,
            vec![STEPS_PER_LEVEL_P2],
        ));
        // last-level root binding at final
        out.push(TransitionConstraintDegree::with_cycles(
            3,
            vec![STEPS_PER_LEVEL_P2],
        ));
        // cross-level acc transport
        // when consecutive merkle steps
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

        let p_map = periodic[0];
        let p_final = periodic[1 + POSEIDON_ROUNDS];
        let p_pad = periodic[1 + POSEIDON_ROUNDS + 1];
        let p_pad_last = periodic[1 + POSEIDON_ROUNDS + 2];

        // gates
        let g = cur[ctx.cols.merkle_g];
        let dir = cur[ctx.cols.merkle_dir];
        let acc = cur[ctx.cols.merkle_acc];
        let sib = cur[ctx.cols.merkle_sib];

        // dir boolean at map
        result[*ix] = p_map * g * dir * (dir - E::ONE);
        *ix += 1;

        // lane selection at map:
        // lane_l/r based on dir and (acc,sib)
        let left = (E::ONE - dir) * acc + dir * sib;
        let right = (E::ONE - dir) * sib + dir * acc;
        result[*ix] = p_map * g * (cur[ctx.cols.lane_l] - left);
        *ix += 1;
        result[*ix] = p_map * g * (cur[ctx.cols.lane_r] - right);
        *ix += 1;

        // carry acc across rows within
        // level except when next is final
        let mut g_hold = p_map + (p_pad - p_pad_last);
        for j in 0..(POSEIDON_ROUNDS - 1) {
            g_hold += periodic[1 + j];
        }

        result[*ix] = g * g_hold * (next[ctx.cols.merkle_acc] - cur[ctx.cols.merkle_acc]);
        *ix += 1;

        // first-level binding at map
        // if merkle_first==1: acc == merkle_leaf
        let is_first = cur[ctx.cols.merkle_first];
        result[*ix] = p_map * g * is_first * (acc - cur[ctx.cols.merkle_leaf]);
        *ix += 1;

        // last-level root binding at final
        // if merkle_last==1: acc == root
        let is_last = cur[ctx.cols.merkle_last];
        let root = E::from(utils::be_from_le8(&ctx.pub_inputs.merkle_root));
        result[*ix] = p_final * g * is_last * (cur[ctx.cols.merkle_acc] - root);
        *ix += 1;

        // cross-level transport:
        // when current level is merkle
        // and next level is merkle,
        // enforce next.acc == cur.acc
        // at last row of level.
        let g_next = next[ctx.cols.merkle_g];
        result[*ix] =
            p_pad_last * g * g_next * (next[ctx.cols.merkle_acc] - cur[ctx.cols.merkle_acc]);
        *ix += 1;
    }
}

// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::{Assertion, EvaluationFrame, TransitionConstraintDegree};

use crate::layout::{POSEIDON_ROUNDS, STEPS_PER_LEVEL_P2};
use crate::pi;

use super::{AirBlock, BlockCtx};

pub struct KvBlock;

impl KvBlock {
    pub fn push_degrees(out: &mut Vec<TransitionConstraintDegree>) {
        // dir boolean at map
        out.push(TransitionConstraintDegree::with_cycles(
            2,
            vec![STEPS_PER_LEVEL_P2],
        ));
        // lane selections at map (2 constraints)
        out.push(TransitionConstraintDegree::with_cycles(
            3,
            vec![STEPS_PER_LEVEL_P2],
        ));
        out.push(TransitionConstraintDegree::with_cycles(
            3,
            vec![STEPS_PER_LEVEL_P2],
        ));
        // version transition (map hold, final bump)
        out.push(TransitionConstraintDegree::with_cycles(
            2,
            vec![STEPS_PER_LEVEL_P2],
        ));
        // final tie acc==lane_l (gated by fin & map)
        out.push(TransitionConstraintDegree::with_cycles(
            3,
            vec![STEPS_PER_LEVEL_P2],
        ));
        // carry acc on non-final rows
        out.push(TransitionConstraintDegree::with_cycles(
            1,
            vec![STEPS_PER_LEVEL_P2],
        ));
    }
}

impl<E> AirBlock<E> for KvBlock
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
        let p_pad_last = periodic[1 + POSEIDON_ROUNDS + 2];

        // Carry within the level except across
        // (last round -> final) and (last pad -> next map)
        let mut g_hold = p_map + (p_pad - p_pad_last);
        for j in 0..(POSEIDON_ROUNDS - 1) {
            g_hold += periodic[1 + j];
        }

        // mixers: s1 ~ deg1, s2 ~ deg2,
        // s3 ~ deg3 (after dividing by z)
        let p_last = periodic[1 + POSEIDON_ROUNDS + 3];
        let s1 = p_last * p_map;
        let pi = cur[ctx.cols.pi_prog];
        let s2 = s1 * pi;
        let s3 = s2 * pi;

        let kv_map = cur[ctx.cols.kv_g_map];
        let kv_fin = cur[ctx.cols.kv_g_final];
        let dir = cur[ctx.cols.kv_dir];
        let sib = cur[ctx.cols.kv_sib];
        let acc = cur[ctx.cols.kv_acc];

        // dir boolean at map
        result[*ix] = p_map * kv_map * dir * (dir - E::ONE) + s2;
        *ix += 1;

        // lane selection at map
        let left_sel = (E::ONE - dir) * acc + dir * sib;
        let right_sel = (E::ONE - dir) * sib + dir * acc;
        result[*ix] = p_map * kv_map * (cur[ctx.cols.lane_l] - left_sel) + s3;
        *ix += 1;
        result[*ix] = p_map * kv_map * (cur[ctx.cols.lane_r] - right_sel) + s3;
        *ix += 1;

        // version transition: hold on map
        // (kv_map), bump on final (kv_fin)
        let ver = cur[ctx.cols.kv_version];
        let ver_next = next[ctx.cols.kv_version];
        result[*ix] = (p_map * kv_map) * (ver_next - ver)
            + (p_final * kv_fin) * (ver_next - (ver + E::ONE))
            + s2;
        *ix += 1;

        // final tie acc == lane_l only
        // for KV map-final levels.
        result[*ix] =
            p_final * kv_fin * kv_map * (cur[ctx.cols.kv_acc] - cur[ctx.cols.lane_l]) + s2;
        *ix += 1;
        // carry acc across rows whose next is NOT final
        result[*ix] = g_hold * (next[ctx.cols.kv_acc] - cur[ctx.cols.kv_acc]) + s1;
        *ix += 1;
    }

    fn append_assertions(
        ctx: &BlockCtx<E>,
        out: &mut Vec<Assertion<<E as FieldElement>::BaseField>>,
        last: usize,
    ) {
        if (ctx.pub_inputs.feature_mask & pi::FM_KV) == 0 {
            return;
        }

        let steps = STEPS_PER_LEVEL_P2;
        let lvls = (last + 1) / steps;
        let cols = ctx.cols;

        // Enforce KV gate one-hot via boundary
        // assertions at map/final per level.
        for lvl in 0..lvls {
            if ((ctx.pub_inputs.kv_levels_mask >> lvl) & 1) == 1 {
                let base = lvl * steps;
                let row_map = base + crate::schedule::pos_map();
                let row_final = base + crate::schedule::pos_final();

                // At map: kv_g_map=1, kv_g_final=0
                out.push(Assertion::single(cols.kv_g_map, row_map, BE::from(1u32)));
                out.push(Assertion::single(cols.kv_g_final, row_map, BE::from(0u32)));

                // At final: kv_g_final=1, kv_g_map=0
                out.push(Assertion::single(
                    cols.kv_g_final,
                    row_final,
                    BE::from(1u32),
                ));
                out.push(Assertion::single(cols.kv_g_map, row_final, BE::from(0u32)));
            }
        }

        // EXPECT ties via boundary per marked KV level
        if (ctx.pub_inputs.feature_mask & pi::FM_KV_EXPECT) != 0 {
            let map_exp = crate::pi::be_from_le8(&ctx.pub_inputs.kv_map_acc_bytes);
            let fin_exp = crate::pi::be_from_le8(&ctx.pub_inputs.kv_fin_acc_bytes);

            for lvl in 0..lvls {
                if ((ctx.pub_inputs.kv_levels_mask >> lvl) & 1) == 1 {
                    let base = lvl * steps;
                    let row_map = base + crate::schedule::pos_map();
                    let row_final = base + crate::schedule::pos_final();
                    let row_next = row_final + 1;

                    out.push(Assertion::single(cols.kv_acc, row_map, map_exp));
                    out.push(Assertion::single(cols.kv_acc, row_final, fin_exp));
                    out.push(Assertion::single(cols.kv_prev_acc, row_next, fin_exp));
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::layout::Columns;
    use winterfell::EvaluationFrame;

    #[test]
    fn dir_non_boolean_fails_at_map() {
        let cols = Columns::baseline();

        let mut frame = EvaluationFrame::<BE>::new(cols.width(0));
        let mut periodic = vec![BE::ZERO; 1 + POSEIDON_ROUNDS + 1 + 1 + 1 + 1];

        let pi = pi::PublicInputs::default();
        let rc_vec = vec![[BE::ZERO; 12]; POSEIDON_ROUNDS];
        let mds_box = Box::new({
            let mut m = [[BE::ZERO; 12]; 12];
            for (i, row) in m.iter_mut().enumerate() {
                row[i] = BE::ONE;
            }

            m
        });
        let dom_box = Box::new([BE::ONE, BE::from(2u64)]);
        let ctx = BlockCtx::<BE>::new(&cols, &pi, &rc_vec, &mds_box, &dom_box);

        // map row: p_map=1
        periodic[0] = BE::ONE;
        periodic[1 + POSEIDON_ROUNDS] = BE::ZERO;

        // set gates
        frame.current_mut()[cols.kv_g_map] = BE::ONE;
        frame.current_mut()[cols.kv_g_final] = BE::ZERO;

        // dir=2 (non-boolean),
        // set other values harmless
        frame.current_mut()[cols.kv_dir] = BE::from(2u64);
        frame.current_mut()[cols.kv_acc] = BE::from(5u64);
        frame.current_mut()[cols.kv_sib] = BE::from(7u64);

        // carry acc across non-final rows
        frame.next_mut()[cols.kv_acc] = frame.current()[cols.kv_acc];

        let mut res = vec![BE::ZERO; 8];
        let mut ix = 0usize;
        KvBlock::eval_block(&ctx, &frame, &periodic, &mut res, &mut ix);

        // first constraint is dir*(dir-1)
        assert_ne!(res[0], BE::ZERO);
    }

    #[test]
    fn kv_constraints_zero_on_valid_map_row() {
        let cols = Columns::baseline();
        let mut frame = EvaluationFrame::<BE>::new(cols.width(0));
        let mut periodic = vec![BE::ZERO; 1 + POSEIDON_ROUNDS + 1 + 1 + 1 + 1];

        let pi = pi::PublicInputs::default();
        let rc_vec = vec![[BE::ZERO; 12]; POSEIDON_ROUNDS];
        let mds_box = Box::new({
            let mut m = [[BE::ZERO; 12]; 12];
            for (i, row) in m.iter_mut().enumerate() {
                row[i] = BE::ONE;
            }

            m
        });
        let dom_box = Box::new([BE::ONE, BE::from(2u64)]);
        let ctx = BlockCtx::<BE>::new(&cols, &pi, &rc_vec, &mds_box, &dom_box);

        // map row
        periodic[0] = BE::ONE;
        periodic[1 + POSEIDON_ROUNDS] = BE::ZERO;

        frame.current_mut()[cols.kv_g_map] = BE::ONE;
        frame.current_mut()[cols.kv_g_final] = BE::ZERO;

        // dir boolean 0, lanes match selection
        frame.current_mut()[cols.kv_dir] = BE::ZERO;
        frame.current_mut()[cols.kv_acc] = BE::from(5u64);
        frame.current_mut()[cols.kv_sib] = BE::from(7u64);
        frame.current_mut()[cols.lane_l] = BE::from(5u64);
        frame.current_mut()[cols.lane_r] = BE::from(7u64);

        // version hold
        frame.current_mut()[cols.kv_version] = BE::from(3u64);
        frame.next_mut()[cols.kv_version] = BE::from(3u64);
        // carry acc
        frame.next_mut()[cols.kv_acc] = frame.current()[cols.kv_acc];

        let mut res = vec![BE::ZERO; 6];
        let mut ix = 0usize;
        KvBlock::eval_block(&ctx, &frame, &periodic, &mut res, &mut ix);

        // All constraints should
        // be zero on a valid map row.
        for (i, v) in res.iter().enumerate() {
            assert_eq!(*v, BE::ZERO, "idx {i}");
        }
    }

    #[test]
    fn version_wrong_at_final_fails() {
        let cols = Columns::baseline();
        let mut frame = EvaluationFrame::<BE>::new(cols.width(0));
        let mut periodic = vec![BE::ZERO; 1 + POSEIDON_ROUNDS + 1 + 1 + 1 + 1];

        let pi = pi::PublicInputs::default();
        let rc_vec = vec![[BE::ZERO; 12]; POSEIDON_ROUNDS];
        let mds_box = Box::new({
            let mut m = [[BE::ZERO; 12]; 12];
            for (i, row) in m.iter_mut().enumerate() {
                row[i] = BE::ONE;
            }

            m
        });
        let dom_box = Box::new([BE::ONE, BE::from(2u64)]);
        let ctx = BlockCtx::<BE>::new(&cols, &pi, &rc_vec, &mds_box, &dom_box);

        // final row
        periodic[0] = BE::ZERO;
        periodic[1 + POSEIDON_ROUNDS] = BE::ONE;

        frame.current_mut()[cols.kv_g_map] = BE::ONE; // kv_map can be 1 same level
        frame.current_mut()[cols.kv_g_final] = BE::ONE;

        // wrong version bump (should +1)
        frame.current_mut()[cols.kv_version] = BE::from(10u64);
        frame.next_mut()[cols.kv_version] = BE::from(10u64);

        let mut res = vec![BE::ZERO; 8];
        let mut ix = 0usize;
        KvBlock::eval_block(&ctx, &frame, &periodic, &mut res, &mut ix);

        // version index = 3
        assert_ne!(res[3], BE::ZERO);
    }

    #[test]
    fn final_tie_acc_vs_lane_mismatch_fails() {
        let cols = Columns::baseline();
        let mut frame = EvaluationFrame::<BE>::new(cols.width(0));
        let mut periodic = vec![BE::ZERO; 1 + POSEIDON_ROUNDS + 1 + 1 + 1 + 1];

        let pi = pi::PublicInputs::default();
        let rc_vec = vec![[BE::ZERO; 12]; POSEIDON_ROUNDS];
        let mds_box = Box::new({
            let mut m = [[BE::ZERO; 12]; 12];
            for (i, row) in m.iter_mut().enumerate() {
                row[i] = BE::ONE;
            }

            m
        });
        let dom_box = Box::new([BE::ONE, BE::from(2u64)]);
        let ctx = BlockCtx::<BE>::new(&cols, &pi, &rc_vec, &mds_box, &dom_box);

        // final row
        periodic[0] = BE::ONE; // kv_map may also be 1
        periodic[1 + POSEIDON_ROUNDS] = BE::ONE;

        frame.current_mut()[cols.kv_g_map] = BE::ONE;
        frame.current_mut()[cols.kv_g_final] = BE::ONE;

        // mismatch acc vs lane_l
        frame.current_mut()[cols.kv_acc] = BE::from(9u64);
        frame.current_mut()[cols.lane_l] = BE::from(1u64);

        let mut res = vec![BE::ZERO; 8];
        let mut ix = 0usize;
        KvBlock::eval_block(&ctx, &frame, &periodic, &mut res, &mut ix);

        // final tie index = 4
        assert_ne!(res[4], BE::ZERO);
    }
}

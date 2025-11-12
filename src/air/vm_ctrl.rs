// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::{EvaluationFrame, TransitionConstraintDegree};

use super::{AirBlock, BlockCtx};
use crate::air::mixers;
use crate::layout::{NR, POSEIDON_ROUNDS, STEPS_PER_LEVEL_P2};

pub struct VmCtrlBlock;

impl VmCtrlBlock {
    pub fn push_degrees(out: &mut Vec<TransitionConstraintDegree>, sponge: bool) {
        // selector bits booleanity
        // for ALU roles (dst0,a,b,c,dst1) => (5*NR)
        for _ in 0..(5 * NR) {
            out.push(TransitionConstraintDegree::with_cycles(
                2,
                vec![STEPS_PER_LEVEL_P2],
            ));
        }

        // selector sums for
        // ALU roles: dst0,a,b,c,dst1 (5)
        for _ in 0..5 {
            out.push(TransitionConstraintDegree::with_cycles(
                1,
                vec![STEPS_PER_LEVEL_P2],
            ));
        }

        // no-overlap constraint per register
        // between dst0 and dst1 (NR)
        for _ in 0..NR {
            out.push(TransitionConstraintDegree::with_cycles(
                2,
                vec![STEPS_PER_LEVEL_P2],
            ));
        }

        if sponge {
            // Sponge lane selectors
            // booleanity (10 * NR).
            for _ in 0..(10 * NR) {
                out.push(TransitionConstraintDegree::with_cycles(
                    2,
                    vec![STEPS_PER_LEVEL_P2],
                ));
            }

            // Sponge lane
            // selector sums (10)
            for _ in 0..10 {
                out.push(TransitionConstraintDegree::with_cycles(
                    2,
                    vec![STEPS_PER_LEVEL_P2],
                ));
            }
        }

        // select cond boolean
        out.push(TransitionConstraintDegree::with_cycles(
            2,
            vec![STEPS_PER_LEVEL_P2],
        ));

        // op_* booleans (17)
        for _ in 0..17 {
            out.push(TransitionConstraintDegree::with_cycles(
                2,
                vec![STEPS_PER_LEVEL_P2],
            ));
        }

        // one-hot across ops:
        // sum is boolean (1)
        out.push(TransitionConstraintDegree::with_cycles(
            2,
            vec![STEPS_PER_LEVEL_P2],
        ));

        // ROM ↔ op one-hot equality
        for _ in 0..17 {
            out.push(TransitionConstraintDegree::with_cycles(
                2,
                vec![STEPS_PER_LEVEL_P2],
            ));
        }

        // PC carry (1) and increment at last pad (1)
        out.push(TransitionConstraintDegree::with_cycles(
            1,
            vec![STEPS_PER_LEVEL_P2],
        ));
        out.push(TransitionConstraintDegree::with_cycles(
            1,
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
        let next = frame.next();
        let p_map = periodic[0];

        // Mixer:
        // - s_low = p_last * p_map yields CE quotient degree ~120;
        // - s_high = s_low * pi_prog raises CE quotient degree to ~247;
        //   deg(p_last)=~127,
        //   deg(p_map)=~120,
        //   deg(pi_prog)=~127,
        //   minus z-degree 127.
        let pi_prog = cur[ctx.cols.pi_prog];
        let s_low = mixers::low(periodic);
        let s_high = mixers::pi1(periodic, pi_prog);

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
        let b_divmod = cur[ctx.cols.op_divmod];
        let b_mulwide = cur[ctx.cols.op_mulwide];
        let b_div128 = cur[ctx.cols.op_div128];
        let b_load = cur[ctx.cols.op_load];
        let b_store = cur[ctx.cols.op_store];

        let mut sum_dst0 = E::ZERO;
        let mut sum_a = E::ZERO;
        let mut sum_b = E::ZERO;
        let mut sum_c = E::ZERO;
        let mut sum_dst1 = E::ZERO;

        for i in 0..NR {
            let sd0 = cur[ctx.cols.sel_dst0_index(i)];
            let sa = cur[ctx.cols.sel_a_index(i)];
            let sb = cur[ctx.cols.sel_b_index(i)];
            let sc = cur[ctx.cols.sel_c_index(i)];
            let sd1 = cur[ctx.cols.sel_dst1_index(i)];

            sum_dst0 += sd0;
            sum_a += sa;
            sum_b += sb;
            sum_c += sc;
            sum_dst1 += sd1;

            result[*ix] = p_map * sd0 * (sd0 - E::ONE) + s_high;
            *ix += 1;
            result[*ix] = p_map * sa * (sa - E::ONE) + s_high;
            *ix += 1;
            result[*ix] = p_map * sb * (sb - E::ONE) + s_high;
            *ix += 1;
            result[*ix] = p_map * sc * (sc - E::ONE) + s_high;
            *ix += 1;
            result[*ix] = p_map * sd1 * (sd1 - E::ONE) + s_high;
            *ix += 1;
        }

        // role usage gates: which roles
        // must select exactly one src.
        let uses_a = b_mov
            + b_add
            + b_sub
            + b_mul
            + b_neg
            + b_eq
            + b_sel
            + b_divmod
            + b_div128
            + b_mulwide
            + b_load
            + b_store;
        let uses_b =
            b_add + b_sub + b_mul + b_eq + b_sel + b_divmod + b_div128 + b_mulwide + b_store;
        let uses_c = b_sel + b_assert + b_assert_bit + b_assert_range;
        let op_any = b_const
            + b_mov
            + b_add
            + b_sub
            + b_mul
            + b_neg
            + b_eq
            + b_sel
            + b_sponge
            + b_assert
            + b_assert_bit
            + b_assert_range
            + b_divmod;

        // dst0 required for all
        // write ops except sponge
        // (1 for most, 1 for divmod as well)
        let uses_dst0 = op_any - b_sponge + b_load;

        // dst1 required for two-dest ops
        let uses_dst1 = b_divmod + b_div128 + b_mulwide;

        // emit sums in declared order:
        // dst0, a, b, c, dst1
        result[*ix] = p_map * (sum_dst0 - uses_dst0) + s_low;
        *ix += 1;
        result[*ix] = p_map * (sum_a - uses_a) + s_low;
        *ix += 1;
        result[*ix] = p_map * (sum_b - uses_b) + s_low;
        *ix += 1;
        result[*ix] = p_map * (sum_c - uses_c) + s_low;
        *ix += 1;
        result[*ix] = p_map * (sum_dst1 - uses_dst1) + s_low;
        *ix += 1;

        // no-overlap:
        // for each reg, sd0_i * sd1_i == 0
        for i in 0..NR {
            let sd0 = cur[ctx.cols.sel_dst0_index(i)];
            let sd1 = cur[ctx.cols.sel_dst1_index(i)];
            // for non-divmod ops,
            // all sd1 bits are 0,
            // making this term 0
            result[*ix] = p_map * sd0 * sd1 + s_high;
            *ix += 1;
        }

        // Sponge selectors booleanity
        // and per-lane sum constraints
        // (only when sponge feature is enabled).
        if ctx.pub_inputs.get_features().sponge {
            for lane in 0..10 {
                // Booleanity for packed bits and active at map
                for b in 0..crate::layout::SPONGE_IDX_BITS {
                    let bitv = cur[ctx.cols.sel_s_b_index(lane, b)];
                    result[*ix] = p_map * b_sponge * bitv * (bitv - E::ONE) + s_high;
                    *ix += 1;
                }
                let act = cur[ctx.cols.sel_s_active_index(lane)];
                result[*ix] = p_map * b_sponge * act * (act - E::ONE) + s_high;
                *ix += 1;
            }
        }

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
            b_const,
            b_mov,
            b_add,
            b_sub,
            b_mul,
            b_neg,
            b_eq,
            b_sel,
            b_sponge,
            b_assert,
            b_assert_bit,
            b_assert_range,
            b_divmod,
            b_div128,
            b_mulwide,
            b_load,
            b_store,
        ] {
            result[*ix] = p_map * b * (b - E::ONE) + s_high;
            *ix += 1;
        }

        let op_sum = b_const
            + b_mov
            + b_add
            + b_sub
            + b_mul
            + b_neg
            + b_eq
            + b_sel
            + b_sponge
            + b_assert
            + b_assert_bit
            + b_assert_range
            + b_divmod
            + b_div128
            + b_mulwide
            + b_load
            + b_store;
        result[*ix] = p_map * op_sum * (op_sum - E::ONE) + s_high;
        *ix += 1;

        // ROM ↔ op equality;
        // gated when program_commitment != 0
        let rom_enabled = if ctx.pub_inputs.program_commitment.iter().any(|b| *b != 0) {
            E::ONE
        } else {
            E::ZERO
        };

        for (k, b) in [
            b_const,
            b_mov,
            b_add,
            b_sub,
            b_mul,
            b_neg,
            b_eq,
            b_sel,
            b_sponge,
            b_assert,
            b_assert_bit,
            b_assert_range,
            b_divmod,
            b_div128,
            b_mulwide,
            b_load,
            b_store,
        ]
        .iter()
        .enumerate()
        {
            let rom_b = cur[ctx.cols.rom_op_index(k)];
            result[*ix] = rom_enabled * p_map * (*b - rom_b) + s_high;
            *ix += 1;
        }

        // PC carry within level
        // and increment at last pad
        let p_pad = periodic[1 + POSEIDON_ROUNDS + 1];
        let p_pad_last = periodic[1 + POSEIDON_ROUNDS + 2];

        let mut g_carry = p_map + (p_pad - p_pad_last);
        for gr in (0..(POSEIDON_ROUNDS - 1)).map(|j| periodic[1 + j]) {
            g_carry += gr;
        }

        let pc_cur = cur[ctx.cols.pc];
        let pc_next = next[ctx.cols.pc];

        // carry PC on non-final-next rows
        result[*ix] = rom_enabled * (g_carry * (pc_next - pc_cur)) + s_low;
        *ix += 1;

        // increment at last pad
        // row: next_pc = pc + 1
        result[*ix] = rom_enabled * (p_pad_last * (pc_next - (pc_cur + E::ONE))) + s_low;
        *ix += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::layout::{Columns, POSEIDON_ROUNDS};
    use winterfell::EvaluationFrame;

    #[test]
    fn sponge_selectors_gated_off_without_feature() {
        let cols = Columns::baseline();

        let mut frame_a = EvaluationFrame::<BE>::new(cols.width(0));
        let mut frame_b = EvaluationFrame::<BE>::new(cols.width(0));
        let mut periodic = vec![BE::ZERO; 1 + POSEIDON_ROUNDS + 1 + 1 + 1 + 1];

        // Map row active
        periodic[0] = BE::ONE;

        // op_sponge set; all ALU selectors 0
        frame_a.current_mut()[cols.op_sponge] = BE::ONE;
        frame_b.current_mut()[cols.op_sponge] = BE::ONE;

        // differ only in sel_s for lane0, reg0
        // frame_a: sel=2 (invalid); frame_b: sel=1 (valid)
        frame_a.current_mut()[cols.sel_s_b_index(0, 0)] = BE::from(2u64);
        frame_b.current_mut()[cols.sel_s_b_index(0, 0)] = BE::from(1u64);
        frame_a.current_mut()[cols.sel_s_active_index(0)] = BE::ONE;
        frame_b.current_mut()[cols.sel_s_active_index(0)] = BE::ONE;

        // Build ctx without SPONGE feature
        let pi_no_sponge = crate::pi::PublicInputs::default();

        let rc_binding = Box::new([[BE::ZERO; 12]; POSEIDON_ROUNDS]);
        let mds_binding = Box::new([[BE::ZERO; 12]; 12]);
        let dom_binding = Box::new([BE::ZERO; 2]);

        let rc3_binding = Box::new([[BE::ZERO; 3]; POSEIDON_ROUNDS]);
        let mds3_binding = Box::new([[BE::ZERO; 3]; 3]);
        let w_enc0_binding = Box::new([BE::ZERO; 59]);
        let w_enc1_binding = Box::new([BE::ZERO; 59]);

        let ctx = BlockCtx::new(
            &cols,
            &pi_no_sponge,
            &rc_binding,
            &mds_binding,
            &dom_binding,
            &rc3_binding,
            &mds3_binding,
            &w_enc0_binding,
            &w_enc1_binding,
        );

        let mut ra = vec![BE::ZERO; 256];
        let mut rb = vec![BE::ZERO; 256];
        let mut ia = 0usize;
        let mut ib = 0usize;

        VmCtrlBlock::eval_block(&ctx, &frame_a, &periodic, &mut ra, &mut ia);
        VmCtrlBlock::eval_block(&ctx, &frame_b, &periodic, &mut rb, &mut ib);

        // With sponge disabled, changing sel_s
        // must not change evaluation.
        assert_eq!(ia, ib);
        assert_eq!(ra, rb);
    }

    #[test]
    fn sponge_selectors_on_feature_affect_eval() {
        let cols = Columns::baseline();

        let mut frame_a = EvaluationFrame::<BE>::new(cols.width(0));
        let mut frame_b = EvaluationFrame::<BE>::new(cols.width(0));
        let mut periodic = vec![BE::ZERO; 1 + POSEIDON_ROUNDS + 1 + 1 + 1 + 1];

        // Map row active
        periodic[0] = BE::ONE;

        // op_sponge set; all ALU selectors 0
        frame_a.current_mut()[cols.op_sponge] = BE::ONE;
        frame_b.current_mut()[cols.op_sponge] = BE::ONE;

        // differ only in sel_s for lane0, reg0
        frame_a.current_mut()[cols.sel_s_b_index(0, 0)] = BE::from(2u64); // invalid
        frame_b.current_mut()[cols.sel_s_b_index(0, 0)] = BE::from(1u64); // valid
        frame_a.current_mut()[cols.sel_s_active_index(0)] = BE::ONE;
        frame_b.current_mut()[cols.sel_s_active_index(0)] = BE::ONE;

        // Build ctx with SPONGE feature
        let mut pi = crate::pi::PublicInputs::default();
        pi.feature_mask |= crate::pi::FM_SPONGE | crate::pi::FM_VM;

        let rc_binding = Box::new([[BE::ZERO; 12]; POSEIDON_ROUNDS]);
        let mds_binding = Box::new([[BE::ZERO; 12]; 12]);
        let dom_binding = Box::new([BE::ZERO; 2]);
        let rc3_binding = Box::new([[BE::ZERO; 3]; POSEIDON_ROUNDS]);
        let mds3_binding = Box::new([[BE::ZERO; 3]; 3]);
        let w_enc0_binding = Box::new([BE::ZERO; 59]);
        let w_enc1_binding = Box::new([BE::ZERO; 59]);

        let ctx = BlockCtx::new(
            &cols,
            &pi,
            &rc_binding,
            &mds_binding,
            &dom_binding,
            &rc3_binding,
            &mds3_binding,
            &w_enc0_binding,
            &w_enc1_binding,
        );

        let mut ra = vec![BE::ZERO; 256];
        let mut rb = vec![BE::ZERO; 256];
        let mut ia = 0usize;
        let mut ib = 0usize;

        VmCtrlBlock::eval_block(&ctx, &frame_a, &periodic, &mut ra, &mut ia);
        VmCtrlBlock::eval_block(&ctx, &frame_b, &periodic, &mut rb, &mut ib);

        assert_eq!(ia, ib);
        assert_ne!(ra, rb);
    }

    #[test]
    fn two_ops_set_violation() {
        let cols = Columns::baseline();
        let mut frame = EvaluationFrame::<BE>::new(cols.width(0));
        let mut periodic = vec![BE::ZERO; 1 + POSEIDON_ROUNDS + 1 + 1 + 1 + 1];

        // map row
        periodic[0] = BE::ONE;

        // op_add and op_sub both set
        frame.current_mut()[cols.op_add] = BE::ONE;
        frame.current_mut()[cols.op_sub] = BE::ONE;

        // Evaluate
        let mut res = vec![BE::ZERO; 256];
        let mut ix = 0usize;

        let rc_box = Box::new([[BE::ZERO; 12]; POSEIDON_ROUNDS]);
        let mds_box = Box::new({
            let mut m = [[BE::ZERO; 12]; 12];
            for (i, row) in m.iter_mut().enumerate() {
                row[i] = BE::ONE;
            }

            m
        });

        let rc3_box = Box::new([[BE::ZERO; 3]; POSEIDON_ROUNDS]);
        let mds3_box = Box::new([[BE::ZERO; 3]; 3]);
        let w_enc0_box = Box::new([BE::ZERO; 59]);
        let w_enc1_box = Box::new([BE::ZERO; 59]);

        VmCtrlBlock::eval_block(
            &BlockCtx::new(
                &cols,
                &Default::default(),
                &rc_box,
                &mds_box,
                &Box::new([BE::ZERO; 2]),
                &rc3_box,
                &mds3_box,
                &w_enc0_box,
                &w_enc1_box,
            ),
            &frame,
            &periodic,
            &mut res,
            &mut ix,
        );

        assert!(res.iter().any(|v| *v != BE::ZERO));
    }

    #[test]
    fn packed_bits_booleanity_violation() {
        let cols = Columns::baseline();
        let mut frame = EvaluationFrame::<BE>::new(cols.width(0));
        let mut periodic = vec![BE::ZERO; 1 + POSEIDON_ROUNDS + 1 + 1 + 1 + 1];

        // map row
        periodic[0] = BE::ONE;
        // sponge gate
        frame.current_mut()[cols.op_sponge] = BE::ONE;

        // set bit b0=2 (invalid), active=1
        frame.current_mut()[cols.sel_s_b_index(0, 0)] = BE::from(2u64);
        frame.current_mut()[cols.sel_s_b_index(0, 1)] = BE::ZERO;
        frame.current_mut()[cols.sel_s_b_index(0, 2)] = BE::ZERO;
        frame.current_mut()[cols.sel_s_active_index(0)] = BE::ONE;

        // Evaluate
        let mut res = vec![BE::ZERO; 256];
        let mut ix = 0usize;

        let rc_box = Box::new([[BE::ZERO; 12]; POSEIDON_ROUNDS]);
        let mds_box = Box::new([[BE::ZERO; 12]; 12]);
        let dom_box = Box::new([BE::ZERO; 2]);
        let rc3_box = Box::new([[BE::ZERO; 3]; POSEIDON_ROUNDS]);
        let mds3_box = Box::new([[BE::ZERO; 3]; 3]);
        let w_enc0_box = Box::new([BE::ZERO; 59]);
        let w_enc1_box = Box::new([BE::ZERO; 59]);

        // Enable SPONGE feature in PI
        // so booleanity constraints are active.
        let mut pi = crate::pi::PublicInputs::default();
        pi.feature_mask |= crate::pi::FM_SPONGE | crate::pi::FM_VM;

        VmCtrlBlock::eval_block(
            &BlockCtx::new(
                &cols, &pi, &rc_box, &mds_box, &dom_box, &rc3_box, &mds3_box, &w_enc0_box, &w_enc1_box,
            ),
            &frame,
            &periodic,
            &mut res,
            &mut ix,
        );

        assert!(res.iter().any(|v| *v != BE::ZERO));
    }
}

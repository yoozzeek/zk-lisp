// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! ROM accumulator constraints tied to program commitment.
//!
//! Models a t=3 Poseidon-like hash over linear encodings
//! of opcode/selector rows and binds its final state to
//! the field-level program commitment.

use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::{Assertion, EvaluationFrame, TransitionConstraintDegree};

use crate::air::{AirModule, AirSharedContext};
use crate::layout::{POSEIDON_ROUNDS, STEPS_PER_LEVEL_P2};
use crate::utils;

pub(super) struct RomAir;

impl AirModule for RomAir {
    fn push_degrees(_ctx: &AirSharedContext, out: &mut Vec<TransitionConstraintDegree>) {
        // Per-round t=3
        // Poseidon-like transitions
        for _ in 0..POSEIDON_ROUNDS {
            for _ in 0..3 {
                out.push(TransitionConstraintDegree::with_cycles(
                    3,
                    vec![STEPS_PER_LEVEL_P2],
                ));
            }
        }

        // Hold constraints on pad
        // rows except last pad.
        for _ in 0..3 {
            out.push(TransitionConstraintDegree::with_cycles(
                1,
                vec![STEPS_PER_LEVEL_P2],
            ));
        }

        // Map row bindings for enc0/enc1
        for _ in 0..2 {
            out.push(TransitionConstraintDegree::with_cycles(
                1,
                vec![STEPS_PER_LEVEL_P2],
            ));
        }
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

        // Per-round transitions
        // (gated by round selector)
        for j in 0..POSEIDON_ROUNDS {
            let gr = periodic[1 + j];
            let s: [E; 3] = core::array::from_fn(|i| cur[ctx.cols.rom_s_index(i)]);
            let s3 = s.map(|v| {
                let v2 = v * v;
                v2 * v
            });

            let rc = &ctx.rom_rc[j];
            let y: [E; 3] = core::array::from_fn(|i| {
                let acc = (0..3).fold(E::ZERO, |acc, k| acc + E::from(ctx.rom_mds[i][k]) * s3[k]);
                acc + E::from(rc[i])
            });

            for (i, yi) in y.iter().enumerate() {
                result[*ix] = gr * (next[ctx.cols.rom_s_index(i)] - *yi);
                *ix += 1;
            }
        }

        // Hold lanes on non-round
        // pad rows except last pad.
        let p_pad = periodic[1 + POSEIDON_ROUNDS + 1];
        let p_pad_last = periodic[1 + POSEIDON_ROUNDS + 2];
        let g_hold = p_pad - p_pad_last;

        for i in 0..3 {
            result[*ix] = g_hold * (next[ctx.cols.rom_s_index(i)] - cur[ctx.cols.rom_s_index(i)]);
            *ix += 1;
        }

        // Map row encodings for lane1/lane2
        let p_map = periodic[0];
        if p_map != E::ZERO {
            // Use precomputed weights
            let enc0 = utils::rom_linear_encode_from_slice(cur, &ctx.cols, &ctx.rom_w_enc0);
            let enc1 = utils::rom_linear_encode_from_slice(cur, &ctx.cols, &ctx.rom_w_enc1);

            result[*ix] = p_map * (cur[ctx.cols.rom_s_index(1)] - enc0);
            *ix += 1;
            result[*ix] = p_map * (cur[ctx.cols.rom_s_index(2)] - enc1);
            *ix += 1;
        } else {
            // Keep CE alignment when p_map==0
            result[*ix] = E::ZERO;
            *ix += 1;
            result[*ix] = E::ZERO;
            *ix += 1;
        }
    }

    fn append_assertions(
        ctx: &AirSharedContext,
        out: &mut Vec<Assertion<<BE as FieldElement>::BaseField>>,
        last: usize,
    ) {
        // Initial accumulator zero at the first
        // map row. Subsequent ROM state is fully
        // determined by transition constraints
        // and map-row encodings.
        let row_map0 = crate::schedule::pos_map();
        out.push(Assertion::single(
            ctx.cols.rom_s_index(0),
            row_map0,
            BE::from(0u32),
        ));

        // Bind final ROM accumulator lanes to
        // the backend-supplied handle derived
        // deterministically from the program.
        // This ties the ROM trace to the offline
        // accumulator and ensures ROM↔VM/program
        // consistency across prove/verify.
        out.push(Assertion::single(
            ctx.cols.rom_s_index(0),
            last,
            ctx.rom_acc[0],
        ));
        out.push(Assertion::single(
            ctx.cols.rom_s_index(1),
            last,
            ctx.rom_acc[1],
        ));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::layout::Columns;

    #[test]
    fn round_constraints_zero_on_valid_row() {
        let cols = Columns::baseline();

        let mut frame = EvaluationFrame::<BE>::new(cols.width(0));
        let mut periodic = vec![BE::ZERO; 1 + POSEIDON_ROUNDS + 1 + 1 + 1 + 1];

        // choose round j and set selector
        let j = 2usize.min(POSEIDON_ROUNDS - 1);
        periodic[1 + j] = BE::ONE;

        // current state s
        for i in 0..3 {
            frame.current_mut()[cols.rom_s_index(i)] = BE::from((i as u64) + 3);
        }

        // derive simple MDS
        // and RC (identity + zeros)
        let mut rc3 = [[BE::ZERO; 3]; POSEIDON_ROUNDS];
        for i in 0..3 {
            rc3[j][i] = BE::from((i as u64) + 1);
        }

        let mut mds3 = [[BE::ZERO; 3]; 3];
        mds3[0][0] = BE::ONE;
        mds3[1][1] = BE::ONE;
        mds3[2][2] = BE::ONE;

        // compute y = s^3 + rc
        let s3: [BE; 3] = core::array::from_fn(|k| {
            let v = frame.current()[cols.rom_s_index(k)];
            v * v * v
        });
        let y: [BE; 3] = core::array::from_fn(|i| s3[i] + rc3[j][i]);

        frame.next_mut()[cols.rom_s_index(0)] = y[0];
        frame.next_mut()[cols.rom_s_index(1)] = y[1];
        frame.next_mut()[cols.rom_s_index(2)] = y[2];

        let mut res = vec![BE::ZERO; 3 * POSEIDON_ROUNDS + 3 + 2];
        let mut ix = 0usize;

        let rc_box = [[BE::ZERO; 12]; POSEIDON_ROUNDS];
        let mds_box = [[BE::ZERO; 12]; 12];
        let dom_box = [BE::ZERO; 2];
        let w_enc0_box = [BE::ZERO; 59];
        let w_enc1_box = [BE::ZERO; 59];

        let ctx = &AirSharedContext {
            pub_inputs: Default::default(),
            cols,
            features: Default::default(),
            poseidon_rc: rc_box,
            poseidon_mds: mds_box,
            poseidon_dom: dom_box,
            rom_rc: rc3,
            rom_mds: mds3,
            rom_w_enc0: w_enc0_box,
            rom_w_enc1: w_enc1_box,
            rom_acc: [BE::ZERO; 3],
            program_fe: [BE::ZERO; 2],
        };

        RomAir::eval_block(ctx, &frame, &periodic, &mut res, &mut ix);

        assert!(res.iter().all(|v| *v == BE::ZERO));
    }

    #[test]
    fn map_enc_bindings_hold() {
        let cols = Columns::baseline();
        let mut frame = EvaluationFrame::<BE>::new(cols.width(0));
        let mut periodic = vec![BE::ZERO; 1 + POSEIDON_ROUNDS + 1 + 1 + 1 + 1];
        periodic[0] = BE::ONE; // map row

        // set some op bit and selectors and witnesses
        frame.current_mut()[cols.op_add] = BE::ONE;
        frame.current_mut()[cols.sel_dst0_index(1)] = BE::ONE;
        frame.current_mut()[cols.sel_a_index(2)] = BE::ONE;
        frame.current_mut()[cols.sel_b_index(3)] = BE::ONE;
        frame.current_mut()[cols.sel_c_index(4)] = BE::ONE;
        frame.current_mut()[cols.imm] = BE::from(7u64);
        frame.current_mut()[cols.eq_inv] = BE::from(9u64);

        // compute enc0/enc1 using the same logic as
        // [`utils::rom_linear_encode_from_slice`]. This
        // keeps the test robust against encoder tweaks.
        let w_enc0_box = utils::rom_weights_for_seed(utils::ROM_W_SEED_0);
        let w_enc1_box = utils::rom_weights_for_seed(utils::ROM_W_SEED_1);

        let enc0 = utils::rom_linear_encode_from_slice::<BE>(frame.current(), &cols, &w_enc0_box);
        let enc1 = utils::rom_linear_encode_from_slice::<BE>(frame.current(), &cols, &w_enc1_box);

        frame.current_mut()[cols.rom_s_index(1)] = enc0;
        frame.current_mut()[cols.rom_s_index(2)] = enc1;

        let mut res = vec![BE::ZERO; 3 * POSEIDON_ROUNDS + 3 + 2];
        let mut ix = 0usize;

        let rc_box = [[BE::ZERO; 12]; POSEIDON_ROUNDS];
        let mds_box = [[BE::ZERO; 12]; 12];
        let dom_box = [BE::ZERO; 2];
        let rc3_box = [[BE::ZERO; 3]; POSEIDON_ROUNDS];
        let mds3_box = [[BE::ZERO; 3]; 3];

        let ctx = &AirSharedContext {
            pub_inputs: Default::default(),
            cols,
            features: Default::default(),
            poseidon_rc: rc_box,
            poseidon_mds: mds_box,
            poseidon_dom: dom_box,
            rom_rc: rc3_box,
            rom_mds: mds3_box,
            rom_w_enc0: w_enc0_box,
            rom_w_enc1: w_enc1_box,
            rom_acc: [BE::ZERO; 3],
            program_fe: [BE::ZERO; 2],
        };

        RomAir::eval_block(ctx, &frame, &periodic, &mut res, &mut ix);

        assert!(res.iter().all(|v| *v == BE::ZERO));
    }
}

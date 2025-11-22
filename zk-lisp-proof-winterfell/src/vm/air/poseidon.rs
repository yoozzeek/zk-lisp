// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Poseidon2 sponge constraints over the trace lanes.
//!
//! Enforces per-round Poseidon transitions, holds lane
//! values on non-round rows and, when enabled, binds
//! VM register values into sponge absorb lanes.

use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::{EvaluationFrame, TransitionConstraintDegree};

use super::{AirModule, AirSharedContext};
use crate::vm::layout::{POSEIDON_ROUNDS, STEPS_PER_LEVEL_P2};

pub(crate) struct PoseidonAir;

impl AirModule for PoseidonAir {
    fn push_degrees(ctx: &AirSharedContext, out: &mut Vec<TransitionConstraintDegree>) {
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
        // pad rows except last pad
        // base=1 (linear), cycles=1
        for _ in 0..12 {
            out.push(TransitionConstraintDegree::with_cycles(
                1,
                vec![STEPS_PER_LEVEL_P2],
            ));
        }

        // When VM is enabled AND sponge ops
        // are present enforce VM->lane bindings
        // on map rows of absorb operations.
        if ctx.features.vm && ctx.features.sponge {
            // VM->lane binding at map row
            // for sponge absorb lanes (0..9).
            //
            // The binding constraints have different effective
            // algebraic degrees per lane due to the way packed
            // index bits and the active flag are wired in the
            // trace builder:
            //   - lane 0:   base degree 4
            //   - lanes 1–2: base degree 5
            //   - lanes 3–9: base degree 3
            let lane_bases: [usize; 10] = [4, 5, 5, 3, 3, 3, 3, 3, 3, 3];
            for &base in lane_bases.iter() {
                out.push(TransitionConstraintDegree::with_cycles(
                    base,
                    vec![STEPS_PER_LEVEL_P2],
                ));
            }
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
            let rc_row = &ctx.poseidon_rc[j];
            let y: [E; 12] = core::array::from_fn(|i| {
                let acc = (0..12).fold(E::ZERO, |acc, k| {
                    acc + E::from(ctx.poseidon_mds[i][k]) * s3[k]
                });
                acc + E::from(rc_row[i])
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
        if ctx.features.vm && ctx.features.sponge {
            let b_sponge = cur[ctx.cols.op_sponge];
            let pa = cur[ctx.cols.pose_active];

            for lane in 0..10 {
                // Packed bits b0..b2 and active
                let b0 = cur[ctx.cols.sel_s_b_index(lane, 0)];
                let b1 = cur[ctx.cols.sel_s_b_index(lane, 1)];
                let b2 = cur[ctx.cols.sel_s_b_index(lane, 2)];
                let act = cur[ctx.cols.sel_s_active_index(lane)];

                // Mux over 8 registers using 3 bits
                let r0 = cur[ctx.cols.r_index(0)];
                let r1 = cur[ctx.cols.r_index(1)];
                let r2 = cur[ctx.cols.r_index(2)];
                let r3 = cur[ctx.cols.r_index(3)];
                let r4 = cur[ctx.cols.r_index(4)];
                let r5 = cur[ctx.cols.r_index(5)];
                let r6 = cur[ctx.cols.r_index(6)];
                let r7 = cur[ctx.cols.r_index(7)];

                let one = E::ONE;

                let s0 = b0 * r1 + (one - b0) * r0;
                let s1 = b0 * r3 + (one - b0) * r2;
                let s2 = b0 * r5 + (one - b0) * r4;
                let s3 = b0 * r7 + (one - b0) * r6;
                let t0 = b1 * s1 + (one - b1) * s0;
                let t1 = b1 * s3 + (one - b1) * s2;

                let sel_val = b2 * t1 + (one - b2) * t0;
                let lane_expect = act * sel_val;

                result[*ix] =
                    p_map * pa * b_sponge * (cur[ctx.cols.lane_index(lane)] - lane_expect);
                *ix += 1;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vm::layout::Columns;

    #[test]
    fn round_constraints_zero_on_valid_row() {
        let cols = Columns::baseline();

        let mut frame = EvaluationFrame::<BE>::new(cols.width(0));
        let mut periodic = vec![BE::ZERO; 1 + POSEIDON_ROUNDS + 1 + 1 + 1 + 1];

        // choose round j
        let j = 3usize.min(POSEIDON_ROUNDS - 1);
        periodic[1 + j] = BE::ONE; // gr for round j

        // Build suite and state
        let sid = [5u8; 32];
        let ps = crate::poseidon::get_poseidon_suite(&sid);

        let mut rc_arr = [[BE::ZERO; 12]; POSEIDON_ROUNDS];
        for (i, row) in ps.rc.iter().enumerate().take(POSEIDON_ROUNDS) {
            rc_arr[i] = *row;
        }

        // current state s
        for (i, idx) in (0..12).map(|k| cols.lane_index(k)).enumerate() {
            frame.current_mut()[idx] = BE::from((i as u64) + 1);
        }

        // pose_active on
        frame.current_mut()[cols.pose_active] = BE::ONE;

        // compute y = MDS*s^3 + rc[j]
        let s3: [BE; 12] = core::array::from_fn(|k| {
            let v = frame.current()[cols.lane_index(k)];
            v * v * v
        });

        let y: [BE; 12] = core::array::from_fn(|i| {
            let acc = (0..12).fold(BE::ZERO, |acc, k| acc + ps.mds[i][k] * s3[k]);
            acc + ps.rc[j][i]
        });

        for (i, idx) in (0..12).map(|k| cols.lane_index(k)).enumerate() {
            frame.next_mut()[idx] = y[i];
        }

        // Evaluate
        let mut res = vec![BE::ZERO; 12 * POSEIDON_ROUNDS + 12];
        let mut ix = 0usize;

        let rc3_box = [[BE::ZERO; 3]; POSEIDON_ROUNDS];
        let mds3_box = [[BE::ZERO; 3]; 3];
        let w_enc0_box = [BE::ZERO; 59];
        let w_enc1_box = [BE::ZERO; 59];

        let ctx = &AirSharedContext {
            pub_inputs: Default::default(),
            cols,
            features: Default::default(),
            poseidon_rc: rc_arr,
            poseidon_mds: ps.mds,
            poseidon_dom: ps.dom,
            rom_rc: rc3_box,
            rom_mds: mds3_box,
            rom_w_enc0: w_enc0_box,
            rom_w_enc1: w_enc1_box,
            rom_s_initial: [BE::ZERO; 3],
            rom_s_final: [BE::ZERO; 3],
            pc_init: BE::ZERO,
            program_fe: [BE::ZERO; 2],
            main_args: Vec::new(),
        };

        PoseidonAir::eval_block(ctx, &frame, &periodic, &mut res, &mut ix);

        assert!(res.iter().all(|v| *v == BE::ZERO));
    }

    #[test]
    fn hold_constraints_hold_on_pad() {
        let cols = Columns::baseline();

        let mut frame = EvaluationFrame::<BE>::new(cols.width(0));
        let mut periodic = vec![BE::ZERO; 1 + POSEIDON_ROUNDS + 1 + 1 + 1 + 1];

        // pad gating
        periodic[1 + POSEIDON_ROUNDS + 1] = BE::ONE; // p_pad
        periodic[1 + POSEIDON_ROUNDS + 2] = BE::ZERO; // not last pad

        // set same current/next lanes
        for (i, idx) in (0..12).map(|k| cols.lane_index(k)).enumerate() {
            let v = BE::from((i as u64) + 3);
            frame.current_mut()[idx] = v;
            frame.next_mut()[idx] = v;
        }

        let mut res = vec![BE::ZERO; 12 * POSEIDON_ROUNDS + 12];
        let mut ix = 0usize;

        let rc_box = [[BE::ZERO; 12]; POSEIDON_ROUNDS];
        let rc3_box = [[BE::ZERO; 3]; POSEIDON_ROUNDS];
        let mds3_box = [[BE::ZERO; 3]; 3];
        let w_enc0_box = [BE::ZERO; 59];
        let w_enc1_box = [BE::ZERO; 59];

        let ctx = &AirSharedContext {
            pub_inputs: Default::default(),
            cols,
            features: Default::default(),
            poseidon_rc: rc_box,
            poseidon_mds: [[BE::ZERO; 12]; 12],
            poseidon_dom: [BE::ZERO; 2],
            rom_rc: rc3_box,
            rom_mds: mds3_box,
            rom_w_enc0: w_enc0_box,
            rom_w_enc1: w_enc1_box,
            rom_s_initial: [BE::ZERO; 3],
            rom_s_final: [BE::ZERO; 3],
            pc_init: BE::ZERO,
            program_fe: [BE::ZERO; 2],
            main_args: Vec::new(),
        };

        PoseidonAir::eval_block(ctx, &frame, &periodic, &mut res, &mut ix);

        assert!(res.iter().all(|v| *v == BE::ZERO));
    }

    #[test]
    fn round_gated_by_pose_active() {
        let cols = Columns::baseline();

        let mut frame = EvaluationFrame::<BE>::new(cols.width(0));
        let mut periodic = vec![BE::ZERO; 1 + POSEIDON_ROUNDS + 1 + 1 + 1 + 1];

        // choose round j and set gr
        let j = 1usize.min(POSEIDON_ROUNDS - 1);
        periodic[1 + j] = BE::ONE;

        // set arbitrary current/next
        for (i, idx) in (0..12).map(|k| cols.lane_index(k)).enumerate() {
            frame.current_mut()[idx] = BE::from((i as u64) + 11);
            frame.next_mut()[idx] = BE::from((i as u64) + 7);
        }

        // pose_active off
        frame.current_mut()[cols.pose_active] = BE::ZERO;

        // pad off
        periodic[1 + POSEIDON_ROUNDS + 1] = BE::ZERO;
        periodic[1 + POSEIDON_ROUNDS + 2] = BE::ZERO;

        let mut res = vec![BE::ZERO; 12 * POSEIDON_ROUNDS + 12];
        let mut ix = 0usize;

        let rc_box = [[BE::ZERO; 12]; POSEIDON_ROUNDS];
        let rc3_box = [[BE::ZERO; 3]; POSEIDON_ROUNDS];
        let mds3_box = [[BE::ZERO; 3]; 3];
        let w_enc0_box = [BE::ZERO; 59];
        let w_enc1_box = [BE::ZERO; 59];

        let ctx = &AirSharedContext {
            pub_inputs: Default::default(),
            cols,
            features: Default::default(),
            poseidon_rc: rc_box,
            poseidon_mds: [[BE::ZERO; 12]; 12],
            poseidon_dom: [BE::ZERO; 2],
            rom_rc: rc3_box,
            rom_mds: mds3_box,
            rom_w_enc0: w_enc0_box,
            rom_w_enc1: w_enc1_box,
            rom_s_initial: [BE::ZERO; 3],
            rom_s_final: [BE::ZERO; 3],
            pc_init: BE::ZERO,
            program_fe: [BE::ZERO; 2],
            main_args: Vec::new(),
        };

        PoseidonAir::eval_block(ctx, &frame, &periodic, &mut res, &mut ix);

        assert!(res.iter().all(|v| *v == BE::ZERO));
    }

    #[test]
    fn sponge_binding_mux_positive() {
        let cols = Columns::baseline();

        let mut frame = EvaluationFrame::<BE>::new(cols.width(0));
        let mut periodic = vec![BE::ZERO; 1 + POSEIDON_ROUNDS + 1 + 1 + 1 + 1];
        // map row active
        periodic[0] = BE::ONE;

        // pose_active and op_sponge on
        frame.current_mut()[cols.pose_active] = BE::ONE;
        frame.current_mut()[cols.op_sponge] = BE::ONE;

        // set registers r0..r7 to known values
        for i in 0..8 {
            frame.current_mut()[cols.r_index(i)] = BE::from((10 + i) as u64);
        }

        // choose lane 0,
        // index = 5 (b2,b1,b0 = 1,0,1),
        // active=1
        frame.current_mut()[cols.sel_s_b_index(0, 0)] = BE::ONE; // b0
        frame.current_mut()[cols.sel_s_b_index(0, 1)] = BE::ZERO; // b1
        frame.current_mut()[cols.sel_s_b_index(0, 2)] = BE::ONE; // b2
        frame.current_mut()[cols.sel_s_active_index(0)] = BE::ONE;

        // expected lane value = r5 = 15
        let expected = BE::from(15u64);
        frame.current_mut()[cols.lane_index(0)] = expected;

        // Build ctx with VM+SPONGE
        // features to enable binding constraints
        let mut pi = zk_lisp_proof::pi::PublicInputs::default();
        pi.feature_mask |= zk_lisp_proof::pi::FM_VM | zk_lisp_proof::pi::FM_SPONGE;

        let features = pi.get_features();

        let rc_box = [[BE::ZERO; 12]; POSEIDON_ROUNDS];
        let mds_box = [[BE::ZERO; 12]; 12];
        let dom_box = [BE::ZERO; 2];

        let mut res = vec![BE::ZERO; 12 * POSEIDON_ROUNDS + 12 + 16];
        let mut ix = 0usize;

        let rc3_box = [[BE::ZERO; 3]; POSEIDON_ROUNDS];
        let mds3_box = [[BE::ZERO; 3]; 3];
        let w_enc0_box = [BE::ZERO; 59];
        let w_enc1_box = [BE::ZERO; 59];

        let ctx = &AirSharedContext {
            pub_inputs: pi,
            cols,
            features,
            poseidon_rc: rc_box,
            poseidon_mds: mds_box,
            poseidon_dom: dom_box,
            rom_rc: rc3_box,
            rom_mds: mds3_box,
            rom_w_enc0: w_enc0_box,
            rom_w_enc1: w_enc1_box,
            rom_s_initial: [BE::ZERO; 3],
            rom_s_final: [BE::ZERO; 3],
            pc_init: BE::ZERO,
            program_fe: [BE::ZERO; 2],
            main_args: Vec::new(),
        };

        PoseidonAir::eval_block(ctx, &frame, &periodic, &mut res, &mut ix);

        assert!(res.iter().all(|v| *v == BE::ZERO));
    }

    #[test]
    fn sponge_binding_mux_negative() {
        let cols = Columns::baseline();

        let mut frame = EvaluationFrame::<BE>::new(cols.width(0));
        let mut periodic = vec![BE::ZERO; 1 + POSEIDON_ROUNDS + 1 + 1 + 1 + 1];
        periodic[0] = BE::ONE; // map

        frame.current_mut()[cols.pose_active] = BE::ONE;
        frame.current_mut()[cols.op_sponge] = BE::ONE;

        for i in 0..8 {
            frame.current_mut()[cols.r_index(i)] = BE::from((20 + i) as u64);
        }

        // pick index 3 (b2,b1,b0=0,1,1),
        // active=1
        frame.current_mut()[cols.sel_s_b_index(0, 0)] = BE::ONE;
        frame.current_mut()[cols.sel_s_b_index(0, 1)] = BE::ONE;
        frame.current_mut()[cols.sel_s_b_index(0, 2)] = BE::ZERO;
        frame.current_mut()[cols.sel_s_active_index(0)] = BE::ONE;

        // put wrong lane
        // value (e.g., r5)
        frame.current_mut()[cols.lane_index(0)] = BE::from(25u64);

        let mut pi = zk_lisp_proof::pi::PublicInputs::default();
        pi.feature_mask |= zk_lisp_proof::pi::FM_VM | zk_lisp_proof::pi::FM_SPONGE;

        let rc_box = [[BE::ZERO; 12]; POSEIDON_ROUNDS];
        let mds_box = [[BE::ZERO; 12]; 12];
        let dom_box = [BE::ZERO; 2];

        let mut res = vec![BE::ZERO; 12 * POSEIDON_ROUNDS + 12 + 16];
        let mut ix = 0usize;

        let rc3_box = [[BE::ZERO; 3]; POSEIDON_ROUNDS];
        let mds3_box = [[BE::ZERO; 3]; 3];
        let w_enc0_box = [BE::ZERO; 59];
        let w_enc1_box = [BE::ZERO; 59];

        let features = pi.get_features();
        let ctx = &AirSharedContext {
            pub_inputs: pi,
            cols,
            features,
            poseidon_rc: rc_box,
            poseidon_mds: mds_box,
            poseidon_dom: dom_box,
            rom_rc: rc3_box,
            rom_mds: mds3_box,
            rom_w_enc0: w_enc0_box,
            rom_w_enc1: w_enc1_box,
            rom_s_initial: [BE::ZERO; 3],
            rom_s_final: [BE::ZERO; 3],
            pc_init: BE::ZERO,
            program_fe: [BE::ZERO; 2],
            main_args: Vec::new(),
        };

        PoseidonAir::eval_block(ctx, &frame, &periodic, &mut res, &mut ix);

        assert!(res.iter().any(|v| *v != BE::ZERO));
    }
}

// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

mod kv;
mod merkle;
mod mixers;
mod poseidon;
mod schedule;
mod vm_alu;
mod vm_ctrl;

use crate::air::{
    kv::KvBlock, merkle::MerkleBlock, poseidon::PoseidonBlock, schedule::ScheduleBlock,
    vm_alu::VmAluBlock, vm_ctrl::VmCtrlBlock,
};
use crate::layout::{Columns, NR, POSEIDON_ROUNDS, STEPS_PER_LEVEL_P2};
use crate::pi::{FeaturesMap, PublicInputs};
use crate::poseidon as poseidon_core;
use crate::schedule as schedule_core;

use core::marker::PhantomData;
use winterfell::math::FieldElement;
use winterfell::math::fft;
use winterfell::math::fields::f128::{BaseElement as BE, BaseElement};
use winterfell::{
    Air, AirContext, Assertion, EvaluationFrame, ProofOptions, TraceInfo,
    TransitionConstraintDegree,
};

pub struct BlockCtx<'a, E: FieldElement> {
    pub cols: &'a Columns,
    pub pub_inputs: &'a PublicInputs,
    pub poseidon_rc: &'a [[BE; 12]; POSEIDON_ROUNDS],
    pub poseidon_mds: &'a [[BE; 12]; 12],
    pub poseidon_dom: &'a [BE; 2],
    _pd: PhantomData<E>,
}

impl<'a, E: FieldElement> BlockCtx<'a, E> {
    pub fn new(
        cols: &'a Columns,
        pub_inputs: &'a PublicInputs,
        poseidon_rc: &'a [[BE; 12]; POSEIDON_ROUNDS],
        poseidon_mds: &'a [[BE; 12]; 12],
        poseidon_dom: &'a [BE; 2],
    ) -> Self {
        Self {
            cols,
            pub_inputs,
            poseidon_rc,
            poseidon_mds,
            poseidon_dom,
            _pd: PhantomData,
        }
    }
}

pub trait AirBlock<E: FieldElement> {
    #[allow(dead_code)]
    fn push_degrees(out: &mut Vec<TransitionConstraintDegree>);

    fn eval_block(
        ctx: &BlockCtx<E>,
        frame: &EvaluationFrame<E>,
        periodic: &[E],
        result: &mut [E],
        ix: &mut usize,
    );

    fn append_assertions(ctx: &BlockCtx<E>, out: &mut Vec<Assertion<E::BaseField>>, last: usize) {
        let _ = (ctx, out, last);
    }
}

#[derive(Clone)]
#[allow(dead_code)]
pub struct ZkLispAir {
    ctx: AirContext<BaseElement>,
    pub_inputs: PublicInputs,
    cols: Columns,
    features: FeaturesMap,

    poseidon_rc: [[BaseElement; 12]; POSEIDON_ROUNDS],
    poseidon_mds: [[BaseElement; 12]; 12],
    poseidon_dom: [BaseElement; 2],
}

impl Air for ZkLispAir {
    type BaseField = BaseElement;
    type PublicInputs = PublicInputs;

    fn new(info: TraceInfo, pub_inputs: Self::PublicInputs, options: ProofOptions) -> Self {
        let mut degrees = Vec::new();

        let features = pub_inputs.get_features();
        if features.poseidon {
            <PoseidonBlock as AirBlock<BE>>::push_degrees(&mut degrees);

            // When VM is enabled AND sponge ops
            // are present enforce VM->lane bindings
            // on map rows of absorb operations.
            if features.vm && features.sponge {
                PoseidonBlock::push_degrees_vm_bind(&mut degrees);
            }
        }
        if features.vm {
            VmCtrlBlock::push_degrees(&mut degrees, features.sponge);
            <VmAluBlock as AirBlock<BE>>::push_degrees(&mut degrees);
        }
        if features.kv {
            <KvBlock as AirBlock<BE>>::push_degrees(&mut degrees);
        }
        if features.merkle {
            <MerkleBlock as AirBlock<BE>>::push_degrees(&mut degrees);
        }

        // Boundary assertions count per level:
        let levels = (info.length() / STEPS_PER_LEVEL_P2).max(1);

        // Strict schedule/domain boundary
        // assertions per level:
        // ones at positions: (2 + R)
        // zeros at non-positions: (4R + 2)
        // domain tags at map: 2
        let mut num_assertions =
            (2 + POSEIDON_ROUNDS) * levels + (4 * POSEIDON_ROUNDS + 2) * levels + 2 * levels;

        if features.vm {
            // bind program commitment at lvl0 map row
            // + PC=0 at lvl0 map when program
            // commitment is set (added in schedule block).
            num_assertions += 1;

            if pub_inputs.program_commitment.iter().any(|b| *b != 0) {
                num_assertions += 1;
            }

            // bind VM args at lvl0 map row
            num_assertions += pub_inputs.vm_args.len();
        }
        if features.vm && features.vm_expect {
            // one assertion for expected
            // output at computed row.
            num_assertions += 1;
        }
        if features.kv && features.kv_expect {
            // offset for EXPECT ties alignment
            num_assertions += 2 * (pub_inputs.kv_levels_mask.count_ones() as usize) + 1;
        }
        if features.kv {
            num_assertions += 4 * (pub_inputs.kv_levels_mask.count_ones() as usize);
        }
        if num_assertions == 0 {
            num_assertions = 1;
        }

        // Debug: print expected evals and context
        Self::print_evals_debug(&pub_inputs, &info, &features, &degrees);

        // Ensure at least one degree exists
        let degrees = if degrees.is_empty() {
            vec![TransitionConstraintDegree::new(1)]
        } else {
            degrees
        };

        let ctx = AirContext::new(info, degrees, num_assertions, options);
        let cols = Columns::baseline();

        Self::print_degrees_debug(&ctx, &pub_inputs, &features);

        let suite_id = &pub_inputs.program_commitment;
        let ps = poseidon_core::get_poseidon_suite(suite_id);

        let mut rc_arr = [[BaseElement::ZERO; 12]; POSEIDON_ROUNDS];
        for (i, row) in ps.rc.iter().enumerate().take(POSEIDON_ROUNDS) {
            rc_arr[i] = *row;
        }

        let mds = ps.mds;
        let dom = ps.dom;

        Self {
            ctx,
            pub_inputs,
            cols,
            features,
            poseidon_rc: rc_arr,
            poseidon_mds: mds,
            poseidon_dom: dom,
        }
    }

    fn context(&self) -> &AirContext<Self::BaseField> {
        &self.ctx
    }

    fn evaluate_transition<E: FieldElement<BaseField = Self::BaseField>>(
        &self,
        frame: &EvaluationFrame<E>,
        periodic_values: &[E],
        result: &mut [E],
    ) {
        let bctx = BlockCtx::<E>::new(
            &self.cols,
            &self.pub_inputs,
            &self.poseidon_rc,
            &self.poseidon_mds,
            &self.poseidon_dom,
        );

        let mut ix = 0usize;

        if self.features.poseidon {
            PoseidonBlock::eval_block(&bctx, frame, periodic_values, result, &mut ix);
        }
        if self.features.vm {
            vm_ctrl::VmCtrlBlock::eval_block(&bctx, frame, periodic_values, result, &mut ix);
            vm_alu::VmAluBlock::eval_block(&bctx, frame, periodic_values, result, &mut ix);
        }
        if self.features.kv {
            kv::KvBlock::eval_block(&bctx, frame, periodic_values, result, &mut ix);
        }
        if self.features.merkle {
            merkle::MerkleBlock::eval_block(&bctx, frame, periodic_values, result, &mut ix);
        }

        debug_assert_eq!(ix, result.len());

        // Fail-closed in release builds if
        // transition constraint count mismatches
        if ix != result.len() {
            #[cfg(not(debug_assertions))]
            {
                tracing::error!(
                    target = "proof.air",
                    "constraint count mismatch at runtime: wrote {} of {}",
                    ix,
                    result.len()
                );

                if !result.is_empty() {
                    result[0] = E::ONE;
                }
            }
        }
    }

    fn get_assertions(&self) -> Vec<Assertion<Self::BaseField>> {
        let last = self.ctx.trace_len().saturating_sub(1);
        let mut out = Vec::new();

        // Schedule/domain-tag assertions (per-level)
        let bctx_sched = BlockCtx::<BaseElement>::new(
            &self.cols,
            &self.pub_inputs,
            &self.poseidon_rc,
            &self.poseidon_mds,
            &self.poseidon_dom,
        );
        ScheduleBlock::append_assertions(&bctx_sched, &mut out, last);

        // Kv per-level boundary assertions
        if self.features.kv {
            let bctx = BlockCtx::<BaseElement>::new(
                &self.cols,
                &self.pub_inputs,
                &self.poseidon_rc,
                &self.poseidon_mds,
                &self.poseidon_dom,
            );
            KvBlock::append_assertions(&bctx, &mut out, last);
        }

        // VM PI binding assertions (inputs/outputs)
        if self.features.vm {
            // Bind inputs at level 0 map row
            let row_map0 = schedule_core::pos_map();
            for (i, &a) in self.pub_inputs.vm_args.iter().enumerate() {
                if i < NR {
                    out.push(Assertion::single(
                        self.cols.r_index(i),
                        row_map0,
                        BE::from(a),
                    ));
                }
            }

            // Expected output at selected row
            if self.features.vm_expect {
                let row = (self.pub_inputs.vm_out_row as usize).min(last);
                let reg = (self.pub_inputs.vm_out_reg as usize).min(NR - 1);
                let exp = crate::pi::be_from_le8(&self.pub_inputs.vm_expected_bytes);

                tracing::debug!(
                    target = "proof.air",
                    "vm_expect: assert reg={} row={} exp={:?}",
                    reg,
                    row,
                    exp
                );

                out.push(Assertion::single(self.cols.r_index(reg), row, exp));
            }
        }

        if out.is_empty() {
            out.push(Assertion::single(self.cols.mask, last, BE::from(0u32)));
        }

        // Debug: validate assertion columns
        let width = self.cols.width(self.pub_inputs.feature_mask);
        let mut bad = 0usize;
        let mut max_col = 0usize;

        for a in &out {
            let c = a.column();
            if c > max_col {
                max_col = c;
            }
            if c >= width {
                bad += 1;
            }
        }

        tracing::debug!(
            target="proof.air",
            assertions_len=%out.len(),
            width=%width,
            last=%last,
            bad_cols=%bad,
            max_col=%max_col,
        );
        out
    }

    fn get_periodic_column_values(&self) -> Vec<Vec<Self::BaseField>> {
        let n = self.ctx.trace_len();
        let sels_u8 = schedule_core::build_periodic_selectors(n);

        sels_u8
            .into_iter()
            .map(|col| {
                col.into_iter()
                    .map(|b| if b == 1 { BE::ONE } else { BE::ZERO })
                    .collect()
            })
            .collect()
    }

    fn get_periodic_column_polys(&self) -> Vec<Vec<Self::BaseField>> {
        let n = self.ctx.trace_len();
        let cycle = STEPS_PER_LEVEL_P2;

        // p_map, p_rounds[R], p_final,
        // p_pad, p_pad_last, p_last.
        let cols_len = 1 + POSEIDON_ROUNDS + 1 + 1 + 1 + 1;

        let mut values: Vec<Vec<BE>> = (0..cols_len).map(|_| Vec::new()).collect();

        for pos in 0..cycle {
            // p_map
            values[0].push(if pos == schedule_core::pos_map() {
                BE::ONE
            } else {
                BE::ZERO
            });

            // rounds
            for j in 0..POSEIDON_ROUNDS {
                values[1 + j].push(if pos == 1 + j { BE::ONE } else { BE::ZERO });
            }

            // p_final
            values[1 + POSEIDON_ROUNDS].push(if pos == schedule_core::pos_final() {
                BE::ONE
            } else {
                BE::ZERO
            });

            // p_pad
            let is_pad = pos != schedule_core::pos_map()
                && pos != schedule_core::pos_final()
                && !schedule_core::is_round_pos(pos);
            values[1 + POSEIDON_ROUNDS + 1].push(if is_pad { BE::ONE } else { BE::ZERO });

            // p_pad_last (last position in level)
            values[1 + POSEIDON_ROUNDS + 2].push(if pos == (cycle - 1) {
                BE::ONE
            } else {
                BE::ZERO
            });
        }

        // p_last over full n as a true
        // polynomial over the full trace domain.
        let mut p_last = vec![BE::ZERO; n];
        if n > 0 {
            p_last[n - 1] = BE::ONE;
        }

        // interpolate to polynomial
        // coefficients over size-n domain.
        if n > 0 {
            let inv_twiddles_n = fft::get_inv_twiddles::<BE>(n);
            fft::interpolate_poly(&mut p_last, &inv_twiddles_n);
        }

        values[1 + POSEIDON_ROUNDS + 3] = p_last;

        // interpolate first (1 + R + 1 + 1 + 1)
        // columns (excluding p_last) all of which
        // have length "cycle"; compute twiddles once.
        let inv_twiddles_cycle = fft::get_inv_twiddles::<BE>(cycle);

        for col in values.iter_mut().take(1 + POSEIDON_ROUNDS + 1 + 1 + 1) {
            debug_assert_eq!(col.len(), cycle);

            fft::interpolate_poly(col, &inv_twiddles_cycle);
        }

        values
    }
}

impl ZkLispAir {
    #[inline]
    fn print_evals_debug(
        _pub_inputs: &PublicInputs,
        info: &TraceInfo,
        features: &FeaturesMap,
        degrees: &[TransitionConstraintDegree],
    ) {
        let trace_len = info.length();
        let evals: Vec<usize> = degrees
            .iter()
            .map(|d| d.get_evaluation_degree(trace_len) - (trace_len - 1))
            .collect();

        tracing::debug!(
            target = "proof.air",
            "expected_eval_degrees_len={} evals={:?}",
            evals.len(),
            evals
        );

        // print per-block slices for easier debugging
        let mut ofs = 0usize;
        let mut dbg: Vec<(&str, Vec<usize>)> = Vec::new();

        if features.poseidon {
            let len = 12 * POSEIDON_ROUNDS + 12; // rounds + holds
            dbg.push(("poseidon", evals[ofs..ofs + len].to_vec()));
            ofs += len;
        }
        if features.vm {
            // vm_ctrl dynamic length:
            // 4*NR bit bools + 4 sums + 1 (sel cond)
            // + 10 op bools + 1 one-hot
            // + optional sponge: 10*NR bit bools + 10 sums
            let len = 4 * NR + 4 + 1 + 10 + 1 + if features.sponge { 10 * NR + 10 } else { 0 };
            dbg.push(("vm_ctrl", evals[ofs..ofs + len].to_vec()));
            ofs += len;

            // vm_alu (19)
            let len = 19;
            dbg.push(("vm_alu", evals[ofs..ofs + len].to_vec()));
            ofs += len;
        }
        if features.kv {
            let len = 6;
            dbg.push(("kv", evals[ofs..ofs + len].to_vec()));
        }

        tracing::debug!(target = "proof.air", "per_block_evals: {:?}", dbg);
    }

    #[inline]
    fn print_degrees_debug(
        ctx: &AirContext<BE>,
        _pub_inputs: &PublicInputs,
        features: &FeaturesMap,
    ) {
        let tl = ctx.trace_len();
        let ce = ctx.ce_domain_size();
        let lde = ctx.lde_domain_size();
        let blow_ce = ce / tl;

        tracing::debug!(
            target = "proof.air",
            "ctx: trace_len={} ce_domain_size={} lde_domain_size={} ce_blowup={} exemptions={}",
            tl,
            ce,
            lde,
            blow_ce,
            ctx.num_transition_exemptions()
        );

        let mut ofs = 0usize;
        let mut ranges = Vec::new();

        if features.poseidon {
            let len = 12 * POSEIDON_ROUNDS + 12; // rounds + holds
            ranges.push(("poseidon", ofs, ofs + len));
            ofs += len;
        }
        if features.vm {
            let len = 4 * NR + 4 + 1 + 10 + 1 + if features.sponge { 10 * NR + 10 } else { 0 };
            ranges.push(("vm_ctrl", ofs, ofs + len));
            ofs += len;

            let len2 = 19;
            ranges.push(("vm_alu", ofs, ofs + len2));
            ofs += len2;
        }
        if features.kv {
            let len = 6;
            ranges.push(("kv", ofs, ofs + len));
            ofs += len;
        }

        tracing::debug!(target = "proof.air", "deg_ranges: {:?}", ranges);
        tracing::debug!(target = "proof.air", "deg_len={} (computed)", ofs);
    }
}

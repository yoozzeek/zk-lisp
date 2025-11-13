// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

mod merkle;
mod mixers;
mod poseidon;
mod ram;
mod rom;
mod schedule;
mod vm_alu;
mod vm_ctrl;

use crate::air::{
    merkle::MerkleBlock, poseidon::PoseidonBlock, ram::RamBlock, rom::RomBlock,
    schedule::ScheduleBlock, vm_alu::VmAluBlock, vm_ctrl::VmCtrlBlock,
};
use crate::layout::{Columns, NR, POSEIDON_ROUNDS, STEPS_PER_LEVEL_P2};
use crate::pi::{FeaturesMap, PublicInputs};
use crate::poseidon::{derive_rom_mds_cauchy_3x3, derive_rom_round_constants_3};
use crate::schedule as schedule_core;
use crate::{poseidon as poseidon_core, utils};

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
    pub rom_rc: &'a [[BE; 3]; POSEIDON_ROUNDS],
    pub rom_mds: &'a [[BE; 3]; 3],
    pub rom_w_enc0: &'a [BE; 59],
    pub rom_w_enc1: &'a [BE; 59],
    _pd: PhantomData<E>,
}

impl<'a, E: FieldElement> BlockCtx<'a, E> {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        cols: &'a Columns,
        pub_inputs: &'a PublicInputs,
        poseidon_rc: &'a [[BE; 12]; POSEIDON_ROUNDS],
        poseidon_mds: &'a [[BE; 12]; 12],
        poseidon_dom: &'a [BE; 2],
        rom_rc: &'a [[BE; 3]; POSEIDON_ROUNDS],
        rom_mds: &'a [[BE; 3]; 3],
        rom_w_enc0: &'a [BE; 59],
        rom_w_enc1: &'a [BE; 59],
    ) -> Self {
        Self {
            cols,
            pub_inputs,
            poseidon_rc,
            poseidon_mds,
            poseidon_dom,
            rom_rc,
            rom_mds,
            rom_w_enc0,
            rom_w_enc1,
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
    rom_rc: [[BaseElement; 3]; POSEIDON_ROUNDS],
    rom_mds: [[BaseElement; 3]; 3],
    rom_w_enc0: [BaseElement; 59],
    rom_w_enc1: [BaseElement; 59],
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
        if features.ram {
            <RamBlock as AirBlock<BE>>::push_degrees(&mut degrees);
        }
        if features.merkle {
            <MerkleBlock as AirBlock<BE>>::push_degrees(&mut degrees);
        }
        // ROM accumulator when program
        // commitment is provided.
        if pub_inputs.program_commitment.iter().any(|b| *b != 0) {
            <RomBlock as AirBlock<BE>>::push_degrees(&mut degrees);
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
                num_assertions += 1; // PC=0 at lvl0 map
            }

            // bind VM args at lvl0 map row
            num_assertions += pub_inputs.vm_args.len();
        }
        if features.vm && features.vm_expect {
            // one assertion for expected
            // output at computed row.
            num_assertions += 1;
        }
        if num_assertions == 0 {
            num_assertions = 1;
        }

        // ROM accumulator boundaries:
        // - initial s0(map0) = 0 (1)
        // - final s0(last) = f0 and s1(last) = f1 (2)
        if pub_inputs.program_commitment.iter().any(|b| *b != 0) {
            num_assertions += 3;
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

        // Derive ROM t=3 params
        let rc_vec = derive_rom_round_constants_3(suite_id, POSEIDON_ROUNDS);
        let mut rom_rc_arr = [[BaseElement::ZERO; 3]; POSEIDON_ROUNDS];

        for (i, row) in rc_vec.iter().enumerate().take(POSEIDON_ROUNDS) {
            rom_rc_arr[i] = *row;
        }

        let rom_mds_arr = derive_rom_mds_cauchy_3x3(suite_id);

        // Precompute ROM encoding weights
        // W_k = g^k, k=1..59 for seeds
        // ROM_W_SEED_0 and ROM_W_SEED_1.
        let compute_weights = |seed: u32| -> [BaseElement; 59] {
            let g = BaseElement::from(3u64);

            // compute g^seed via exp
            let mut acc = BaseElement::ONE;
            let mut base = g;
            let mut e = seed as u64;

            while e > 0 {
                if (e & 1) == 1 {
                    acc *= base;
                }

                base *= base;
                e >>= 1;
            }

            let mut out = [BaseElement::ZERO; 59];
            let mut cur = acc * g; // g^(seed+1)

            for item in out.iter_mut() {
                *item = cur;
                cur *= g;
            }

            out
        };

        let rom_w_enc0 = compute_weights(utils::ROM_W_SEED_0);
        let rom_w_enc1 = compute_weights(utils::ROM_W_SEED_1);

        Self {
            ctx,
            pub_inputs,
            cols,
            features,
            poseidon_rc: rc_arr,
            poseidon_mds: mds,
            poseidon_dom: dom,
            rom_rc: rom_rc_arr,
            rom_mds: rom_mds_arr,
            rom_w_enc0,
            rom_w_enc1,
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
            &self.rom_rc,
            &self.rom_mds,
            &self.rom_w_enc0,
            &self.rom_w_enc1,
        );

        let mut ix = 0usize;

        if self.features.poseidon {
            PoseidonBlock::eval_block(&bctx, frame, periodic_values, result, &mut ix);
        }
        if self.features.vm {
            VmCtrlBlock::eval_block(&bctx, frame, periodic_values, result, &mut ix);
            VmAluBlock::eval_block(&bctx, frame, periodic_values, result, &mut ix);
        }
        if self.features.merkle {
            MerkleBlock::eval_block(&bctx, frame, periodic_values, result, &mut ix);
        }
        if self.features.ram {
            RamBlock::eval_block(&bctx, frame, periodic_values, result, &mut ix);
        }

        // ROM accumulator block is
        // independent of pose_active
        // and always runs when commit != 0
        if self.pub_inputs.program_commitment.iter().any(|b| *b != 0) {
            RomBlock::eval_block(&bctx, frame, periodic_values, result, &mut ix);
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
            &self.rom_rc,
            &self.rom_mds,
            &self.rom_w_enc0,
            &self.rom_w_enc1,
        );
        ScheduleBlock::append_assertions(&bctx_sched, &mut out, last);

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

        // ROM accumulator boundary assertions:
        // first map = 0, last = commit
        if self.pub_inputs.program_commitment.iter().any(|b| *b != 0) {
            RomBlock::append_assertions(&bctx_sched, &mut out, last);
        }

        if self.features.ram {
            // Final equality of grand-products
            out.push(Assertion::single(
                self.cols.ram_gp_unsorted,
                last,
                BE::from(0u32),
            ));
            out.push(Assertion::single(
                self.cols.ram_gp_sorted,
                last,
                BE::from(0u32),
            ));
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
    #[allow(unused_assignments)]
    fn print_evals_debug(
        pub_inputs: &PublicInputs,
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
        // ROM block
        if pub_inputs.program_commitment.iter().any(|b| *b != 0) {
            let len = 3 * POSEIDON_ROUNDS + 3 + 2;
            dbg.push(("rom", evals[ofs..ofs + len].to_vec()));
            ofs += len;
        }
        if features.vm {
            // vm_ctrl dynamic length:
            // 5*NR role booleans + 5 role sums + NR no-overlap
            // + optional sponge: 10*NR lane booleans + 10 lane sums
            // + 1 select-cond + 17 op booleans + 1 one-hot + 17 rom-op eq + 2 PC
            let len = 5 * NR
                + 5
                + NR
                + if features.sponge { 10 * NR + 10 } else { 0 }
                + 1
                + 17
                + 1
                + 17
                + 2;
            dbg.push(("vm_ctrl", evals[ofs..ofs + len].to_vec()));
            ofs += len;

            // vm_alu base (58)
            let len = 58;
            dbg.push(("vm_alu", evals[ofs..ofs + len].to_vec()));
            ofs += len;
        }
        if features.ram {
            // ram block length:
            // 6 base constraints
            // + 33 (32 bit booleanities + equality)
            // = 39
            let len = 39;
            dbg.push(("ram", evals[ofs..ofs + len].to_vec()));
            ofs += len;
        }

        tracing::debug!(target = "proof.air", "per_block_evals: {:?}", dbg);
    }

    #[inline]
    #[allow(unused_assignments)]
    fn print_degrees_debug(
        ctx: &AirContext<BE>,
        pub_inputs: &PublicInputs,
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
        if pub_inputs.program_commitment.iter().any(|b| *b != 0) {
            let len = 3 * POSEIDON_ROUNDS + 3 + 2;
            ranges.push(("rom", ofs, ofs + len));
            ofs += len;
        }
        if features.vm {
            let len = 5 * NR
                + 5
                + NR
                + if features.sponge { 10 * NR + 10 } else { 0 }
                + 1
                + 17
                + 1
                + 17
                + 2;
            ranges.push(("vm_ctrl", ofs, ofs + len));
            ofs += len;

            let len2 = 58;
            ranges.push(("vm_alu", ofs, ofs + len2));
            ofs += len2;
        }
        if features.ram {
            let len = 39;
            ranges.push(("ram", ofs, ofs + len));
            ofs += len;
        }

        tracing::debug!(target = "proof.air", "deg_ranges: {:?}", ranges);
        tracing::debug!(target = "proof.air", "deg_len={} (computed)", ofs);
    }
}

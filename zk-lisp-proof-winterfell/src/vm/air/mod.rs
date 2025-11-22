// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Composite Winterfell AIR for the zk-lisp virtual machine.
//!
//! Glues together Poseidon, VM ALU/CTRL, RAM, Merkle and ROM
//! modules, derives per-feature constraint degrees and builds
//! boundary assertions from backend-agnostic public inputs.

mod alu;
mod ctrl;
mod merkle;
mod mixers;
mod poseidon;
mod ram;
mod rom;
mod schedule;

use crate::poseidon::{derive_rom_mds_cauchy_3x3, derive_rom_round_constants_3};
use crate::vm::air::{merkle::MerkleAir, poseidon::PoseidonAir, schedule::ScheduleAir};
use crate::vm::layout::{
    Columns, LayoutConfig, NR, POSEIDON_ROUNDS, SPONGE_IDX_BITS, STEPS_PER_LEVEL_P2,
};
use crate::vm::schedule as schedule_core;
use crate::{poseidon as poseidon_core, utils};

use alu::VmAluAir;
use ctrl::VmCtrlAir;
use ram::RamAir;
use rom::RomAir;
use std::collections::BTreeMap;
use std::sync::Arc;
use winterfell::math::FieldElement;
use winterfell::math::fft;
use winterfell::math::fields::f128::{BaseElement as BE, BaseElement};
use winterfell::{
    Air, AirContext, Assertion, EvaluationFrame, ProofOptions, TraceInfo,
    TransitionConstraintDegree,
};
use zk_lisp_proof::pi::{FeaturesMap, PublicInputs as CorePublicInputs};

use crate::AirPublicInputs;

trait AirModule {
    fn push_degrees(ctx: &AirSharedContext, out: &mut Vec<TransitionConstraintDegree>);

    fn eval_block<E>(
        ctx: &AirSharedContext,
        frame: &EvaluationFrame<E>,
        periodic: &[E],
        result: &mut [E],
        ix: &mut usize,
    ) where
        E: FieldElement<BaseField = BE> + From<BE>;

    fn append_assertions(ctx: &AirSharedContext, out: &mut Vec<Assertion<BE>>, last: usize) {
        let _ = (ctx, out, last);
    }
}

struct AirSharedContext {
    pub pub_inputs: CorePublicInputs,
    pub cols: Columns,
    pub features: FeaturesMap,
    pub poseidon_rc: [[BaseElement; 12]; POSEIDON_ROUNDS],
    pub poseidon_mds: [[BaseElement; 12]; 12],
    pub poseidon_dom: [BaseElement; 2],
    pub rom_rc: [[BaseElement; 3]; POSEIDON_ROUNDS],
    pub rom_mds: [[BaseElement; 3]; 3],
    pub rom_w_enc0: [BaseElement; 59],
    pub rom_w_enc1: [BaseElement; 59],

    /// Segment-local ROM t=3 state at the beginning and end
    /// of the trace as observed by the prover.
    pub rom_s_initial: [BaseElement; 3],
    pub rom_s_final: [BaseElement; 3],

    /// Program counter at the first map row of the trace.
    pub pc_init: BaseElement,

    /// Field-level program commitment derived from the
    /// Blake3 program_commitment (two field elements).
    pub program_fe: [BaseElement; 2],

    /// Runtime public arguments to `main` flattened
    /// into base-field "slots".
    pub main_args: Vec<BaseElement>,
}

#[derive(Clone)]
pub struct ZkLispAir {
    ctx: AirContext<BaseElement>,
    shared_ctx: Arc<AirSharedContext>,
}

impl Air for ZkLispAir {
    type BaseField = BaseElement;
    type PublicInputs = AirPublicInputs;

    fn new(info: TraceInfo, pub_inputs: Self::PublicInputs, options: ProofOptions) -> Self {
        let mut degrees = Vec::new();

        let core = pub_inputs.core;

        // Select effective feature mask
        // for this trace instance.
        let eff_mask = if pub_inputs.segment_feature_mask != 0 {
            pub_inputs.segment_feature_mask
        } else {
            core.feature_mask
        };

        let suite_id = &core.program_commitment;
        let ps = poseidon_core::get_poseidon_suite(suite_id);

        let mut rc_arr = [[BaseElement::ZERO; 12]; POSEIDON_ROUNDS];
        for (i, row) in ps.rc.iter().enumerate().take(POSEIDON_ROUNDS) {
            rc_arr[i] = *row;
        }

        let mds = ps.mds;
        let dom = ps.dom;

        let features = zk_lisp_proof::pi::FeaturesMap::from_mask(eff_mask);
        let rom_enabled = core.program_commitment.iter().any(|b| *b != 0);
        let layout_cfg = if pub_inputs.segment_feature_mask != 0 {
            LayoutConfig {
                vm: true,
                ram: features.ram,
                sponge: features.sponge,
                merkle: features.merkle,
                rom: rom_enabled,
            }
        } else {
            // Fallback to the conservative baseline layout
            LayoutConfig {
                vm: true,
                ram: true,
                sponge: true,
                merkle: true,
                rom: rom_enabled,
            }
        };

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

        // Derive field-level
        // program commitment once.
        let program_fe = if core.program_commitment.iter().any(|b| *b != 0) {
            crate::commit::program_field_commitment(&core.program_commitment)
        } else {
            [BaseElement::ZERO; 2]
        };

        // Flatten typed main_args into base-field
        // slots using the same encoding as PI.
        let main_args_fe: Vec<BaseElement> =
            crate::utils::encode_main_args_to_slots(&core.main_args);

        let cols = Columns::for_config(&layout_cfg);
        let shared_ctx = Arc::new(AirSharedContext {
            pub_inputs: core.clone(),
            cols,
            features,
            poseidon_rc: rc_arr,
            poseidon_mds: mds,
            poseidon_dom: dom,
            rom_rc: rom_rc_arr,
            rom_mds: rom_mds_arr,
            rom_w_enc0,
            rom_w_enc1,
            rom_s_initial: pub_inputs.rom_s_in,
            rom_s_final: pub_inputs.rom_s_out,
            pc_init: pub_inputs.pc_init,
            program_fe,
            main_args: main_args_fe,
        });

        // Init AIR modules
        if features.poseidon {
            PoseidonAir::push_degrees(&shared_ctx, &mut degrees);
        }

        if features.vm {
            VmCtrlAir::push_degrees(&shared_ctx, &mut degrees);
            VmAluAir::push_degrees(&shared_ctx, &mut degrees);
        }

        if features.ram {
            RamAir::push_degrees(&shared_ctx, &mut degrees);
        }

        if features.merkle {
            MerkleAir::push_degrees(&shared_ctx, &mut degrees);
        }

        // ROM accumulator when program
        // commitment is provided.
        if rom_enabled {
            RomAir::push_degrees(&shared_ctx, &mut degrees);
        }

        // Boundary assertions count per level
        let levels = (info.length() / STEPS_PER_LEVEL_P2).max(1);

        // Strict schedule/domain boundary
        // assertions per level:
        // ones at positions: (2 + R)
        // zeros at non-positions: (4R + 2)
        // domain tags at map: 2
        let mut num_assertions =
            (2 + POSEIDON_ROUNDS) * levels + (4 * POSEIDON_ROUNDS + 2) * levels + 2 * levels;

        if features.vm {
            // PC binding at level-0 map row
            // is always present in ScheduleAir
            num_assertions += 1;

            // pi_prog binding is added only when
            // this trace starts from PC=0 and the
            // program commitment is set .
            if pub_inputs.pc_init == BE::from(0u32)
                && core.program_commitment.iter().any(|b| *b != 0)
            {
                num_assertions += 1;
            }

            // Bind runtime public main_args slots to the
            // tail of the register file at level 0 map row.
            let main_slots_len = utils::encode_main_args_to_slots(&core.main_args).len();
            if main_slots_len > 0 {
                num_assertions += main_slots_len;
            }
        }
        if features.vm && features.vm_expect {
            // one assertion for expected
            // output at computed row.
            num_assertions += 1;
        }
        if num_assertions == 0 {
            num_assertions = 1;
        }

        // ROM accumulator boundary:
        // - initial s0(map0) = 0
        // - final lanes 0/1 at last row bound
        //   to rom_acc[0/1].
        if rom_enabled {
            // ROM now binds three lanes at both the initial map row and the final row.
            num_assertions += 6;
        }

        print_evals_debug(&core, &info, &features, &degrees);

        // Ensure at least one degree exists
        let degrees = if degrees.is_empty() {
            vec![TransitionConstraintDegree::new(1)]
        } else {
            degrees
        };

        let ctx = AirContext::new(info, degrees, num_assertions, options);
        print_degrees_debug(&ctx, &core, &features);

        Self { ctx, shared_ctx }
    }

    fn context(&self) -> &AirContext<Self::BaseField> {
        &self.ctx
    }

    fn evaluate_transition<E>(
        &self,
        frame: &EvaluationFrame<E>,
        periodic_values: &[E],
        result: &mut [E],
    ) where
        E: FieldElement<BaseField = Self::BaseField> + From<Self::BaseField>,
    {
        let ctx = &self.shared_ctx;
        let mut ix = 0usize;

        if ctx.features.poseidon {
            PoseidonAir::eval_block(ctx, frame, periodic_values, result, &mut ix);
        }

        if ctx.features.vm {
            VmCtrlAir::eval_block(ctx, frame, periodic_values, result, &mut ix);
            VmAluAir::eval_block(ctx, frame, periodic_values, result, &mut ix);
        }

        if ctx.features.ram {
            RamAir::eval_block(ctx, frame, periodic_values, result, &mut ix);
        }

        if ctx.features.merkle {
            MerkleAir::eval_block(ctx, frame, periodic_values, result, &mut ix);
        }

        // ROM accumulator block is
        // independent of pose_active
        // and always runs when commit != 0
        if ctx.pub_inputs.program_commitment.iter().any(|b| *b != 0) {
            RomAir::eval_block(ctx, frame, periodic_values, result, &mut ix);
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
        let ctx = &self.shared_ctx;
        let last = self.ctx.trace_len().saturating_sub(1);
        let mut out = Vec::new();

        ScheduleAir::append_assertions(ctx, &mut out, last);

        // VM PI binding assertions
        if ctx.features.vm {
            // Expected output at selected row
            if ctx.features.vm_expect {
                let row = (ctx.pub_inputs.vm_out_row as usize).min(last);
                let reg = (ctx.pub_inputs.vm_out_reg as usize).min(NR - 1);
                let exp = crate::utils::be_from_le8(&ctx.pub_inputs.vm_expected_bytes);

                tracing::debug!(
                    target = "proof.air",
                    "vm_expect: assert reg={} row={} exp={:?}",
                    reg,
                    row,
                    exp
                );

                out.push(Assertion::single(ctx.cols.r_index(reg), row, exp));
            }

            // Bind runtime public main_args (already
            // flattened into base-field slots) to the
            // tail of the register file at level 0 map row.
            if !ctx.main_args.is_empty() {
                let slots = ctx.main_args.len();
                assert!(slots <= NR, "main_args must fit into NR registers");

                let tail_start = NR - slots;
                let row0_map = schedule_core::pos_map();

                for (j, val) in ctx.main_args.iter().enumerate() {
                    let reg_idx = tail_start + j;
                    let col = ctx.cols.r_index(reg_idx);
                    out.push(Assertion::single(col, row0_map, *val));
                }
            }
        }

        // ROM accumulator boundary assertions:
        // first map = 0, last = commit
        if ctx.pub_inputs.program_commitment.iter().any(|b| *b != 0) {
            RomAir::append_assertions(ctx, &mut out, last);
        }

        if ctx.features.ram {
            // RAM grand-product accumulators are wired via transition
            // constraints (including final-row equality between unsorted
            // and sorted views). Global initial/final values are
            // tracked at the recursion layer via AggAirPublicInputs and
            // RecursionPublic; we intentionally avoid forcing them to
            // zero here to keep the AIR usable for segment-local proofs.
        }

        if out.is_empty() {
            out.push(Assertion::single(ctx.cols.mask, last, BE::from(0u32)));
        }

        // Deduplicate assertions by (column, step). Winterfell
        // rejects overlapping assertions even when they bind
        // the same value; keeping just one instance preserves
        // semantics and matches the intent of the AIR.
        let mut seen: BTreeMap<(usize, usize), BE> = BTreeMap::new();
        let mut dedup = Vec::with_capacity(out.len());

        for a in out.into_iter() {
            let key = (a.column(), a.first_step());
            let val = a.values()[0];

            if let Some(prev) = seen.get(&key) {
                // If overlapping assertions disagree, this is
                // a logic bug in the AIR; enforce only in debug.
                debug_assert_eq!(
                    *prev, val,
                    "conflicting boundary assertions for column {} step {}: {:?} vs {:?}",
                    key.0, key.1, prev, val,
                );

                // Identical assertion already recorded (or debug-only
                // conflict already reported); skip.
                continue;
            }

            seen.insert(key, val);
            dedup.push(a);
        }

        // Debug:
        // validate assertion columns
        let width = ctx.cols.width(ctx.pub_inputs.feature_mask);

        let mut bad = 0usize;
        let mut max_col = 0usize;

        for a in &dedup {
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
            assertions_len=%dedup.len(),
            width=%width,
            last=%last,
            bad_cols=%bad,
            max_col=%max_col,
        );

        dedup
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

#[inline]
#[allow(unused_assignments)]
fn print_evals_debug(
    pub_inputs: &CorePublicInputs,
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
        // Poseidon: per-round (12 lanes * R) + holds (12),
        // plus optional VM->sponge lane bindings when
        // both VM and sponge features are enabled.
        let base_len = 12 * POSEIDON_ROUNDS + 12;
        let extra = if features.vm && features.sponge {
            10
        } else {
            0
        };
        let len = base_len + extra;

        if ofs + len <= evals.len() {
            dbg.push(("poseidon", evals[ofs..ofs + len].to_vec()));
            ofs += len;
        }
    }

    if features.vm {
        // vm_ctrl dynamic length:
        // 5*NR role booleans + 5 role sums + NR no-overlap
        // + optional sponge: (10 lanes * SPONGE_IDX_BITS) bit booleans
        //   + 10 lane-active booleans
        // + 1 select-cond + 17 op booleans + 1 one-hot + 17 rom-op eq + 2 PC
        let sponge_extra = if features.sponge {
            10 * SPONGE_IDX_BITS + 10
        } else {
            0
        };

        let len = 5 * NR + 5 + NR + sponge_extra + 1 + 17 + 1 + 17 + 2;
        if ofs + len <= evals.len() {
            dbg.push(("vm_ctrl", evals[ofs..ofs + len].to_vec()));
            ofs += len;
        }

        // vm_alu: carry (NR) + write (NR) + 42 misc
        let len = 2 * NR + 42;
        if ofs + len <= evals.len() {
            dbg.push(("vm_alu", evals[ofs..ofs + len].to_vec()));
            ofs += len;
        }
    }

    if features.ram {
        // ram block length:
        // 6 base constraints
        // + 33 (32 bit booleanities + equality)
        // + 1 final-row GP equality
        // = 40
        let len = 40;
        if ofs + len <= evals.len() {
            dbg.push(("ram", evals[ofs..ofs + len].to_vec()));
            ofs += len;
        }
    }

    if features.merkle {
        // merkle block: 7 constraints
        let len = 7;
        if ofs + len <= evals.len() {
            dbg.push(("merkle", evals[ofs..ofs + len].to_vec()));
            ofs += len;
        }
    }

    // ROM block comes last in degree construction
    if pub_inputs.program_commitment.iter().any(|b| *b != 0) {
        let len = 3 * POSEIDON_ROUNDS + 3 + 2;
        if ofs + len <= evals.len() {
            dbg.push(("rom", evals[ofs..ofs + len].to_vec()));
            ofs += len;
        }
    }

    tracing::debug!(target = "proof.air", "per_block_evals: {:?}", dbg);
}

#[inline]
#[allow(unused_assignments)]
fn print_degrees_debug(
    ctx: &AirContext<BE>,
    pub_inputs: &CorePublicInputs,
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
        let base_len = 12 * POSEIDON_ROUNDS + 12;
        let extra = if features.vm && features.sponge {
            10
        } else {
            0
        };
        let len = base_len + extra;
        ranges.push(("poseidon", ofs, ofs + len));
        ofs += len;
    }

    if features.vm {
        let sponge_extra = if features.sponge {
            10 * SPONGE_IDX_BITS + 10
        } else {
            0
        };
        let len = 5 * NR + 5 + NR + sponge_extra + 1 + 17 + 1 + 17 + 2;
        ranges.push(("vm_ctrl", ofs, ofs + len));
        ofs += len;

        let len2 = 2 * NR + 42;
        ranges.push(("vm_alu", ofs, ofs + len2));
        ofs += len2;
    }

    if features.ram {
        let len = 40;
        ranges.push(("ram", ofs, ofs + len));
        ofs += len;
    }

    if features.merkle {
        let len = 7;
        ranges.push(("merkle", ofs, ofs + len));
        ofs += len;
    }

    if pub_inputs.program_commitment.iter().any(|b| *b != 0) {
        let len = 3 * POSEIDON_ROUNDS + 3 + 2;
        ranges.push(("rom", ofs, ofs + len));
        ofs += len;
    }

    tracing::debug!(target = "proof.air", "deg_ranges: {:?}", ranges);
    tracing::debug!(target = "proof.air", "deg_len={} (computed)", ofs);
}

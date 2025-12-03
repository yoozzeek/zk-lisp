// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

use crate::vm::layout::VM_USAGE_RAM_DELTA_CLK;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::{AirContext, TraceInfo, TransitionConstraintDegree};
use zk_lisp_proof::pi::{FeaturesMap, PublicInputs as CorePublicInputs};

#[inline]
#[allow(unused_assignments)]
pub(super) fn print_evals_debug(
    pub_inputs: &CorePublicInputs,
    info: &TraceInfo,
    features: &FeaturesMap,
    degrees: &[TransitionConstraintDegree],
    vm_usage_mask: u32,
    ram_delta_clk_bits: u32,
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

    let ranges =
        compute_deg_ranges_for_debug(pub_inputs, features, vm_usage_mask, ram_delta_clk_bits);
    let mut dbg: Vec<(&str, Vec<usize>)> = Vec::new();

    for (name, start, end) in ranges {
        if start >= evals.len() {
            break;
        }

        let end_clipped = core::cmp::min(end, evals.len());
        dbg.push((name, evals[start..end_clipped].to_vec()));
    }

    tracing::debug!(target = "proof.air", "per_block_evals: {:?}", dbg);
}

#[inline]
#[allow(unused_assignments)]
pub(super) fn print_degrees_debug(
    ctx: &AirContext<BE>,
    pub_inputs: &CorePublicInputs,
    features: &FeaturesMap,
    vm_usage_mask: u32,
    ram_delta_clk_bits: u32,
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

    let ranges =
        compute_deg_ranges_for_debug(pub_inputs, features, vm_usage_mask, ram_delta_clk_bits);
    let deg_len = ranges.last().map(|&(_, _, end)| end).unwrap_or(0);

    tracing::debug!(target = "proof.air", "deg_ranges: {:?}", ranges);
    tracing::debug!(target = "proof.air", "deg_len={} (computed)", deg_len);
}

fn compute_deg_ranges_for_debug(
    pub_inputs: &CorePublicInputs,
    features: &FeaturesMap,
    vm_usage_mask: u32,
    ram_delta_clk_bits: u32,
) -> Vec<(&'static str, usize, usize)> {
    use crate::vm::layout::{
        NR, POSEIDON_ROUNDS, SPONGE_IDX_BITS, VM_USAGE_ASSERT, VM_USAGE_ASSERT_BIT,
        VM_USAGE_ASSERT_RANGE, VM_USAGE_DIV128, VM_USAGE_DIVMOD, VM_USAGE_EQ, VM_USAGE_MULWIDE,
        VM_USAGE_SPONGE,
    };

    let mut ofs = 0usize;
    let mut ranges = Vec::new();

    // Poseidon
    if features.poseidon {
        let base_len = 12 * POSEIDON_ROUNDS + 12;
        // VM→sponge bindings активны только если и VM, и sponge feature, и sponge реально используется
        let extra =
            if features.vm && features.sponge && (vm_usage_mask & (1 << VM_USAGE_SPONGE)) != 0 {
                10
            } else {
                0
            };
        let len = base_len + extra;
        ranges.push(("poseidon", ofs, ofs + len));
        ofs += len;
    }

    // VM (CTRL + ALU)
    if features.vm {
        // CTRL: роли (5*NR), суммы ролей (5), no-overlap (NR)
        let len_roles = 5 * NR + 5 + NR;
        // Sponge‑селектора в CTRL включаются только если feature.sponge и sponge реально используется
        let sponge_extra = if features.sponge && (vm_usage_mask & (1 << VM_USAGE_SPONGE)) != 0 {
            10 * SPONGE_IDX_BITS + 10
        } else {
            0
        };
        // остальной хвост CTRL: select‑cond, 17 op‑bool, one‑hot, 17 ROM‑eq, 2 PC
        let len_tail = 1 + 17 + 1 + 17 + 2;
        let len_ctrl = len_roles + sponge_extra + len_tail;

        ranges.push(("vm_ctrl", ofs, ofs + len_ctrl));
        ofs += len_ctrl;

        // ALU: carry+write всегда, остальное по vm_usage_mask
        let mut len_alu = 2 * NR;

        let use_eq = (vm_usage_mask & (1 << VM_USAGE_EQ)) != 0;
        let use_divmod = (vm_usage_mask & (1 << VM_USAGE_DIVMOD)) != 0;
        let use_mulwide = (vm_usage_mask & (1 << VM_USAGE_MULWIDE)) != 0;
        let use_div128 = (vm_usage_mask & (1 << VM_USAGE_DIV128)) != 0;
        let use_assert = (vm_usage_mask & (1 << VM_USAGE_ASSERT)) != 0;
        let use_assert_bit = (vm_usage_mask & (1 << VM_USAGE_ASSERT_BIT)) != 0;
        let use_assert_range = (vm_usage_mask & (1 << VM_USAGE_ASSERT_RANGE)) != 0;

        if use_eq {
            len_alu += 2;
        }
        if use_divmod {
            len_alu += 2;
        }
        if use_assert {
            len_alu += 1;
        }
        if use_assert_bit {
            len_alu += 1;
        }
        if use_assert_range {
            // 32 booleanity + 1 equality
            len_alu += 32 + 1;
        }
        if use_mulwide {
            len_alu += 1;
        }
        if use_div128 {
            len_alu += 2;
        }

        ranges.push(("vm_alu", ofs, ofs + len_alu));
        ofs += len_alu;
    }

    // RAM
    if features.ram {
        let use_delta = (vm_usage_mask & (1 << VM_USAGE_RAM_DELTA_CLK)) != 0;
        // 2 gp + 1 last_write + 1 read==last
        // + 1 forbid + 1 same_bool + [bit-booleanities] + [eq] + 1 final GP eq
        let base = 6usize; // gp_uns, gp_sorted, last_write, read==last, forbid, same
        let bits = if use_delta {
            ram_delta_clk_bits.count_ones() as usize
        } else {
            0
        };

        let eq = if use_delta { 1 } else { 0 };
        let len = base + bits + eq + 1; // +1 final GP eq

        ranges.push(("ram", ofs, ofs + len));
        ofs += len;
    }

    // Merkle
    if features.merkle {
        let len = 7;
        ranges.push(("merkle", ofs, ofs + len));
        ofs += len;
    }

    // ROM
    if pub_inputs.program_commitment.iter().any(|b| *b != 0) {
        let len = 3 * POSEIDON_ROUNDS + 3 + 2;
        ranges.push(("rom", ofs, ofs + len));
    }

    ranges
}

// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin

//! Offline ROM accumulator computation for zk-lisp programs.
//!
//! This module computes a t=3 Poseidon-like accumulator over
//! virtual ROM map-rows derived directly from the compiled
//! program.

use crate::layout::Columns;
use crate::poseidon::{derive_rom_mds_cauchy_3x3, derive_rom_round_constants_3};
use crate::utils::{self, ROM_W_SEED_0, ROM_W_SEED_1};

use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;
use zk_lisp_compiler::Program;
use zk_lisp_compiler::builder::Op;

/// Compute the offline ROM
/// accumulator state for a program.
pub fn rom_acc_from_program(program: &Program) -> [BE; 3] {
    let cols = Columns::baseline();

    let rc3 = derive_rom_round_constants_3(&program.commitment, crate::layout::POSEIDON_ROUNDS);
    let mds3 = derive_rom_mds_cauchy_3x3(&program.commitment);

    let w_enc0 = utils::rom_weights_for_seed(ROM_W_SEED_0);
    let w_enc1 = utils::rom_weights_for_seed(ROM_W_SEED_1);

    let levels = program.ops.len();
    let total_levels = levels.next_power_of_two().max(1);

    let width = cols.width(0);
    let mut row = vec![BE::ZERO; width];

    let mut s0_prev = BE::ZERO;
    let mut s1_prev = BE::ZERO;
    let mut s2_prev = BE::ZERO;

    for lvl in 0..total_levels {
        // Clear virtual map-row
        for v in row.iter_mut() {
            *v = BE::ZERO;
        }

        if lvl < levels {
            let op = &program.ops[lvl];
            encode_map_row_for_op(&mut row, &cols, op);
        }

        // Compute encodings from virtual row
        let enc0 = utils::rom_linear_encode_from_slice(&row, &cols, &w_enc0);
        let enc1 = utils::rom_linear_encode_from_slice(&row, &cols, &w_enc1);

        // Poseidon-like t=3 permutation
        let mut s = [s0_prev, enc0, enc1];

        for rc_row in rc3.iter().take(crate::layout::POSEIDON_ROUNDS) {
            let s3 = [s[0] * s[0] * s[0], s[1] * s[1] * s[1], s[2] * s[2] * s[2]];

            let y0 = mds3[0][0] * s3[0] + mds3[0][1] * s3[1] + mds3[0][2] * s3[2] + rc_row[0];
            let y1 = mds3[1][0] * s3[0] + mds3[1][1] * s3[1] + mds3[1][2] * s3[2] + rc_row[1];
            let y2 = mds3[2][0] * s3[0] + mds3[2][1] * s3[1] + mds3[2][2] * s3[2] + rc_row[2];

            s = [y0, y1, y2];
        }

        s0_prev = s[0];
        s1_prev = s[1];
        s2_prev = s[2];
    }

    [s0_prev, s1_prev, s2_prev]
}

fn encode_map_row_for_op(row: &mut [BE], cols: &Columns, op: &Op) {
    use zk_lisp_compiler::builder::Op::*;

    // Helper to zero selectors
    // before setting.
    let clear_selectors = |row: &mut [BE], cols: &Columns| {
        for i in 0..crate::layout::NR {
            row[cols.sel_dst0_index(i)] = BE::ZERO;
            row[cols.sel_dst1_index(i)] = BE::ZERO;
            row[cols.sel_a_index(i)] = BE::ZERO;
            row[cols.sel_b_index(i)] = BE::ZERO;
            row[cols.sel_c_index(i)] = BE::ZERO;
        }
    };

    clear_selectors(row, cols);

    // Clear op bits
    for &c in [
        cols.op_const,
        cols.op_mov,
        cols.op_add,
        cols.op_sub,
        cols.op_mul,
        cols.op_neg,
        cols.op_eq,
        cols.op_select,
        cols.op_sponge,
        cols.op_assert,
        cols.op_assert_bit,
        cols.op_assert_range,
        cols.op_divmod,
        cols.op_div128,
        cols.op_mulwide,
        cols.op_load,
        cols.op_store,
    ]
    .iter()
    {
        row[c] = BE::ZERO;
    }

    match *op {
        Const { dst, imm } => {
            row[cols.op_const] = BE::ONE;
            row[cols.sel_dst0_index(dst as usize)] = BE::ONE;
            row[cols.imm] = BE::from(imm);
        }
        Mov { dst, src } => {
            row[cols.op_mov] = BE::ONE;
            row[cols.sel_dst0_index(dst as usize)] = BE::ONE;
            row[cols.sel_a_index(src as usize)] = BE::ONE;
        }
        Add { dst, a, b } => {
            row[cols.op_add] = BE::ONE;
            row[cols.sel_dst0_index(dst as usize)] = BE::ONE;
            row[cols.sel_a_index(a as usize)] = BE::ONE;
            row[cols.sel_b_index(b as usize)] = BE::ONE;
        }
        Sub { dst, a, b } => {
            row[cols.op_sub] = BE::ONE;
            row[cols.sel_dst0_index(dst as usize)] = BE::ONE;
            row[cols.sel_a_index(a as usize)] = BE::ONE;
            row[cols.sel_b_index(b as usize)] = BE::ONE;
        }
        Mul { dst, a, b } => {
            row[cols.op_mul] = BE::ONE;
            row[cols.sel_dst0_index(dst as usize)] = BE::ONE;
            row[cols.sel_a_index(a as usize)] = BE::ONE;
            row[cols.sel_b_index(b as usize)] = BE::ONE;
        }
        Neg { dst, a } => {
            row[cols.op_neg] = BE::ONE;
            row[cols.sel_dst0_index(dst as usize)] = BE::ONE;
            row[cols.sel_a_index(a as usize)] = BE::ONE;
        }
        Eq { dst, a, b } => {
            row[cols.op_eq] = BE::ONE;
            row[cols.sel_dst0_index(dst as usize)] = BE::ONE;
            row[cols.sel_a_index(a as usize)] = BE::ONE;
            row[cols.sel_b_index(b as usize)] = BE::ONE;

            // eq_inv is a witness depending on runtime
            // registers; ROM encoding ignores it.
        }
        Select { dst, c, a, b } => {
            row[cols.op_select] = BE::ONE;
            row[cols.sel_dst0_index(dst as usize)] = BE::ONE;
            row[cols.sel_c_index(c as usize)] = BE::ONE;
            row[cols.sel_a_index(a as usize)] = BE::ONE;
            row[cols.sel_b_index(b as usize)] = BE::ONE;
        }
        Assert { dst, c } => {
            row[cols.op_assert] = BE::ONE;
            row[cols.sel_dst0_index(dst as usize)] = BE::ONE;
            row[cols.sel_c_index(c as usize)] = BE::ONE;
        }
        AssertBit { dst, r } => {
            row[cols.op_assert_bit] = BE::ONE;
            row[cols.sel_dst0_index(dst as usize)] = BE::ONE;
            row[cols.sel_c_index(r as usize)] = BE::ONE;
        }
        AssertRange { dst, r, .. } => {
            // 32-bit range:
            // stage=1 (imm=1), mode64=0 (eq_inv=0)
            row[cols.op_assert_range] = BE::ONE;
            row[cols.sel_dst0_index(dst as usize)] = BE::ONE;
            row[cols.sel_c_index(r as usize)] = BE::ONE;
            row[cols.imm] = BE::ONE;
        }
        AssertRangeLo { dst, r } => {
            // Stage 0 of 64-bit:
            // stage=0 (imm=0), mode64=1 (eq_inv=1)
            row[cols.op_assert_range] = BE::ONE;
            row[cols.sel_dst0_index(dst as usize)] = BE::ONE;
            row[cols.sel_c_index(r as usize)] = BE::ONE;
            row[cols.imm] = BE::ZERO;
            row[cols.eq_inv] = BE::ONE;
        }
        AssertRangeHi { dst, r } => {
            // Stage 1 of 64-bit:
            // stage=1 (imm=1), mode64=1 (eq_inv=1)
            row[cols.op_assert_range] = BE::ONE;
            row[cols.sel_dst0_index(dst as usize)] = BE::ONE;
            row[cols.sel_c_index(r as usize)] = BE::ONE;
            row[cols.imm] = BE::ONE;
            row[cols.eq_inv] = BE::ONE;
        }
        DivMod { dst_q, dst_r, a, b } => {
            row[cols.op_divmod] = BE::ONE;
            row[cols.sel_dst0_index(dst_q as usize)] = BE::ONE;
            row[cols.sel_dst1_index(dst_r as usize)] = BE::ONE;
            row[cols.sel_a_index(a as usize)] = BE::ONE;
            row[cols.sel_b_index(b as usize)] = BE::ONE;
        }
        DivMod128 {
            a_hi,
            a_lo: _,
            b,
            dst_q,
            dst_r,
        } => {
            row[cols.op_div128] = BE::ONE;
            row[cols.sel_dst0_index(dst_q as usize)] = BE::ONE;
            row[cols.sel_dst1_index(dst_r as usize)] = BE::ONE;
            row[cols.sel_a_index(a_hi as usize)] = BE::ONE;
            row[cols.sel_b_index(b as usize)] = BE::ONE;

            // imm carries low limb at runtime;
            // ROM encoding ignores it.
        }
        MulWide {
            dst_hi,
            dst_lo,
            a,
            b,
        } => {
            row[cols.op_mulwide] = BE::ONE;
            row[cols.sel_dst0_index(dst_lo as usize)] = BE::ONE;
            row[cols.sel_dst1_index(dst_hi as usize)] = BE::ONE;
            row[cols.sel_a_index(a as usize)] = BE::ONE;
            row[cols.sel_b_index(b as usize)] = BE::ONE;
        }
        Load { dst, addr } => {
            row[cols.op_load] = BE::ONE;
            row[cols.sel_dst0_index(dst as usize)] = BE::ONE;
            row[cols.sel_a_index(addr as usize)] = BE::ONE;
        }
        Store { addr, src } => {
            row[cols.op_store] = BE::ONE;
            row[cols.sel_a_index(addr as usize)] = BE::ONE;
            row[cols.sel_b_index(src as usize)] = BE::ONE;
        }
        SAbsorbN { .. } => {
            row[cols.op_sponge] = BE::ONE;
        }
        SSqueeze { .. } => {
            row[cols.op_sponge] = BE::ONE;
        }
        MerkleStepFirst { .. } | MerkleStep { .. } | MerkleStepLast { .. } | End => {
            // Merkle and End ops do not set
            // ALU opcode bits or selectors
            // on map rows; ROM sees zero row.
        }
    }
}

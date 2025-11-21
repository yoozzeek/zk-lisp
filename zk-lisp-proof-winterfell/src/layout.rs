// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Column layout for the unified zk-lisp execution trace.
//!
//! [`Columns`] defines indices for all VM, RAM, Merkle,
//! Poseidon and ROM columns, keeping AIR and trace builder
//! code in sync over a single baseline layout.

use winterfell::math::fields::f128::BaseElement as BE;

/// Conservative number of full rounds for t=12
/// under full S-box (all lanes cubic each round).
/// This matches current t=4 rounds (27) for safety;
/// can be reduced after separate security review.
pub const POSEIDON_ROUNDS: usize = 27;
pub const STEPS_PER_LEVEL_P2: usize = 32;

pub const NR: usize = 8;

/// Number of index bits for SPONGE
/// lane register selection (NR=8 -> 3 bits)
pub const SPONGE_IDX_BITS: usize = 3;

#[derive(Clone, Debug)]
pub struct Columns {
    // Poseidon lanes (t=12: r=10, c=2)
    pub lane_l: usize,      // lane 0
    pub lane_r: usize,      // lane 1
    pub lane_c0: usize,     // lane 10
    pub lane_c1: usize,     // lane 11
    pub lanes_start: usize, // start index of lane[0..12)

    // Schedule gates
    pub g_map: usize,
    pub g_final: usize,
    // start index for g_r[0..POSEIDON_ROUNDS)
    pub g_r_start: usize,

    // Generic activity mask for padding rows
    pub mask: usize,

    // VM register file r0..r7
    pub r_start: usize,

    // Op decode (one-hot for ALU ops)
    pub op_const: usize,
    pub op_mov: usize,
    pub op_add: usize,
    pub op_sub: usize,
    pub op_mul: usize,
    pub op_neg: usize,
    pub op_eq: usize,
    pub op_select: usize,
    pub op_sponge: usize,
    pub op_assert: usize,
    pub op_assert_bit: usize,
    pub op_assert_range: usize,
    pub op_divmod: usize,
    pub op_div128: usize,
    pub op_mulwide: usize,
    pub op_load: usize,
    pub op_store: usize,

    // Operand selectors
    // one-hot per role (8 each).
    pub sel_dst0_start: usize,
    pub sel_a_start: usize,
    pub sel_b_start: usize,
    pub sel_c_start: usize,
    pub sel_dst1_start: usize,

    // Packed sponge lane selectors:
    // For each lane i in 0..10,
    pub sel_s_bits_start: usize,
    pub sel_s_active_start: usize,

    // Immediate for Const
    pub imm: usize,

    // Aux for Eq
    pub eq_inv: usize,

    // RAM columns
    pub ram_sorted: usize,
    pub ram_s_addr: usize,
    pub ram_s_clk: usize,
    pub ram_s_val: usize,
    pub ram_s_is_write: usize,
    pub ram_s_last_write: usize,
    pub ram_gp_unsorted: usize,
    pub ram_gp_sorted: usize,

    // Merkle columns
    pub merkle_g: usize,
    pub merkle_dir: usize,
    pub merkle_sib: usize,
    pub merkle_acc: usize,
    pub merkle_first: usize,
    pub merkle_last: usize,
    pub merkle_leaf: usize,

    // PI columns
    pub pi_prog: usize,

    // PC/ROM tie-in
    pub pc: usize,

    // Rom columns
    pub rom_op_start: usize,

    // Poseidon per-level activity gate
    pub pose_active: usize,

    // Gadget witnesses:
    // reusable 32-bit pool
    pub gadget_b_start: usize,

    width: usize,
}

impl Columns {
    pub fn baseline() -> Self {
        let lanes_start = 0;
        let lane_l = lanes_start;
        let lane_r = lanes_start + 1;
        let lane_c0 = lanes_start + 10;
        let lane_c1 = lanes_start + 11;

        // 12 lanes occupy [0..12)
        let g_map = lanes_start + 12;
        let g_final = g_map + 1;
        let g_r_start = g_final + 1;
        let mask = g_r_start + POSEIDON_ROUNDS;

        let r_start = mask + 1; // [r0..r7]
        let op_const = r_start + NR; // op bits begin
        let op_mov = op_const + 1;
        let op_add = op_mov + 1;
        let op_sub = op_add + 1;
        let op_mul = op_sub + 1;
        let op_neg = op_mul + 1;
        let op_eq = op_neg + 1;
        let op_select = op_eq + 1;
        let op_sponge = op_select + 1;
        let op_assert = op_sponge + 1;
        let op_assert_bit = op_assert + 1;
        let op_assert_range = op_assert_bit + 1;
        let op_divmod = op_assert_range + 1;
        let op_div128 = op_divmod + 1;
        let op_mulwide = op_div128 + 1;
        let op_load = op_mulwide + 1;
        let op_store = op_load + 1;

        let sel_dst0_start = op_store + 1; // 8 cols
        let sel_a_start = sel_dst0_start + NR; // 8 cols
        let sel_b_start = sel_a_start + NR; // 8 cols
        let sel_c_start = sel_b_start + NR; // 8 cols
        let sel_dst1_start = sel_c_start + NR; // 8 cols

        // Sponge lane selectors
        // bits: 10 * SPONGE_IDX_BITS;
        let sel_s_bits_start = sel_dst1_start + NR;
        let sel_s_active_start = sel_s_bits_start + (10 * SPONGE_IDX_BITS);

        // Immediate and aux
        let imm = sel_s_active_start + 10; // after active flags
        let eq_inv = imm + 1; // 1 col

        // RAM columns
        let ram_sorted = eq_inv + 1;
        let ram_s_addr = ram_sorted + 1;
        let ram_s_clk = ram_s_addr + 1;
        let ram_s_val = ram_s_clk + 1;
        let ram_s_is_write = ram_s_val + 1;
        let ram_s_last_write = ram_s_is_write + 1;
        let ram_gp_unsorted = ram_s_last_write + 1;
        let ram_gp_sorted = ram_gp_unsorted + 1;

        // Merkle block columns
        let merkle_g = ram_gp_sorted + 1;
        let merkle_dir = merkle_g + 1;
        let merkle_sib = merkle_dir + 1;
        let merkle_acc = merkle_sib + 1;
        let merkle_first = merkle_acc + 1;
        let merkle_last = merkle_first + 1;
        let merkle_leaf = merkle_last + 1;

        // PI columns
        let pi_prog = merkle_leaf + 1;

        // PC column
        let pc = pi_prog + 1;

        // ROM op mirror (17 columns)
        let rom_op_start = pc + 1;

        // Append pose_active followed
        // by gadget witness columns
        let pose_active = rom_op_start + 17;

        // Gadget: 32 reusable bit witnesses
        let gadget_b_start = pose_active + 1;

        // ROM accumulator t=3 lanes after gadget bits
        let rom_s_start = gadget_b_start + 32;

        let width = rom_s_start + 3;

        Self {
            lane_l,
            lane_r,
            lane_c0,
            lane_c1,
            lanes_start,
            g_map,
            g_final,
            g_r_start,
            mask,
            r_start,
            op_const,
            op_mov,
            op_add,
            op_sub,
            op_mul,
            op_neg,
            op_eq,
            op_select,
            op_sponge,
            op_assert,
            op_assert_bit,
            op_assert_range,
            op_divmod,
            op_div128,
            op_mulwide,
            op_load,
            op_store,
            sel_dst0_start,
            sel_a_start,
            sel_b_start,
            sel_c_start,
            sel_dst1_start,
            sel_s_bits_start,
            sel_s_active_start,
            imm,
            eq_inv,
            ram_sorted,
            ram_s_addr,
            ram_s_clk,
            ram_s_val,
            ram_s_is_write,
            ram_s_last_write,
            ram_gp_unsorted,
            ram_gp_sorted,
            merkle_g,
            merkle_dir,
            merkle_sib,
            merkle_acc,
            merkle_first,
            merkle_last,
            merkle_leaf,
            pi_prog,
            pc,
            rom_op_start,
            pose_active,
            gadget_b_start,
            width,
        }
    }

    pub fn g_r_index(&self, j: usize) -> usize {
        debug_assert!(j < POSEIDON_ROUNDS);

        self.g_r_start + j
    }

    pub fn r_index(&self, i: usize) -> usize {
        debug_assert!(i < NR);

        self.r_start + i
    }

    pub fn sel_dst0_index(&self, i: usize) -> usize {
        debug_assert!(i < NR);

        self.sel_dst0_start + i
    }

    pub fn sel_dst1_index(&self, i: usize) -> usize {
        debug_assert!(i < NR);

        self.sel_dst1_start + i
    }

    pub fn sel_a_index(&self, i: usize) -> usize {
        debug_assert!(i < NR);

        self.sel_a_start + i
    }

    pub fn sel_b_index(&self, i: usize) -> usize {
        debug_assert!(i < NR);

        self.sel_b_start + i
    }

    pub fn sel_c_index(&self, i: usize) -> usize {
        debug_assert!(i < NR);

        self.sel_c_start + i
    }

    pub fn sel_s_b_index(&self, lane: usize, bit: usize) -> usize {
        debug_assert!(lane < 10);
        debug_assert!(bit < SPONGE_IDX_BITS);

        self.sel_s_bits_start + lane * SPONGE_IDX_BITS + bit
    }

    pub fn sel_s_active_index(&self, lane: usize) -> usize {
        debug_assert!(lane < 10);

        self.sel_s_active_start + lane
    }

    pub fn gadget_b_index(&self, i: usize) -> usize {
        debug_assert!(i < 32);

        self.gadget_b_start + i
    }

    pub fn lane_index(&self, i: usize) -> usize {
        debug_assert!(i < 12);

        self.lanes_start + i
    }

    pub fn rom_op_index(&self, i: usize) -> usize {
        debug_assert!(i < 17);

        self.rom_op_start + i
    }

    pub fn rom_s_index(&self, i: usize) -> usize {
        debug_assert!(i < 3);

        self.gadget_b_start + 32 + i
    }

    pub fn width(&self, _feature_mask: u64) -> usize {
        self.width
    }
}

#[inline]
pub fn fe_u32(v: u32) -> BE {
    BE::from(v as u64)
}

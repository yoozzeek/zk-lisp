// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use winterfell::math::fields::f128::BaseElement as BE;

pub const POSEIDON_ROUNDS: usize = 27;
pub const STEPS_PER_LEVEL_P2: usize = 32;

pub const NR: usize = 8;

#[derive(Clone, Debug)]
pub struct Columns {
    // Poseidon lanes
    pub lane_l: usize,
    pub lane_r: usize,
    pub lane_c0: usize,
    pub lane_c1: usize,

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
    pub op_hash2: usize,
    pub op_assert: usize,

    // Operand selectors
    // one-hot per role (8 each).
    pub sel_dst_start: usize,
    pub sel_a_start: usize,
    pub sel_b_start: usize,
    pub sel_c_start: usize,

    // Immediate for Const
    pub imm: usize,

    // Aux for Eq
    pub eq_inv: usize,

    // KV columns
    pub kv_g_map: usize,
    pub kv_g_final: usize,
    pub kv_dir: usize,
    pub kv_sib: usize,
    pub kv_acc: usize,
    pub kv_version: usize,
    pub kv_prev_acc: usize,

    // PI columns
    pub pi_prog: usize,

    // Poseidon per-level activity gate
    pub pose_active: usize,

    width: usize,
}

impl Columns {
    pub fn baseline() -> Self {
        let lane_l = 0;
        let lane_r = 1;
        let lane_c0 = 2;
        let lane_c1 = 3;

        let g_map = 4;
        let g_final = 5;
        let g_r_start = 6;
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
        let op_hash2 = op_select + 1;
        let op_assert = op_hash2 + 1;

        let sel_dst_start = op_assert + 1; // 8 cols
        let sel_a_start = sel_dst_start + NR; // 8 cols
        let sel_b_start = sel_a_start + NR; // 8 cols
        let sel_c_start = sel_b_start + NR; // 8 cols

        let imm = sel_c_start + NR; // 1 col
        let eq_inv = imm + 1; // 1 col

        // KV columns
        let kv_g_map = eq_inv + 1;
        let kv_g_final = kv_g_map + 1;
        let kv_dir = kv_g_final + 1;
        let kv_sib = kv_dir + 1;
        let kv_acc = kv_sib + 1;
        let kv_version = kv_acc + 1;

        // PI columns (keep original index)
        let pi_prog = kv_version + 1;

        // Extra KV column placed after PI
        // to avoid shifting existing indices.
        let kv_prev_acc = pi_prog + 1;

        // Append pose_active at the very end
        let pose_active = kv_prev_acc + 1;

        let width = pose_active + 1;

        Self {
            lane_l,
            lane_r,
            lane_c0,
            lane_c1,
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
            op_hash2,
            op_assert,
            sel_dst_start,
            sel_a_start,
            sel_b_start,
            sel_c_start,
            imm,
            eq_inv,
            kv_g_map,
            kv_g_final,
            kv_dir,
            kv_sib,
            kv_acc,
            kv_version,
            kv_prev_acc,
            pi_prog,
            pose_active,
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

    pub fn sel_dst_index(&self, i: usize) -> usize {
        debug_assert!(i < NR);
        self.sel_dst_start + i
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

    pub fn width(&self, _feature_mask: u64) -> usize {
        self.width
    }
}

#[inline]
pub fn fe_u32(v: u32) -> BE {
    BE::from(v as u64)
}

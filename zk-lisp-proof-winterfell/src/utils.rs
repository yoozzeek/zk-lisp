// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

//! Shared low-level helpers for the Winterfell backend.
//!
//! Includes cached field constants, ROM linear encoders and
//! trace utilities such as [`vm_output_from_trace`] used by
//! both AIR and trace construction code.

use crate::layout::{self, NR};
use crate::schedule;

use std::sync::OnceLock;
use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::{Trace, TraceTable};

pub const ROM_W_SEED_0: u32 = 17;
pub const ROM_W_SEED_1: u32 = 1037;

// Cached 2^64 in BaseElement
static POW2_64_BE: OnceLock<BE> = OnceLock::new();

#[inline]
pub fn pow2_64() -> BE {
    *POW2_64_BE.get_or_init(|| {
        let mut acc = BE::ONE;
        let two = BE::from(2u64);

        for _ in 0..64 {
            acc *= two;
        }

        acc
    })
}

// ROM helpers:
// - weights_for_seed(seed): [g^(seed+1), ..., g^(seed+59)] for g=3
// - linear encoders from a row slice or a trace row
#[inline]
pub fn rom_weights_for_seed(seed: u32) -> [BE; 59] {
    let g = BE::from(3u64);

    // fast exp to g^seed
    let mut acc = BE::ONE;
    let mut base = g;
    let mut e = seed as u64;

    while e > 0 {
        if (e & 1) == 1 {
            acc *= base;
        }

        base *= base;
        e >>= 1;
    }

    // fill [g^(seed+1) .. g^(seed+59)]
    let mut out = [BE::ZERO; 59];
    let mut cur = acc * g;

    for item in out.iter_mut() {
        *item = cur;
        cur *= g;
    }

    out
}

#[inline]
pub fn rom_linear_encode_from_slice<E: FieldElement<BaseField = BE> + From<BE>>(
    cur: &[E],
    cols: &layout::Columns,
    weights: &[BE; 59],
) -> E {
    let mut k = 0usize;
    let mut sum = E::ZERO;

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
        sum += cur[c] * E::from(weights[k]);
        k += 1;
    }

    for i in 0..NR {
        sum += cur[cols.sel_dst0_index(i)] * E::from(weights[k]);
        k += 1;
    }

    for i in 0..NR {
        sum += cur[cols.sel_a_index(i)] * E::from(weights[k]);
        k += 1;
    }

    for i in 0..NR {
        sum += cur[cols.sel_b_index(i)] * E::from(weights[k]);
        k += 1;
    }

    for i in 0..NR {
        sum += cur[cols.sel_c_index(i)] * E::from(weights[k]);
        k += 1;
    }

    for i in 0..NR {
        sum += cur[cols.sel_dst1_index(i)] * E::from(weights[k]);
        k += 1;
    }

    sum += cur[cols.imm] * E::from(weights[k]);
    k += 1;

    sum += cur[cols.eq_inv] * E::from(weights[k]);

    sum
}

#[inline]
pub fn rom_linear_encode_from_trace(
    trace: &TraceTable<BE>,
    row: usize,
    cols: &layout::Columns,
    weights: &[BE; 59],
) -> BE {
    let mut k = 0usize;
    let mut sum = BE::ZERO;

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
        sum += trace.get(c, row) * weights[k];
        k += 1;
    }

    for i in 0..NR {
        sum += trace.get(cols.sel_dst0_index(i), row) * weights[k];
        k += 1;
    }

    for i in 0..NR {
        sum += trace.get(cols.sel_a_index(i), row) * weights[k];
        k += 1;
    }

    for i in 0..NR {
        sum += trace.get(cols.sel_b_index(i), row) * weights[k];
        k += 1;
    }

    for i in 0..NR {
        sum += trace.get(cols.sel_c_index(i), row) * weights[k];
        k += 1;
    }

    for i in 0..NR {
        sum += trace.get(cols.sel_dst1_index(i), row) * weights[k];
        k += 1;
    }

    sum += trace.get(cols.imm, row) * weights[k];
    k += 1;

    sum += trace.get(cols.eq_inv, row) * weights[k];

    sum
}

#[inline]
pub fn vm_output_from_trace(trace: &TraceTable<BE>) -> (u8, u32) {
    let cols = layout::Columns::baseline();
    let steps = layout::STEPS_PER_LEVEL_P2;
    let lvls = trace.length() / steps;

    // Scan levels backwards and pick
    // the most recent write at final row.
    for lvl in (0..lvls).rev() {
        let base = lvl * steps;
        let row_fin = base + schedule::pos_final();

        for i in 0..NR {
            if trace.get(cols.sel_dst0_index(i), row_fin) == BE::ONE {
                return (i as u8, (row_fin + 1) as u32);
            }
        }
    }

    // Fallback: no write observed;
    // default to (r0, first row after final of level 0)
    let row_fin0 = schedule::pos_final();
    (0u8, (row_fin0 + 1) as u32)
}

pub fn be_from_le8(bytes32: &[u8; 32]) -> BE {
    // fold first 16 bytes (LE) into
    // a field element: lo + hi * 2^64.
    let mut lo = [0u8; 8];
    let mut hi = [0u8; 8];
    lo.copy_from_slice(&bytes32[0..8]);
    hi.copy_from_slice(&bytes32[8..16]);

    BE::from(u64::from_le_bytes(lo)) + BE::from(u64::from_le_bytes(hi)) * pow2_64()
}

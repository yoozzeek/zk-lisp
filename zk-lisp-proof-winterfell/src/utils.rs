// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Shared low-level helpers for the Winterfell backend.
//!
//! Includes cached field constants, ROM linear encoders and
//! trace utilities such as [`vm_output_from_trace`] used by
//! both AIR and trace construction code.

use crate::layout::{self, NR};
use crate::schedule;

use blake3::Hasher;
use std::sync::OnceLock;
use winterfell::math::FieldElement;
use winterfell::math::StarkField;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::{Trace, TraceTable};
use zk_lisp_proof::pi::VmArg;

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

/// Encode a 128-bit unsigned integer into the base
/// field by interpreting it as a binary polynomial
/// over F and reducing modulo the field modulus.
///
/// This works for all `u128` values without needing
/// to know the modulus explicitly; the mapping is
/// `n -> sum_i bit_i * 2^i (mod p)`.
#[inline]
pub fn be_from_u128(n: u128) -> BE {
    let mut x = n;
    let mut cur = BE::ONE;
    let mut acc = BE::ZERO;

    while x > 0 {
        if (x & 1) != 0 {
            acc += cur;
        }

        // multiply by 2 in the field
        cur += cur;
        x >>= 1;
    }

    acc
}

/// Encode 16 bytes (little-endian) into a single
/// base-field element by first interpreting them
/// as a `u128` and then calling [`be_from_u128`].
#[inline]
pub fn be_from_le_bytes16(b16: &[u8; 16]) -> BE {
    let n = u128::from_le_bytes(*b16);
    be_from_u128(n)
}

/// Expand a typed VM argument into one or more
/// base-field elements used for public-input
/// encoding or VM register seeding.
///
/// Layout:
/// - `VmArg::U64`   -> 1 element (value as u64)
/// - `VmArg::U128`  -> 1 element (binary embedding)
/// - `VmArg::Bytes32` -> 2 elements (lo,hi 16-byte
///   chunks, each embedded via [`be_from_le_bytes16`]).
#[inline]
pub fn encode_vmarg_to_elements(arg: &VmArg, out: &mut Vec<BE>) {
    match arg {
        VmArg::U64(x) => {
            out.push(BE::from(*x));
        }
        VmArg::U128(x) => {
            out.push(be_from_u128(*x));
        }
        VmArg::Bytes32(bytes) => {
            let mut lo = [0u8; 16];
            let mut hi = [0u8; 16];
            lo.copy_from_slice(&bytes[0..16]);
            hi.copy_from_slice(&bytes[16..32]);

            out.push(be_from_le_bytes16(&lo));
            out.push(be_from_le_bytes16(&hi));
        }
    }
}

/// Flatten a slice of VmArgs into a sequence of
/// base-field elements in argument order using
/// [`encode_vmarg_to_elements`].
#[inline]
pub fn encode_main_args_to_slots(args: &[VmArg]) -> Vec<BE> {
    let mut out = Vec::new();
    for arg in args {
        encode_vmarg_to_elements(arg, &mut out);
    }

    out
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

    // Opcode one-hots
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

    // Selector columns (dst0, a, b, c, dst1)
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

    debug_assert!(k <= weights.len());

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

    // Opcode one-hots
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

    // Selector columns
    // (dst0, a, b, c, dst1)
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

    debug_assert!(k <= weights.len());

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

/// Compute a 32-byte hash of the VM state at the given
/// trace row. The state snapshot currently includes only
/// the full register file r0..r{NR-1}, all encoded as
/// canonical little-endian u128 limbs under a fixed
/// Blake3 domain.
pub fn vm_state_hash_row(trace: &TraceTable<BE>, row: usize) -> [u8; 32] {
    let cols = layout::Columns::baseline();
    let n = trace.length();
    if n == 0 {
        return [0u8; 32];
    }

    let row = row.min(n.saturating_sub(1));

    let mut h = Hasher::new();
    h.update(b"zkl/vm/state-v1");

    // Register file r0..r{NR-1}
    for i in 0..NR {
        let r = trace.get(cols.r_index(i), row);
        h.update(&r.as_int().to_le_bytes());
    }

    let digest = h.finalize();

    let mut out = [0u8; 32];
    out.copy_from_slice(digest.as_bytes());

    out
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

/// Fold a 32-byte value into a single base-field element.
///
/// This is a deterministic, injective-enough embedding
/// for digest-style use: we interpret the low and high
/// 16-byte halves as independent 128-bit values mapped
/// via [`be_from_le_bytes16`] and then combine them
/// linearly inside the field. This is not intended as
/// a cryptographic hash by itself; callers must wrap it
/// inside a proper domain-separated hash (e.g. Poseidon).
pub fn fold_bytes32_to_fe(bytes32: &[u8; 32]) -> BE {
    let mut lo16 = [0u8; 16];
    let mut hi16 = [0u8; 16];
    lo16.copy_from_slice(&bytes32[0..16]);
    hi16.copy_from_slice(&bytes32[16..32]);

    let a = be_from_le_bytes16(&lo16);
    let b = be_from_le_bytes16(&hi16);

    // Use 2^64 as a mixing factor between halves;
    // this is a simple linear combination in the
    // field which keeps the mapping deterministic
    // and cheap.
    a + b * pow2_64()
}

/// Fold a base-field element into 32 bytes.
///
/// We encode the internal 128-bit integer representation
/// into the low 16 bytes in little-endian form and leave
/// the upper half zeroed. This is sufficient for digest
/// purposes when combined with a domain-separated hash.
pub fn fe_to_bytes_fold(x: BE) -> [u8; 32] {
    let mut out = [0u8; 32];
    let le16 = x.as_int().to_le_bytes();
    out[0..16].copy_from_slice(&le16);

    out
}

/// Inverse of `fe_to_bytes_fold`: interpret low 16 bytes (LE)
/// as a base-field element and ignore the upper half.
#[inline]
pub fn fe_from_bytes_fold(bytes32: &[u8; 32]) -> BE {
    let mut lo16 = [0u8; 16];
    lo16.copy_from_slice(&bytes32[0..16]);
    be_from_le_bytes16(&lo16)
}

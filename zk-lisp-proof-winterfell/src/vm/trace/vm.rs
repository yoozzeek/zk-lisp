// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! VM execution trace construction for zk-lisp programs.
//!
//! Simulates the VM over compiled ops, populates register
//! file, opcode/selector columns, RAM events and Poseidon
//! activity flags used by downstream trace modules.

use crate::poseidon::get_poseidon_suite;
use crate::utils;
use crate::vm::layout::NR;
use crate::vm::trace::{
    TraceBuilderContext, TraceModule, poseidon::apply_level_absorb, ram::RamEvent, set_sel,
};

use crate::vm::schedule;
use arrayvec::ArrayVec;
use std::collections::BTreeMap;
use winterfell::TraceTable;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::math::{FieldElement, StarkField};
use zk_lisp_compiler::builder;
use zk_lisp_compiler::builder::Op;
use zk_lisp_proof::error::{self, Error};
use zk_lisp_proof::pi::VmArg;

pub(crate) struct VmTraceBuilder<'a> {
    ram_events: &'a mut Vec<RamEvent>,
    mem: &'a mut BTreeMap<u128, BE>,
    secret_args: &'a [VmArg],
    main_args: &'a [VmArg],
}

impl<'a> VmTraceBuilder<'a> {
    pub fn new(
        mem: &'a mut BTreeMap<u128, BE>,
        ram_events: &'a mut Vec<RamEvent>,
        secret_args: &'a [VmArg],
        main_args: &'a [VmArg],
    ) -> Self {
        Self {
            mem,
            ram_events,
            secret_args,
            main_args,
        }
    }
}

impl<'a> TraceModule for VmTraceBuilder<'a> {
    fn fill_table(
        &mut self,
        ctx: &TraceBuilderContext,
        trace: &mut TraceTable<BE>,
    ) -> error::Result<()> {
        let t_all = std::time::Instant::now();
        let mut regs = [BE::ZERO; NR];

        // Reserve tail of register
        // file for runtime public
        // main_args, flattened into slots.
        let main_slots = utils::encode_main_args_to_slots(self.main_args);
        let slots_len = main_slots.len();
        if slots_len > NR {
            return Err(Error::InvalidInput(
                "too many main_args for VM register file",
            ));
        }

        let tail_start = NR - slots_len;

        // Seed initial register file from
        // secret VM arguments when present.
        for (i, arg) in self.secret_args.iter().enumerate() {
            if i >= tail_start {
                break;
            }

            let val_u64 = match arg {
                VmArg::U64(v) => *v,
                _ => {
                    return Err(Error::InvalidInput(
                        "non-u64 secret arg not yet supported for VM registers",
                    ));
                }
            };

            regs[i] = BE::from(val_u64);
        }

        // Seed reserved tail registers from
        // runtime public main_args slots.
        for (j, val) in main_slots.iter().enumerate() {
            let idx = tail_start + j;
            regs[idx] = *val;
        }

        // Buffer absorbed registers across
        // levels until SSqueeze up to 10.
        let mut pending_regs: ArrayVec<u8, 10> = ArrayVec::new();

        let commitment = &ctx.prog.commitment;
        let total_lvls = ctx.prog.ops.len();

        tracing::debug!(
            target="trace.vm",
            levels=%total_lvls,
            "vm fill start",
        );

        for (lvl, op) in ctx.prog.ops.iter().enumerate() {
            // snapshot current regs and
            // compute next_regs for writes at final.
            let mut next_regs = regs;

            if lvl == 0 {
                // bind program commitment at first map row
                let row0_map = schedule::pos_map();
                let pc = utils::be_from_le8(commitment);
                trace.set(ctx.cols.pi_prog, row0_map, pc);
            }

            let base = lvl * ctx.steps;
            let row_map = base + schedule::pos_map();
            let row_final = base + schedule::pos_final();

            // set Poseidon domain tags
            // at map row for all levels
            let suite = get_poseidon_suite(commitment);
            trace.set(ctx.cols.lane_c0, row_map, suite.dom[0]);
            trace.set(ctx.cols.lane_c1, row_map, suite.dom[1]);

            // PC and ROM one-hot mirror at map row
            trace.set(ctx.cols.pc, row_map, BE::from(lvl as u64));

            let rom = op_to_one_hot(op);
            for (k, &bit) in rom.iter().enumerate() {
                trace.set(ctx.cols.rom_op_index(k), row_map, bit);
            }

            // carry register file into
            // the new level at map row.
            for (i, val) in regs.iter().enumerate().take(NR) {
                trace.set(ctx.cols.r_index(i), row_map, *val);
            }

            // zero decode/selectors for this map row
            for i in 0..NR {
                trace.set(ctx.cols.sel_dst0_index(i), row_map, BE::ZERO);
                trace.set(ctx.cols.sel_dst1_index(i), row_map, BE::ZERO);
                trace.set(ctx.cols.sel_a_index(i), row_map, BE::ZERO);
                trace.set(ctx.cols.sel_b_index(i), row_map, BE::ZERO);
                trace.set(ctx.cols.sel_c_index(i), row_map, BE::ZERO);
            }

            trace.set(ctx.cols.imm, row_map, BE::ZERO);
            trace.set(ctx.cols.eq_inv, row_map, BE::ZERO);

            // clear op bits
            let ops = [
                ctx.cols.op_const,
                ctx.cols.op_mov,
                ctx.cols.op_add,
                ctx.cols.op_sub,
                ctx.cols.op_mul,
                ctx.cols.op_neg,
                ctx.cols.op_eq,
                ctx.cols.op_select,
                ctx.cols.op_sponge,
                ctx.cols.op_assert,
                ctx.cols.op_assert_bit,
                ctx.cols.op_assert_range,
                ctx.cols.op_divmod,
                ctx.cols.op_div128,
                ctx.cols.op_mulwide,
                ctx.cols.op_load,
                ctx.cols.op_store,
            ];

            for &c in &ops {
                trace.set(c, row_map, BE::ZERO);
            }

            // Track per-level poseidon
            // activity (sponge/merkle only)
            let mut pose_active = BE::ZERO;

            match *op {
                // ALU: write immediate to dst at final;
                // zero/clear decoders, set op bit
                // and dst selector on map.
                Op::Const { dst, imm } => {
                    trace.set(ctx.cols.op_const, row_map, BE::ONE);
                    set_sel(trace, row_map, ctx.cols.sel_dst0_start, dst);
                    trace.set(ctx.cols.imm, row_map, BE::from(imm));

                    // latch to final
                    trace.set(ctx.cols.op_const, row_final, BE::ONE);
                    set_sel(trace, row_final, ctx.cols.sel_dst0_start, dst);
                    trace.set(ctx.cols.imm, row_final, BE::from(imm));

                    next_regs[dst as usize] = BE::from(imm);
                }
                // ALU: dst = src at final;
                // selector "a" points to src
                Op::Mov { dst, src } => {
                    trace.set(ctx.cols.op_mov, row_map, BE::ONE);
                    set_sel(trace, row_map, ctx.cols.sel_dst0_start, dst);
                    set_sel(trace, row_map, ctx.cols.sel_a_start, src);
                    trace.set(ctx.cols.op_mov, row_final, BE::ONE);
                    set_sel(trace, row_final, ctx.cols.sel_dst0_start, dst);
                    set_sel(trace, row_final, ctx.cols.sel_a_start, src);

                    next_regs[dst as usize] = regs[src as usize];
                }
                // ALU: dst = a + b at final
                Op::Add { dst, a, b } => {
                    trace.set(ctx.cols.op_add, row_map, BE::ONE);
                    set_sel(trace, row_map, ctx.cols.sel_dst0_start, dst);
                    set_sel(trace, row_map, ctx.cols.sel_a_start, a);
                    set_sel(trace, row_map, ctx.cols.sel_b_start, b);

                    trace.set(ctx.cols.op_add, row_final, BE::ONE);
                    set_sel(trace, row_final, ctx.cols.sel_dst0_start, dst);
                    set_sel(trace, row_final, ctx.cols.sel_a_start, a);
                    set_sel(trace, row_final, ctx.cols.sel_b_start, b);

                    next_regs[dst as usize] = regs[a as usize] + regs[b as usize];
                }
                // ALU: dst = a - b at final
                Op::Sub { dst, a, b } => {
                    trace.set(ctx.cols.op_sub, row_map, BE::ONE);
                    set_sel(trace, row_map, ctx.cols.sel_dst0_start, dst);
                    set_sel(trace, row_map, ctx.cols.sel_a_start, a);
                    set_sel(trace, row_map, ctx.cols.sel_b_start, b);

                    trace.set(ctx.cols.op_sub, row_final, BE::ONE);
                    set_sel(trace, row_final, ctx.cols.sel_dst0_start, dst);
                    set_sel(trace, row_final, ctx.cols.sel_a_start, a);
                    set_sel(trace, row_final, ctx.cols.sel_b_start, b);

                    next_regs[dst as usize] = regs[a as usize] - regs[b as usize];
                }
                // ALU: dst = a * b at final
                Op::Mul { dst, a, b } => {
                    trace.set(ctx.cols.op_mul, row_map, BE::ONE);
                    set_sel(trace, row_map, ctx.cols.sel_dst0_start, dst);
                    set_sel(trace, row_map, ctx.cols.sel_a_start, a);
                    set_sel(trace, row_map, ctx.cols.sel_b_start, b);

                    trace.set(ctx.cols.op_mul, row_final, BE::ONE);
                    set_sel(trace, row_final, ctx.cols.sel_dst0_start, dst);
                    set_sel(trace, row_final, ctx.cols.sel_a_start, a);
                    set_sel(trace, row_final, ctx.cols.sel_b_start, b);

                    next_regs[dst as usize] = regs[a as usize] * regs[b as usize];
                }
                // ALU: dst = -a at final
                Op::Neg { dst, a } => {
                    trace.set(ctx.cols.op_neg, row_map, BE::ONE);
                    set_sel(trace, row_map, ctx.cols.sel_dst0_start, dst);
                    set_sel(trace, row_map, ctx.cols.sel_a_start, a);

                    trace.set(ctx.cols.op_neg, row_final, BE::ONE);
                    set_sel(trace, row_final, ctx.cols.sel_dst0_start, dst);
                    set_sel(trace, row_final, ctx.cols.sel_a_start, a);

                    next_regs[dst as usize] = BE::ZERO - regs[a as usize];
                }
                // ALU: dst = (a == b) ? 1 : 0 at final;
                // set eq_inv witness on map
                Op::Eq { dst, a, b } => {
                    trace.set(ctx.cols.op_eq, row_map, BE::ONE);
                    set_sel(trace, row_map, ctx.cols.sel_dst0_start, dst);
                    set_sel(trace, row_map, ctx.cols.sel_a_start, a);
                    set_sel(trace, row_map, ctx.cols.sel_b_start, b);

                    // latch op bit and selectors to final
                    trace.set(ctx.cols.op_eq, row_final, BE::ONE);
                    set_sel(trace, row_final, ctx.cols.sel_dst0_start, dst);
                    set_sel(trace, row_final, ctx.cols.sel_a_start, a);
                    set_sel(trace, row_final, ctx.cols.sel_b_start, b);

                    let diff = regs[a as usize] - regs[b as usize];
                    let w = if diff == BE::ZERO { BE::ONE } else { BE::ZERO };
                    let inv = if diff != BE::ZERO {
                        diff.inv()
                    } else {
                        BE::ZERO
                    };

                    trace.set(ctx.cols.eq_inv, row_map, inv);
                    trace.set(ctx.cols.eq_inv, row_final, inv);

                    next_regs[dst as usize] = w;
                }
                // ALU: dst = c ? a : b at final;
                // c must be boolean
                Op::Select { dst, c, a, b } => {
                    trace.set(ctx.cols.op_select, row_map, BE::ONE);
                    set_sel(trace, row_map, ctx.cols.sel_dst0_start, dst);
                    set_sel(trace, row_map, ctx.cols.sel_c_start, c);
                    set_sel(trace, row_map, ctx.cols.sel_a_start, a);
                    set_sel(trace, row_map, ctx.cols.sel_b_start, b);

                    trace.set(ctx.cols.op_select, row_final, BE::ONE);
                    set_sel(trace, row_final, ctx.cols.sel_dst0_start, dst);
                    set_sel(trace, row_final, ctx.cols.sel_c_start, c);
                    set_sel(trace, row_final, ctx.cols.sel_a_start, a);
                    set_sel(trace, row_final, ctx.cols.sel_b_start, b);

                    let cond = regs[c as usize];
                    next_regs[dst as usize] =
                        cond * regs[a as usize] + (BE::ONE - cond) * regs[b as usize];
                }
                Op::Assert { dst, c } => {
                    trace.set(ctx.cols.op_assert, row_map, BE::ONE);
                    set_sel(trace, row_map, ctx.cols.sel_dst0_start, dst);
                    set_sel(trace, row_map, ctx.cols.sel_c_start, c);

                    trace.set(ctx.cols.op_assert, row_final, BE::ONE);
                    set_sel(trace, row_final, ctx.cols.sel_dst0_start, dst);
                    set_sel(trace, row_final, ctx.cols.sel_c_start, c);

                    // write 1 at final
                    next_regs[dst as usize] = BE::ONE;
                }
                Op::AssertBit { dst, r } => {
                    trace.set(ctx.cols.op_assert_bit, row_map, BE::ONE);
                    set_sel(trace, row_map, ctx.cols.sel_dst0_start, dst);
                    set_sel(trace, row_map, ctx.cols.sel_c_start, r);

                    trace.set(ctx.cols.op_assert_bit, row_final, BE::ONE);
                    set_sel(trace, row_final, ctx.cols.sel_dst0_start, dst);
                    set_sel(trace, row_final, ctx.cols.sel_c_start, r);

                    next_regs[dst as usize] = BE::ONE;
                }
                Op::AssertRange { dst, r, bits } => {
                    // 32-bit mode:
                    // stage=1 (imm=1),
                    // mode64=0 (eq_inv=0)
                    trace.set(ctx.cols.op_assert_range, row_map, BE::ONE);
                    set_sel(trace, row_map, ctx.cols.sel_dst0_start, dst);
                    set_sel(trace, row_map, ctx.cols.sel_c_start, r);
                    trace.set(ctx.cols.imm, row_map, BE::ONE);
                    trace.set(ctx.cols.eq_inv, row_map, BE::ZERO);

                    trace.set(ctx.cols.op_assert_range, row_final, BE::ONE);
                    set_sel(trace, row_final, ctx.cols.sel_dst0_start, dst);
                    set_sel(trace, row_final, ctx.cols.sel_c_start, r);
                    trace.set(ctx.cols.imm, row_final, BE::ONE);
                    trace.set(ctx.cols.eq_inv, row_final, BE::ZERO);

                    // Witness: lower 32 bits
                    let x = regs[r as usize];
                    let mut n: u128 = x.as_int();

                    let k = (bits as usize).min(32);
                    for i in 0..32 {
                        let bit_val = if i < k { (n & 1) as u64 } else { 0u64 };
                        let v = BE::from(bit_val);
                        trace.set(ctx.cols.gadget_b_index(i), row_map, v);
                        trace.set(ctx.cols.gadget_b_index(i), row_final, v);

                        if i < k {
                            n >>= 1;
                        }
                    }

                    next_regs[dst as usize] = BE::ONE;
                }
                Op::AssertRangeLo { dst, r } => {
                    // Stage 0 of 64-bit:
                    // stage=0 (imm=0),
                    // mode64=1 (eq_inv=1)
                    trace.set(ctx.cols.op_assert_range, row_map, BE::ONE);
                    set_sel(trace, row_map, ctx.cols.sel_dst0_start, dst);
                    set_sel(trace, row_map, ctx.cols.sel_c_start, r);
                    trace.set(ctx.cols.imm, row_map, BE::ZERO);
                    trace.set(ctx.cols.eq_inv, row_map, BE::ONE);

                    trace.set(ctx.cols.op_assert_range, row_final, BE::ONE);
                    set_sel(trace, row_final, ctx.cols.sel_dst0_start, dst);
                    set_sel(trace, row_final, ctx.cols.sel_c_start, r);
                    trace.set(ctx.cols.imm, row_final, BE::ZERO);
                    trace.set(ctx.cols.eq_inv, row_final, BE::ONE);

                    // Witness: lower 32 bits
                    let x = regs[r as usize];
                    let mut n: u128 = x.as_int();

                    for i in 0..32 {
                        let bit_val = (n & 1) as u64;
                        let v = BE::from(bit_val);
                        trace.set(ctx.cols.gadget_b_index(i), row_map, v);
                        trace.set(ctx.cols.gadget_b_index(i), row_final, v);

                        n >>= 1;
                    }

                    // Ensure next row after final
                    // reflects sum_lo so ALU write
                    // constraint holds and stage1 can
                    // reconstruct r via eq64 using dst_cur.
                    let sum_lo = BE::from((x.as_int() & 0xFFFF_FFFFu128) as u64);
                    next_regs[dst as usize] = sum_lo;
                }
                Op::AssertRangeHi { dst, r } => {
                    // Stage 1 of 64-bit:
                    // stage=1 (imm=1),
                    // mode64=1 (eq_inv=1)
                    trace.set(ctx.cols.op_assert_range, row_map, BE::ONE);
                    set_sel(trace, row_map, ctx.cols.sel_dst0_start, dst);
                    set_sel(trace, row_map, ctx.cols.sel_c_start, r);
                    trace.set(ctx.cols.imm, row_map, BE::ONE);
                    trace.set(ctx.cols.eq_inv, row_map, BE::ONE);

                    trace.set(ctx.cols.op_assert_range, row_final, BE::ONE);
                    set_sel(trace, row_final, ctx.cols.sel_dst0_start, dst);
                    set_sel(trace, row_final, ctx.cols.sel_c_start, r);
                    trace.set(ctx.cols.imm, row_final, BE::ONE);
                    trace.set(ctx.cols.eq_inv, row_final, BE::ONE);

                    // Witness: upper 32 bits
                    let x = regs[r as usize];
                    let mut n: u128 = x.as_int() >> 32;

                    for i in 0..32 {
                        let bit_val = (n & 1) as u64;
                        let v = BE::from(bit_val);
                        trace.set(ctx.cols.gadget_b_index(i), row_map, v);
                        trace.set(ctx.cols.gadget_b_index(i), row_final, v);

                        n >>= 1;
                    }

                    // dst will be set to
                    // 1 by vm_alu write rule
                    next_regs[dst as usize] = BE::ONE;
                }
                Op::DivMod { dst_q, dst_r, a, b } => {
                    // DivMod: two destinations
                    trace.set(ctx.cols.op_divmod, row_map, BE::ONE);
                    set_sel(trace, row_map, ctx.cols.sel_dst0_start, dst_q);
                    set_sel(trace, row_map, ctx.cols.sel_dst1_start, dst_r);
                    set_sel(trace, row_map, ctx.cols.sel_a_start, a);
                    set_sel(trace, row_map, ctx.cols.sel_b_start, b);

                    trace.set(ctx.cols.op_divmod, row_final, BE::ONE);
                    set_sel(trace, row_final, ctx.cols.sel_dst0_start, dst_q);
                    set_sel(trace, row_final, ctx.cols.sel_dst1_start, dst_r);
                    set_sel(trace, row_final, ctx.cols.sel_a_start, a);
                    set_sel(trace, row_final, ctx.cols.sel_b_start, b);

                    // Compute host-side q,r using u128 division
                    let av = regs[a as usize].as_int();
                    let bv = regs[b as usize].as_int();

                    let q = if bv == 0 { 0u128 } else { av / bv };
                    let r = if bv == 0 { av } else { av % bv };

                    next_regs[dst_q as usize] = BE::from((q & 0xFFFF_FFFF_FFFF_FFFFu128) as u64);
                    next_regs[dst_r as usize] = BE::from((r & 0xFFFF_FFFF_FFFF_FFFFu128) as u64);

                    // Provide inv_b witness in eq_inv
                    let inv = if bv != 0 {
                        BE::from(bv as u64).inv()
                    } else {
                        BE::ZERO
                    };
                    trace.set(ctx.cols.eq_inv, row_map, inv);
                    trace.set(ctx.cols.eq_inv, row_final, inv);
                }
                Op::MulWide {
                    dst_hi,
                    dst_lo,
                    a,
                    b,
                } => {
                    // 64x64 -> 128-bit product,
                    // lo to dst0, hi to dst1.
                    trace.set(ctx.cols.op_mulwide, row_map, BE::ONE);
                    set_sel(trace, row_map, ctx.cols.sel_dst0_start, dst_lo);
                    set_sel(trace, row_map, ctx.cols.sel_dst1_start, dst_hi);
                    set_sel(trace, row_map, ctx.cols.sel_a_start, a);
                    set_sel(trace, row_map, ctx.cols.sel_b_start, b);

                    trace.set(ctx.cols.op_mulwide, row_final, BE::ONE);
                    set_sel(trace, row_final, ctx.cols.sel_dst0_start, dst_lo);
                    set_sel(trace, row_final, ctx.cols.sel_dst1_start, dst_hi);
                    set_sel(trace, row_final, ctx.cols.sel_a_start, a);
                    set_sel(trace, row_final, ctx.cols.sel_b_start, b);

                    let av = regs[a as usize].as_int();
                    let bv = regs[b as usize].as_int();
                    let al = av & 0xFFFF_FFFF_FFFF_FFFFu128;
                    let bl = bv & 0xFFFF_FFFF_FFFF_FFFFu128;

                    let prod = al.wrapping_mul(bl);

                    let lo = (&prod & 0xFFFF_FFFF_FFFF_FFFFu128) as u64;
                    let hi = (&prod >> 64) as u64;

                    next_regs[dst_lo as usize] = BE::from(lo);
                    next_regs[dst_hi as usize] = BE::from(hi);
                }
                Op::DivMod128 {
                    a_hi,
                    a_lo,
                    b,
                    dst_q,
                    dst_r,
                } => {
                    // 128/64 -> q,r
                    // encode lo in imm
                    trace.set(ctx.cols.op_div128, row_map, BE::ONE);
                    set_sel(trace, row_map, ctx.cols.sel_dst0_start, dst_q);
                    set_sel(trace, row_map, ctx.cols.sel_dst1_start, dst_r);
                    set_sel(trace, row_map, ctx.cols.sel_a_start, a_hi);
                    set_sel(trace, row_map, ctx.cols.sel_b_start, b);

                    let lo = regs[a_lo as usize];
                    trace.set(ctx.cols.imm, row_map, lo);

                    trace.set(ctx.cols.op_div128, row_final, BE::ONE);
                    set_sel(trace, row_final, ctx.cols.sel_dst0_start, dst_q);
                    set_sel(trace, row_final, ctx.cols.sel_dst1_start, dst_r);
                    set_sel(trace, row_final, ctx.cols.sel_a_start, a_hi);
                    set_sel(trace, row_final, ctx.cols.sel_b_start, b);
                    trace.set(ctx.cols.imm, row_final, lo);

                    let hi_u = regs[a_hi as usize].as_int();
                    let lo_u = regs[a_lo as usize].as_int();
                    let c_u = regs[b as usize].as_int();

                    let num = (hi_u << 64) | (lo_u & 0xFFFF_FFFF_FFFF_FFFFu128);

                    let (q, r) = if c_u == 0 {
                        (0u128, num)
                    } else {
                        (num / c_u, num % c_u)
                    };

                    next_regs[dst_q as usize] = BE::from((q & 0xFFFF_FFFF_FFFF_FFFFu128) as u64);
                    next_regs[dst_r as usize] = BE::from((r & 0xFFFF_FFFF_FFFF_FFFFu128) as u64);

                    // Provide inv_b witness
                    let inv = if c_u != 0 {
                        BE::from(c_u as u64).inv()
                    } else {
                        BE::ZERO
                    };

                    trace.set(ctx.cols.eq_inv, row_map, inv);
                    trace.set(ctx.cols.eq_inv, row_final, inv);
                }
                Op::SSqueeze { dst } => {
                    // Execute one permutation
                    // absorbing all pending regs (<=10).
                    // This level is Poseidon-active and
                    // must expose VM->lane wiring for
                    // PoseidonAir binding constraints.
                    trace.set(ctx.cols.op_sponge, row_map, BE::ONE);
                    trace.set(ctx.cols.op_sponge, row_final, BE::ONE);
                    set_sel(trace, row_final, ctx.cols.sel_dst0_start, dst);

                    // Reconstruct lane selectors for this
                    // squeeze from the pending register
                    // indices accumulated by prior SAbsorbN
                    // ops. Lane i selects pending_regs[i].
                    let mut inputs: ArrayVec<BE, 10> = ArrayVec::new();
                    let lanes = pending_regs.clone();

                    // Enforce the same strict rate bound as
                    // SAbsorbN: total pending inputs <= 10.
                    // (ArrayVec capacity already enforces this.)
                    for (i, &r) in lanes.iter().enumerate() {
                        let idx = r as usize; // 0..NR-1
                        inputs.push(regs[idx]);

                        // Packed bits for register index
                        let b0 = BE::from((idx & 1) as u64);
                        let b1 = BE::from(((idx >> 1) & 1) as u64);
                        let b2 = BE::from(((idx >> 2) & 1) as u64);
                        let one = BE::ONE;

                        // Set selectors at map row
                        trace.set(ctx.cols.sel_s_b_index(i, 0), row_map, b0);
                        trace.set(ctx.cols.sel_s_b_index(i, 1), row_map, b1);
                        trace.set(ctx.cols.sel_s_b_index(i, 2), row_map, b2);
                        trace.set(ctx.cols.sel_s_active_index(i), row_map, one);

                        // And mirror them at final row to
                        // keep ctrl/ALU constraints aligned.
                        trace.set(ctx.cols.sel_s_b_index(i, 0), row_final, b0);
                        trace.set(ctx.cols.sel_s_b_index(i, 1), row_final, b1);
                        trace.set(ctx.cols.sel_s_b_index(i, 2), row_final, b2);
                        trace.set(ctx.cols.sel_s_active_index(i), row_final, one);
                    }

                    // Clear unused lanes for this level.
                    for lane in lanes.len()..10 {
                        trace.set(ctx.cols.sel_s_active_index(lane), row_map, BE::ZERO);
                        trace.set(ctx.cols.sel_s_active_index(lane), row_final, BE::ZERO);

                        for b in 0..crate::layout::SPONGE_IDX_BITS {
                            trace.set(ctx.cols.sel_s_b_index(lane, b), row_map, BE::ZERO);
                            trace.set(ctx.cols.sel_s_b_index(lane, b), row_final, BE::ZERO);
                        }
                    }

                    // If empty (no prior absorbs), treat
                    // as zeros to keep semantics.
                    pose_active = BE::ONE;
                    apply_level_absorb(trace, commitment, lvl, &inputs);

                    let out = trace.get(ctx.cols.lane_index(0), row_final);
                    next_regs[dst as usize] = out;

                    pending_regs.clear();
                }
                Op::SAbsorbN { regs: ref rr } => {
                    // Mark sponge op at map/final,
                    // set selectors for provided regs.
                    trace.set(ctx.cols.op_sponge, row_map, BE::ONE);
                    trace.set(ctx.cols.op_sponge, row_final, BE::ONE);

                    for (i, &r) in rr.iter().enumerate() {
                        // Enforce lane index bound
                        if i >= 10 {
                            return Err(Error::InvalidInput("sponge rate overflow"));
                        }

                        // Set packed bits and
                        // active for this lane
                        let idx = r as usize; // 0..7
                        let b0 = BE::from((idx & 1) as u64);
                        let b1 = BE::from(((idx >> 1) & 1) as u64);
                        let b2 = BE::from(((idx >> 2) & 1) as u64);
                        let one = BE::ONE;

                        trace.set(ctx.cols.sel_s_b_index(i, 0), row_map, b0);
                        trace.set(ctx.cols.sel_s_b_index(i, 1), row_map, b1);
                        trace.set(ctx.cols.sel_s_b_index(i, 2), row_map, b2);
                        trace.set(ctx.cols.sel_s_active_index(i), row_map, one);

                        trace.set(ctx.cols.sel_s_b_index(i, 0), row_final, b0);
                        trace.set(ctx.cols.sel_s_b_index(i, 1), row_final, b1);
                        trace.set(ctx.cols.sel_s_b_index(i, 2), row_final, b2);
                        trace.set(ctx.cols.sel_s_active_index(i), row_final, one);

                        // Strictly enforce total
                        // pending inputs <= 10
                        push_absorb(&mut pending_regs, r)?;
                    }

                    // For remaining unused lanes
                    // clear active and bits.
                    for lane in rr.len()..10 {
                        trace.set(ctx.cols.sel_s_active_index(lane), row_map, BE::ZERO);
                        trace.set(ctx.cols.sel_s_active_index(lane), row_final, BE::ZERO);

                        for b in 0..crate::layout::SPONGE_IDX_BITS {
                            trace.set(ctx.cols.sel_s_b_index(lane, b), row_map, BE::ZERO);
                            trace.set(ctx.cols.sel_s_b_index(lane, b), row_final, BE::ZERO);
                        }
                    }

                    // No permutation at absorb rows
                    pose_active = BE::ZERO;
                }
                Op::MerkleStepFirst {
                    leaf_reg,
                    dir_reg,
                    sib_reg,
                } => {
                    // mark merkle level active
                    // across the whole level.
                    for r in base..(base + ctx.steps) {
                        trace.set(ctx.cols.merkle_g, r, BE::ONE);
                    }

                    // Poseidon active on this level
                    pose_active = BE::ONE;

                    // first flag and leaf/acc at map
                    let leaf = regs[leaf_reg as usize];
                    trace.set(ctx.cols.merkle_first, row_map, BE::ONE);
                    trace.set(ctx.cols.merkle_leaf, row_map, leaf);
                    trace.set(ctx.cols.merkle_acc, row_map, leaf);

                    // hold acc until final
                    for r in (row_map + 1)..row_final {
                        trace.set(ctx.cols.merkle_acc, r, leaf);
                    }

                    // dir/sib
                    let d = regs[dir_reg as usize];
                    let s = regs[sib_reg as usize];
                    trace.set(ctx.cols.merkle_dir, row_map, d);
                    trace.set(ctx.cols.merkle_sib, row_map, s);

                    // lanes and apply poseidon
                    let left = (BE::ONE - d) * leaf + d * s;
                    let right = (BE::ONE - d) * s + d * leaf;
                    apply_level_absorb(trace, commitment, lvl, &[left, right]);

                    // acc at/after final = lane_l(final)
                    let out = trace.get(ctx.cols.lane_l, row_final);
                    for r in row_final..(base + ctx.steps) {
                        trace.set(ctx.cols.merkle_acc, r, out);
                    }
                }
                Op::MerkleStep { dir_reg, sib_reg } => {
                    for r in base..(base + ctx.steps) {
                        trace.set(ctx.cols.merkle_g, r, BE::ONE);
                    }

                    pose_active = BE::ONE;

                    // Find previous Merkle
                    // level's final row
                    let mut prev_fin = row_map;
                    if lvl > 0 {
                        for pl in (0..lvl).rev() {
                            let pbase = pl * ctx.steps;
                            let pmap = pbase + schedule::pos_map();

                            if trace.get(ctx.cols.merkle_g, pmap) == BE::ONE {
                                prev_fin = pbase + schedule::pos_final();
                                break;
                            }
                        }
                    }

                    let acc_prev = trace.get(ctx.cols.merkle_acc, prev_fin);
                    trace.set(ctx.cols.merkle_acc, row_map, acc_prev);

                    for r in (row_map + 1)..row_final {
                        trace.set(ctx.cols.merkle_acc, r, acc_prev);
                    }

                    let d = regs[dir_reg as usize];
                    let s = regs[sib_reg as usize];
                    trace.set(ctx.cols.merkle_dir, row_map, d);
                    trace.set(ctx.cols.merkle_sib, row_map, s);

                    let left = (BE::ONE - d) * acc_prev + d * s;
                    let right = (BE::ONE - d) * s + d * acc_prev;
                    apply_level_absorb(trace, commitment, lvl, &[left, right]);

                    let out = trace.get(ctx.cols.lane_l, row_final);
                    for r in row_final..(base + ctx.steps) {
                        trace.set(ctx.cols.merkle_acc, r, out);
                    }
                }
                Op::MerkleStepLast { dir_reg, sib_reg } => {
                    for r in base..(base + ctx.steps) {
                        trace.set(ctx.cols.merkle_g, r, BE::ONE);
                    }

                    pose_active = BE::ONE;

                    let mut prev_fin = row_map;
                    if lvl > 0 {
                        for pl in (0..lvl).rev() {
                            let pbase = pl * ctx.steps;
                            let pmap = pbase + schedule::pos_map();

                            if trace.get(ctx.cols.merkle_g, pmap) == BE::ONE {
                                prev_fin = pbase + schedule::pos_final();
                                break;
                            }
                        }
                    }

                    let acc_prev = trace.get(ctx.cols.merkle_acc, prev_fin);
                    trace.set(ctx.cols.merkle_acc, row_map, acc_prev);

                    for r in (row_map + 1)..row_final {
                        trace.set(ctx.cols.merkle_acc, r, acc_prev);
                    }

                    let d = regs[dir_reg as usize];
                    let s = regs[sib_reg as usize];
                    trace.set(ctx.cols.merkle_dir, row_map, d);
                    trace.set(ctx.cols.merkle_sib, row_map, s);

                    let left = (BE::ONE - d) * acc_prev + d * s;
                    let right = (BE::ONE - d) * s + d * acc_prev;
                    apply_level_absorb(trace, commitment, lvl, &[left, right]);

                    trace.set(ctx.cols.merkle_last, row_final, BE::ONE);

                    let out = trace.get(ctx.cols.lane_l, row_final);
                    for r in row_final..(base + ctx.steps) {
                        trace.set(ctx.cols.merkle_acc, r, out);
                    }
                }
                Op::Load { dst, addr } => {
                    trace.set(ctx.cols.op_load, row_map, BE::ONE);
                    set_sel(trace, row_map, ctx.cols.sel_dst0_start, dst);
                    set_sel(trace, row_map, ctx.cols.sel_a_start, addr);

                    trace.set(ctx.cols.op_load, row_final, BE::ONE);
                    set_sel(trace, row_final, ctx.cols.sel_dst0_start, dst);
                    set_sel(trace, row_final, ctx.cols.sel_a_start, addr);

                    let addr_v = regs[addr as usize];
                    let clk = BE::from(lvl as u64);
                    let loaded = self.mem.get(&addr_v.as_int()).copied().unwrap_or(BE::ZERO);

                    // set imm to carry loaded
                    // value for ALU write constraint
                    trace.set(ctx.cols.imm, row_map, loaded);
                    trace.set(ctx.cols.imm, row_final, loaded);

                    // write into dst after final
                    next_regs[dst as usize] = loaded;

                    self.ram_events.push((addr_v, clk, loaded, BE::from(0u64)));
                }
                Op::Store { addr, src } => {
                    trace.set(ctx.cols.op_store, row_map, BE::ONE);
                    set_sel(trace, row_map, ctx.cols.sel_a_start, addr);
                    set_sel(trace, row_map, ctx.cols.sel_b_start, src);

                    trace.set(ctx.cols.op_store, row_final, BE::ONE);
                    set_sel(trace, row_final, ctx.cols.sel_a_start, addr);
                    set_sel(trace, row_final, ctx.cols.sel_b_start, src);

                    let addr_v = regs[addr as usize];
                    let src_v = regs[src as usize];
                    let clk = BE::from(lvl as u64);

                    // update host memory
                    self.mem.insert(addr_v.as_int(), src_v);
                    self.ram_events.push((addr_v, clk, src_v, BE::ONE));
                }
                Op::End => {}
            }

            // rows between map..=final:
            // keep old regs (&pre-write state)
            for r in (row_map + 1)..=row_final {
                for (i, val) in regs.iter().enumerate().take(NR) {
                    trace.set(ctx.cols.r_index(i), r, *val);
                }

                // carry PC across map..final rows
                trace.set(ctx.cols.pc, r, BE::from(lvl as u64));
            }

            // after final within level:
            // keep next_regs
            for r in (row_final + 1)..(base + ctx.steps) {
                for (i, val) in next_regs.iter().enumerate().take(NR) {
                    trace.set(ctx.cols.r_index(i), r, *val);
                }

                trace.set(ctx.cols.pc, r, BE::from(lvl as u64));
            }

            // commit next_regs to regs for next level.
            // also set pose_active across the whole level
            for r in base..(base + ctx.steps) {
                trace.set(ctx.cols.pose_active, r, pose_active);
            }

            regs = next_regs;

            if lvl % 512 == 0 || lvl + 1 == total_lvls {
                tracing::debug!(target="trace.vm", lvl=%lvl, "% progressed");
            }
        }

        tracing::debug!(
            target="trace.vm",
            elapsed_ms=%t_all.elapsed().as_millis(),
            "vm fill done",
        );

        Ok(())
    }
}

fn op_to_one_hot(op: &Op) -> [BE; 17] {
    use builder::Op::*;

    // Order matches Columns.op_* sequence
    // [const, mov, add, sub, mul, neg, eq,
    //  select, sponge, assert, assert_bit,
    //  assert_range, divmod, div128,
    //  mulwide, load, store]
    let mut v = [BE::ZERO; 17];
    match op {
        Const { .. } => v[0] = BE::ONE,
        Mov { .. } => v[1] = BE::ONE,
        Add { .. } => v[2] = BE::ONE,
        Sub { .. } => v[3] = BE::ONE,
        Mul { .. } => v[4] = BE::ONE,
        Neg { .. } => v[5] = BE::ONE,
        Eq { .. } => v[6] = BE::ONE,
        Select { .. } => v[7] = BE::ONE,
        SAbsorbN { .. } | SSqueeze { .. } => v[8] = BE::ONE,
        Assert { .. } => v[9] = BE::ONE,
        AssertBit { .. } => v[10] = BE::ONE,
        AssertRange { .. } | AssertRangeLo { .. } | AssertRangeHi { .. } => v[11] = BE::ONE,
        DivMod { .. } => v[12] = BE::ONE,
        DivMod128 { .. } => v[13] = BE::ONE,
        MulWide { .. } => v[14] = BE::ONE,
        Load { .. } => v[15] = BE::ONE,
        Store { .. } => v[16] = BE::ONE,
        MerkleStepFirst { .. } | MerkleStep { .. } | MerkleStepLast { .. } | End => {
            // Non-ALU ops: leave all zeros
        }
    }

    v
}

// Push an absorbed register
// with strict rate bound.
fn push_absorb(pending: &mut ArrayVec<u8, 10>, r: u8) -> error::Result<()> {
    // rate = 10 lanes for absorption
    if pending.len() >= 10 {
        return Err(Error::InvalidInput("sponge rate overflow"));
    }

    pending.push(r);

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::utils;
    use crate::vm::layout::{Columns, STEPS_PER_LEVEL_P2};
    use crate::vm::trace::build_trace;

    use zk_lisp_compiler::builder::Op;
    use zk_lisp_compiler::{CompilerMetrics, builder, compile_entry};
    use zk_lisp_proof::pi::PublicInputs;

    use crate::vm::schedule;
    use winterfell::Trace;
    // for length()

    #[test]
    fn alu_const_add() {
        let metrics = CompilerMetrics::default();
        let mut b = builder::ProgramBuilder::new();

        b.push(Op::Const { dst: 0, imm: 7 });
        b.push(Op::Const { dst: 1, imm: 9 });
        b.push(Op::Add { dst: 2, a: 0, b: 1 });
        b.push(Op::End);

        let p = b.finalize(metrics).expect("finalize must succeed");

        let trace = build_trace(&p, &PublicInputs::default()).unwrap();
        let cols = Columns::baseline();
        let steps = STEPS_PER_LEVEL_P2;

        // level 0: const r0=7
        let base0 = 0;
        let row0_map = base0 + schedule::pos_map();
        let row0_fin = base0 + schedule::pos_final();

        assert_eq!(trace.get(cols.op_const, row0_map), BE::ONE);
        assert_eq!(trace.get(cols.r_index(0), row0_fin + 1), BE::from(7u64));

        // level 1: const r1=9
        let base1 = steps;
        let row1_map = base1 + schedule::pos_map();
        let row1_fin = base1 + schedule::pos_final();

        assert_eq!(trace.get(cols.op_const, row1_map), BE::ONE);
        assert_eq!(trace.get(cols.r_index(1), row1_fin + 1), BE::from(9u64));

        // level 2: add r2=r0+r1=16
        let base2 = 2 * steps;
        let row2_map = base2 + schedule::pos_map();
        let row2_fin = base2 + schedule::pos_final();

        assert_eq!(trace.get(cols.op_add, row2_map), BE::ONE);
        assert_eq!(trace.get(cols.r_index(2), row2_fin + 1), BE::from(16u64));

        // total rows
        assert_eq!(trace.length(), 4 * steps);
    }

    #[test]
    fn alu_eq_and_select() {
        let metrics = CompilerMetrics::default();
        let mut b = builder::ProgramBuilder::new();

        b.push(Op::Const { dst: 0, imm: 5 });
        b.push(Op::Const { dst: 1, imm: 5 });
        b.push(Op::Eq { dst: 2, a: 0, b: 1 }); // r2=1
        b.push(Op::Select {
            dst: 3,
            c: 2,
            a: 0,
            b: 1,
        }); // r3=r0 (both equal)

        b.push(Op::End);

        let p = b.finalize(metrics).expect("finalize must succeed");

        let trace = build_trace(&p, &PublicInputs::default()).unwrap();
        let cols = Columns::baseline();
        let steps = STEPS_PER_LEVEL_P2;

        // level 2 EQ
        let base2 = 2 * steps;
        let row2_map = base2 + schedule::pos_map();
        let row2_fin = base2 + schedule::pos_final();

        assert_eq!(trace.get(cols.op_eq, row2_map), BE::ONE);
        assert_eq!(trace.get(cols.r_index(2), row2_fin + 1), BE::ONE);

        // level 3 SELECT
        let base3 = 3 * steps;
        let row3_map = base3 + schedule::pos_map();
        let row3_fin = base3 + schedule::pos_final();

        assert_eq!(trace.get(cols.op_select, row3_map), BE::ONE);
        assert_eq!(trace.get(cols.r_index(3), row3_fin + 1), BE::from(5u64));

        assert_eq!(trace.length(), 8 * steps);
    }

    #[test]
    fn sponge_absorb_squeeze_simple() {
        // Check that SAbsorb2+SSqueeze writes
        // Poseidon(left,right) into dst.
        let metrics = CompilerMetrics::default();
        let mut b = builder::ProgramBuilder::new();

        b.push(Op::Const { dst: 0, imm: 1 });
        b.push(Op::Const { dst: 1, imm: 2 });
        b.push(Op::SAbsorbN { regs: vec![0, 1] });
        b.push(Op::SSqueeze { dst: 3 });
        b.push(Op::End);

        let p = b.finalize(metrics).expect("finalize must succeed");

        let trace = build_trace(&p, &PublicInputs::default()).unwrap();
        let cols = Columns::baseline();
        let steps = STEPS_PER_LEVEL_P2;

        // Level 2 (SSqueeze) performs the write
        let base3 = 3 * steps;
        let row3_fin = base3 + schedule::pos_final();

        assert_eq!(trace.get(cols.op_sponge, row3_fin), BE::ONE);

        // Expected hash from inputs at absorb level
        let left = trace.get(cols.r_index(0), 2 * steps + schedule::pos_map());
        let right = trace.get(cols.r_index(1), 2 * steps + schedule::pos_map());
        let expected = crate::poseidon::poseidon_hash_two_lanes(&p.commitment, left, right);

        assert_eq!(trace.get(cols.r_index(3), row3_fin + 1), expected);
    }

    #[test]
    fn program_commit_bound_at_level0() {
        let metrics = CompilerMetrics::default();
        let mut b = builder::ProgramBuilder::new();

        b.push(Op::Const { dst: 0, imm: 1 });
        b.push(Op::End);

        let p = b.finalize(metrics).expect("finalize must succeed");

        let trace = build_trace(&p, &PublicInputs::default()).unwrap();
        let cols = Columns::baseline();

        let row0_map = schedule::pos_map();
        let pc = utils::be_from_le8(&p.commitment);

        assert_eq!(trace.get(cols.pi_prog, row0_map), pc);
    }

    #[test]
    fn rom_matches_op_bits_at_map_rows() {
        let metrics = CompilerMetrics::default();
        let mut b = builder::ProgramBuilder::new();

        b.push(Op::Const { dst: 0, imm: 7 });
        b.push(Op::Const { dst: 1, imm: 9 });
        b.push(Op::Add { dst: 2, a: 0, b: 1 });
        b.push(Op::End);

        let p = b.finalize(metrics).expect("finalize must succeed");

        let trace = build_trace(&p, &PublicInputs::default()).unwrap();
        let cols = Columns::baseline();
        let steps = STEPS_PER_LEVEL_P2;

        for lvl in 0..p.ops.len() {
            let row_map = lvl * steps + schedule::pos_map();
            let ops = [
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
                cols.op_mulwide,
            ];

            for (k, c) in ops.iter().enumerate() {
                assert_eq!(
                    trace.get(*c, row_map),
                    trace.get(cols.rom_op_index(k), row_map),
                    "lvl {lvl} k {k}"
                );
            }
        }
    }

    #[test]
    fn rom_matches_op_bits_for_arith_select_program() {
        let src = r"
(def (main)
  (let ((a 7) (b 9))
    (select (= a b) (+ a b) 0)))
 ";

        let p = compile_entry(src, &[]).unwrap();
        let trace = build_trace(&p, &PublicInputs::default()).unwrap();
        let cols = Columns::baseline();
        let steps = STEPS_PER_LEVEL_P2;

        // check first few levels
        for lvl in 0..p.ops.len() {
            let row_map = lvl * steps + schedule::pos_map();
            let ops = [
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
                cols.op_mulwide,
            ];

            for (k, c) in ops.iter().enumerate() {
                assert_eq!(
                    trace.get(*c, row_map),
                    trace.get(cols.rom_op_index(k), row_map),
                    "lvl {lvl} k {k}"
                );
            }
        }
    }

    #[test]
    fn pc_carries_and_increments_per_level() {
        let src = r"
(def (main)
  (let ((a 7) (b 9))
    (select (= a b) (+ a b) 0)))
";

        let p = compile_entry(src, &[]).unwrap();
        let trace = build_trace(&p, &PublicInputs::default()).unwrap();
        let cols = Columns::baseline();
        let steps = STEPS_PER_LEVEL_P2;
        let total_levels = trace.length() / steps;

        for lvl in 0..total_levels {
            let base = lvl * steps;
            // map row pc == lvl
            assert_eq!(
                trace.get(cols.pc, base + schedule::pos_map()),
                BE::from(lvl as u64)
            );

            // carry across level
            for r in base..(base + steps) {
                assert_eq!(trace.get(cols.pc, r), BE::from(lvl as u64));
            }

            // increment: next map row should be lvl+1 if exists
            if lvl + 1 < total_levels {
                let next_map = (lvl + 1) * steps + schedule::pos_map();
                assert_eq!(trace.get(cols.pc, next_map), BE::from((lvl + 1) as u64));
            }
        }
    }
}

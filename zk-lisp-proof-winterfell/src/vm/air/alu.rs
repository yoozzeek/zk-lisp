// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! ALU transition constraints for the zk-lisp VM.
//!
//! Enforces register carry, arithmetic op semantics, range
//! checks and division gadgets over the unified execution
//! trace when VM features are enabled.

use crate::vm::air::AirModule;
use crate::vm::air::{AirSharedContext, mixers};
use crate::vm::layout::{
    NR, POSEIDON_ROUNDS, STEPS_PER_LEVEL_P2, VM_USAGE_ASSERT, VM_USAGE_ASSERT_BIT,
    VM_USAGE_ASSERT_RANGE, VM_USAGE_DIV128, VM_USAGE_DIVMOD, VM_USAGE_EQ, VM_USAGE_MULWIDE,
};

use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::{EvaluationFrame, TransitionConstraintDegree};

pub(crate) struct VmAluAir;

impl AirModule for VmAluAir {
    fn push_degrees(ctx: &AirSharedContext, out: &mut Vec<TransitionConstraintDegree>) {
        let mask = ctx.vm_usage_mask;

        let use_eq = (mask & (1 << VM_USAGE_EQ)) != 0;
        let use_divmod = (mask & (1 << VM_USAGE_DIVMOD)) != 0;
        let use_mulwide = (mask & (1 << VM_USAGE_MULWIDE)) != 0;
        let use_div128 = (mask & (1 << VM_USAGE_DIV128)) != 0;
        let use_assert = (mask & (1 << VM_USAGE_ASSERT)) != 0;
        let use_assert_bit = (mask & (1 << VM_USAGE_ASSERT_BIT)) != 0;
        let use_assert_range = (mask & (1 << VM_USAGE_ASSERT_RANGE)) != 0;

        let deg_carry = TransitionConstraintDegree::with_cycles(1, vec![STEPS_PER_LEVEL_P2]);

        // Write path uses pi^6 mixer and p_final;
        // keep the original 7 here.
        let deg_write = TransitionConstraintDegree::with_cycles(7, vec![STEPS_PER_LEVEL_P2]);

        // All high-degree gadgets (Eq ties, Div/Mod, MulWide,
        // Div128 and assertions) share the same high-degree mixer
        // family (pi^4 / pi^6), and in debug runs we observe base
        // degree 5 for their polynomials. We keep 5 here and rely
        // on vm_usage_mask to drop unused gadgets per segment.
        let deg5 = TransitionConstraintDegree::with_cycles(5, vec![STEPS_PER_LEVEL_P2]);

        // carry registers on non-final rows
        for _ in 0..NR {
            out.push(deg_carry.clone());
        }

        // write registers at final (op-gated)
        for _ in 0..NR {
            out.push(deg_write.clone());
        }

        // equality ties (dst reflects [a==b]) (2)
        if use_eq {
            for _ in 0..2 {
                out.push(deg5.clone());
            }
        }

        // DivMod: a - b*q - r, and b*inv - 1 (2)
        if use_divmod {
            for _ in 0..2 {
                out.push(deg5.clone());
            }
        }

        // assert enforcer (c==1 at final) (1)
        if use_assert {
            out.push(deg5.clone());
        }

        // AssertBit: booleanity r(r-1)=0 at final (1)
        if use_assert_bit {
            out.push(deg5.clone());
        }

        // AssertRange (32-bit): 32 booleanities + 1 equality (33)
        if use_assert_range {
            for _ in 0..32 {
                out.push(deg5.clone());
            }
            out.push(deg5.clone());
        }

        // MulWide equality (1): a*b == lo + hi*2^64
        if use_mulwide {
            out.push(deg5.clone());
        }

        // Div128 constraints (2): num == b*q + r and b*inv - 1
        if use_div128 {
            for _ in 0..2 {
                out.push(deg5.clone());
            }
        }
    }

    fn eval_block<E>(
        ctx: &AirSharedContext,
        frame: &EvaluationFrame<E>,
        periodic: &[E],
        result: &mut [E],
        ix: &mut usize,
    ) where
        E: FieldElement<BaseField = BE> + From<BE>,
    {
        let cur = frame.current();
        let next = frame.next();

        // usage flags derived from per-segment alu_usage_mask
        let mask = ctx.vm_usage_mask;
        let use_eq = (mask & (1 << VM_USAGE_EQ)) != 0;
        let use_divmod = (mask & (1 << VM_USAGE_DIVMOD)) != 0;
        let use_mulwide = (mask & (1 << VM_USAGE_MULWIDE)) != 0;
        let use_div128 = (mask & (1 << VM_USAGE_DIV128)) != 0;
        let use_assert = (mask & (1 << VM_USAGE_ASSERT)) != 0;
        let use_assert_bit = (mask & (1 << VM_USAGE_ASSERT_BIT)) != 0;
        let use_assert_range = (mask & (1 << VM_USAGE_ASSERT_RANGE)) != 0;

        let p_map = periodic[0];
        let p_final = periodic[1 + POSEIDON_ROUNDS];
        let p_pad = periodic[1 + POSEIDON_ROUNDS + 1];
        let p_pad_last = periodic[1 + POSEIDON_ROUNDS + 2];

        // mixers
        let pi = cur[ctx.cols.pi_prog];
        let s_low = mixers::low(periodic);
        let s_write = mixers::pi6(periodic, pi); // pi^6
        // keep eq mixer degree lower than writes
        let s_eq = mixers::pi4(periodic, pi);

        // carry when next row is not final within the level
        let mut g_carry = p_map + (p_pad - p_pad_last);
        for gr in (0..(POSEIDON_ROUNDS - 1)).map(|j| periodic[1 + j]) {
            g_carry += gr;
        }

        // reconstruct a/b/c from
        // role selectors and regs.
        let mut a_val = E::ZERO;
        let mut b_val = E::ZERO;
        let mut c_val = E::ZERO;

        for i in 0..NR {
            let r = cur[ctx.cols.r_index(i)];
            a_val += cur[ctx.cols.sel_a_index(i)] * r;
            b_val += cur[ctx.cols.sel_b_index(i)] * r;
            c_val += cur[ctx.cols.sel_c_index(i)] * r;
        }

        // carry r[i] across rows where next is not final
        for i in 0..NR {
            result[*ix] = g_carry * (next[ctx.cols.r_index(i)] - cur[ctx.cols.r_index(i)]) + s_low;
            *ix += 1;
        }

        // compute op result (excluding Eq),
        // including Hash2 via lane_l.
        let imm = cur[ctx.cols.imm];
        let b_const = cur[ctx.cols.op_const];
        let b_mov = cur[ctx.cols.op_mov];
        let b_add = cur[ctx.cols.op_add];
        let b_sub = cur[ctx.cols.op_sub];
        let b_mul = cur[ctx.cols.op_mul];
        let b_neg = cur[ctx.cols.op_neg];
        let b_eq = cur[ctx.cols.op_eq];
        let b_sel = cur[ctx.cols.op_select];
        let b_sponge = cur[ctx.cols.op_sponge];
        let b_assert = cur[ctx.cols.op_assert];
        let mode64 = cur[ctx.cols.eq_inv]; // reused as flag on range rows
        let b_assert_bit = cur[ctx.cols.op_assert_bit];
        let b_assert_range = cur[ctx.cols.op_assert_range];
        let b_divmod = cur[ctx.cols.op_divmod];
        let b_mulwide = cur[ctx.cols.op_mulwide];
        let b_div128 = cur[ctx.cols.op_div128];
        let b_load = cur[ctx.cols.op_load];

        // include Eq via dst0_next so
        // generic write can be uniform for Eq
        let mut dst0_next = E::ZERO; // sum dst0_i * r_i_next
        for i in 0..NR {
            dst0_next += cur[ctx.cols.sel_dst0_index(i)] * next[ctx.cols.r_index(i)];
        }

        let mut dst0_cur = E::ZERO; // sum dst0_i * r_i_cur
        for i in 0..NR {
            dst0_cur += cur[ctx.cols.sel_dst0_index(i)] * cur[ctx.cols.r_index(i)];
        }

        // For native DivMod: q = dst0_next, r = dst1_next
        let mut dst1_next = E::ZERO; // sum dst1_i * r_i_next
        for i in 0..NR {
            dst1_next += cur[ctx.cols.sel_dst1_index(i)] * next[ctx.cols.r_index(i)];
        }

        // Base result for single-dst ops
        let mut res = b_const * imm
            + b_mov * a_val
            + b_add * (a_val + b_val)
            + b_sub * (a_val - b_val)
            + b_mul * (a_val * b_val)
            + b_neg * (E::ZERO - a_val)
            + b_sel * (c_val * a_val + (E::ONE - c_val) * b_val)
            + b_sponge * cur[ctx.cols.lane_l]
            + if use_eq { b_eq * dst0_next } else { E::ZERO }
            + if use_assert { b_assert * E::ONE } else { E::ZERO }
            + if use_assert_bit { b_assert_bit * E::ONE } else { E::ZERO }
            // load: write value carried in imm
            + b_load * cur[ctx.cols.imm];

        // AssertRange: precompute sum
        // of 32 bits for write/equality
        let mut sum = E::ZERO;
        let mut pow2 = E::ONE;

        for i in 0..32 {
            let bi = cur[ctx.cols.gadget_b_index(i)];
            sum += pow2 * bi;
            pow2 = pow2 + pow2; // *2
        }

        // range write behavior:
        // stage=0 -> write sum (lo);
        // stage=1 -> write 1
        if use_assert_range {
            res += b_assert_range * ((E::ONE - imm) * sum + imm * E::ONE);
        }

        // write at final:
        // For most ops:
        //   next = (1-sd0-sd1)*cur + sd0*res
        // For DivMod native:
        //   q = dst0_next,
        //   r = dst1_next already set by trace
        for i in 0..NR {
            let sd0 = cur[ctx.cols.sel_dst0_index(i)];
            let sd1 = cur[ctx.cols.sel_dst1_index(i)];
            let keep = E::ONE - sd0 - sd1;

            // For non two-dest ops sd1==0
            // and sd0 gates res; For two-dest
            // ops (divmod, mulwide, div128), sd0/sd1
            // gate lo/hi via dst0_next/dst1_next.
            let uses_two = use_divmod || use_mulwide || use_div128;
            let b_two = if uses_two {
                b_divmod + b_mulwide + b_div128
            } else {
                E::ZERO
            };

            let w0 = (E::ONE - b_two) * res + b_two * dst0_next;
            let w1 = b_two * dst1_next;

            result[*ix] = p_final
                * (next[ctx.cols.r_index(i)]
                    - (keep * cur[ctx.cols.r_index(i)] + sd0 * w0 + sd1 * w1))
                + s_write;
            *ix += 1;
        }

        let diff = a_val - b_val;
        let inv = cur[ctx.cols.eq_inv];

        if use_eq {
            // if dst0_next==1 => diff==0
            result[*ix] = p_final * b_eq * (dst0_next * diff) + s_eq;
            *ix += 1;

            // if diff!=0 => dst0_next==0
            // via (1 - dst0_next) - diff*inv == 0
            result[*ix] = p_final * b_eq * ((E::ONE - dst0_next) - diff * inv) + s_eq;
            *ix += 1;
        }

        // DivMod constraints after Eq ties
        // q = dst0_next, r = dst1_next;
        // inv_b stored in eq_inv on these rows.
        if use_divmod {
            let inv_b = cur[ctx.cols.eq_inv];
            result[*ix] = p_final * b_divmod * (a_val - b_val * dst0_next - dst1_next) + s_eq;
            *ix += 1;
            result[*ix] = p_final * b_divmod * (b_val * inv_b - E::ONE) + s_eq;
            *ix += 1;
        }

        // MulWide: a*b == lo + hi*2^64,
        // where lo=dst0_next, hi=dst1_next
        let p2_64 = E::from(crate::utils::pow2_64());
        if use_mulwide {
            result[*ix] =
                p_final * b_mulwide * (a_val * b_val - (dst0_next + dst1_next * p2_64)) + s_eq;
            *ix += 1;
        }

        // Div128: num = a*2^64 + imm;
        // enforce num == b*q + r and inv witness
        let num128 = a_val * p2_64 + imm;
        if use_div128 {
            result[*ix] = p_final * b_div128 * (num128 - (b_val * dst0_next + dst1_next)) + s_eq;
            *ix += 1;

            let inv_b = cur[ctx.cols.eq_inv];
            result[*ix] = p_final * b_div128 * (b_val * inv_b - E::ONE) + s_eq;
            *ix += 1;
        }

        // assert: require c_val == 1 at final
        // and enforce c booleanity for SELECT at final
        if use_assert {
            result[*ix] =
                p_final * (b_assert * (c_val - E::ONE) + b_sel * (c_val * (c_val - E::ONE))) + s_eq;
            *ix += 1;
        }

        // AssertBit: c_val in {0,1}
        if use_assert_bit {
            result[*ix] = p_final * b_assert_bit * (c_val * (c_val - E::ONE)) + s_eq;
            *ix += 1;
        }

        // Now emit booleanity for
        // each bit (after write)
        if use_assert_range {
            for i in 0..32 {
                let bi = cur[ctx.cols.gadget_b_index(i)];
                result[*ix] = p_final * b_assert_range * (bi * (bi - E::ONE)) + s_eq;
                *ix += 1;
            }

            // Equality on stage==1
            // If mode64==0: c == sum (32-bit)
            // If mode64==1: c == dst0_cur + (sum << 32)
            let mut p2_32 = E::ONE;
            for _ in 0..32 {
                p2_32 = p2_32 + p2_32;
            }

            let eq32 = c_val - sum;
            let eq64 = c_val - (dst0_cur + sum * p2_32);
            let eq_term = imm * (mode64 * eq64 + (E::ONE - mode64) * eq32);
            result[*ix] = p_final * b_assert_range * eq_term + s_eq;
            *ix += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vm::layout::Columns;
    use winterfell::EvaluationFrame;

    #[test]
    fn assert_enforcer_violates_when_false() {
        let cols = Columns::baseline();
        let mut frame = EvaluationFrame::<BE>::new(cols.width(0));
        let mut periodic = vec![BE::ZERO; 1 + POSEIDON_ROUNDS + 1 + 1 + 1 + 1];

        // final row
        periodic[1 + POSEIDON_ROUNDS] = BE::ONE;

        // Select c from r0, set r0 = 0 => c_val = 0 -> violation
        frame.current_mut()[cols.op_assert] = BE::ONE;
        frame.current_mut()[cols.sel_c_index(0)] = BE::ONE;
        frame.current_mut()[cols.r_index(0)] = BE::ZERO;

        // next row copies registers
        // (not used for assert constraint besides dst)
        // Allocate a sufficiently large buffer
        // for all constraints in this block.
        let mut res = vec![BE::ZERO; 1024];
        let mut ix = 0usize;

        let rc_box = [[BE::ZERO; 12]; POSEIDON_ROUNDS];
        let mds_box = {
            let mut m = [[BE::ZERO; 12]; 12];
            for (i, row) in m.iter_mut().enumerate() {
                row[i] = BE::ONE;
            }

            m
        };
        let rc3_box = [[BE::ZERO; 3]; POSEIDON_ROUNDS];
        let mds3_box = [[BE::ZERO; 3]; 3];
        let w_enc0_box = [BE::ZERO; 59];
        let w_enc1_box = [BE::ZERO; 59];

        let ctx = &AirSharedContext {
            pub_inputs: Default::default(),
            cols,
            features: Default::default(),
            poseidon_rc: rc_box,
            poseidon_mds: mds_box,
            poseidon_dom: [BE::ZERO; 2],
            rom_rc: rc3_box,
            rom_mds: mds3_box,
            rom_w_enc0: w_enc0_box,
            rom_w_enc1: w_enc1_box,
            rom_s_initial: [BE::ZERO; 3],
            rom_s_final: [BE::ZERO; 3],
            pc_init: BE::ZERO,
            program_fe: [BE::ZERO; 2],
            main_args: Vec::new(),
            vm_usage_mask: 1 << VM_USAGE_ASSERT,
            ram_delta_clk_bits: 0,
        };

        VmAluAir::eval_block(ctx, &frame, &periodic, &mut res, &mut ix);

        assert!(res.iter().any(|v| *v != BE::ZERO));
    }
}

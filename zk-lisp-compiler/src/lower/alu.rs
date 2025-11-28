// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

use crate::builder::Op;
use crate::lower::ctx::LowerCtx;
use crate::lower::{Ast, RVal};
use crate::{Error, lower};

pub fn lower_safe_add(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    cx.with_ctx("safe-add", |cx| {
        if rest.len() != 2 {
            return Err(Error::InvalidForm("safe-add".into()));
        }

        let av = lower::lower_expr(cx, rest[0].clone())?;
        let bv = lower::lower_expr(cx, rest[1].clone())?;

        if let (Some(ai), Some(bi)) = (av.as_imm(), bv.as_imm()) {
            let sum = ai as u128 + bi as u128;
            if sum <= u64::MAX as u128 {
                return Ok(RVal::Imm(sum as u64));
            }
        }

        let a = av.into_owned(cx)?;
        let b = bv.into_owned(cx)?;

        // inputs in u64
        let a_r = cx.val_reg(&a)?;
        let b_r = cx.val_reg(&b)?;

        assert_range_bits_for_reg(cx, a_r, 64)?;
        assert_range_bits_for_reg(cx, b_r, 64)?;

        // Reuse the left operand register as destination
        let dst = a_r;
        cx.builder.push(Op::Add {
            dst,
            a: a_r,
            b: b_r,
        });

        // result in u64
        assert_range_bits_for_reg(cx, dst, 64)?;

        // The destination register is `a_r`;
        // only free `b`.
        lower::free_if_owned(cx, b);

        Ok(RVal::Owned(dst))
    })
}

pub fn lower_safe_sub(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    cx.with_ctx("safe-sub", |cx| {
        if rest.len() != 2 {
            return Err(Error::InvalidForm("safe-sub".into()));
        }

        let av = lower::lower_expr(cx, rest[0].clone())?;
        let bv = lower::lower_expr(cx, rest[1].clone())?;

        if let (Some(ai), Some(bi)) = (av.as_imm(), bv.as_imm()) {
            if ai >= bi {
                return Ok(RVal::Imm(ai - bi));
            }
        }

        let a = av.into_owned(cx)?;
        let b = bv.into_owned(cx)?;

        // inputs in u64
        let a_r = cx.val_reg(&a)?;
        let b_r = cx.val_reg(&b)?;

        assert_range_bits_for_reg(cx, a_r, 64)?;
        assert_range_bits_for_reg(cx, b_r, 64)?;

        let dst = a_r;
        cx.builder.push(Op::Sub {
            dst,
            a: a_r,
            b: b_r,
        });

        // no wrap-around:
        // enforce result in u64
        assert_range_bits_for_reg(cx, dst, 64)?;

        // Only free the non-destination temp
        lower::free_if_owned(cx, b);

        Ok(RVal::Owned(dst))
    })
}

pub fn lower_safe_mul(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    cx.with_ctx("safe-mul", |cx| {
        if rest.len() != 2 {
            return Err(Error::InvalidForm("safe-mul".into()));
        }

        let av = lower::lower_expr(cx, rest[0].clone())?;
        let bv = lower::lower_expr(cx, rest[1].clone())?;

        if let (Some(ai), Some(bi)) = (av.as_imm(), bv.as_imm()) {
            let prod = (ai as u128) * (bi as u128);
            if prod <= u64::MAX as u128 {
                return Ok(RVal::Imm(prod as u64));
            }
        }

        let a = av.into_owned(cx)?;
        let b = bv.into_owned(cx)?;

        // Use 32x32->64 safe policy
        let a_r = cx.val_reg(&a)?;
        let b_r = cx.val_reg(&b)?;

        assert_range_bits_for_reg(cx, a_r, 32)?;
        assert_range_bits_for_reg(cx, b_r, 32)?;

        let dst = a_r;
        cx.builder.push(Op::Mul {
            dst,
            a: a_r,
            b: b_r,
        });

        assert_range_bits_for_reg(cx, dst, 64)?;

        lower::free_if_owned(cx, b);

        Ok(RVal::Owned(dst))
    })
}

// (divmod-q a b) -> floor(a/b)
pub fn lower_divmod_q(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    cx.with_ctx("divmod-q", |cx| {
        if rest.len() != 2 {
            return Err(Error::InvalidForm("divmod-q".into()));
        }

        let av = lower::lower_expr(cx, rest[0].clone())?;
        let bv = lower::lower_expr(cx, rest[1].clone())?;

        let a = av.into_owned(cx)?;
        let b = bv.into_owned(cx)?;

        // Enforce inputs in u64
        let a_r = cx.val_reg(&a)?;
        let b_r = cx.val_reg(&b)?;

        assert_range_bits_for_reg(cx, a_r, 64)?;
        assert_range_bits_for_reg(cx, b_r, 64)?;

        // Enforce b != 0
        let zero_b = cx.alloc()?;
        cx.builder.push(Op::Const {
            dst: zero_b,
            imm: 0,
        });

        let eq_b0 = cx.alloc()?;
        cx.builder.push(Op::Eq {
            dst: eq_b0,
            a: b_r,
            b: zero_b,
        });

        cx.free_reg(zero_b);

        let one_b = cx.alloc()?;
        cx.builder.push(Op::Const { dst: one_b, imm: 1 });

        let cond_b = cx.alloc()?;
        cx.builder.push(Op::Sub {
            dst: cond_b,
            a: one_b,
            b: eq_b0,
        });

        cx.free_reg(one_b);

        let assert_b_nz = cx.alloc()?;
        cx.builder.push(Op::Assert {
            dst: assert_b_nz,
            c: cond_b,
        });

        cx.free_reg(eq_b0);
        cx.free_reg(cond_b);
        cx.free_reg(assert_b_nz);

        // produce q,r in two regs
        let rq = cx.alloc()?;
        let rr = cx.alloc()?;
        cx.builder.push(Op::DivMod {
            dst_q: rq,
            dst_r: rr,
            a: a_r,
            b: b_r,
        });

        // r = a - q*b
        let qmulb = cx.alloc()?;
        cx.builder.push(Op::Mul {
            dst: qmulb,
            a: rq,
            b: b_r,
        });

        // Range constraints on remainder
        assert_range_bits_for_reg(cx, rr, 64)?;

        // Enforce a = b*q + r first,
        // while qmulb is alive.
        let sum1 = cx.alloc()?;
        cx.builder.push(Op::Add {
            dst: sum1,
            a: qmulb,
            b: rr,
        });

        let eq = cx.alloc()?;
        cx.builder.push(Op::Eq {
            dst: eq,
            a: sum1,
            b: a_r,
        });

        let assert_eq = cx.alloc()?;
        cx.builder.push(Op::Assert {
            dst: assert_eq,
            c: eq,
        });

        // Free equality temps and qmulb
        cx.free_reg(sum1);
        cx.free_reg(eq);
        cx.free_reg(assert_eq);
        cx.free_reg(qmulb);

        // Enforce r < b via t = b - r;
        // t in u64 and t != 0
        let t = cx.alloc()?;
        cx.builder.push(Op::Sub {
            dst: t,
            a: b_r,
            b: rr,
        });

        assert_range_bits_for_reg(cx, t, 64)?;

        // Assert t != 0 with minimal live regs
        let zero = cx.alloc()?;
        cx.builder.push(Op::Const { dst: zero, imm: 0 });

        let eq_t0 = cx.alloc()?;
        cx.builder.push(Op::Eq {
            dst: eq_t0,
            a: t,
            b: zero,
        });

        cx.free_reg(zero);

        let one = cx.alloc()?;
        cx.builder.push(Op::Const { dst: one, imm: 1 });

        let cond = cx.alloc()?;
        cx.builder.push(Op::Sub {
            dst: cond,
            a: one,
            b: eq_t0,
        });

        cx.free_reg(one);

        let assert_ok = cx.alloc()?;
        cx.builder.push(Op::Assert {
            dst: assert_ok,
            c: cond,
        });

        // Free temps (keep rq; drop rr)
        cx.free_reg(eq_t0);
        cx.free_reg(cond);
        cx.free_reg(assert_ok);
        cx.free_reg(rr);
        cx.free_reg(t);

        // Free inputs if owned locally
        lower::free_if_owned(cx, a);
        lower::free_if_owned(cx, b);

        Ok(RVal::Owned(rq))
    })
}

// (divmod-r a b) -> a % b
pub fn lower_divmod_r(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    cx.with_ctx("divmod-r", |cx| {
        if rest.len() != 2 {
            return Err(Error::InvalidForm("divmod-r".into()));
        }

        let av = lower::lower_expr(cx, rest[0].clone())?;
        let bv = lower::lower_expr(cx, rest[1].clone())?;

        let a = av.into_owned(cx)?;
        let b = bv.into_owned(cx)?;

        // Enforce inputs in u64
        let a_r = cx.val_reg(&a)?;
        let b_r = cx.val_reg(&b)?;

        assert_range_bits_for_reg(cx, a_r, 64)?;
        assert_range_bits_for_reg(cx, b_r, 64)?;

        // Enforce b != 0
        let zero_b = cx.alloc()?;
        cx.builder.push(Op::Const {
            dst: zero_b,
            imm: 0,
        });

        let eq_b0 = cx.alloc()?;
        cx.builder.push(Op::Eq {
            dst: eq_b0,
            a: b_r,
            b: zero_b,
        });

        cx.free_reg(zero_b);

        let one_b = cx.alloc()?;
        cx.builder.push(Op::Const { dst: one_b, imm: 1 });

        let cond_b = cx.alloc()?;
        cx.builder.push(Op::Sub {
            dst: cond_b,
            a: one_b,
            b: eq_b0,
        });

        cx.free_reg(one_b);

        let assert_b_nz = cx.alloc()?;
        cx.builder.push(Op::Assert {
            dst: assert_b_nz,
            c: cond_b,
        });

        cx.free_reg(eq_b0);
        cx.free_reg(cond_b);
        cx.free_reg(assert_b_nz);

        // produce q,r in two regs
        let rq = cx.alloc()?;
        let rr = cx.alloc()?;
        cx.builder.push(Op::DivMod {
            dst_q: rq,
            dst_r: rr,
            a: a_r,
            b: b_r,
        });

        let qmulb = cx.alloc()?;
        cx.builder.push(Op::Mul {
            dst: qmulb,
            a: rq,
            b: b_r,
        });

        // Range constraints and r < b
        assert_range_bits_for_reg(cx, rr, 64)?;

        // Enforce a = b*q + r first (mulb is alive)
        let sum1 = cx.alloc()?;
        cx.builder.push(Op::Add {
            dst: sum1,
            a: qmulb,
            b: rr,
        });

        let eq = cx.alloc()?;
        cx.builder.push(Op::Eq {
            dst: eq,
            a: sum1,
            b: a_r,
        });

        let assert_eq = cx.alloc()?;
        cx.builder.push(Op::Assert {
            dst: assert_eq,
            c: eq,
        });

        cx.free_reg(sum1);
        cx.free_reg(eq);
        cx.free_reg(assert_eq);
        cx.free_reg(qmulb);

        let t = cx.alloc()?;
        cx.builder.push(Op::Sub {
            dst: t,
            a: b_r,
            b: rr,
        });

        assert_range_bits_for_reg(cx, t, 64)?;

        let zero = cx.alloc()?;
        cx.builder.push(Op::Const { dst: zero, imm: 0 });

        let eq_t0 = cx.alloc()?;
        cx.builder.push(Op::Eq {
            dst: eq_t0,
            a: t,
            b: zero,
        });

        cx.free_reg(zero);

        let one = cx.alloc()?;
        cx.builder.push(Op::Const { dst: one, imm: 1 });

        let cond = cx.alloc()?;
        cx.builder.push(Op::Sub {
            dst: cond,
            a: one,
            b: eq_t0,
        });

        cx.free_reg(one);

        let assert_ok = cx.alloc()?;
        cx.builder.push(Op::Assert {
            dst: assert_ok,
            c: cond,
        });

        // Free temps (keep rr)
        cx.free_reg(eq_t0);
        cx.free_reg(cond);
        cx.free_reg(assert_ok);
        cx.free_reg(t);

        // Free inputs and q
        cx.free_reg(rq);

        lower::free_if_owned(cx, a);
        lower::free_if_owned(cx, b);

        Ok(RVal::Owned(rr))
    })
}

// (mulwide-hi a b) -> upper 64 bits of a*b
pub fn lower_mulwide_hi(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    cx.with_ctx("mulwide-hi", |cx| {
        if rest.len() != 2 {
            return Err(Error::InvalidForm("mulwide-hi".into()));
        }

        let av = lower::lower_expr(cx, rest[0].clone())?;
        let bv = lower::lower_expr(cx, rest[1].clone())?;

        let a = av.into_owned(cx)?;
        let b = bv.into_owned(cx)?;

        // inputs in u64
        let a_r = cx.val_reg(&a)?;
        let b_r = cx.val_reg(&b)?;

        assert_range_bits_for_reg(cx, a_r, 64)?;
        assert_range_bits_for_reg(cx, b_r, 64)?;

        // produce hi/lo in two regs
        let rhi = cx.alloc()?;
        let rlo = cx.alloc()?;

        cx.builder.push(Op::MulWide {
            dst_hi: rhi,
            dst_lo: rlo,
            a: a_r,
            b: b_r,
        });

        lower::free_if_owned(cx, a);
        lower::free_if_owned(cx, b);

        // outputs in u64
        assert_range_bits_for_reg(cx, rhi, 64)?;
        assert_range_bits_for_reg(cx, rlo, 64)?;

        cx.free_reg(rlo);

        Ok(RVal::Owned(rhi))
    })
}

// (mulwide-lo a b) -> lower 64 bits of a*b
pub fn lower_mulwide_lo(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    cx.with_ctx("mulwide-lo", |cx| {
        if rest.len() != 2 {
            return Err(Error::InvalidForm("mulwide-lo".into()));
        }

        let av = lower::lower_expr(cx, rest[0].clone())?;
        let bv = lower::lower_expr(cx, rest[1].clone())?;

        let a = av.into_owned(cx)?;
        let b = bv.into_owned(cx)?;

        // inputs in u64
        let a_r = cx.val_reg(&a)?;
        let b_r = cx.val_reg(&b)?;

        assert_range_bits_for_reg(cx, a_r, 64)?;
        assert_range_bits_for_reg(cx, b_r, 64)?;

        // produce hi/lo in two regs
        let rhi = cx.alloc()?;
        let rlo = cx.alloc()?;

        cx.builder.push(Op::MulWide {
            dst_hi: rhi,
            dst_lo: rlo,
            a: a_r,
            b: b_r,
        });

        lower::free_if_owned(cx, a);
        lower::free_if_owned(cx, b);

        // outputs in u64
        assert_range_bits_for_reg(cx, rhi, 64)?;
        assert_range_bits_for_reg(cx, rlo, 64)?;

        cx.free_reg(rhi);

        Ok(RVal::Owned(rlo))
    })
}

// (muldiv a b c) -> floor((a*b)/c)
pub fn lower_muldiv_floor(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    cx.with_ctx("muldiv", |cx| {
        if rest.len() != 3 {
            return Err(Error::InvalidForm("muldiv".into()));
        }

        let av = lower::lower_expr(cx, rest[0].clone())?;
        let bv = lower::lower_expr(cx, rest[1].clone())?;
        let cv = lower::lower_expr(cx, rest[2].clone())?;

        let a = av.into_owned(cx)?;
        let b = bv.into_owned(cx)?;
        let c = cv.into_owned(cx)?;

        // Enforce inputs in u64
        let a_r = cx.val_reg(&a)?;
        let b_r = cx.val_reg(&b)?;
        let c_r = cx.val_reg(&c)?;

        assert_range_bits_for_reg(cx, a_r, 64)?;
        assert_range_bits_for_reg(cx, b_r, 64)?;
        assert_range_bits_for_reg(cx, c_r, 64)?;

        // Wide multiply
        let rhi = cx.alloc()?;
        let rlo = cx.alloc()?;
        cx.builder.push(Op::MulWide {
            dst_hi: rhi,
            dst_lo: rlo,
            a: a_r,
            b: b_r,
        });

        lower::free_if_owned(cx, a);
        lower::free_if_owned(cx, b);

        // 128/64 division -> q,r
        let rq = cx.alloc()?;
        let rr = cx.alloc()?;
        cx.builder.push(Op::DivMod128 {
            a_hi: rhi,
            a_lo: rlo,
            b: c_r,
            dst_q: rq,
            dst_r: rr,
        });

        // Outputs in u64
        assert_range_bits_for_reg(cx, rq, 64)?;
        assert_range_bits_for_reg(cx, rr, 64)?;

        lower::free_if_owned(cx, c);

        cx.free_reg(rhi);
        cx.free_reg(rlo);
        cx.free_reg(rr);

        Ok(RVal::Owned(rq))
    })
}

fn assert_range_bits_for_reg(cx: &mut LowerCtx, r: u8, bits: u8) -> Result<(), Error> {
    cx.with_ctx("assert-range-bits", |cx| {
        match bits {
            32 => {
                let dst = cx.alloc()?;
                cx.builder.push(Op::AssertRange { dst, r, bits: 32 });

                cx.free_reg(dst);
            }
            64 => {
                let dst = cx.alloc()?;
                cx.builder.push(Op::AssertRangeLo { dst, r });
                cx.builder.push(Op::AssertRangeHi { dst, r });

                cx.free_reg(dst);
            }
            _ => {
                return Err(Error::InvalidForm(
                    "assert-range: bits must be 32 or 64".into(),
                ));
            }
        }

        Ok(())
    })
}

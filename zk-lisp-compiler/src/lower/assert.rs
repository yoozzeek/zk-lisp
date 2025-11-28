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
use crate::lower::{Ast, Atom, RVal};
use crate::{Error, lower};

pub fn lower_assert(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 1 {
        return Err(Error::InvalidForm("assert".into()));
    }

    let c = lower::lower_expr(cx, rest[0].clone())?;

    if let Some(cv) = c.as_imm() {
        return if cv == 1 {
            Ok(RVal::Imm(1))
        } else {
            Err(Error::InvalidForm("assert: constant false".into()))
        };
    }

    let c = c.into_owned(cx)?;
    let dst = cx.alloc()?;

    cx.builder.push(Op::Assert {
        dst,
        c: cx.val_reg(&c)?,
    });
    lower::free_if_owned(cx, c);

    Ok(RVal::Owned(dst))
}

// (assert-bit x) -> assert(x in {0,1}) and return 1
pub fn lower_assert_bit(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 1 {
        return Err(Error::InvalidForm("assert-bit".into()));
    }

    let x = lower::lower_expr(cx, rest[0].clone())?;
    if let Some(v) = x.as_imm() {
        return if v == 0 || v == 1 {
            Ok(RVal::Imm(1))
        } else {
            Err(Error::InvalidForm("assert-bit: constant not a bit".into()))
        };
    }

    let x = x.into_owned(cx)?;
    let dst = cx.alloc()?;

    cx.builder.push(Op::AssertBit {
        dst,
        r: cx.val_reg(&x)?,
    });

    lower::free_if_owned(cx, x);

    Ok(RVal::Owned(dst))
}

pub fn lower_assert_range(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 2 {
        return Err(Error::InvalidForm("assert-range".into()));
    }

    // parse bits
    let bits = match &rest[1] {
        Ast::Atom(Atom::Int(v)) => *v,
        _ => {
            return Err(Error::InvalidForm(
                "assert-range: bits must be integer".into(),
            ));
        }
    };

    let x = lower::lower_expr(cx, rest[0].clone())?;

    if bits == 32 {
        if let Some(v) = x.as_imm() {
            let limit = 1u128 << 32;
            return if (v as u128) < limit {
                Ok(RVal::Imm(1))
            } else {
                Err(Error::InvalidForm(
                    "assert-range: constant out of range".into(),
                ))
            };
        }

        let x = x.into_owned(cx)?;
        let dst = cx.alloc()?;

        cx.builder.push(Op::AssertRange {
            dst,
            r: cx.val_reg(&x)?,
            bits: 32,
        });

        lower::free_if_owned(cx, x);

        Ok(RVal::Owned(dst))
    } else if bits == 64 {
        // Lo then Hi
        if let Some(_v) = x.as_imm() {
            // compile-time: 0 <= v < 2^64 for u64
            return Ok(RVal::Imm(1));
        }

        let x = x.into_owned(cx)?;
        let dst = cx.alloc()?;

        cx.builder.push(Op::AssertRangeLo {
            dst,
            r: cx.val_reg(&x)?,
        });
        cx.builder.push(Op::AssertRangeHi {
            dst,
            r: cx.val_reg(&x)?,
        });

        lower::free_if_owned(cx, x);

        return Ok(RVal::Owned(dst));
    } else {
        return Err(Error::InvalidForm(
            "assert-range: bits must be 32 or 64".into(),
        ));
    }
}

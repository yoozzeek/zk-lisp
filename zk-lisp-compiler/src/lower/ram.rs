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
use crate::lower::{Ast, Atom, RVal, STACK_BASE};
use crate::{Error, lower};

// (push x): store x at [STACK_BASE + SP];
// SP = SP + 1; returns 0
pub fn lower_push(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 1 {
        return Err(Error::InvalidForm("push".into()));
    }

    let v = lower::lower_expr(cx, rest[0].clone())?;
    let v = v.into_owned(cx)?;

    // base = STACK_BASE
    let r_base = cx.alloc()?;
    cx.builder.push(Op::Const {
        dst: r_base,
        imm: STACK_BASE,
    });

    // addr = base + SP
    let r_addr = cx.alloc()?;
    let sp = ensure_sp(cx)?;

    cx.builder.push(Op::Add {
        dst: r_addr,
        a: r_base,
        b: sp,
    });

    // Mem[addr] <- v
    cx.builder.push(Op::Store {
        addr: r_addr,
        src: cx.val_reg(&v)?,
    });

    cx.free_reg(r_addr);
    cx.free_reg(r_base);

    lower::free_if_owned(cx, v);

    // SP = SP + 1
    let r_one = cx.alloc()?;
    cx.builder.push(Op::Const { dst: r_one, imm: 1 });

    let sp = ensure_sp(cx)?;
    cx.builder.push(Op::Add {
        dst: sp,
        a: sp,
        b: r_one,
    });

    cx.free_reg(r_one);

    Ok(RVal::Imm(0))
}

// (pop): SP = SP - 1;
// return Mem[STACK_BASE + SP]
pub fn lower_pop(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if !rest.is_empty() {
        return Err(Error::InvalidForm("pop".into()));
    }

    // SP = SP - 1
    let r_one = cx.alloc()?;
    cx.builder.push(Op::Const { dst: r_one, imm: 1 });

    let sp = ensure_sp(cx)?;
    cx.builder.push(Op::Sub {
        dst: sp,
        a: sp,
        b: r_one,
    });

    cx.free_reg(r_one);

    // addr = STACK_BASE + SP
    let r_base = cx.alloc()?;
    cx.builder.push(Op::Const {
        dst: r_base,
        imm: STACK_BASE,
    });

    let r_addr = cx.alloc()?;
    let sp = ensure_sp(cx)?;

    cx.builder.push(Op::Add {
        dst: r_addr,
        a: r_base,
        b: sp,
    });

    // dst <- Mem[addr]
    let r_dst = cx.alloc()?;
    cx.builder.push(Op::Load {
        dst: r_dst,
        addr: r_addr,
    });

    cx.free_reg(r_addr);
    cx.free_reg(r_base);

    Ok(RVal::Owned(r_dst))
}

// (push* a b c ...) =>
// (begin (push a) (push b) (push c) ...)
pub fn lower_push_star(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.is_empty() {
        return Ok(RVal::Imm(0));
    }

    for it in rest {
        let _ = lower_push(cx, core::slice::from_ref(it))?;
        // lower_push already returns
        // 0 and frees its temps
    }

    Ok(RVal::Imm(0))
}

// (pop* n) => pop N times
// return last value
pub fn lower_pop_star(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 1 {
        return Err(Error::InvalidForm("pop*".into()));
    }

    // require compile-time
    // integer literal for N.
    let n = match &rest[0] {
        Ast::Atom(Atom::Int(v)) => *v as usize,
        _ => {
            return Err(Error::InvalidForm(
                "pop*: count must be integer literal".into(),
            ));
        }
    };

    if n == 0 {
        return Err(Error::InvalidForm("pop*: count must be >= 1".into()));
    }

    let mut last: Option<RVal> = None;
    for _ in 0..n {
        let v = lower_pop(cx, &[])?;
        if let Some(prev) = last.take() {
            lower::free_if_owned(cx, prev);
        }

        last = Some(v);
    }

    Ok(last.unwrap())
}

// Ensure SP exists and is initialized once
fn ensure_sp(cx: &mut LowerCtx) -> Result<u8, Error> {
    if let Some(r) = cx.sp_reg {
        return Ok(r);
    }

    let r = cx.alloc()?;
    cx.builder.push(Op::Const { dst: r, imm: 0 });
    cx.sp_reg = Some(r);

    Ok(r)
}

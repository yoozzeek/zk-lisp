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

pub fn lower_if(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 3 {
        return Err(Error::InvalidForm("if".into()));
    }

    let c = lower::lower_expr(cx, rest[0].clone())?;
    let t = lower::lower_expr(cx, rest[1].clone())?;
    let e = lower::lower_expr(cx, rest[2].clone())?;

    if let Some(cv) = c.as_imm() {
        return if cv == 0 {
            lower::free_if_owned(cx, t);
            Ok(e)
        } else if cv == 1 {
            lower::free_if_owned(cx, e);
            Ok(t)
        } else {
            Err(Error::InvalidForm("if: cond must be boolean (0/1)".into()))
        };
    }

    let c = c.into_owned(cx)?;
    let t = t.into_owned(cx)?;
    let e = e.into_owned(cx)?;

    let dst = cx.alloc()?;

    cx.builder.push(Op::Select {
        dst,
        c: cx.val_reg(&c)?,
        a: cx.val_reg(&t)?,
        b: cx.val_reg(&e)?,
    });

    lower::free_if_owned(cx, c);
    lower::free_if_owned(cx, t);
    lower::free_if_owned(cx, e);

    Ok(RVal::Owned(dst))
}

pub fn lower_when(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    // (when cond body1 body2 ...)
    cx.with_ctx("when", |cx| {
        if rest.len() < 2 {
            return Err(Error::InvalidForm("when: expected cond and body".into()));
        }

        let cond_ast = rest[0].clone();
        let body_forms = &rest[1..];
        let body_ast = lower::implicit_begin(body_forms);

        let expanded = Ast::List(vec![
            Ast::Atom(Atom::Sym("if".to_string())),
            cond_ast,
            body_ast,
            Ast::Atom(Atom::Int(0)),
        ]);

        lower::lower_expr(cx, expanded)
    })
}

pub fn lower_eq(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 2 {
        return Err(Error::InvalidForm("=".into()));
    }

    let a = lower::lower_expr(cx, rest[0].clone())?;
    let b = lower::lower_expr(cx, rest[1].clone())?;

    if let (Some(ai), Some(bi)) = (a.as_imm(), b.as_imm()) {
        return Ok(RVal::Imm(if ai == bi { 1 } else { 0 }));
    }

    let a = a.into_owned(cx)?;
    let b = b.into_owned(cx)?;

    let dst = cx.alloc()?;

    cx.builder.push(Op::Eq {
        dst,
        a: cx.val_reg(&a)?,
        b: cx.val_reg(&b)?,
    });

    lower::free_if_owned(cx, a);
    lower::free_if_owned(cx, b);

    Ok(RVal::Owned(dst))
}

pub fn lower_neg(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 1 {
        return Err(Error::InvalidForm("neg".into()));
    }

    let a = lower::lower_expr(cx, rest[0].clone())?;

    if let Some(ai) = a.as_imm() {
        // In the field, -ai is p - ai;
        // since p >> 2^64, the only case
        // that remains in [0, 2^64) is ai == 0.
        if ai == 0 {
            return Ok(RVal::Imm(0));
        }
    }

    let a = a.into_owned(cx)?;

    // Safe reuse
    let dst = match a {
        RVal::Owned(r) => r,
        _ => cx.alloc()?,
    };

    cx.builder.push(Op::Neg {
        dst,
        a: cx.val_reg(&a)?,
    });

    // reused 'a' remains
    // owned as result
    if let RVal::Owned(_) = a {
        // keep
    } else {
        lower::free_if_owned(cx, a);
    }

    Ok(RVal::Owned(dst))
}

pub fn lower_in_set(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    // (in-set x (s1 s2 ...)) -> assert(prod(x - si) == 0)
    if rest.len() != 2 {
        return Err(Error::InvalidForm("in-set".into()));
    }

    let x = lower::lower_expr(cx, rest[0].clone())?;
    let x = x.into_owned(cx)?;

    let set_list = match &rest[1] {
        Ast::List(items) => items.clone(),
        _ => return Err(Error::InvalidForm("in-set: expects list".into())),
    };

    if set_list.is_empty() {
        return Err(Error::InvalidForm("in-set: empty set".into()));
    }

    // Build product
    let mut r_prod: Option<u8> = None;

    for it in set_list.into_iter() {
        let si = lower::lower_expr(cx, it)?;
        let si = si.into_owned(cx)?;

        let r_diff = cx.alloc()?;

        cx.builder.push(Op::Sub {
            dst: r_diff,
            a: cx.val_reg(&x)?,
            b: cx.val_reg(&si)?,
        });

        lower::free_if_owned(cx, si);

        r_prod = Some(match r_prod.take() {
            None => r_diff,
            Some(prev) => {
                let r_mul = cx.alloc()?;

                cx.builder.push(Op::Mul {
                    dst: r_mul,
                    a: prev,
                    b: r_diff,
                });

                cx.free_reg(prev);
                cx.free_reg(r_diff);

                r_mul
            }
        });
    }

    let r_zero = cx.alloc()?;

    cx.builder.push(Op::Const {
        dst: r_zero,
        imm: 0,
    });

    let prev = r_prod.unwrap();
    let r_eq = cx.alloc()?;

    cx.builder.push(Op::Eq {
        dst: r_eq,
        a: prev,
        b: r_zero,
    });

    cx.free_reg(r_zero);
    cx.free_reg(prev);

    let r_out = cx.alloc()?;

    cx.builder.push(Op::Assert {
        dst: r_out,
        c: r_eq,
    });

    cx.free_reg(r_eq);

    // do not free x if
    // it was borrowed.
    if let RVal::Owned(rx) = x {
        cx.free_reg(rx);
    }

    Ok(RVal::Owned(r_out))
}

pub fn lower_select(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 3 {
        return Err(Error::InvalidForm("select".into()));
    }

    let c = lower::lower_expr(cx, rest[0].clone())?;
    let a = lower::lower_expr(cx, rest[1].clone())?;
    let b = lower::lower_expr(cx, rest[2].clone())?;

    // Constant fold when
    // condition is immediate 0/1
    if let Some(cv) = c.as_imm() {
        if cv == 0 {
            lower::free_if_owned(cx, a);
            return Ok(b);
        } else if cv == 1 {
            lower::free_if_owned(cx, b);
            return Ok(a);
        } else {
            return Err(Error::InvalidForm(
                "select: cond must be boolean (0/1)".into(),
            ));
        }
    }

    let c = c.into_owned(cx)?;
    let a = a.into_owned(cx)?;
    let b = b.into_owned(cx)?;

    let dst = cx.alloc()?;

    cx.builder.push(Op::Select {
        dst,
        c: cx.val_reg(&c)?,
        a: cx.val_reg(&a)?,
        b: cx.val_reg(&b)?,
    });

    // free temps (keep dst)
    lower::free_if_owned(cx, c);
    lower::free_if_owned(cx, a);
    lower::free_if_owned(cx, b);

    Ok(RVal::Owned(dst))
}

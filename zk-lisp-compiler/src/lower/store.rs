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

pub fn lower_load(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 1 {
        return Err(Error::InvalidForm("load".into()));
    }

    let addr = lower::lower_expr(cx, rest[0].clone())?;
    let addr = addr.into_owned(cx)?;
    let dst = cx.alloc()?;

    cx.builder.push(Op::Load {
        dst,
        addr: cx.val_reg(&addr)?,
    });

    // free temp address
    lower::free_if_owned(cx, addr);

    Ok(RVal::Owned(dst))
}

pub fn lower_store(cx: &mut LowerCtx, rest: &[Ast]) -> Result<(), Error> {
    if rest.len() != 2 {
        return Err(Error::InvalidForm("store".into()));
    }

    let addr_v = lower::lower_expr(cx, rest[0].clone())?;
    let val_v = lower::lower_expr(cx, rest[1].clone())?;

    // Materialize immediates only
    let addr_v = match addr_v {
        RVal::Imm(_) => addr_v.into_owned(cx)?,
        other => other,
    };
    let val_v = match val_v {
        RVal::Imm(_) => val_v.into_owned(cx)?,
        other => other,
    };

    let addr_reg = cx.val_reg(&addr_v)?;
    let val_reg = cx.val_reg(&val_v)?;

    cx.builder.push(Op::Store {
        addr: addr_reg,
        src: val_reg,
    });

    // Free only Owned temps;
    // borrowed regs stay live for their callers.
    lower::free_if_owned(cx, addr_v);
    lower::free_if_owned(cx, val_v);

    Ok(())
}

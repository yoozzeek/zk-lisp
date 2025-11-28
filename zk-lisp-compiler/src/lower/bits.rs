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

// (bit? x) -> 1 if x in {0,1}, else 0
pub fn lower_bit_pred(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 1 {
        return Err(Error::InvalidForm("bit?".into()));
    }

    let x = lower::lower_expr(cx, rest[0].clone())?;

    // If immediate, compute directly
    if let Some(xi) = x.as_imm() {
        return Ok(RVal::Imm(if xi == 0 || xi == 1 { 1 } else { 0 }));
    }

    // t = x * (x - 1)
    let x = x.into_owned(cx)?;
    let one = {
        let r = cx.alloc()?;
        cx.builder.push(Op::Const { dst: r, imm: 1 });

        r
    };
    let xm1 = {
        let r = cx.alloc()?;
        cx.builder.push(Op::Sub {
            dst: r,
            a: cx.val_reg(&x)?,
            b: one,
        });

        r
    };
    let t = {
        let r = cx.alloc()?;
        cx.builder.push(Op::Mul {
            dst: r,
            a: cx.val_reg(&x)?,
            b: xm1,
        });

        r
    };

    // eq = (t == 0)
    let z = {
        let r = cx.alloc()?;
        cx.builder.push(Op::Const { dst: r, imm: 0 });

        r
    };
    let eq = {
        let r = cx.alloc()?;
        cx.builder.push(Op::Eq { dst: r, a: t, b: z });

        r
    };

    // free temps
    cx.free_reg(one);
    cx.free_reg(xm1);
    cx.free_reg(t);
    cx.free_reg(z);

    Ok(RVal::Owned(eq))
}

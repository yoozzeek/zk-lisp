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

pub fn lower_hash2(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 2 {
        return Err(Error::InvalidForm("hash2".into()));
    }

    let a = lower::lower_expr(cx, rest[0].clone())?;
    let b = lower::lower_expr(cx, rest[1].clone())?;

    // Only materialize immediates;
    // borrowed regs can be used directly
    let a = if a.as_imm().is_some() {
        a.into_owned(cx)?
    } else {
        a
    };
    let b = if b.as_imm().is_some() {
        b.into_owned(cx)?
    } else {
        b
    };

    // Lower to SAbsorbN(2) + SSqueeze
    cx.builder.push(Op::SAbsorbN {
        regs: vec![cx.val_reg(&a)?, cx.val_reg(&b)?],
    });

    let dst = cx.alloc()?;

    cx.builder.push(Op::SSqueeze { dst });

    lower::free_if_owned(cx, a);
    lower::free_if_owned(cx, b);

    Ok(RVal::Owned(dst))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compile_str;

    #[test]
    fn lower_hash2_produces_sponge_ops() {
        let src = "(let ((x 1) (y 2)) (hash2 x y))";
        let p = compile_str(src).unwrap();
        // hash represented via sponge ops SAbsorbN/SSqueeze
        assert!(
            p.ops
                .iter()
                .any(|op| matches!(op, Op::SAbsorbN { .. } | Op::SSqueeze { .. }))
        );
    }
}

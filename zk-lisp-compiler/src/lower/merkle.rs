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

pub fn lower_merkle_verify(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 2 {
        return Err(Error::InvalidForm("merkle-verify".into()));
    }

    let leaf_v = lower::lower_expr(cx, rest[0].clone())?;
    let leaf_v = if leaf_v.as_imm().is_some() {
        leaf_v.into_owned(cx)?
    } else {
        leaf_v
    };
    let leaf_r = cx.val_reg(&leaf_v)?;

    let pairs_ast = match &rest[1] {
        Ast::List(items) => items.clone(),
        _ => return Err(Error::InvalidForm("merkle-verify: path".into())),
    };
    if pairs_ast.is_empty() {
        return Err(Error::InvalidForm("merkle-verify: empty path".into()));
    }

    // First step
    let (dir0_v, sib0_v) = {
        let p = &pairs_ast[0];
        let (d_ast, s_ast) = match p {
            Ast::List(ps) if ps.len() == 2 => (&ps[0], &ps[1]),
            _ => return Err(Error::InvalidForm("merkle-verify: pair".into())),
        };

        let d = lower::lower_expr(cx, d_ast.clone())?;
        let d = d.into_owned(cx)?;

        let s = lower::lower_expr(cx, s_ast.clone())?;
        let s = s.into_owned(cx)?;

        (d, s)
    };

    cx.builder.push(Op::MerkleStepFirst {
        leaf_reg: leaf_r,
        dir_reg: cx.val_reg(&dir0_v)?,
        sib_reg: cx.val_reg(&sib0_v)?,
    });

    // free temps
    lower::free_if_owned(cx, leaf_v);
    lower::free_if_owned(cx, dir0_v);
    lower::free_if_owned(cx, sib0_v);

    // Middle steps
    for p in pairs_ast
        .iter()
        .skip(1)
        .take(pairs_ast.len().saturating_sub(2))
    {
        let (d_ast, s_ast) = match p {
            Ast::List(ps) if ps.len() == 2 => (&ps[0], &ps[1]),
            _ => return Err(Error::InvalidForm("merkle-verify: pair".into())),
        };

        let d = lower::lower_expr(cx, d_ast.clone())?;
        let d = if d.as_imm().is_some() {
            d.into_owned(cx)?
        } else {
            d
        };

        let s = lower::lower_expr(cx, s_ast.clone())?;
        let s = if s.as_imm().is_some() {
            s.into_owned(cx)?
        } else {
            s
        };

        cx.builder.push(Op::MerkleStep {
            dir_reg: cx.val_reg(&d)?,
            sib_reg: cx.val_reg(&s)?,
        });

        lower::free_if_owned(cx, d);
        lower::free_if_owned(cx, s);
    }

    // Last step (if path len >= 2)
    if pairs_ast.len() >= 2 {
        let p_last = pairs_ast.last().unwrap();
        let (d_ast, s_ast) = match p_last {
            Ast::List(ps) if ps.len() == 2 => (&ps[0], &ps[1]),
            _ => return Err(Error::InvalidForm("merkle-verify: pair".into())),
        };

        let d = lower::lower_expr(cx, d_ast.clone())?;
        let d = if d.as_imm().is_some() {
            d.into_owned(cx)?
        } else {
            d
        };

        let s = lower::lower_expr(cx, s_ast.clone())?;
        let s = if s.as_imm().is_some() {
            s.into_owned(cx)?
        } else {
            s
        };

        cx.builder.push(Op::MerkleStepLast {
            dir_reg: cx.val_reg(&d)?,
            sib_reg: cx.val_reg(&s)?,
        });

        lower::free_if_owned(cx, d);
        lower::free_if_owned(cx, s);
    }

    // Return 0 immediate;
    // verification is enforced by AIR.
    Ok(RVal::Imm(0))
}

// Lower (load-ca leaf ((d0 s0) (d1 s1) ...)) -> leaf value;
// Verifies membership by binding
// last-level root to PI via MerkleStepLast.
pub fn lower_load_ca(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 2 {
        return Err(Error::InvalidForm("load-ca".into()));
    }

    let leaf = lower::lower_expr(cx, rest[0].clone())?;
    let leaf = leaf.into_owned(cx)?;

    // list of (dir sib)
    let path_list = match &rest[1] {
        Ast::List(items) => items,
        _ => return Err(Error::InvalidForm("load-ca: path".into())),
    };

    if path_list.is_empty() {
        return Err(Error::InvalidForm("load-ca: empty path".into()));
    }

    // first step
    let (dir0_reg, sib0_reg) = parse_dir_sib_pair(cx, &path_list[0])?;
    cx.builder.push(Op::MerkleStepFirst {
        leaf_reg: cx.val_reg(&leaf)?,
        dir_reg: dir0_reg,
        sib_reg: sib0_reg,
    });

    cx.free_reg(dir0_reg);
    cx.free_reg(sib0_reg);

    for pair in path_list
        .iter()
        .skip(1)
        .take(path_list.len().saturating_sub(2))
    {
        let (dir_r, sib_r) = parse_dir_sib_pair(cx, pair)?;
        cx.builder.push(Op::MerkleStep {
            dir_reg: dir_r,
            sib_reg: sib_r,
        });

        cx.free_reg(dir_r);
        cx.free_reg(sib_r);
    }

    // last step binds
    // acc to PI root
    if path_list.len() > 1 {
        let (dir_l, sib_l) = parse_dir_sib_pair(cx, path_list.last().unwrap())?;
        cx.builder.push(Op::MerkleStepLast {
            dir_reg: dir_l,
            sib_reg: sib_l,
        });

        cx.free_reg(dir_l);
        cx.free_reg(sib_l);
    }

    Ok(leaf)
}

// Lower (store-ca new_leaf ((d0 s0) (d1 s1) ...)) -> 0;
// acc holds new_root.
pub fn lower_store_ca(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 2 {
        return Err(Error::InvalidForm("store-ca".into()));
    }

    let leaf = lower::lower_expr(cx, rest[0].clone())?;
    let leaf = leaf.into_owned(cx)?;

    let path_list = match &rest[1] {
        Ast::List(items) => items,
        _ => return Err(Error::InvalidForm("store-ca: path".into())),
    };

    if path_list.is_empty() {
        return Err(Error::InvalidForm("store-ca: empty path".into()));
    }

    let (dir0_reg, sib0_reg) = parse_dir_sib_pair(cx, &path_list[0])?;
    cx.builder.push(Op::MerkleStepFirst {
        leaf_reg: cx.val_reg(&leaf)?,
        dir_reg: dir0_reg,
        sib_reg: sib0_reg,
    });

    cx.free_reg(dir0_reg);
    cx.free_reg(sib0_reg);

    // rest; no Last at the end
    // to avoid binding to PI root.
    for pair in path_list.iter().skip(1) {
        let (dir_r, sib_r) = parse_dir_sib_pair(cx, pair)?;
        cx.builder.push(Op::MerkleStep {
            dir_reg: dir_r,
            sib_reg: sib_r,
        });

        cx.free_reg(dir_r);
        cx.free_reg(sib_r);
    }

    // free temp leaf
    cx.free_reg(cx.val_reg(&leaf)?);

    Ok(RVal::Imm(0))
}

fn parse_dir_sib_pair(cx: &mut LowerCtx, pair: &Ast) -> Result<(u8, u8), Error> {
    let Ast::List(items) = pair else {
        return Err(Error::InvalidForm("path: pair".into()));
    };

    if items.len() != 2 {
        return Err(Error::InvalidForm("path: pair arity".into()));
    }

    let dir = lower::lower_expr(cx, items[0].clone())?.into_owned(cx)?;
    let sib = lower::lower_expr(cx, items[1].clone())?.into_owned(cx)?;

    Ok((cx.val_reg(&dir)?, cx.val_reg(&sib)?))
}

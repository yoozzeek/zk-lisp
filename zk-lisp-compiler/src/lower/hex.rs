// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

use crate::Error;
use crate::builder::Op;
use crate::lower::ctx::LowerCtx;
use crate::lower::{Ast, Atom, RVal};

pub fn lower_hex_to_bytes32(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    // (hex-to-bytes32 "0x...")
    if rest.len() != 1 {
        return Err(Error::InvalidForm("hex-to-bytes32".into()));
    }

    let s = match &rest[0] {
        Ast::Atom(Atom::Str(st)) => st.clone(),
        _ => {
            return Err(Error::InvalidForm(
                "hex-to-bytes32: expects string literal".into(),
            ));
        }
    };

    let hex_str = s.strip_prefix("0x").unwrap_or(&s);
    let decoded = match hex::decode(hex_str) {
        Ok(b) => b,
        Err(_) => return Err(Error::InvalidForm("hex-to-bytes32: invalid hex".into())),
    };

    if decoded.len() > 32 {
        return Err(Error::InvalidForm("hex-to-bytes32: length > 32".into()));
    }

    // Pad to 32
    let mut buf = [0u8; 32];
    buf[..decoded.len()].copy_from_slice(&decoded);

    // Build chunk commitments
    // from u64 pairs via sponge ops.
    let c_hash = |cx: &mut LowerCtx, lo: u64, hi: u64| -> Result<u8, Error> {
        let r_lo = cx.alloc()?;
        cx.builder.push(Op::Const { dst: r_lo, imm: lo });

        let r_hi = cx.alloc()?;
        cx.builder.push(Op::Const { dst: r_hi, imm: hi });

        cx.builder.push(Op::SAbsorbN {
            regs: vec![r_lo, r_hi],
        });

        let r_c = cx.alloc()?;

        cx.builder.push(Op::SSqueeze { dst: r_c });

        cx.free_reg(r_lo);
        cx.free_reg(r_hi);

        Ok(r_c)
    };

    let (lo0, hi0) = u64_pair_from_le_16(&buf[0..16]);
    let r_c0 = c_hash(cx, lo0, hi0)?;
    let (lo1, hi1) = u64_pair_from_le_16(&buf[16..32]);
    let r_c1 = c_hash(cx, lo1, hi1)?;

    let r_payload = {
        let dst = cx.alloc()?;
        cx.builder.push(Op::SAbsorbN {
            regs: vec![r_c0, r_c1],
        });
        cx.builder.push(Op::SSqueeze { dst });

        cx.free_reg(r_c0);
        cx.free_reg(r_c1);

        dst
    };

    // t0 = H(TAG, L)
    let tag8 = {
        let d = blake3::hash(b"zkl/bytes32");
        let mut t = [0u8; 8];
        t.copy_from_slice(&d.as_bytes()[0..8]);

        u64::from_le_bytes(t)
    };

    let r_tag = cx.alloc()?;
    cx.builder.push(Op::Const {
        dst: r_tag,
        imm: tag8,
    });

    let r_len = cx.alloc()?;
    cx.builder.push(Op::Const {
        dst: r_len,
        imm: decoded.len() as u64,
    });

    let r_t0 = {
        let dst = cx.alloc()?;
        cx.builder.push(Op::SAbsorbN {
            regs: vec![r_tag, r_len],
        });
        cx.builder.push(Op::SSqueeze { dst });

        cx.free_reg(r_tag);
        cx.free_reg(r_len);

        dst
    };

    // digest = H(t0, payload)
    let r_digest = cx.alloc()?;
    cx.builder.push(Op::SAbsorbN {
        regs: vec![r_t0, r_payload],
    });
    cx.builder.push(Op::SSqueeze { dst: r_digest });

    cx.free_reg(r_t0);
    cx.free_reg(r_payload);

    Ok(RVal::Owned(r_digest))
}

fn u64_pair_from_le_16(b16: &[u8]) -> (u64, u64) {
    debug_assert!(b16.len() == 16);

    let mut lo8 = [0u8; 8];
    let mut hi8 = [0u8; 8];
    lo8.copy_from_slice(&b16[0..8]);
    hi8.copy_from_slice(&b16[8..16]);

    (u64::from_le_bytes(lo8), u64::from_le_bytes(hi8))
}

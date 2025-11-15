// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

use zk_lisp_compiler::compile_entry;

#[test]
fn assert_bit_const_false_errors() {
    let src = "(def (main) (assert-bit 2))";
    let err = compile_entry(src, &[]).expect_err("must error");
    let msg = format!("{err}");

    assert!(msg.contains("assert-bit: constant not a bit"));
}

#[test]
fn assert_range_const_oob_errors() {
    let src = "(def (main) (assert-range 4294967296 32))";
    let err = compile_entry(src, &[]).expect_err("must error");
    let msg = format!("{err}");

    assert!(msg.contains("assert-range: constant out of range"));
}

#[test]
fn assert_range_bits_invalid_errors() {
    let src = "(def (main) (assert-range 5 12))";
    let err = compile_entry(src, &[]).expect_err("must error");
    let msg = format!("{err}");

    assert!(msg.contains("assert-range: bits must be 32 or 64"));
}

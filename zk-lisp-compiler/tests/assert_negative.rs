// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use zk_lisp_compiler::compile_str;

#[test]
fn assert_negative_const_false_errors() {
    // assert(false) must be rejected at compile time
    let src = "(let ((a 5) (b 6)) (assert (= a b)))";

    let err = compile_str(src).expect_err("compile must fail");
    let msg = err.to_string();

    assert!(msg.contains("assert: constant false"));
}

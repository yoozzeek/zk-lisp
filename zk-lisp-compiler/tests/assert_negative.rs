// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

use zk_lisp_compiler::compile_str;

#[test]
fn assert_negative_const_false_errors() {
    // assert(false) must be rejected at compile time
    let src = "(let ((a 5) (b 6)) (assert (= a b)))";

    let err = compile_str(src).expect_err("compile must fail");
    let msg = err.to_string();

    assert!(msg.contains("assert: constant false"));
}

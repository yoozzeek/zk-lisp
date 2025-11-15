// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use zk_lisp_compiler::compile_str;

#[test]
fn def_call_wrong_arity_errors() {
    // Wrong number of args in function
    // call must be a compile-time error.
    let src_missing = r"
(def (add2 a b) (+ a b))
(add2 7)";
    let err1 = compile_str(src_missing).expect_err("compile must fail");
    let msg1 = err1.to_string();

    assert!(msg1.contains("expects 2"));

    let src_extra = r"
(def (add2 a b) (+ a b))
(add2 7 8 9)";
    let err2 = compile_str(src_extra).expect_err("compile must fail");
    let msg2 = err2.to_string();

    assert!(msg2.contains("expects 2"));
}

#[test]
fn recursion_direct_errors() {
    // Direct recursion must be detected
    // and rejected at compile time.
    let src = r"
(def (f x) (f x))
(f 1)";
    let err = compile_str(src).expect_err("compile must fail");
    let msg = err.to_string();

    assert!(msg.to_lowercase().contains("recursion"));
}

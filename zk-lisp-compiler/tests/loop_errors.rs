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
fn recur_outside_loop_errors() {
    let src = "(recur 1)";
    let err = compile_str(src).expect_err("compile must fail");
    let msg = err.to_string();

    assert!(msg.contains("recur outside loop"));
}

#[test]
fn loop_max_must_be_literal_int() {
    let src = "(loop :max x ((i 0)) i)";
    let err = compile_str(src).expect_err("compile must fail");
    let msg = err.to_string();

    assert!(msg.contains(":max must be integer literal"));
}

#[test]
fn loop_empty_binding_list_errors() {
    let src = "(loop :max 3 () 42)";
    let err = compile_str(src).expect_err("compile must fail");
    let msg = err.to_string();

    assert!(msg.contains("empty binding list"));
}

#[test]
fn loop_recur_arity_mismatch_errors() {
    let src = "
        (def (main)
          (loop :max 2 ((x 0))
            x
            (recur 1 2)))
        (main)
    ";

    let err = compile_str(src).expect_err("compile must fail");
    let msg = err.to_string();

    assert!(msg.contains("recur: arity must match loop bindings"));
}

#[test]
fn loop_recur_must_be_tail_only() {
    let src = "
        (def (main)
          (loop :max 2 ((x 0))
            (recur 1)
            (recur 2)))
        (main)
    ";

    let err = compile_str(src).expect_err("compile must fail");
    let msg = err.to_string();

    assert!(msg.contains("recur: only allowed in tail position of loop body"));
}

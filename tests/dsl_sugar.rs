// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use winterfell::math::fields::f128::BaseElement as BE;
use zk_lisp::compiler::compile_entry;
use zk_lisp::layout::Columns;
use zk_lisp::pi;
use zk_lisp::prove::{self, build_trace_with_pi};

#[test]
fn begin_variadic_and_def_let_multiform() {
    // def: multi-form body, implicit begin
    // let: multi-form body, implicit begin
    // begin: variadic sequence
    let src = r#"
(def (main)
  (let ((x 5) (y 6))
    (begin
      (assert (= (+ x y) 11))
      (begin (push (+ x y)) (pop)))))
"#;

    let program = compile_entry(src, &[]).expect("compile");

    let pi = pi::PublicInputsBuilder::for_program(&program)
        .build()
        .expect("pi");
    let trace = build_trace_with_pi(&program, &pi).expect("trace");

    let cols = Columns::baseline();
    let (out_reg, out_row) = prove::compute_vm_output(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::from(11u64));
}

#[test]
fn def_multiform_body_implicit_begin() {
    // def with multiple forms after header;
    // call from main to produce output
    let src = r#"
(def (foo a b)
  (assert (= (+ a b) 9))
  (+ a b))

(def (main) (foo 4 5))
"#;

    let program = compile_entry(src, &[]).expect("compile");

    let pi = pi::PublicInputsBuilder::for_program(&program)
        .build()
        .expect("pi");
    let trace = build_trace_with_pi(&program, &pi).expect("trace");
    let (out_reg, out_row) = prove::compute_vm_output(&trace);
    let cols = Columns::baseline();
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);
    assert_eq!(v, BE::from(9u64));
}

#[test]
fn push_star_and_pop_star_macros() {
    let src = r#"
(def (main)
  (begin
    (push* 7 11)
    (+ (pop* 1) (pop))))
"#;

    let program = compile_entry(src, &[]).expect("compile");

    let pi = pi::PublicInputsBuilder::for_program(&program)
        .build()
        .expect("pi");
    let trace = build_trace_with_pi(&program, &pi).expect("trace");

    let cols = Columns::baseline();
    let (out_reg, out_row) = prove::compute_vm_output(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::from(18u64));
}

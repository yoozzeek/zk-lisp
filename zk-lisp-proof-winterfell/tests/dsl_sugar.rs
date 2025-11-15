// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

use winterfell::math::fields::f128::BaseElement as BE;

use zk_lisp_compiler::compile_entry;
use zk_lisp_proof::pi::PublicInputsBuilder;
use zk_lisp_proof_winterfell::layout::Columns;
use zk_lisp_proof_winterfell::trace::build_trace;
use zk_lisp_proof_winterfell::utils::vm_output_from_trace;

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
    let pi = PublicInputsBuilder::from_program(&program)
        .build()
        .expect("pi");
    let trace = build_trace(&program, &pi).expect("trace");
    let cols = Columns::baseline();
    let (out_reg, out_row) = vm_output_from_trace(&trace);
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
    let pi = PublicInputsBuilder::from_program(&program)
        .build()
        .expect("pi");
    let trace = build_trace(&program, &pi).expect("trace");
    let (out_reg, out_row) = vm_output_from_trace(&trace);
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
    let pi = PublicInputsBuilder::from_program(&program)
        .build()
        .expect("pi");
    let trace = build_trace(&program, &pi).expect("trace");

    let cols = Columns::baseline();
    let (out_reg, out_row) = vm_output_from_trace(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::from(18u64));
}

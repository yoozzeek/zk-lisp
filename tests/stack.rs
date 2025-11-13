// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use winterfell::math::fields::f128::BaseElement as BE;
use zk_lisp::compiler::compile_entry;
use zk_lisp::layout::Columns;
use zk_lisp::pi;
use zk_lisp::prove::{self, build_trace_with_pi};

#[test]
fn stack_push_pop_simple() {
    let src = "(def (main) (begin (push 7) (pop)))";
    let program = compile_entry(src, &[]).expect("compile");

    let pi = pi::PublicInputsBuilder::for_program(&program)
        .build()
        .expect("pi");
    let trace = build_trace_with_pi(&program, &pi).expect("trace");

    let cols = Columns::baseline();
    let (out_reg, out_row) = prove::compute_vm_output(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::from(7u64));
}

#[test]
fn stack_push_push_pop_add() {
    // x = (push 7; push 11; pop) => 11
    // then result = x + pop() => 11 + 7 = 18
    let src = r#"
(def (main)
  (let ((x (begin (push* 7 11)
                  (pop))))
    (+ x (pop))))
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

#[test]
fn stack_fill_empty_sum() {
    // push 1..5, then pop
    // 5 times and sum => 15
    let src = r#"
(def (main)
  (begin
    (push* 1 2 3 4 5)
    (+ (pop)
       (+ (pop)
          (+ (pop)
             (+ (pop) (pop)))))))
"#;

    let program = compile_entry(src, &[]).expect("compile");

    let pi = pi::PublicInputsBuilder::for_program(&program)
        .build()
        .expect("pi");
    let trace = build_trace_with_pi(&program, &pi).expect("trace");

    let cols = Columns::baseline();
    let (out_reg, out_row) = prove::compute_vm_output(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::from(15u64));
}

#[test]
fn stack_with_load_store_interop() {
    // push 7 at base+0;
    // load base+0 -> 7;
    // store base+0 <- 9;
    // pop -> 9;
    // total = 7 + 9 = 16
    let src = r#"
(def (main)
  (let ((addr 1000000))
    (begin
      (push 7)
      (+ (load addr)
         (begin (store addr 9)
                (pop))))))
"#;

    let program = compile_entry(src, &[]).expect("compile");

    let pi = pi::PublicInputsBuilder::for_program(&program)
        .build()
        .expect("pi");
    let trace = build_trace_with_pi(&program, &pi).expect("trace");

    let cols = Columns::baseline();
    let (out_reg, out_row) = prove::compute_vm_output(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::from(16u64));
}

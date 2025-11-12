// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use winterfell::math::fields::f128::BaseElement as BE;
use zk_lisp::compiler::compile_entry;
use zk_lisp::prove;

#[test]
fn store_then_load_same_address() {
    let src = r"
(def (main)
  (seq (store 42 7)
       (load 42)))
";
    let p = compile_entry(src, &[]).expect("compile");
    let trace = prove::build_trace(&p).expect("trace");

    let cols = zk_lisp::layout::Columns::baseline();
    let (out_reg, out_row) = prove::compute_vm_output(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::from(7u64));
}

#[test]
fn double_load_after_single_store_ok() {
    let src = r"
(def (main)
  (seq (store 7 11)
       (seq (load 7)
            (load 7))))
";
    let p = compile_entry(src, &[]).expect("compile");
    let trace = prove::build_trace(&p).expect("trace");

    let cols = zk_lisp::layout::Columns::baseline();
    let (out_reg, out_row) = prove::compute_vm_output(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::from(11u64));
}

#[test]
fn store_same_addr_updates_shadow() {
    let src = r"
(def (main)
  (seq (store 7 11)
       (seq (store 7 13)
            (load 7))))
";
    let p = compile_entry(src, &[]).expect("compile");
    let trace = prove::build_trace(&p).expect("trace");

    let cols = zk_lisp::layout::Columns::baseline();
    let (out_reg, out_row) = prove::compute_vm_output(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::from(13u64));
}

#[test]
fn switch_addr_then_load_new_ok() {
    let src = r"
(def (main)
  (seq (store 1 5)
       (seq (store 2 7)
            (load 2))))
";
    let p = compile_entry(src, &[]).expect("compile");
    let trace = prove::build_trace(&p).expect("trace");

    let cols = zk_lisp::layout::Columns::baseline();
    let (out_reg, out_row) = prove::compute_vm_output(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::from(7u64));
}

#[test]
fn store_then_load_different_addr_errors() {
    let src = r"
(def (main)
  (seq (store 1 5)
       (load 2)))
";
    let p = compile_entry(src, &[]).expect("compile");
    let err = prove::build_trace(&p).expect_err("load must read from active addr");
    let msg = format!("{err:?}").to_lowercase();
    
    assert!(msg.contains("load address must equal active addr"));
}

#[test]
fn computed_addr_and_value_ok() {
    let src = r"
(def (main)
  (let ((a (+ 40 2))
        (v (* 3 3)))
    (seq (store a v)
         (load a))))
";
    let p = compile_entry(src, &[]).expect("compile");
    let trace = prove::build_trace(&p).expect("trace");

    let cols = zk_lisp::layout::Columns::baseline();
    let (out_reg, out_row) = prove::compute_vm_output(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::from(9u64));
}

#[test]
fn switch_addr_then_load_old_addr_errors() {
    let src = r"
(def (main)
  (seq (store 1 5)
       (seq (store 2 7)
            (load 1))))
";
    let p = compile_entry(src, &[]).expect("compile");
    let err = prove::build_trace(&p).expect_err("load must read from new active addr");
    let msg = format!("{err:?}").to_lowercase();
    
    assert!(msg.contains("load address must equal active addr"));
}

#[test]
fn load_before_store_errors() {
    // load address must equal
    // active addr (which is none at start)
    let src = "(def (main) (load 1))";
    let p = compile_entry(src, &[]).expect("compile");
    let err = prove::build_trace(&p).expect_err("load without prior store must fail");
    let msg = format!("{err:?}");

    assert!(
        msg.to_lowercase()
            .contains("load address must equal active addr")
    );
}

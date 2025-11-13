// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use winterfell::math::fields::f128::BaseElement as BE;
use zk_lisp::compiler::compile_entry;
use zk_lisp::prove;
use zk_lisp::{pi, PreflightMode};
use winterfell::{ProofOptions, FieldExtension, BatchingMethod};

fn proof_opts() -> ProofOptions {
    ProofOptions::new(
        1,
        8,
        0,
        FieldExtension::None,
        2,
        1,
        BatchingMethod::Linear,
        BatchingMethod::Linear,
    )
}

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
fn store_same_addr_updates_value() {
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
fn store_then_load_different_addr_reads_zero_without_prior_store() {
    let src = r"
(def (main)
  (seq (store 1 5)
       (load 2)))
";
    let p = compile_entry(src, &[]).expect("compile");
    let trace = prove::build_trace(&p).expect("trace");

    let cols = zk_lisp::layout::Columns::baseline();
    let (out_reg, out_row) = prove::compute_vm_output(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::from(0u64));
}

#[test]
#[ignore]
fn ram_perm_store_then_load_preflight_ok() {
    let src = r"
(def (main)
  (seq (store 10 77)
       (load 10)))
";
    let p = compile_entry(src, &[]).expect("compile");

    let pi = pi::PublicInputsBuilder::for_program(&p).build().expect("pi");
    let trace = prove::build_trace_with_pi(&p, &pi).expect("trace");

    let opts = proof_opts();
    prove::preflight_check(PreflightMode::Console, &opts, &pi, &trace).expect("preflight ok");
}

#[test]
#[ignore]
fn ram_perm_many_addresses_preflight_ok() {
    // Write 5 addresses, then read them back
    let src = r"
(def (main)
  (seq (store 1 11)
       (seq (store 2 22)
            (seq (store 3 33)
                 (seq (store 4 44)
                      (seq (store 5 55)
                           (seq (load 3)
                                (load 5))))))))
";
    let p = compile_entry(src, &[]).expect("compile");

    let pi = pi::PublicInputsBuilder::for_program(&p).build().expect("pi");
    let trace = prove::build_trace_with_pi(&p, &pi).expect("trace");

    let opts = proof_opts();
    prove::preflight_check(PreflightMode::Console, &opts, &pi, &trace).expect("preflight ok");
}

#[test]
#[ignore]
fn ram_perm_interleaved_preflight_ok() {
    let src = r"
(def (main)
  (seq (store 1 5)
       (seq (store 2 7)
            (seq (load 1)
                 (load 2)))))
";
    let p = compile_entry(src, &[]).expect("compile");
    let pi = pi::PublicInputsBuilder::for_program(&p).build().expect("pi");
    let trace = prove::build_trace_with_pi(&p, &pi).expect("trace");

    let opts = proof_opts();
    prove::preflight_check(PreflightMode::Console, &opts, &pi, &trace).expect("preflight ok");
}

#[test]
#[ignore]
fn ram_perm_double_store_then_load_preflight_ok() {
    let src = r"
(def (main)
  (seq (store 9 1)
       (seq (store 9 2)
            (load 9))))
";
    let p = compile_entry(src, &[]).expect("compile");
    let pi = pi::PublicInputsBuilder::for_program(&p).build().expect("pi");
    let trace = prove::build_trace_with_pi(&p, &pi).expect("trace");

    let opts = proof_opts();
    prove::preflight_check(PreflightMode::Console, &opts, &pi, &trace).expect("preflight ok");
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
fn switch_addr_then_load_old_addr_reads_old_value() {
    let src = r"
(def (main)
  (seq (store 1 5)
       (seq (store 2 7)
            (load 1))))
";
    let p = compile_entry(src, &[]).expect("compile");
    let trace = prove::build_trace(&p).expect("trace");

    let cols = zk_lisp::layout::Columns::baseline();
    let (out_reg, out_row) = prove::compute_vm_output(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    // expected load 1 should read
    // last stored value at addr 1 (5)
    assert_eq!(v, BE::from(5u64));
}

#[test]
fn load_before_store_reads_zero() {
    // load address must equal
    // active addr (which is none at start)
    let src = "(def (main) (load 1))";
    let p = compile_entry(src, &[]).expect("compile");
    let trace = prove::build_trace(&p).expect("trace");

    let cols = zk_lisp::layout::Columns::baseline();
    let (out_reg, out_row) = prove::compute_vm_output(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);
    
    assert_eq!(v, BE::from(0u64));
}

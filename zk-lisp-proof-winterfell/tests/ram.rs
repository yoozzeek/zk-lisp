// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::{BatchingMethod, FieldExtension, ProofOptions};

use zk_lisp_compiler::compile_entry;
use zk_lisp_proof::frontend::PreflightMode;
use zk_lisp_proof::pi::{self, PublicInputsBuilder};
use zk_lisp_proof_winterfell::layout::Columns;
use zk_lisp_proof_winterfell::preflight::run as run_preflight;
use zk_lisp_proof_winterfell::trace::build_trace;
use zk_lisp_proof_winterfell::utils::vm_output_from_trace;

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
  (begin (store 42 7)
         (load 42)))";
    let p = compile_entry(src, &[]).expect("compile");
    let trace = build_trace(&p, &pi::PublicInputs::default()).expect("trace");
    let cols = Columns::baseline();
    let (out_reg, out_row) = vm_output_from_trace(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::from(7u64));
}

#[test]
fn double_load_after_single_store_ok() {
    let src = r"
(def (main)
  (begin (store 7 11)
         (load 7)
         (load 7)))";
    let p = compile_entry(src, &[]).expect("compile");
    let trace = build_trace(&p, &pi::PublicInputs::default()).expect("trace");
    let cols = Columns::baseline();
    let (out_reg, out_row) = vm_output_from_trace(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::from(11u64));
}

#[test]
fn store_same_addr_updates_value() {
    let src = r"
(def (main)
  (begin (store 7 11)
         (store 7 13)
         (load 7)))";
    let p = compile_entry(src, &[]).expect("compile");
    let trace = build_trace(&p, &pi::PublicInputs::default()).expect("trace");
    let cols = Columns::baseline();
    let (out_reg, out_row) = vm_output_from_trace(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::from(13u64));
}

#[test]
fn switch_addr_then_load_new_ok() {
    let src = r"
(def (main)
  (begin (store 1 5)
         (store 2 7)
         (load 2)))";
    let p = compile_entry(src, &[]).expect("compile");
    let trace = build_trace(&p, &pi::PublicInputs::default()).expect("trace");
    let cols = Columns::baseline();
    let (out_reg, out_row) = vm_output_from_trace(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::from(7u64));
}

#[test]
fn store_then_load_different_addr_reads_zero_without_prior_store() {
    let src = r"
(def (main)
  (begin (store 1 5)
         (load 2)))";
    let p = compile_entry(src, &[]).expect("compile");
    let trace = build_trace(&p, &pi::PublicInputs::default()).expect("trace");
    let cols = Columns::baseline();
    let (out_reg, out_row) = vm_output_from_trace(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::from(0u64));
}

#[test]
fn ram_perm_store_then_load_preflight_ok() {
    let src = r"
(def (main)
  (begin (store 10 77)
         (load 10)))";
    let p = compile_entry(src, &[]).expect("compile");
    let pi = PublicInputsBuilder::from_program(&p).build().expect("pi");
    let trace = build_trace(&p, &pi).expect("trace");
    let opts = proof_opts();

    run_preflight(PreflightMode::Console, &opts, &pi, &trace).expect("preflight ok");
}

#[test]
fn ram_perm_many_addresses_preflight_ok() {
    // Write 5 addresses, then read them back
    let src = r"
(def (main)
  (begin (store 1 11)
         (store 2 22)
         (store 3 33)
         (store 4 44)
         (store 5 55)
         (load 3)
         (load 5)))";

    let p = compile_entry(src, &[]).expect("compile");
    let pi = PublicInputsBuilder::from_program(&p).build().expect("pi");
    let trace = build_trace(&p, &pi).expect("trace");
    let opts = proof_opts();

    run_preflight(PreflightMode::Console, &opts, &pi, &trace).expect("preflight ok");
}

#[test]
fn ram_perm_interleaved_preflight_ok() {
    let src = r"
(def (main)
  (begin (store 1 5)
         (store 2 7)
         (load 1)
         (load 2)))";
    let p = compile_entry(src, &[]).expect("compile");
    let pi = PublicInputsBuilder::from_program(&p).build().expect("pi");
    let trace = build_trace(&p, &pi).expect("trace");
    let opts = proof_opts();

    run_preflight(PreflightMode::Console, &opts, &pi, &trace).expect("preflight ok");
}

#[test]
fn ram_perm_double_store_then_load_preflight_ok() {
    let src = r"
(def (main)
  (begin (store 9 1)
         (store 9 2)
         (load 9)))";
    let p = compile_entry(src, &[]).expect("compile");
    let pi = PublicInputsBuilder::from_program(&p).build().expect("pi");
    let trace = build_trace(&p, &pi).expect("trace");
    let opts = proof_opts();

    run_preflight(PreflightMode::Console, &opts, &pi, &trace).expect("preflight ok");
}

#[test]
fn computed_addr_and_value_ok() {
    let src = r"
(def (main)
  (let ((a (+ 40 2))
        (v (* 3 3)))
    (store a v)
    (load a)))";
    let p = compile_entry(src, &[]).expect("compile");
    let trace = build_trace(&p, &pi::PublicInputs::default()).expect("trace");
    let cols = Columns::baseline();
    let (out_reg, out_row) = vm_output_from_trace(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::from(9u64));
}

#[test]
fn switch_addr_then_load_old_addr_reads_old_value() {
    let src = r"
(def (main)
  (begin (store 1 5)
         (store 2 7)
         (load 1)))";
    let p = compile_entry(src, &[]).expect("compile");
    let trace = build_trace(&p, &pi::PublicInputs::default()).expect("trace");
    let cols = Columns::baseline();
    let (out_reg, out_row) = vm_output_from_trace(&trace);
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
    let trace = build_trace(&p, &pi::PublicInputs::default()).expect("trace");
    let cols = Columns::baseline();
    let (out_reg, out_row) = vm_output_from_trace(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::from(0u64));
}

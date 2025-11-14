// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;
use zk_lisp::compiler::compile_entry;
use zk_lisp::{build_trace, pi, prove};

#[test]
fn bit_pred_immediate() {
    let src = "(def (main) (bit? 1))";
    let p = compile_entry(src, &[]).expect("compile");
    let trace = build_trace(&p, &pi::PublicInputs::default()).expect("trace");
    let cols = zk_lisp::layout::Columns::baseline();
    let (out_reg, out_row) = zk_lisp::vm_output_from_trace(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::ONE);
}

#[test]
fn bit_pred_computed() {
    // (bit? (- 1 1)) == (bit? 0) == 1
    let src = "(def (main) (bit? (- 1 1)))";
    let p = compile_entry(src, &[]).expect("compile");
    let trace = build_trace(&p, &pi::PublicInputs::default()).expect("trace");
    let cols = zk_lisp::layout::Columns::baseline();
    let (out_reg, out_row) = zk_lisp::vm_output_from_trace(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::ONE);
}

#[test]
fn assert_bit_ok() {
    let src = "(def (main) (assert-bit 1))";
    let p = compile_entry(src, &[]).expect("compile");
    let trace = build_trace(&p, &pi::PublicInputs::default()).expect("trace");
    let cols = zk_lisp::layout::Columns::baseline();
    let (out_reg, out_row) = zk_lisp::vm_output_from_trace(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::ONE);
}

#[test]
fn assert_bit_const_false_errors() {
    let src = "(def (main) (assert-bit 2))";
    let err = compile_entry(src, &[]).expect_err("must error");
    let msg = format!("{err}");

    assert!(msg.contains("assert-bit: constant not a bit"));
}

#[test]
fn assert_range_ok_8bits() {
    let src = "(def (main) (assert-range 255 32))";
    let p = compile_entry(src, &[]).expect("compile");
    let trace = build_trace(&p, &pi::PublicInputs::default()).expect("trace");
    let cols = zk_lisp::layout::Columns::baseline();
    let (out_reg, out_row) = zk_lisp::vm_output_from_trace(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::ONE);
}

#[test]
fn assert_range_const_oob_errors() {
    let src = "(def (main) (assert-range 4294967296 32))";
    let err = compile_entry(src, &[]).expect_err("must error");
    let msg = format!("{err}");

    assert!(msg.contains("assert-range: constant out of range"));
}

#[test]
fn assert_range_bits_invalid_errors() {
    let src = "(def (main) (assert-range 5 12))";
    let err = compile_entry(src, &[]).expect_err("must error");
    let msg = format!("{err}");

    assert!(msg.contains("assert-range: bits must be 32 or 64"));
}

// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;

use zk_lisp_compiler::compile_entry;
use zk_lisp_proof::pi::PublicInputsBuilder;
use zk_lisp_proof_winterfell::layout::Columns;
use zk_lisp_proof_winterfell::trace::build_trace;
use zk_lisp_proof_winterfell::utils::vm_output_from_trace;

#[test]
fn bit_pred_immediate() {
    let src = "(def (main) (bit? 1))";
    let p = compile_entry(src, &[]).expect("compile");
    let pi = PublicInputsBuilder::from_program(&p).build().expect("pi");
    let trace = build_trace(&p, &pi).expect("trace");
    let cols = Columns::baseline();
    let (out_reg, out_row) = vm_output_from_trace(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::ONE);
}

#[test]
fn bit_pred_computed() {
    // (bit? (- 1 1)) == (bit? 0) == 1
    let src = "(def (main) (bit? (- 1 1)))";
    let p = compile_entry(src, &[]).expect("compile");
    let pi = PublicInputsBuilder::from_program(&p).build().expect("pi");
    let trace = build_trace(&p, &pi).expect("trace");
    let cols = Columns::baseline();
    let (out_reg, out_row) = vm_output_from_trace(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::ONE);
}

#[test]
fn assert_bit_ok() {
    let src = "(def (main) (assert-bit 1))";
    let p = compile_entry(src, &[]).expect("compile");
    let pi = PublicInputsBuilder::from_program(&p).build().expect("pi");
    let trace = build_trace(&p, &pi).expect("trace");
    let cols = Columns::baseline();
    let (out_reg, out_row) = vm_output_from_trace(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::ONE);
}

#[test]
fn assert_range_ok_8bits() {
    let src = "(def (main) (assert-range 255 32))";
    let p = compile_entry(src, &[]).expect("compile");
    let pi = PublicInputsBuilder::from_program(&p).build().expect("pi");
    let trace = build_trace(&p, &pi).expect("trace");
    let cols = Columns::baseline();
    let (out_reg, out_row) = vm_output_from_trace(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::ONE);
}

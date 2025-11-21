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
use zk_lisp_proof_winterfell::utils::vm_output_from_trace;
use zk_lisp_proof_winterfell::vm::layout::Columns;
use zk_lisp_proof_winterfell::vm::trace::build_trace;

#[test]
fn mulwide_hi_basic() {
    // 2^63 * 2 = 2^64 -> hi=1, lo=0
    let src = r"
(def (main)
  (mulwide-hi 9223372036854775808 2))
";
    let p = compile_entry(src, &[]).expect("compile");
    let pi = PublicInputsBuilder::from_program(&p).build().expect("pi");
    let trace = build_trace(&p, &pi).expect("trace");

    let cols = Columns::baseline();
    let (out_reg, out_row) = vm_output_from_trace(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::from(1u64));
}

#[test]
fn mulwide_lo_basic() {
    // 3 * 5 = 15 -> lo=15
    let src = "(def (main) (mulwide-lo 3 5))";
    let p = compile_entry(src, &[]).expect("compile");
    let pi = PublicInputsBuilder::from_program(&p).build().expect("pi");
    let trace = build_trace(&p, &pi).expect("trace");

    let cols = Columns::baseline();
    let (out_reg, out_row) = vm_output_from_trace(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::from(15u64));
}

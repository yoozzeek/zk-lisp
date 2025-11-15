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
use zk_lisp_proof::pi::PublicInputs;
use zk_lisp_proof_winterfell::layout::Columns;
use zk_lisp_proof_winterfell::trace::build_trace;
use zk_lisp_proof_winterfell::utils::vm_output_from_trace;

#[test]
fn muldiv_basic_no_overflow() {
    // (3*10)/4 = 7
    let src = "(def (main) (muldiv 3 10 4))";
    let p = compile_entry(src, &[]).expect("compile");
    let trace = build_trace(&p, &PublicInputs::default()).expect("trace");

    let cols = Columns::baseline();
    let (out_reg, out_row) = vm_output_from_trace(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::from(7u64));
}

#[test]
fn muldiv_wide_floor() {
    // 2^63 * 3 / 5 => floor((9223372036854775808*3)/5)
    // = floor(27670116110564327424/5) = 5534023222112865484
    let src = r"
(def (main)
  (muldiv 9223372036854775808 3 5))";
    let p = compile_entry(src, &[]).expect("compile");
    let trace = build_trace(&p, &PublicInputs::default()).expect("trace");

    let cols = Columns::baseline();
    let (out_reg, out_row) = vm_output_from_trace(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::from(5534023222112865484u64));
}

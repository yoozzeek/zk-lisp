// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use winterfell::math::fields::f128::BaseElement as BE;
use zk_lisp::compiler::compile_entry;
use zk_lisp::prove;

#[test]
fn muldiv_basic_no_overflow() {
    // (3*10)/4 = 7
    let src = "(def (main) (muldiv 3 10 4))";
    let p = compile_entry(src, &[]).expect("compile");
    let trace = prove::build_trace(&p).expect("trace");

    let cols = zk_lisp::layout::Columns::baseline();
    let (out_reg, out_row) = prove::compute_vm_output(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::from(7u64));
}

#[test]
fn muldiv_wide_floor() {
    // 2^63 * 3 / 5 => floor((9223372036854775808*3)/5)
    // = floor(27670116110564327424/5) = 5534023222112865484
    let src = r"
(def (main)
  (muldiv 9223372036854775808 3 5))
";
    let p = compile_entry(src, &[]).expect("compile");
    let trace = prove::build_trace(&p).expect("trace");

    let cols = zk_lisp::layout::Columns::baseline();
    let (out_reg, out_row) = prove::compute_vm_output(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::from(5534023222112865484u64));
}

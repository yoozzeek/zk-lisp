// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use winterfell::math::fields::f128::BaseElement as BE;
use zk_lisp::compiler::compile_entry;
use zk_lisp::prove;

#[test]
fn mulwide_hi_basic() {
    // 2^63 * 2 = 2^64 -> hi=1, lo=0
    let src = r"
(def (main)
  (mulwide-hi 9223372036854775808 2))
";
    let p = compile_entry(src, &[]).expect("compile");
    let trace = prove::build_trace(&p).expect("trace");

    let cols = zk_lisp::layout::Columns::baseline();
    let (out_reg, out_row) = prove::compute_vm_output(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::from(1u64));
}

#[test]
fn mulwide_lo_basic() {
    // 3 * 5 = 15 -> lo=15
    let src = "(def (main) (mulwide-lo 3 5))";
    let p = compile_entry(src, &[]).expect("compile");
    let trace = prove::build_trace(&p).expect("trace");

    let cols = zk_lisp::layout::Columns::baseline();
    let (out_reg, out_row) = prove::compute_vm_output(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::from(15u64));
}

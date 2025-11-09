// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use winterfell::Trace;
use zk_lisp::compiler::compile_entry;
use zk_lisp::layout;
use zk_lisp::pi::PublicInputsBuilder;
use zk_lisp::prove::build_trace_with_pi;

fn u128_to_bytes32(n: u128) -> [u8; 32] {
    let mut b = [0u8; 32];
    b[0..16].copy_from_slice(&n.to_le_bytes());

    b
}

#[test]
fn program_meta_points_to_main_return_cell() {
    // main returns (+ arg 7)
    let src = r#"
        (def (main x)
          (+ x 7))
    "#;

    let x = 5u64;
    let program = compile_entry(src, &[x]).expect("compile");

    // Build trace without PI binding is fine
    // here since the arg is an immediate const
    // embedded in the program; but include a
    // minimal PI anyway for VM feature enablement.
    let expected = u128_to_bytes32(12);
    let pi = PublicInputsBuilder::for_program(&program)
        .vm_args(&[x])
        .vm_expect_from_meta(&program, &expected)
        .build()
        .expect("pi");

    let trace = build_trace_with_pi(&program, &pi);

    let cols = layout::Columns::baseline();
    let row = program.meta.out_row as usize;
    let reg = program.meta.out_reg as usize;
    let row_dbg = row.min(trace.length().saturating_sub(1));

    // Expect the value 12 at meta-selected cell.
    let got = trace.get(cols.r_index(reg), row_dbg);
    let want = zk_lisp::pi::be_from_le8(&expected);

    assert_eq!(got, want);
}

// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.

use zk_lisp_compiler::compile_str;

#[test]
fn str64_max_len_error() {
    // 65 bytes string should fail at compile time
    let s65 = "A".repeat(65);
    let src = format!("(str64 \"{s65}\")");

    let err = compile_str(&src).expect_err("compile must fail for >64 bytes");
    let msg = err.to_string();

    assert!(msg.contains("str64: length > 64"));
}

#[test]
fn bytes32_max_len_error() {
    // 33 bytes hex (66 hex chars) should fail at compile time
    let long_hex = format!("0x{}", "11".repeat(33));
    let src = format!("(hex-to-bytes32 \"{long_hex}\")");

    let err = compile_str(&src).expect_err("compile must fail for >32 bytes");
    let msg = err.to_string();

    assert!(msg.contains("hex-to-bytes32: length > 32"));
}

// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

use zk_lisp_compiler::compile_str;

#[test]
fn bytes32_max_len_error() {
    // 33 bytes hex (66 hex chars) should fail at compile time
    let long_hex = format!("0x{}", "11".repeat(33));
    let src = format!("(hex-to-bytes32 \"{long_hex}\")");

    let err = compile_str(&src).expect_err("compile must fail for >32 bytes");
    let msg = err.to_string();

    assert!(msg.contains("hex-to-bytes32: length > 32"));
}

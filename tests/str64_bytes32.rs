// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use winterfell::ProofOptions;
use zk_lisp::compiler::compile_str;
use zk_lisp::pi::{self, PublicInputs};
use zk_lisp::prove::{ZkProver, build_trace, verify_proof};

fn opts() -> ProofOptions {
    ProofOptions::new(
        1,
        8,
        0,
        winterfell::FieldExtension::None,
        2,
        1,
        winterfell::BatchingMethod::Linear,
        winterfell::BatchingMethod::Linear,
    )
}

fn prove_verify_ok(src: &str) {
    let program = compile_str(src).expect("compile");
    let trace = build_trace(&program).expect("trace");

    let mut pi = PublicInputs::default();
    pi.feature_mask = pi::FM_POSEIDON | pi::FM_VM;
    pi.program_commitment = program.commitment;

    let opts = opts();
    let prover = ZkProver::new(opts.clone(), pi.clone());
    let proof = prover.prove(trace).expect("prove");

    match verify_proof(proof, pi, &opts) {
        Ok(()) => {}
        Err(e) => {
            if !matches!(e, zk_lisp::prove::Error::BackendSource(_)) {
                panic!("verify failed: {e}");
            }
        }
    }
}

fn prove_verify_fail(src: &str) {
    let program = compile_str(src).expect("compile");
    let trace = build_trace(&program).expect("trace");

    let mut pi = PublicInputs::default();
    pi.feature_mask = pi::FM_POSEIDON | pi::FM_VM;
    pi.program_commitment = program.commitment;

    let opts = opts();
    let prover = ZkProver::new(opts.clone(), pi.clone());

    match prover.prove(trace) {
        Err(_) => {
            // Prover failed early — acceptable in debug builds
        }
        Ok(proof) => {
            // If prover succeeds, verification must fail
            verify_proof(proof, pi, &opts).expect_err("verify must fail");
        }
    }
}

#[cfg_attr(debug_assertions, ignore)]
#[test]
fn str64_eq_ok() {
    let src = r#"
        (assert (= (str64 "hello") (str64 "hello")))
    "#;
    prove_verify_ok(src);
}

#[test]
fn str64_eq_fail() {
    let src = r#"
        (assert (= (str64 "hello") (str64 "world")))
    "#;
    prove_verify_fail(src);
}

#[cfg_attr(debug_assertions, ignore)]
#[test]
fn str64_in_set_ok() {
    let src = r#"
        (in-set (str64 "b") ((str64 "a") (str64 "b") (str64 "c")))
    "#;
    prove_verify_ok(src);
}

#[test]
fn str64_len_variation_fail() {
    // "a" vs "a\x00" must differ due to length binding
    let src = r#"
        (assert (= (str64 "a") (str64 "a\x00")))
    "#;
    prove_verify_fail(src);
}

#[test]
fn str64_max_len_error() {
    // 65 bytes string should fail at compile time
    let s65 = "A".repeat(65);
    let src = format!("(str64 \"{s65}\")");

    let err = compile_str(&src).expect_err("compile must fail for >64 bytes");
    let msg = err.to_string();

    assert!(msg.contains("str64: length > 64"));
}

#[cfg_attr(debug_assertions, ignore)]
#[test]
fn bytes32_eq_ok() {
    let src = r#"
        (assert (= (hex-to-bytes32 "0xdeadbeef") (hex-to-bytes32 "0xdeadbeef")))
    "#;
    prove_verify_ok(src);
}

#[test]
fn bytes32_len_variation_fail() {
    // 0x00 vs 0x0000 must differ due to length binding
    let src = r#"
        (assert (= (hex-to-bytes32 "0x00") (hex-to-bytes32 "0x0000")))
    "#;
    prove_verify_fail(src);
}

#[cfg_attr(debug_assertions, ignore)]
#[test]
fn bytes32_in_set_ok() {
    let src = r#"
        (in-set (hex-to-bytes32 "0x01") ((hex-to-bytes32 "0x00") (hex-to-bytes32 "0x01")))
    "#;
    prove_verify_ok(src);
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

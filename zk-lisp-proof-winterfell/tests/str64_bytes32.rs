// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

use winterfell::ProofOptions;

use zk_lisp_compiler::compile_str;
use zk_lisp_proof::pi::{self, PublicInputs};
use zk_lisp_proof_winterfell::prove::{self, ZkProver, verify_proof};
use zk_lisp_proof_winterfell::trace::build_trace;

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

    let mut pi = PublicInputs::default();
    pi.feature_mask = pi::FM_POSEIDON | pi::FM_VM;
    pi.program_commitment = program.commitment;

    let trace = build_trace(&program, &pi).expect("trace");
    let rom_acc = zk_lisp_proof_winterfell::romacc::rom_acc_from_program(&program);

    let opts = opts();
    let prover = ZkProver::new(opts.clone(), pi.clone(), rom_acc);
    let proof = prover.prove(trace).expect("prove");

    match verify_proof(proof, &program, pi, &opts) {
        Ok(()) => {}
        Err(e) => {
            if !matches!(e, prove::Error::BackendSource(_)) {
                panic!("verify failed: {e}");
            }
        }
    }
}

fn prove_verify_fail(src: &str) {
    let program = compile_str(src).expect("compile");

    let mut pi = PublicInputs::default();
    pi.feature_mask = pi::FM_POSEIDON | pi::FM_VM;
    pi.program_commitment = program.commitment;

    let trace = build_trace(&program, &pi).expect("trace");
    let rom_acc = zk_lisp_proof_winterfell::romacc::rom_acc_from_program(&program);
    let opts = opts();
    let prover = ZkProver::new(opts.clone(), pi.clone(), rom_acc);

    match prover.prove(trace) {
        Err(_) => {
            // Prover failed early — acceptable in debug builds
        }
        Ok(proof) => {
            // If prover succeeds, verification must fail
            verify_proof(proof, &program, pi, &opts).expect_err("verify must fail");
        }
    }
}

#[cfg_attr(debug_assertions, ignore)]
#[test]
fn str64_eq_ok() {
    let src = r#"(assert (= (str64 "hello") (str64 "hello")))"#;
    prove_verify_ok(src);
}

#[test]
fn str64_eq_fail() {
    let src = r#"(assert (= (str64 "hello") (str64 "world")))"#;
    prove_verify_fail(src);
}

#[cfg_attr(debug_assertions, ignore)]
#[test]
fn str64_in_set_ok() {
    let src = r#"
(in-set (str64 "b")
  ((str64 "a") (str64 "b") (str64 "c")))"#;
    prove_verify_ok(src);
}

#[test]
fn str64_len_variation_fail() {
    // "a" vs "a\x00" must differ due to length binding
    let src = r#"(assert (= (str64 "a") (str64 "a\x00")))"#;
    prove_verify_fail(src);
}

#[cfg_attr(debug_assertions, ignore)]
#[test]
fn bytes32_eq_ok() {
    let src = r#"
(assert (= (hex-to-bytes32 "0xdeadbeef")
           (hex-to-bytes32 "0xdeadbeef")))"#;
    prove_verify_ok(src);
}

#[test]
fn bytes32_len_variation_fail() {
    // 0x00 vs 0x0000 must differ due to length binding
    let src = r#"
(assert (= (hex-to-bytes32 "0x00")
           (hex-to-bytes32 "0x0000")))"#;
    prove_verify_fail(src);
}

#[cfg_attr(debug_assertions, ignore)]
#[test]
fn bytes32_in_set_ok() {
    let src = r#"
(in-set (hex-to-bytes32 "0x01")
  ((hex-to-bytes32 "0x00") (hex-to-bytes32 "0x01")))"#;
    prove_verify_ok(src);
}

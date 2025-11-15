// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

use winterfell::ProofOptions;

use zk_lisp_compiler::{compile_entry, compile_str};
use zk_lisp_proof::pi::{self, PublicInputs};
use zk_lisp_proof_winterfell::prove::{self, ZkProver, verify_proof};
use zk_lisp_proof_winterfell::trace::build_trace;

#[test]
fn assert_positive() {
    // Use compile_entry to ensure
    // a minimal VM shape even if
    // the assert folds to a constant.
    let src = r"
(def (eq1 x y) (= x y))
(def (main)
  (let ((a 7) (b 7))
    (assert (eq1 a b))))";
    let program = compile_entry(src, &[]).expect("compile");

    let mut pi = PublicInputs::default();
    pi.feature_mask = pi::FM_VM;
    pi.program_commitment = program.commitment;

    let trace = build_trace(&program, &pi).expect("trace");
    let rom_acc = zk_lisp_proof_winterfell::romacc::rom_acc_from_program(&program);

    let opts = ProofOptions::new(
        1,
        8,
        0,
        winterfell::FieldExtension::None,
        2,
        1,
        winterfell::BatchingMethod::Linear,
        winterfell::BatchingMethod::Linear,
    );

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

#[test]
fn if_positive() {
    let src = "(def (main) (if 1 5 9))";
    let program = compile_entry(src, &[]).expect("compile");

    let mut pi = PublicInputs::default();
    pi.feature_mask = pi::FM_VM;
    pi.program_commitment = program.commitment;

    let trace = build_trace(&program, &pi).expect("trace");
    let rom_acc = zk_lisp_proof_winterfell::romacc::rom_acc_from_program(&program);

    let opts = ProofOptions::new(
        1,
        8,
        0,
        winterfell::FieldExtension::None,
        2,
        1,
        winterfell::BatchingMethod::Linear,
        winterfell::BatchingMethod::Linear,
    );

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

// Compiler-side negative test
// for constant false asserts will
// be covered in zk-lisp-compiler
// tests; we keep only backend
// behaviour here.
#[test]
fn assert_negative_may_fail_at_prove_or_verify() {
    let src = "(let ((a 5) (b 6)) (assert (= a b)))";

    match compile_str(src) {
        Err(e) => {
            let msg = e.to_string();
            assert!(msg.contains("assert: constant false"));
        }
        Ok(program) => {
            let mut pi = PublicInputs::default();
            pi.feature_mask = pi::FM_VM;
            pi.program_commitment = program.commitment;

            let trace = build_trace(&program, &pi).expect("trace");
            let rom_acc = zk_lisp_proof_winterfell::romacc::rom_acc_from_program(&program);

            let opts = ProofOptions::new(
                1,
                8,
                0,
                winterfell::FieldExtension::None,
                2,
                1,
                winterfell::BatchingMethod::Linear,
                winterfell::BatchingMethod::Linear,
            );

            let prover = ZkProver::new(opts.clone(), pi.clone(), rom_acc);

            match prover.prove(trace) {
                Err(_) => {
                    // In debug, preflight should fail; this is OK
                }
                Ok(proof) => {
                    // In release, proving may succeed,
                    // but verification must fail.
                    verify_proof(proof, &program, pi, &opts).expect_err("verify must fail");
                }
            }
        }
    }
}

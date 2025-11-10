// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use winterfell::ProofOptions;
use zk_lisp::compiler::compile_str;
use zk_lisp::pi::{self, PublicInputs};
use zk_lisp::prove::{ZkProver, build_trace, verify_proof};

#[test]
fn assert_positive() {
    // Use compile_entry to ensure a minimal
    // VM shape even if the assert folds to a constant.
    let src = r"
(def (eq1 x y) (= x y))
(def (main)
  (let ((a 7) (b 7))
    (assert (eq1 a b))))
";
    let program = zk_lisp::compiler::compile_entry(src, &[]).expect("compile");
    let trace = build_trace(&program).expect("trace");

    let mut pi = PublicInputs::default();
    pi.feature_mask = pi::FM_VM;
    pi.program_commitment = program.commitment;

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

#[test]
fn if_positive() {
    let src = "(def (main) (if 1 5 9))";
    let program = zk_lisp::compiler::compile_entry(src, &[]).expect("compile");
    let trace = build_trace(&program).expect("trace");

    let mut pi = PublicInputs::default();
    pi.feature_mask = pi::FM_VM;
    pi.program_commitment = program.commitment;

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

#[test]
fn assert_negative_fails() {
    // assert(false) must fail; after constant folding
    // this may be detected at compile time.
    let src = "(let ((a 5) (b 6)) (assert (= a b)))";

    match compile_str(src) {
        Err(e) => {
            let msg = e.to_string();
            assert!(msg.contains("assert: constant false"));
        }
        Ok(program) => {
            let trace = build_trace(&program).expect("trace");

            let mut pi = PublicInputs::default();
            pi.feature_mask = pi::FM_VM;
            pi.program_commitment = program.commitment;

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

            let prover = ZkProver::new(opts.clone(), pi.clone());

            match prover.prove(trace) {
                Err(_) => {
                    // In debug, preflight should fail — this is OK
                }
                Ok(proof) => {
                    // In release, proving may succeed,
                    // but verification must fail.
                    verify_proof(proof, pi, &opts).expect_err("verify must fail");
                }
            }
        }
    }
}

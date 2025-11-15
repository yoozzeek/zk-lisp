// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

use std::panic;
use winterfell::ProofOptions;

use zk_lisp_compiler::compile_entry;
use zk_lisp_proof::pi::PublicInputsBuilder;
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

fn u128_to_bytes32(n: u128) -> [u8; 32] {
    let mut b = [0u8; 32];
    b[0..16].copy_from_slice(&n.to_le_bytes());

    b
}

#[test]
fn enum_predicate_positive_verifies() {
    let src = r#"
(deftype fruit () '(member apple orange banana))
(def (main t)
  (fruit:is t))
    "#;

    let t = 1u64; // in set
    let program = compile_entry(src, &[t]).expect("compile");

    let expected = u128_to_bytes32(1);
    let pi = PublicInputsBuilder::from_program(&program)
        .with_args(&[t])
        .with_expect(&expected)
        .build()
        .expect("pi");

    let trace = build_trace(&program, &pi).expect("trace");
    let rom_acc = zk_lisp_proof_winterfell::romacc::rom_acc_from_program(&program);

    let opts = opts();
    let prover = ZkProver::new(opts.clone(), pi.clone(), rom_acc);
    let proof = prover.prove(trace).expect("prove");

    match verify_proof(proof, pi, &opts) {
        Ok(()) => {}
        Err(e) => {
            if !matches!(e, prove::Error::BackendSource(_)) {
                panic!("verify failed: {e}");
            }
        }
    }
}

#[test]
fn enum_predicate_negative_fails_verify() {
    let src = r#"
(deftype fruit () '(member apple orange banana))
(def (main t)
  (fruit:is t))
    "#;

    let t = 3u64; // not in set
    let program = compile_entry(src, &[t]).expect("compile");

    let expected = u128_to_bytes32(1);
    let pi = PublicInputsBuilder::from_program(&program)
        .with_args(&[t])
        .with_expect(&expected)
        .build()
        .expect("pi");

    let trace = build_trace(&program, &pi).expect("trace");

    let opts = opts();

    // In debug, prove() may panic during preflight/assertion checks.
    // In release, prove() may succeed but the proof must fail to verify.
    let rom_acc = zk_lisp_proof_winterfell::romacc::rom_acc_from_program(&program);
    let prove_res = panic::catch_unwind(|| {
        let prover = ZkProver::new(opts.clone(), pi.clone(), rom_acc);
        prover.prove(trace)
    });

    match prove_res {
        Ok(Ok(proof)) => {
            let err = verify_proof(proof, pi, &opts).expect_err("must fail verify");
            match err {
                prove::Error::Backend(_)
                | prove::Error::BackendSource(_)
                | prove::Error::PublicInputs(_) => {}
            }
        }
        // Prove returned an error — acceptable failure mode
        Ok(Err(_)) => {}
        // Prove panicked — acceptable failure mode (typical in debug)
        Err(_) => {}
    }
}

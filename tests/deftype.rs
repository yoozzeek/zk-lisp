// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use std::panic;
use winterfell::ProofOptions;
use zk_lisp::compiler::compile_entry;
use zk_lisp::pi::PublicInputsBuilder;
use zk_lisp::prove::{ZkProver, build_trace_with_pi, verify_proof};

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
    let pi = PublicInputsBuilder::for_program(&program)
        .vm_args(&[t])
        .vm_expect_from_meta(&program, &expected)
        .build()
        .expect("pi");

    let trace = build_trace_with_pi(&program, &pi);

    let opts = opts();
    let prover = ZkProver::new(opts.clone(), pi.clone());
    let proof = prover.prove(trace).expect("prove");

    verify_proof(proof, pi, &opts).expect("verify ok");
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
    let pi = PublicInputsBuilder::for_program(&program)
        .vm_args(&[t])
        .vm_expect_from_meta(&program, &expected)
        .build()
        .expect("pi");

    let trace = build_trace_with_pi(&program, &pi);

    let opts = opts();

    // In debug, prove() may panic during preflight/assertion checks.
    // In release, prove() may succeed but the proof must fail to verify.
    let prove_res = panic::catch_unwind(|| {
        let prover = ZkProver::new(opts.clone(), pi.clone());
        prover.prove(trace)
    });

    match prove_res {
        Ok(Ok(proof)) => {
            let err = verify_proof(proof, pi, &opts).expect_err("must fail verify");
            match err {
                zk_lisp::prove::Error::Backend(_) => {}
            }
        }
        // Prove returned an error — acceptable failure mode
        Ok(Err(_)) => {}
        // Prove panicked — acceptable failure mode (typical in debug)
        Err(_) => {}
    }
}

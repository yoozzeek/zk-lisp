// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

use std::panic;
use winterfell::ProofOptions;

use zk_lisp_compiler::compile_entry;
use zk_lisp_proof::error::Error as CoreError;
use zk_lisp_proof::pi::{PublicInputsBuilder, VmArg};
use zk_lisp_proof_winterfell::prove::{self, ZkProver, verify_proof};
use zk_lisp_proof_winterfell::romacc;
use zk_lisp_proof_winterfell::trace::build_trace;

fn opts() -> ProofOptions {
    ProofOptions::new(
        64, // queries
        16, // blowup
        16, // grind
        winterfell::FieldExtension::None,
        2,
        1,
        winterfell::BatchingMethod::Linear,
        winterfell::BatchingMethod::Linear,
    )
}

#[test]
fn secret_arg_positive_verifies() {
    // (def (main) (assert (= (secret-arg 0) 3)))
    let src = r#"
(def (main)
  (assert (= (secret-arg 0) 3)))
"#;

    let program = compile_entry(src, &[]).expect("compile");

    let pi = PublicInputsBuilder::from_program(&program)
        .with_public_args(&[])
        .with_secret_args(&[VmArg::U64(3)])
        .build()
        .expect("pi");

    // Build trace and full proof
    let trace = build_trace(&program, &pi).expect("trace");
    let rom_acc = romacc::rom_acc_from_program(&program);

    let opts = opts();
    let prover = ZkProver::new(opts.clone(), pi.clone(), rom_acc);
    let proof = prover.prove(trace).expect("prove");

    // Verify must succeed with correct secret arg
    verify_proof(proof, &program, pi, &opts, 64).expect("verify");
}

#[test]
fn secret_arg_negative_fails_verify() {
    // Same program but wrong secret -> proof must fail
    let src = r#"
(def (main)
  (assert (= (secret-arg 0) 3)))
"#;

    let program = compile_entry(src, &[]).expect("compile");

    let pi = PublicInputsBuilder::from_program(&program)
        .with_public_args(&[])
        .with_secret_args(&[VmArg::U64(4)])
        .build()
        .expect("pi");

    let trace = build_trace(&program, &pi).expect("trace");
    let rom_acc = romacc::rom_acc_from_program(&program);
    let opts = opts();

    // In debug, prove() may panic due to
    // failed assertions; in release, prove() may
    // succeed but verify() must fail.
    let prove_res = panic::catch_unwind(|| {
        let prover = ZkProver::new(opts.clone(), pi.clone(), rom_acc);
        prover.prove(trace)
    });

    match prove_res {
        Ok(Ok(proof)) => {
            let err = verify_proof(proof, &program, pi, &opts, 64)
                .expect_err("must fail verify with wrong secret");
            match err {
                prove::Error::Backend(_)
                | prove::Error::BackendSource(_)
                | prove::Error::PublicInputs(_) => {}
            }
        }
        // Prove returned an error; acceptable failure mode
        Ok(Err(_)) => {}
        // Prove panicked; acceptable (typical in debug)
        Err(_) => {}
    }
}

#[test]
fn secret_arg_non_u64_rejected() {
    let src = r#"
(def (main)
  (assert (= (secret-arg 0) 3)))
"#;

    let program = compile_entry(src, &[]).expect("compile");

    // Provide non-u64 secret arg;
    // VM trace builder should reject
    // this with a clear InvalidInput error.
    let pi = PublicInputsBuilder::from_program(&program)
        .with_public_args(&[])
        .with_secret_args(&[VmArg::Bytes32([1u8; 32])])
        .build()
        .expect("pi");

    let err = build_trace(&program, &pi).expect_err("must reject non-u64 secret arg");

    match err {
        CoreError::InvalidInput(msg) => {
            assert!(
                msg.contains("non-u64 secret arg"),
                "unexpected message: {msg}"
            );
        }
        other => panic!("unexpected error: {other}"),
    }
}

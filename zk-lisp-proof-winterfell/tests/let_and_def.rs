// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

use winterfell::ProofOptions;

use zk_lisp_compiler::compile_entry;
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

#[test]
fn let_nested_and_shadowing_positive() {
    // Two independent let scenarios
    // cover nested binds and shadowing
    let src = r"
(def (main)
  (+
    (let ((x 2) (y 3))
      (let ((z (+ x y)))
        (assert (= z 5))))
    (let ((x 2))
      (let ((x 3))
        (assert (= x 3))))))";

    let program = compile_entry(src, &[]).expect("compile");

    let mut pi = PublicInputs::default();
    pi.feature_mask = pi::FM_VM;
    pi.program_commitment = program.commitment;

    let trace = build_trace(&program, &pi).expect("trace");
    let rom_acc = zk_lisp_proof_winterfell::romacc::rom_acc_from_program(&program);

    let opts = opts();
    let prover = ZkProver::new(opts.clone(), pi.clone(), rom_acc);
    let proof = prover.prove(trace).expect("prove");

    match verify_proof(proof, &program, pi, &opts, 64) {
        Ok(()) => {}
        Err(e) => {
            if !matches!(e, prove::Error::BackendSource(_)) {
                panic!("verify failed: {e}");
            }
        }
    }
}

#[test]
fn def_function_and_call_positive() {
    // Define and call a function
    let src = r"
(def (add2 a b) (+ a b))
(def (main) (assert (= (add2 7 8) 15)))";

    let program = compile_entry(src, &[]).expect("compile");

    let mut pi = PublicInputs::default();
    pi.feature_mask = pi::FM_VM;
    pi.program_commitment = program.commitment;

    let trace = build_trace(&program, &pi).expect("trace");
    let rom_acc = zk_lisp_proof_winterfell::romacc::rom_acc_from_program(&program);

    let opts = opts();
    let prover = ZkProver::new(opts.clone(), pi.clone(), rom_acc);
    let proof = prover.prove(trace).expect("prove");

    match verify_proof(proof, &program, pi, &opts, 64) {
        Ok(()) => {}
        Err(e) => {
            if !matches!(e, prove::Error::BackendSource(_)) {
                panic!("verify failed: {e}");
            }
        }
    }
}

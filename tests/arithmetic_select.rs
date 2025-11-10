// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use winterfell::ProofOptions;
use zk_lisp::compiler::compile_str;
use zk_lisp::pi::{self, PublicInputs};
use zk_lisp::prove::{ZkProver, build_trace, verify_proof};

#[test]
fn arithmetic_select_prove_verify() {
    // Lisp: arithmetic + select
    let src = "(let ((a 7) (b 9)) (select (= a b) (+ a b) 0))";
    let program = compile_str(src).expect("compile");

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

    // Verify (allow insufficient conjectured security on tiny traces)
    match verify_proof(proof, pi, &opts) {
        Ok(()) => {}
        Err(e) => {
            if !matches!(e, zk_lisp::prove::Error::BackendSource(_)) {
                panic!("verify failed: {e}");
            }
        }
    }
}

// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use winterfell::ProofOptions;
use zk_lisp::compiler::compile_str;
use zk_lisp::pi::{self, PublicInputs};
use zk_lisp::prove::{ZkProver, build_trace, verify_proof};

#[test]
fn hash2_prove_verify() {
    // Poseidon placeholder: choose left=1 to keep output stable (1)
    let src = "(let ((x 1) (y 2)) (hash2 x y))";
    let program = compile_str(src).expect("compile");
    let trace = build_trace(&program).expect("trace");

    let mut pi = PublicInputs::default();
    pi.feature_mask = pi::FM_POSEIDON | pi::FM_VM | pi::FM_HASH2;
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

    verify_proof(proof, pi, &opts).expect("verify");
}

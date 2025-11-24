// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025

use zk_lisp_compiler::builder::{Op, ProgramBuilder};
use zk_lisp_proof::ProverOptions;
use zk_lisp_proof::pi::PublicInputsBuilder;
use zk_lisp_proof_winterfell::prove::{VerifyBoundaries, verify_proof_fast};

fn make_opts() -> ProverOptions {
    ProverOptions {
        min_security_bits: 20,
        blowup: 8,
        grind: 8,
        queries: 8,
        max_segment_rows: None,
    }
}

fn build_small_program() -> zk_lisp_compiler::Program {
    let metrics = zk_lisp_compiler::CompilerMetrics::default();
    let mut b = ProgramBuilder::new();

    b.push(Op::Const { dst: 0, imm: 1 });
    b.push(Op::Const { dst: 1, imm: 2 });
    b.push(Op::Add { dst: 2, a: 0, b: 1 });
    b.push(Op::End);

    b.finalize(metrics).expect("program build")
}

#[test]
fn verify_fast_matches_normal_verify() {
    let program = build_small_program();
    let pi = PublicInputsBuilder::from_program(&program)
        .build()
        .expect("pi build");
    let opts = make_opts();

    // Build a step proof and boundaries from it.
    let steps = zk_lisp_proof_winterfell::prove::prove_program_steps(&program, &pi, &opts)
        .expect("prove_step must succeed");

    let proof = steps[0].proof.inner.clone();
    let pi_core = steps[0].pi_core.clone();

    let side = VerifyBoundaries::from_step(&steps[0]);

    // Fast verify (no trace rebuild)
    verify_proof_fast(
        proof,
        &program,
        pi_core,
        &side,
        &winterfell::ProofOptions::new(
            opts.queries as usize,
            opts.blowup as usize,
            opts.grind,
            winterfell::FieldExtension::None,
            2,
            1,
            winterfell::BatchingMethod::Linear,
            winterfell::BatchingMethod::Linear,
        ),
        opts.min_security_bits,
    )
    .expect("verify_proof_fast must succeed");
}

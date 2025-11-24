// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Tests for ZlStepProof binary serialization.

use zk_lisp_compiler::builder::{Op, ProgramBuilder};
use zk_lisp_proof::ProverOptions;
use zk_lisp_proof::error;
use zk_lisp_proof::pi::PublicInputsBuilder;
use zk_lisp_proof_winterfell::proof::step::StepProof;
use zk_lisp_proof_winterfell::prove::prove_program;

fn make_step_opts() -> ProverOptions {
    ProverOptions {
        min_security_bits: 40,
        blowup: 8,
        grind: 8,
        queries: 8,
        max_segment_rows: None,
        max_concurrent_segments: None,
    }
}

fn build_step_program() -> zk_lisp_compiler::Program {
    let metrics = zk_lisp_compiler::CompilerMetrics::default();
    let mut b = ProgramBuilder::new();

    b.push(Op::End);

    b.finalize(metrics).expect("program build must succeed")
}

fn build_step_public_inputs(
    program: &zk_lisp_compiler::Program,
) -> zk_lisp_proof::pi::PublicInputs {
    PublicInputsBuilder::from_program(program)
        .build()
        .expect("pi build")
}

#[test]
fn step_proof_roundtrip_to_from_bytes_preserves_digest_and_meta() {
    let program = build_step_program();
    let pi = build_step_public_inputs(&program);
    let opts = make_step_opts();

    // Multi-step API must be consistent with single-step
    // API for the current single-segment planner.
    let steps = prove_program(&program, &pi, &opts).expect("prove_program_steps must succeed");
    assert_eq!(steps.len(), 1);

    let step_from_vec = &steps[0];
    let program = build_step_program();
    let pi = build_step_public_inputs(&program);
    let opts = make_step_opts();

    let steps = prove_program(&program, &pi, &opts).expect("step proof must succeed");
    let step = &steps[0];

    // Ensure prove_program_steps agrees with prove_step.
    assert_eq!(step_from_vec.digest(), step.digest());

    let digest = step.digest();
    let state_in = step.state_in_hash();
    let state_out = step.state_out_hash();
    let suite_id = step.proof.header.suite_id;
    let meta = step.proof.meta;
    let pi_core = step.pi_core.clone();

    let bytes = step
        .to_bytes()
        .expect("step proof serialization must succeed");

    let step2 = StepProof::from_bytes(&bytes).expect("step proof deserialization must succeed");

    // Step digest and state
    // hashes must be preserved.
    assert_eq!(digest, step2.digest());
    assert_eq!(state_in, step2.state_in_hash());
    assert_eq!(state_out, step2.state_out_hash());

    // Suite id and per-proof
    // metadata must match.
    assert_eq!(suite_id, step2.proof.header.suite_id);
    assert_eq!(meta.m, step2.proof.meta.m);
    assert_eq!(meta.rho, step2.proof.meta.rho);
    assert_eq!(meta.q, step2.proof.meta.q);
    assert_eq!(meta.o, step2.proof.meta.o);
    assert_eq!(meta.lambda, step2.proof.meta.lambda);
    assert_eq!(meta.pi_len, step2.proof.meta.pi_len);
    assert_eq!(meta.v_units, step2.proof.meta.v_units);

    // Core public inputs relevant
    // for AIR / recursion must match.
    assert_eq!(pi_core.program_id, step2.pi_core.program_id);
    assert_eq!(pi_core.program_commitment, step2.pi_core.program_commitment);
    assert_eq!(pi_core.merkle_root, step2.pi_core.merkle_root);
    assert_eq!(pi_core.feature_mask, step2.pi_core.feature_mask);
    assert_eq!(pi_core.main_args, step2.pi_core.main_args);
}

#[test]
fn step_proof_decode_rejects_invalid_magic() {
    let program = build_step_program();
    let pi = build_step_public_inputs(&program);
    let opts = make_step_opts();

    let steps = prove_program(&program, &pi, &opts).expect("step proof must succeed");
    let mut bytes = steps[0]
        .to_bytes()
        .expect("step proof serialization must succeed");

    // Corrupt magic tag.
    bytes[0] ^= 0xFF;

    let err = StepProof::from_bytes(&bytes).expect_err("invalid magic must be rejected");
    match err {
        error::Error::InvalidInput(msg) => {
            assert!(msg.contains("magic"));
        }
    }
}

#[test]
fn step_proof_decode_rejects_truncated_prefix() {
    let program = build_step_program();
    let pi = build_step_public_inputs(&program);
    let opts = make_step_opts();

    let steps = prove_program(&program, &pi, &opts).expect("step proof must succeed");
    let bytes = steps[0]
        .to_bytes()
        .expect("step proof serialization must succeed");

    // Drop most of the buffer so that
    // header / lambda bits are incomplete.
    let truncated = &bytes[..8];

    let err = StepProof::from_bytes(truncated).expect_err("truncated step proof must be rejected");
    match err {
        error::Error::InvalidInput(_msg) => {}
    }
}

#[test]
fn step_proof_decode_rejects_truncated_inner_proof() {
    let program = build_step_program();
    let pi = build_step_public_inputs(&program);
    let opts = make_step_opts();

    let steps = prove_program(&program, &pi, &opts).expect("step proof must succeed");
    let bytes = steps[0]
        .to_bytes()
        .expect("step proof serialization must succeed");

    // Truncate from the end so that inner proof
    // bytes do not match the advertised length.
    let truncated = &bytes[..bytes.len() - 1];

    let err = StepProof::from_bytes(truncated).expect_err("truncated inner proof must be rejected");
    match err {
        error::Error::InvalidInput(_msg) => {}
    }
}

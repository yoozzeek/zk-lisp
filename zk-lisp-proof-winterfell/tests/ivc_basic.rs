// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! End-to-end tests for the Winterfell IVC backend.
//!
//! These tests exercise the minimal IVC aggregation
//! flow over one or more step proofs using the
//! `IvBackend` interface implemented by
//! `WinterfellBackend`.

use zk_lisp_compiler::builder::{Op, ProgramBuilder};
use zk_lisp_proof::frontend::exec_root as frontend_exec_root;
use zk_lisp_proof::ivc::{IvBackend, IvPublic};
use zk_lisp_proof::{ProverOptions, pi::PublicInputsBuilder};
use zk_lisp_proof_winterfell::WinterfellBackend;

fn make_opts() -> ProverOptions {
    ProverOptions {
        min_security_bits: 40,
        blowup: 8,
        grind: 8,
        queries: 20,
    }
}

fn build_tiny_program() -> zk_lisp_compiler::Program {
    // A minimal no-op program: End
    let metrics = zk_lisp_compiler::CompilerMetrics::default();
    let mut b = ProgramBuilder::new();

    b.push(Op::End);

    b.finalize(metrics).expect("program build must succeed")
}

fn build_public_inputs(program: &zk_lisp_compiler::Program) -> zk_lisp_proof::pi::PublicInputs {
    PublicInputsBuilder::from_program(program)
        .build()
        .expect("pi build")
}

#[test]
fn ivc_single_step_roundtrip() {
    let program = build_tiny_program();
    let pi = build_public_inputs(&program);
    let opts = make_opts();

    // Produce a single step proof using the
    // backend-specific helper, then derive
    // its digest via IvBackend.
    let step = zk_lisp_proof_winterfell::prove::prove_step(&program, &pi, &opts)
        .expect("step proof must succeed");
    let step_digest = <WinterfellBackend as IvBackend>::step_digest(&step);

    let suite_id = pi.program_commitment;
    let prev_iv_digest = [0u8; 32];
    let exec_root =
        frontend_exec_root::<WinterfellBackend>(&suite_id, &prev_iv_digest, &[step_digest]);

    // Bind IVC public state to the VM state hashes
    // recorded in the step proof itself.
    let state_initial = step.state_in_hash();
    let state_final = step.state_out_hash();

    let meta = &step.proof.meta;
    let iv_pi = IvPublic {
        suite_id,
        program_id: pi.program_id,
        program_commitment: pi.program_commitment,
        state_initial,
        state_final,
        prev_iv_digest,
        exec_root,
        steps_count: 1,
        steps_ms: vec![meta.m],
        v_units_total: meta.v_units,
    };

    // Prove IVC over a single child step.
    let (iv_proof, iv_digest) = <WinterfellBackend as IvBackend>::prove_ivc(
        None,
        std::slice::from_ref(&step),
        &iv_pi,
        &opts,
    )
    .expect("ivc prove must succeed");

    // IvDigest must be stable and
    // derived from the same inputs.
    let recomputed = zk_lisp_proof_winterfell::zl_ivc::iv_digest(&iv_pi, &[step_digest]);
    assert_eq!(iv_digest, recomputed);

    // And the proof must verify under the same IvPublic.
    <WinterfellBackend as IvBackend>::verify_ivc(iv_proof, &iv_pi, &opts)
        .expect("ivc verify must succeed");
}

#[test]
fn ivc_prev_digest_non_zero_without_prev_rejected() {
    let program = build_tiny_program();
    let pi = build_public_inputs(&program);
    let opts = make_opts();

    let step = zk_lisp_proof_winterfell::prove::prove_step(&program, &pi, &opts)
        .expect("step proof must succeed");

    let suite_id = pi.program_commitment;
    let step_digest = <WinterfellBackend as IvBackend>::step_digest(&step);
    let prev_zero = [0u8; 32];
    let exec_root = frontend_exec_root::<WinterfellBackend>(&suite_id, &prev_zero, &[step_digest]);

    let meta = &step.proof.meta;
    let iv_pi = IvPublic {
        suite_id,
        program_id: pi.program_id,
        program_commitment: pi.program_commitment,
        state_initial: step.state_in_hash(),
        state_final: step.state_out_hash(),
        prev_iv_digest: [1u8; 32],
        exec_root,
        steps_count: 1,
        steps_ms: vec![meta.m],
        v_units_total: meta.v_units,
    };

    let err = <WinterfellBackend as IvBackend>::prove_ivc(
        None,
        std::slice::from_ref(&step),
        &iv_pi,
        &opts,
    )
    .expect_err("ivc prove must fail when prev_iv_digest is non-zero but prev is None");

    let msg = format!("{err}");
    assert!(msg.contains("prev_iv_digest must be zero for the first IVC step"));
}

#[test]
fn ivc_prev_digest_zero_with_prev_rejected() {
    let program = build_tiny_program();
    let pi = build_public_inputs(&program);
    let opts = make_opts();

    let step = zk_lisp_proof_winterfell::prove::prove_step(&program, &pi, &opts)
        .expect("step proof must succeed");

    let suite_id = pi.program_commitment;
    let step_digest = <WinterfellBackend as IvBackend>::step_digest(&step);
    let prev_zero = [0u8; 32];
    let exec_root = frontend_exec_root::<WinterfellBackend>(&suite_id, &prev_zero, &[step_digest]);

    let meta = &step.proof.meta;
    let iv_pi = IvPublic {
        suite_id,
        program_id: pi.program_id,
        program_commitment: pi.program_commitment,
        state_initial: step.state_in_hash(),
        state_final: step.state_out_hash(),
        prev_iv_digest: [0u8; 32],
        exec_root,
        steps_count: 1,
        steps_ms: vec![meta.m],
        v_units_total: meta.v_units,
    };

    let (iv_proof, _iv_digest) = <WinterfellBackend as IvBackend>::prove_ivc(
        None,
        std::slice::from_ref(&step),
        &iv_pi,
        &opts,
    )
    .expect("ivc prove must succeed with zero prev_iv_digest and prev=None");

    let err = <WinterfellBackend as IvBackend>::prove_ivc(
        Some(iv_proof),
        std::slice::from_ref(&step),
        &iv_pi,
        &opts,
    )
    .expect_err("ivc prove must fail when prev is Some but prev_iv_digest is zero");

    let msg = format!("{err}");
    assert!(msg.contains("prev_iv_digest must be non-zero when prev proof is supplied"));
}

// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Multistep end-to-end tests for the Winterfell IVC backend.

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
    // r0 <- 1; r1 <- 2; r0 <- r0 + r1; End
    let metrics = zk_lisp_compiler::CompilerMetrics::default();
    let mut b = ProgramBuilder::new();

    b.push(Op::Const { dst: 0, imm: 1 });
    b.push(Op::Const { dst: 1, imm: 2 });
    b.push(Op::Add { dst: 0, a: 0, b: 1 });
    b.push(Op::End);

    b.finalize(metrics).expect("program build must succeed")
}

fn build_public_inputs(program: &zk_lisp_compiler::Program) -> zk_lisp_proof::pi::PublicInputs {
    PublicInputsBuilder::from_program(program)
        .build()
        .expect("pi build")
}

#[test]
fn ivc_two_step_chain_prev_digest_tamper_rejected() {
    let program = build_tiny_program();
    let pi = build_public_inputs(&program);
    let opts = make_opts();

    let step1 = zk_lisp_proof_winterfell::prove::prove_step(&program, &pi, &opts)
        .expect("step1 proof must succeed");
    let step2 = zk_lisp_proof_winterfell::prove::prove_step(&program, &pi, &opts)
        .expect("step2 proof must succeed");

    let suite_id = pi.program_commitment;
    let zero = [0u8; 32];

    // Valid first step binds IvPublic
    // state to the VM state hashes
    // recorded in the step proof.
    let d1 = <WinterfellBackend as IvBackend>::step_digest(&step1);
    let exec_root1 = frontend_exec_root::<WinterfellBackend>(&suite_id, &zero, &[d1]);

    let iv1 = IvPublic {
        suite_id,
        program_id: pi.program_id,
        program_commitment: pi.program_commitment,
        state_initial: step1.state_in_hash(),
        state_final: step1.state_out_hash(),
        prev_iv_digest: zero,
        exec_root: exec_root1,
        steps_count: 1,
        steps_ms: vec![step1.proof.meta.m],
        v_units_total: step1.proof.meta.v_units,
    };

    let (iv_proof1, iv_digest1) = <WinterfellBackend as IvBackend>::prove_ivc(
        None,
        std::slice::from_ref(&step1),
        &iv1,
        &opts,
    )
    .expect("ivc step1 prove must succeed");

    // Valid second step with
    // its own state hashes.
    let d2 = <WinterfellBackend as IvBackend>::step_digest(&step2);
    let exec_root2 = frontend_exec_root::<WinterfellBackend>(&suite_id, &iv_digest1, &[d2]);

    let iv2 = IvPublic {
        suite_id,
        program_id: pi.program_id,
        program_commitment: pi.program_commitment,
        state_initial: step2.state_in_hash(),
        state_final: step2.state_out_hash(),
        prev_iv_digest: iv_digest1,
        exec_root: exec_root2,
        steps_count: 1,
        steps_ms: vec![step2.proof.meta.m],
        v_units_total: step2.proof.meta.v_units,
    };

    let (iv_proof2, _iv_digest2) = <WinterfellBackend as IvBackend>::prove_ivc(
        Some(iv_proof1),
        std::slice::from_ref(&step2),
        &iv2,
        &opts,
    )
    .expect("ivc step2 prove must succeed");

    // Tamper with prev_iv_digest in public inputs: the proof
    // should no longer verify under the mutated chain token.
    let mut iv2_bad = iv2;
    iv2_bad.prev_iv_digest[0] ^= 1;

    let err = <WinterfellBackend as IvBackend>::verify_ivc(iv_proof2, &iv2_bad, &opts)
        .expect_err("ivc verify must fail when prev_iv_digest is tampered");

    let _msg = format!("{err}");
}

#[test]
fn ivc_two_step_chain_aggregates_tamper_rejected() {
    let program = build_tiny_program();
    let pi = build_public_inputs(&program);
    let opts = make_opts();

    let step1 = zk_lisp_proof_winterfell::prove::prove_step(&program, &pi, &opts)
        .expect("step1 proof must succeed");
    let step2 = zk_lisp_proof_winterfell::prove::prove_step(&program, &pi, &opts)
        .expect("step2 proof must succeed");

    let suite_id = pi.program_commitment;
    let zero = [0u8; 32];

    // Build a valid first IVC step over step1.
    let d1 = <WinterfellBackend as IvBackend>::step_digest(&step1);
    let exec_root1 = frontend_exec_root::<WinterfellBackend>(&suite_id, &zero, &[d1]);

    let iv1 = IvPublic {
        suite_id,
        program_id: pi.program_id,
        program_commitment: pi.program_commitment,
        state_initial: step1.state_in_hash(),
        state_final: step1.state_out_hash(),
        prev_iv_digest: zero,
        exec_root: exec_root1,
        steps_count: 1,
        steps_ms: vec![step1.proof.meta.m],
        v_units_total: step1.proof.meta.v_units,
    };

    let (iv_proof1, iv_digest1) = <WinterfellBackend as IvBackend>::prove_ivc(
        None,
        std::slice::from_ref(&step1),
        &iv1,
        &opts,
    )
    .expect("ivc step1 prove must succeed");

    let d2 = <WinterfellBackend as IvBackend>::step_digest(&step2);
    let exec_root2 = frontend_exec_root::<WinterfellBackend>(&suite_id, &iv_digest1, &[d2]);

    let iv2 = IvPublic {
        suite_id,
        program_id: pi.program_id,
        program_commitment: pi.program_commitment,
        state_initial: step2.state_in_hash(),
        state_final: step2.state_out_hash(),
        prev_iv_digest: iv_digest1,
        exec_root: exec_root2,
        steps_count: 1,
        steps_ms: vec![step2.proof.meta.m],
        v_units_total: step2.proof.meta.v_units,
    };

    let (iv_proof2, _iv_digest2) = <WinterfellBackend as IvBackend>::prove_ivc(
        Some(iv_proof1),
        std::slice::from_ref(&step2),
        &iv2,
        &opts,
    )
    .expect("ivc step2 prove must succeed");

    // 1) prev_iv_digest tamper: already covered in a dedicated test,
    // but we also check here that verify fails when the chain token changes.
    let mut iv2_prev_bad = iv2.clone();
    iv2_prev_bad.prev_iv_digest[0] ^= 1;

    let _err =
        <WinterfellBackend as IvBackend>::verify_ivc(iv_proof2.clone(), &iv2_prev_bad, &opts)
            .expect_err("ivc verify must fail when prev_iv_digest is tampered");

    // 2) exec_root tamper: final root_out must match exec_root.
    let mut iv2_root_bad = iv2.clone();
    iv2_root_bad.exec_root[0] ^= 1;

    let _err =
        <WinterfellBackend as IvBackend>::verify_ivc(iv_proof2.clone(), &iv2_root_bad, &opts)
            .expect_err("ivc verify must fail when exec_root is tampered");

    // 3) v_units_total tamper: AIR enforces v_units_acc(last) == v_units_total.
    let mut iv2_v_units_bad = iv2.clone();
    iv2_v_units_bad.v_units_total = iv2_v_units_bad.v_units_total.saturating_add(1);

    let _err = <WinterfellBackend as IvBackend>::verify_ivc(iv_proof2, &iv2_v_units_bad, &opts)
        .expect_err("ivc verify must fail when v_units_total is tampered");
}

#[test]
fn ivc_two_step_chain_steps_ms_tamper_rejected_at_prove() {
    let program = build_tiny_program();
    let pi = build_public_inputs(&program);
    let opts = make_opts();

    let step1 = zk_lisp_proof_winterfell::prove::prove_step(&program, &pi, &opts)
        .expect("step1 proof must succeed");
    let step2 = zk_lisp_proof_winterfell::prove::prove_step(&program, &pi, &opts)
        .expect("step2 proof must succeed");

    let suite_id = pi.program_commitment;
    let zero = [0u8; 32];

    // First step is valid and binds
    // IvPublic state to the VM state
    // hashes recorded in the step proof.
    let d1 = <WinterfellBackend as IvBackend>::step_digest(&step1);
    let exec_root1 = frontend_exec_root::<WinterfellBackend>(&suite_id, &zero, &[d1]);

    let iv1 = IvPublic {
        suite_id,
        program_id: pi.program_id,
        program_commitment: pi.program_commitment,
        state_initial: step1.state_in_hash(),
        state_final: step1.state_out_hash(),
        prev_iv_digest: zero,
        exec_root: exec_root1,
        steps_count: 1,
        steps_ms: vec![step1.proof.meta.m],
        v_units_total: step1.proof.meta.v_units,
    };

    let (iv_proof1, iv_digest1) = <WinterfellBackend as IvBackend>::prove_ivc(
        None,
        std::slice::from_ref(&step1),
        &iv1,
        &opts,
    )
    .expect("ivc step1 prove must succeed");

    // Second step: build IvPublic with inconsistent steps_ms.
    let d2 = <WinterfellBackend as IvBackend>::step_digest(&step2);
    let exec_root2 = frontend_exec_root::<WinterfellBackend>(&suite_id, &iv_digest1, &[d2]);

    let iv2_bad = IvPublic {
        suite_id,
        program_id: pi.program_id,
        program_commitment: pi.program_commitment,
        state_initial: step2.state_in_hash(),
        state_final: step2.state_out_hash(),
        prev_iv_digest: iv_digest1,
        exec_root: exec_root2,
        steps_count: 1,
        steps_ms: vec![step2.proof.meta.m + 1], // mismatch with step meta
        v_units_total: step2.proof.meta.v_units,
    };

    let err = <WinterfellBackend as IvBackend>::prove_ivc(
        Some(iv_proof1),
        std::slice::from_ref(&step2),
        &iv2_bad,
        &opts,
    )
    .expect_err("ivc prove must fail when steps_ms does not match step meta");

    let msg = format!("{err}");
    assert!(msg.contains("steps_ms entry does not match step meta"));
}

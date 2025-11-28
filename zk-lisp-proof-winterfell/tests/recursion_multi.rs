// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Multi-step recursion chain tests for WinterfellBackend.

use zk_lisp_compiler::builder::{Op, ProgramBuilder};
use zk_lisp_proof::frontend::recursion_prove;
use zk_lisp_proof::pi::PublicInputsBuilder;
use zk_lisp_proof::recursion::{
    RecursionChainError, RecursionDigest, RecursionPublic, verify_chain,
};
use zk_lisp_proof::{ProverOptions, pi::PublicInputs as CorePublicInputs};
use zk_lisp_proof_winterfell::WinterfellBackend;
use zk_lisp_proof_winterfell::agg::pi::AggAirPublicInputs;

fn make_opts() -> ProverOptions {
    ProverOptions {
        min_security_bits: 40,
        blowup: 8,
        grind: 8,
        queries: 8,
        max_segment_rows: None,
        max_concurrent_segments: None,
    }
}

fn build_tiny_program() -> zk_lisp_compiler::Program {
    // A minimal no-op program: End
    let metrics = zk_lisp_compiler::CompilerMetrics::default();
    let mut b = ProgramBuilder::new();

    b.push(Op::End);

    b.finalize(metrics).expect("program build must succeed")
}

fn build_public_inputs(program: &zk_lisp_compiler::Program) -> CorePublicInputs {
    PublicInputsBuilder::from_program(program)
        .build()
        .expect("pi build")
}

fn build_agg_pi_for_single_step(
    step: &zk_lisp_proof_winterfell::proof::step::StepProof,
) -> AggAirPublicInputs {
    AggAirPublicInputs::from_step_proof(step).expect("agg PI build must succeed for step")
}

fn build_recursion_public_single_step(
    pi: &CorePublicInputs,
    step: &zk_lisp_proof_winterfell::proof::step::StepProof,
    agg_pi: &AggAirPublicInputs,
    prev_digest: RecursionDigest,
) -> RecursionPublic {
    RecursionPublic {
        suite_id: pi.program_commitment,
        program_id: pi.program_id,
        program_commitment: pi.program_commitment,
        state_initial: step.state_in_hash(),
        state_final: step.state_out_hash(),
        ram_gp_unsorted_initial: agg_pi.ram_gp_unsorted_initial,
        ram_gp_unsorted_final: agg_pi.ram_gp_unsorted_final,
        ram_gp_sorted_initial: agg_pi.ram_gp_sorted_initial,
        ram_gp_sorted_final: agg_pi.ram_gp_sorted_final,
        rom_s_initial: agg_pi.rom_s_initial,
        rom_s_final: agg_pi.rom_s_final,
        prev_digest,
        children_root: agg_pi.children_root,
        children_count: agg_pi.children_count,
        children_ms: agg_pi.children_ms.clone(),
        v_units_total: agg_pi.v_units_total,
    }
}

#[test]
fn recursion_two_step_chain_prev_digest_tamper_rejected() {
    let program = build_tiny_program();
    let pi = build_public_inputs(&program);
    let opts = make_opts();

    let steps1 = zk_lisp_proof_winterfell::prove::prove_program(&program, &pi, &opts)
        .expect("step1 proof must succeed");
    let steps2 = zk_lisp_proof_winterfell::prove::prove_program(&program, &pi, &opts)
        .expect("step2 proof must succeed");

    let step1 = &steps1[0];
    let step2 = &steps2[0];

    let agg_pi1 = build_agg_pi_for_single_step(&step1);
    let agg_pi2 = build_agg_pi_for_single_step(&step2);

    let (rc_proof1, rc_digest1) =
        recursion_prove::<WinterfellBackend>(std::slice::from_ref(&step1), &agg_pi1, &opts)
            .expect("recursion_prove must succeed for step1");

    let (rc_proof2, rc_digest2) =
        recursion_prove::<WinterfellBackend>(std::slice::from_ref(&step2), &agg_pi2, &opts)
            .expect("recursion_prove must succeed for step2");

    // Build a valid two-step recursion chain.
    let rc_pub1 = build_recursion_public_single_step(&pi, &step1, &agg_pi1, [0u8; 32]);
    let mut rc_pub2 = build_recursion_public_single_step(&pi, &step2, &agg_pi2, rc_digest1);

    // Enforce RAM/ROM chaining invariants at the DSL layer:
    // second step must start from the global boundary state
    // produced by the first step.
    rc_pub2.state_initial = rc_pub1.state_final;
    rc_pub2.ram_gp_unsorted_initial = rc_pub1.ram_gp_unsorted_final;
    rc_pub2.ram_gp_sorted_initial = rc_pub1.ram_gp_sorted_final;
    rc_pub2.rom_s_initial = rc_pub1.rom_s_final;

    let chain_ok = std::iter::once((
        rc_proof1.clone(),
        rc_digest1,
        agg_pi1.clone(),
        rc_pub1.clone(),
    ))
    .chain(std::iter::once((
        rc_proof2.clone(),
        rc_digest2,
        agg_pi2.clone(),
        rc_pub2.clone(),
    )));

    verify_chain::<WinterfellBackend, _>(chain_ok, &opts)
        .expect("recursion chain verify must succeed for honest two-step chain");

    // Now tamper prev_digest in the second chain public: the
    // chain checker must reject the mutated token.
    let mut rc_pub2_bad = rc_pub2;
    rc_pub2_bad.prev_digest[0] ^= 1;

    let chain_bad = std::iter::once((rc_proof1, rc_digest1, agg_pi1, rc_pub1)).chain(
        std::iter::once((rc_proof2, rc_digest2, agg_pi2, rc_pub2_bad)),
    );

    let err = verify_chain::<WinterfellBackend, _>(chain_bad, &opts)
        .expect_err("verify_recursion_chain must fail when prev_digest is tampered");

    match err {
        RecursionChainError::Invalid(msg) => {
            assert_eq!(
                msg,
                "RecursionPublic.prev_digest must match previous RecursionDigest",
            );
        }
        RecursionChainError::Backend(e) => {
            panic!("expected Invalid error, got backend error: {e:?}");
        }
    }
}

#[test]
fn recursion_two_step_chain_aggregates_tamper_rejected() {
    let program = build_tiny_program();
    let pi = build_public_inputs(&program);
    let opts = make_opts();

    let steps1 = zk_lisp_proof_winterfell::prove::prove_program(&program, &pi, &opts)
        .expect("step1 proof must succeed");
    let steps2 = zk_lisp_proof_winterfell::prove::prove_program(&program, &pi, &opts)
        .expect("step2 proof must succeed");

    let step1 = &steps1[0];
    let step2 = &steps2[0];

    let agg_pi1 = build_agg_pi_for_single_step(&step1);
    let agg_pi2 = build_agg_pi_for_single_step(&step2);

    let (rc_proof1, rc_digest1) =
        recursion_prove::<WinterfellBackend>(std::slice::from_ref(&step1), &agg_pi1, &opts)
            .expect("recursion_prove must succeed for step1");

    let (rc_proof2, rc_digest2) =
        recursion_prove::<WinterfellBackend>(std::slice::from_ref(&step2), &agg_pi2, &opts)
            .expect("recursion_prove must succeed for step2");

    // Build a valid chain first.
    let rc_pub1 = build_recursion_public_single_step(&pi, &step1, &agg_pi1, [0u8; 32]);
    let mut rc_pub2 = build_recursion_public_single_step(&pi, &step2, &agg_pi2, rc_digest1);

    // Enforce RAM/ROM chaining invariants at the DSL layer
    // for the second step.
    rc_pub2.state_initial = rc_pub1.state_final;
    rc_pub2.ram_gp_unsorted_initial = rc_pub1.ram_gp_unsorted_final;
    rc_pub2.ram_gp_sorted_initial = rc_pub1.ram_gp_sorted_final;
    rc_pub2.rom_s_initial = rc_pub1.rom_s_final;

    let chain_ok = std::iter::once((
        rc_proof1.clone(),
        rc_digest1,
        agg_pi1.clone(),
        rc_pub1.clone(),
    ))
    .chain(std::iter::once((
        rc_proof2.clone(),
        rc_digest2,
        agg_pi2.clone(),
        rc_pub2.clone(),
    )));

    verify_chain::<WinterfellBackend, _>(chain_ok, &opts)
        .expect("recursion chain verify must succeed for honest two-step chain");

    // 1) prev_digest tamper: already covered in a dedicated test,
    // but we also check here that verify fails when the chain token changes.
    let mut rc_pub2_prev_bad = rc_pub2.clone();
    rc_pub2_prev_bad.prev_digest[0] ^= 1;

    let chain_prev_bad = std::iter::once((
        rc_proof1.clone(),
        rc_digest1,
        agg_pi1.clone(),
        rc_pub1.clone(),
    ))
    .chain(std::iter::once((
        rc_proof2.clone(),
        rc_digest2,
        agg_pi2.clone(),
        rc_pub2_prev_bad,
    )));

    let _err = verify_chain::<WinterfellBackend, _>(chain_prev_bad, &opts)
        .expect_err("verify_recursion_chain must fail when prev_digest is tampered");

    // 2) children_root tamper: aggregation proof is bound to
    // AggAirPublicInputs.children_root, so verification must
    let mut agg_pi2_root_bad = agg_pi2.clone();
    agg_pi2_root_bad.children_root[0] ^= 1;

    let chain_root_bad = std::iter::once((
        rc_proof1.clone(),
        rc_digest1,
        agg_pi1.clone(),
        rc_pub1.clone(),
    ))
    .chain(std::iter::once((
        rc_proof2.clone(),
        rc_digest2,
        agg_pi2_root_bad,
        rc_pub2.clone(),
    )));

    let _err = verify_chain::<WinterfellBackend, _>(chain_root_bad, &opts)
        .expect_err("verify_recursion_chain must fail when children_root is tampered");

    // 3) v_units_total tamper: ZlAggAir enforces that the
    // final accumulator equals this value.
    let mut agg_pi2_v_units_bad = agg_pi2.clone();
    agg_pi2_v_units_bad.v_units_total = agg_pi2_v_units_bad.v_units_total.saturating_add(1);

    let chain_v_units_bad = std::iter::once((rc_proof1, rc_digest1, agg_pi1, rc_pub1)).chain(
        std::iter::once((rc_proof2, rc_digest2, agg_pi2_v_units_bad, rc_pub2)),
    );

    let _err = verify_chain::<WinterfellBackend, _>(chain_v_units_bad, &opts)
        .expect_err("verify_recursion_chain must fail when v_units_total is tampered");
}

#[test]
fn recursion_chain_suite_id_mismatch_rejected() {
    let program = build_tiny_program();
    let pi = build_public_inputs(&program);
    let opts = make_opts();

    let steps1 = zk_lisp_proof_winterfell::prove::prove_program(&program, &pi, &opts)
        .expect("step1 proof must succeed");
    let steps2 = zk_lisp_proof_winterfell::prove::prove_program(&program, &pi, &opts)
        .expect("step2 proof must succeed");

    let step1 = &steps1[0];
    let step2 = &steps2[0];

    let agg_pi1 = build_agg_pi_for_single_step(step1);
    let agg_pi2 = build_agg_pi_for_single_step(step2);

    let (rc_proof1, rc_digest1) =
        recursion_prove::<WinterfellBackend>(std::slice::from_ref(step1), &agg_pi1, &opts)
            .expect("recursion_prove must succeed for step1");

    let (rc_proof2, rc_digest2) =
        recursion_prove::<WinterfellBackend>(std::slice::from_ref(step2), &agg_pi2, &opts)
            .expect("recursion_prove must succeed for step2");

    let rc_pub1 = build_recursion_public_single_step(&pi, step1, &agg_pi1, [0u8; 32]);
    let mut rc_pub2 = build_recursion_public_single_step(&pi, step2, &agg_pi2, rc_digest1);

    // Build honest chain first
    rc_pub2.state_initial = rc_pub1.state_final;
    rc_pub2.ram_gp_unsorted_initial = rc_pub1.ram_gp_unsorted_final;
    rc_pub2.ram_gp_sorted_initial = rc_pub1.ram_gp_sorted_final;
    rc_pub2.rom_s_initial = rc_pub1.rom_s_final;

    // Break suite id
    let mut rc_pub2_bad = rc_pub2;
    rc_pub2_bad.suite_id[0] ^= 1;

    let chain = std::iter::once((rc_proof1, rc_digest1, agg_pi1, rc_pub1)).chain(std::iter::once(
        (rc_proof2, rc_digest2, agg_pi2, rc_pub2_bad),
    ));

    let err = verify_chain::<WinterfellBackend, _>(chain, &opts)
        .expect_err("verify_recursion_chain must fail when suite_id differs between steps");

    match err {
        RecursionChainError::Invalid(msg) => {
            assert_eq!(
                msg,
                "RecursionPublic.suite_id must be constant across recursion chain",
            );
        }
        RecursionChainError::Backend(e) => {
            panic!("expected Invalid error, got backend error: {e:?}");
        }
    }
}

#[test]
fn recursion_chain_program_id_mismatch_rejected() {
    let program = build_tiny_program();
    let pi = build_public_inputs(&program);
    let opts = make_opts();

    let steps1 = zk_lisp_proof_winterfell::prove::prove_program(&program, &pi, &opts)
        .expect("step1 proof must succeed");
    let steps2 = zk_lisp_proof_winterfell::prove::prove_program(&program, &pi, &opts)
        .expect("step2 proof must succeed");

    let step1 = &steps1[0];
    let step2 = &steps2[0];

    let agg_pi1 = build_agg_pi_for_single_step(step1);
    let agg_pi2 = build_agg_pi_for_single_step(step2);

    let (rc_proof1, rc_digest1) =
        recursion_prove::<WinterfellBackend>(std::slice::from_ref(step1), &agg_pi1, &opts)
            .expect("recursion_prove must succeed for step1");

    let (rc_proof2, rc_digest2) =
        recursion_prove::<WinterfellBackend>(std::slice::from_ref(step2), &agg_pi2, &opts)
            .expect("recursion_prove must succeed for step2");

    let rc_pub1 = build_recursion_public_single_step(&pi, step1, &agg_pi1, [0u8; 32]);
    let mut rc_pub2 = build_recursion_public_single_step(&pi, step2, &agg_pi2, rc_digest1);

    // Build honest chain first
    rc_pub2.state_initial = rc_pub1.state_final;
    rc_pub2.ram_gp_unsorted_initial = rc_pub1.ram_gp_unsorted_final;
    rc_pub2.ram_gp_sorted_initial = rc_pub1.ram_gp_sorted_final;
    rc_pub2.rom_s_initial = rc_pub1.rom_s_final;

    // Break program id
    let mut rc_pub2_bad = rc_pub2;
    rc_pub2_bad.program_id[0] ^= 1;

    let chain = std::iter::once((rc_proof1, rc_digest1, agg_pi1, rc_pub1)).chain(std::iter::once(
        (rc_proof2, rc_digest2, agg_pi2, rc_pub2_bad),
    ));

    let err = verify_chain::<WinterfellBackend, _>(chain, &opts)
        .expect_err("verify_recursion_chain must fail when program_id differs between steps");

    match err {
        RecursionChainError::Invalid(msg) => {
            assert_eq!(
                msg,
                "RecursionPublic.program_id must be constant across recursion chain",
            );
        }
        RecursionChainError::Backend(e) => {
            panic!("expected Invalid error, got backend error: {e:?}");
        }
    }
}

#[test]
fn recursion_chain_program_commitment_mismatch_rejected() {
    let program = build_tiny_program();
    let pi = build_public_inputs(&program);
    let opts = make_opts();

    let steps1 = zk_lisp_proof_winterfell::prove::prove_program(&program, &pi, &opts)
        .expect("step1 proof must succeed");
    let steps2 = zk_lisp_proof_winterfell::prove::prove_program(&program, &pi, &opts)
        .expect("step2 proof must succeed");

    let step1 = &steps1[0];
    let step2 = &steps2[0];

    let agg_pi1 = build_agg_pi_for_single_step(step1);
    let agg_pi2 = build_agg_pi_for_single_step(step2);

    let (rc_proof1, rc_digest1) =
        recursion_prove::<WinterfellBackend>(std::slice::from_ref(step1), &agg_pi1, &opts)
            .expect("recursion_prove must succeed for step1");

    let (rc_proof2, rc_digest2) =
        recursion_prove::<WinterfellBackend>(std::slice::from_ref(step2), &agg_pi2, &opts)
            .expect("recursion_prove must succeed for step2");

    let rc_pub1 = build_recursion_public_single_step(&pi, step1, &agg_pi1, [0u8; 32]);
    let mut rc_pub2 = build_recursion_public_single_step(&pi, step2, &agg_pi2, rc_digest1);

    // Build honest chain first
    rc_pub2.state_initial = rc_pub1.state_final;
    rc_pub2.ram_gp_unsorted_initial = rc_pub1.ram_gp_unsorted_final;
    rc_pub2.ram_gp_sorted_initial = rc_pub1.ram_gp_sorted_final;
    rc_pub2.rom_s_initial = rc_pub1.rom_s_final;

    // Then break program commitment
    let mut rc_pub2_bad = rc_pub2;
    rc_pub2_bad.program_commitment[0] ^= 1;

    let chain = std::iter::once((rc_proof1, rc_digest1, agg_pi1, rc_pub1)).chain(std::iter::once(
        (rc_proof2, rc_digest2, agg_pi2, rc_pub2_bad),
    ));

    let err = verify_chain::<WinterfellBackend, _>(chain, &opts).expect_err(
        "verify_recursion_chain must fail when program_commitment differs between steps",
    );

    match err {
        RecursionChainError::Invalid(msg) => {
            assert_eq!(
                msg,
                "RecursionPublic.program_commitment must be constant across recursion chain",
            );
        }
        RecursionChainError::Backend(e) => {
            panic!("expected Invalid error, got backend error: {e:?}");
        }
    }
}

#[test]
fn recursion_chain_ram_and_rom_mismatch_rejected() {
    let program = build_tiny_program();
    let pi = build_public_inputs(&program);
    let opts = make_opts();

    let steps1 = zk_lisp_proof_winterfell::prove::prove_program(&program, &pi, &opts)
        .expect("step1 proof must succeed");
    let steps2 = zk_lisp_proof_winterfell::prove::prove_program(&program, &pi, &opts)
        .expect("step2 proof must succeed");

    let step1 = &steps1[0];
    let step2 = &steps2[0];

    let agg_pi1 = build_agg_pi_for_single_step(step1);
    let agg_pi2 = build_agg_pi_for_single_step(step2);

    let (rc_proof1, rc_digest1) =
        recursion_prove::<WinterfellBackend>(std::slice::from_ref(step1), &agg_pi1, &opts)
            .expect("recursion_prove must succeed for step1");

    let (rc_proof2, rc_digest2) =
        recursion_prove::<WinterfellBackend>(std::slice::from_ref(step2), &agg_pi2, &opts)
            .expect("recursion_prove must succeed for step2");

    let rc_pub1 = build_recursion_public_single_step(&pi, step1, &agg_pi1, [0u8; 32]);
    let mut rc_pub2 = build_recursion_public_single_step(&pi, step2, &agg_pi2, rc_digest1);

    // Honest chain
    rc_pub2.state_initial = rc_pub1.state_final;
    rc_pub2.ram_gp_unsorted_initial = rc_pub1.ram_gp_unsorted_final;
    rc_pub2.ram_gp_sorted_initial = rc_pub1.ram_gp_sorted_final;
    rc_pub2.rom_s_initial = rc_pub1.rom_s_final;

    // 1) Break RAM unsorted chain
    let mut rc_pub2_ram_u_bad = rc_pub2.clone();
    rc_pub2_ram_u_bad.ram_gp_unsorted_initial[0] ^= 1;

    let chain_ram_u = std::iter::once((
        rc_proof1.clone(),
        rc_digest1,
        agg_pi1.clone(),
        rc_pub1.clone(),
    ))
    .chain(std::iter::once((
        rc_proof2.clone(),
        rc_digest2,
        agg_pi2.clone(),
        rc_pub2_ram_u_bad,
    )));

    let err = verify_chain::<WinterfellBackend, _>(chain_ram_u, &opts)
        .expect_err("verify_recursion_chain must fail when ram_gp_unsorted_initial != previous ram_gp_unsorted_final");

    match err {
        RecursionChainError::Invalid(msg) => {
            assert_eq!(
                msg,
                "RecursionPublic.ram_gp_unsorted_initial must match previous ram_gp_unsorted_final",
            );
        }
        RecursionChainError::Backend(e) => {
            panic!("expected Invalid error, got backend error: {e:?}");
        }
    }

    // 2) Break RAM sorted chain
    let mut rc_pub2_ram_s_bad = rc_pub2.clone();
    rc_pub2_ram_s_bad.ram_gp_sorted_initial[0] ^= 1;

    let chain_ram_s = std::iter::once((
        rc_proof1.clone(),
        rc_digest1,
        agg_pi1.clone(),
        rc_pub1.clone(),
    ))
    .chain(std::iter::once((
        rc_proof2.clone(),
        rc_digest2,
        agg_pi2.clone(),
        rc_pub2_ram_s_bad,
    )));

    let err = verify_chain::<WinterfellBackend, _>(chain_ram_s, &opts)
        .expect_err("verify_recursion_chain must fail when ram_gp_sorted_initial != previous ram_gp_sorted_final");

    match err {
        RecursionChainError::Invalid(msg) => {
            assert_eq!(
                msg,
                "RecursionPublic.ram_gp_sorted_initial must match previous ram_gp_sorted_final",
            );
        }
        RecursionChainError::Backend(e) => {
            panic!("expected Invalid error, got backend error: {e:?}");
        }
    }

    // 3) Break ROM chain
    let mut rc_pub2_rom_bad = rc_pub2.clone();
    rc_pub2_rom_bad.rom_s_initial[0][0] ^= 1;

    let chain_rom = std::iter::once((rc_proof1, rc_digest1, agg_pi1, rc_pub1)).chain(
        std::iter::once((rc_proof2, rc_digest2, agg_pi2, rc_pub2_rom_bad)),
    );

    let err = verify_chain::<WinterfellBackend, _>(chain_rom, &opts)
        .expect_err("verify_recursion_chain must fail when rom_s_initial != previous rom_s_final");

    match err {
        RecursionChainError::Invalid(msg) => {
            assert_eq!(
                msg,
                "RecursionPublic.rom_s_initial must match previous rom_s_final",
            );
        }
        RecursionChainError::Backend(e) => {
            panic!("expected Invalid error, got backend error: {e:?}");
        }
    }
}

// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Single-step and single-chain recursion tests for WinterfellBackend.

use blake3::Hasher;
use zk_lisp_compiler::builder::{Op, ProgramBuilder};
use zk_lisp_proof::frontend::recursion_prove;
use zk_lisp_proof::pi::PublicInputsBuilder;
use zk_lisp_proof::recursion::{
    RecursionChainError, RecursionDigest, RecursionPublic, verify_recursion_chain,
};
use zk_lisp_proof::{ProverOptions, pi::PublicInputs as CorePublicInputs};
use zk_lisp_proof_winterfell::WinterfellBackend;
use zk_lisp_proof_winterfell::agg_air::AggAirPublicInputs;

fn make_opts() -> ProverOptions {
    ProverOptions {
        min_security_bits: 40,
        blowup: 8,
        grind: 8,
        queries: 8,
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
    step: &zk_lisp_proof_winterfell::zl_step::ZlStepProof,
) -> AggAirPublicInputs {
    AggAirPublicInputs::from_step_proof(step).expect("agg PI build must succeed for step")
}

fn build_recursion_public_single_step(
    pi: &CorePublicInputs,
    step: &zk_lisp_proof_winterfell::zl_step::ZlStepProof,
    agg_pi: &AggAirPublicInputs,
    prev_digest: RecursionDigest,
) -> RecursionPublic {
    RecursionPublic {
        suite_id: pi.program_commitment,
        program_id: pi.program_id,
        program_commitment: pi.program_commitment,
        state_initial: step.state_in_hash(),
        state_final: step.state_out_hash(),
        prev_digest,
        children_root: agg_pi.children_root,
        children_count: agg_pi.children_count,
        children_ms: agg_pi.children_ms.clone(),
        v_units_total: agg_pi.v_units_total,
    }
}

#[test]
fn recursion_single_step_roundtrip() {
    let program = build_tiny_program();
    let pi = build_public_inputs(&program);
    let opts = make_opts();

    let step = zk_lisp_proof_winterfell::prove::prove_step(&program, &pi, &opts)
        .expect("step proof must succeed");

    let agg_pi = build_agg_pi_for_single_step(&step);

    let (rc_proof, rc_digest) =
        recursion_prove::<WinterfellBackend>(std::slice::from_ref(&step), &agg_pi, &opts)
            .expect("recursion_prove must succeed for a single honest step");

    // Expected recursion digest from AggAirPublicInputs.
    let expected_digest = {
        let mut h = Hasher::new();
        h.update(b"zkl/recursion/agg");
        h.update(&agg_pi.suite_id);
        h.update(&agg_pi.batch_id);
        h.update(&agg_pi.children_root);

        h.update(&agg_pi.children_count.to_le_bytes());
        h.update(&agg_pi.v_units_total.to_le_bytes());

        h.update(&agg_pi.profile_meta.m.to_le_bytes());
        h.update(&agg_pi.profile_meta.rho.to_le_bytes());
        h.update(&agg_pi.profile_meta.q.to_le_bytes());
        h.update(&agg_pi.profile_meta.o.to_le_bytes());
        h.update(&agg_pi.profile_meta.lambda.to_le_bytes());
        h.update(&agg_pi.profile_meta.pi_len.to_le_bytes());
        h.update(&agg_pi.profile_meta.v_units.to_le_bytes());

        h.update(&agg_pi.profile_fri.lde_blowup.to_le_bytes());
        h.update(&agg_pi.profile_fri.folding_factor.to_le_bytes());
        h.update(&agg_pi.profile_fri.redundancy.to_le_bytes());
        h.update(&agg_pi.profile_fri.num_layers.to_le_bytes());

        h.update(&agg_pi.profile_queries.num_queries.to_le_bytes());
        h.update(&agg_pi.profile_queries.grinding_factor.to_le_bytes());

        let digest = h.finalize();
        let mut out = [0u8; 32];
        out.copy_from_slice(digest.as_bytes());

        out
    };

    assert_eq!(
        rc_digest, expected_digest,
        "recursion digest must be derived from aggregation public inputs",
    );

    let rc_pub = build_recursion_public_single_step(&pi, &step, &agg_pi, [0u8; 32]);

    verify_recursion_chain::<WinterfellBackend, _>(
        std::iter::once((rc_proof, rc_digest, agg_pi, rc_pub)),
        &opts,
    )
    .expect("recursion chain verify must succeed for a single step");
}

#[test]
fn recursion_chain_prev_digest_non_zero_first_step_rejected() {
    let program = build_tiny_program();
    let pi = build_public_inputs(&program);
    let opts = make_opts();

    let step = zk_lisp_proof_winterfell::prove::prove_step(&program, &pi, &opts)
        .expect("step proof must succeed");

    let agg_pi = build_agg_pi_for_single_step(&step);

    let (rc_proof, rc_digest) =
        recursion_prove::<WinterfellBackend>(std::slice::from_ref(&step), &agg_pi, &opts)
            .expect("recursion_prove must succeed for a single honest step");

    let rc_pub = build_recursion_public_single_step(&pi, &step, &agg_pi, [1u8; 32]);

    let err = verify_recursion_chain::<WinterfellBackend, _>(
        std::iter::once((rc_proof, rc_digest, agg_pi, rc_pub)),
        &opts,
    )
    .expect_err("verify_recursion_chain must fail when first prev_digest is non-zero");

    match err {
        RecursionChainError::Invalid(msg) => {
            assert_eq!(msg, "first RecursionPublic.prev_digest must be zero");
        }
        RecursionChainError::Backend(e) => {
            panic!("expected Invalid error, got backend error: {e:?}");
        }
    }
}

#[test]
fn recursion_chain_state_initial_mismatch_rejected() {
    let program = build_tiny_program();
    let pi = build_public_inputs(&program);
    let opts = make_opts();

    let step1 = zk_lisp_proof_winterfell::prove::prove_step(&program, &pi, &opts)
        .expect("step1 proof must succeed");
    let step2 = zk_lisp_proof_winterfell::prove::prove_step(&program, &pi, &opts)
        .expect("step2 proof must succeed");

    let agg_pi1 = build_agg_pi_for_single_step(&step1);
    let agg_pi2 = build_agg_pi_for_single_step(&step2);

    let (rc_proof1, rc_digest1) =
        recursion_prove::<WinterfellBackend>(std::slice::from_ref(&step1), &agg_pi1, &opts)
            .expect("recursion_prove must succeed for step1");

    let (rc_proof2, rc_digest2) =
        recursion_prove::<WinterfellBackend>(std::slice::from_ref(&step2), &agg_pi2, &opts)
            .expect("recursion_prove must succeed for step2");

    let rc_pub1 = build_recursion_public_single_step(&pi, &step1, &agg_pi1, [0u8; 32]);

    let mut rc_pub2 = build_recursion_public_single_step(&pi, &step2, &agg_pi2, rc_digest1);
    rc_pub2.state_initial = [0u8; 32];

    let chain = std::iter::once((rc_proof1, rc_digest1, agg_pi1, rc_pub1))
        .chain(std::iter::once((rc_proof2, rc_digest2, agg_pi2, rc_pub2)));

    let err = verify_recursion_chain::<WinterfellBackend, _>(chain, &opts).expect_err(
        "verify_recursion_chain must fail when state_initial does not match previous state_final",
    );

    match err {
        RecursionChainError::Invalid(msg) => {
            assert_eq!(
                msg,
                "RecursionPublic.state_initial must match previous state_final",
            );
        }
        RecursionChainError::Backend(e) => {
            panic!("expected Invalid error, got backend error: {e:?}");
        }
    }
}

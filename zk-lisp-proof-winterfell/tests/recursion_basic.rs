// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

use blake3::Hasher;
use zk_lisp_compiler::builder::{Op, ProgramBuilder};
use zk_lisp_proof::frontend::{recursion_prove, recursion_verify};
use zk_lisp_proof::pi::PublicInputsBuilder;
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

#[test]
fn recursion_single_step_roundtrip() {
    let program = build_tiny_program();
    let pi = build_public_inputs(&program);
    let opts = make_opts();

    // Build a real step proof and derive aggregation public inputs
    // via the backend helper.
    let step = zk_lisp_proof_winterfell::prove::prove_step(&program, &pi, &opts)
        .expect("step proof must succeed");

    let agg_pi = build_agg_pi_for_single_step(&step);

    // Expected recursion digest from the effective aggregation
    // public inputs used by ZlAggAir. We intentionally mirror
    // the backend's digest construction here so that the test
    // stays self-contained.
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

    // Prove recursion aggregation over a single step proof
    // using the generic RecursionBackend interface.
    let (rc_proof, rc_digest) =
        recursion_prove::<WinterfellBackend>(std::slice::from_ref(&step), &agg_pi, &opts)
            .expect("recursion_prove must succeed for a single honest step");

    assert_eq!(
        rc_digest, expected_digest,
        "recursion digest must be derived from aggregation public inputs",
    );

    // Verify the recursion proof under the same RecursionPublic.
    recursion_verify::<WinterfellBackend>(rc_proof, &agg_pi, &opts)
        .expect("recursion_verify must succeed for honest aggregation proof");
}

#[test]
fn recursion_rejects_tampered_v_units_total_at_verify() {
    let program = build_tiny_program();
    let pi = build_public_inputs(&program);
    let opts = make_opts();

    let step = zk_lisp_proof_winterfell::prove::prove_step(&program, &pi, &opts)
        .expect("step proof must succeed");

    let agg_pi = build_agg_pi_for_single_step(&step);

    let (rc_proof, _rc_digest) =
        recursion_prove::<WinterfellBackend>(std::slice::from_ref(&step), &agg_pi, &opts)
            .expect("recursion_prove must succeed for a single honest step");

    // Tamper with v_units_total in the public inputs: ZlAggAir
    // enforces that the final accumulator equals this value, so
    // verification must fail under the mutated RecursionPublic.
    let mut bad_pi = agg_pi.clone();
    bad_pi.v_units_total = bad_pi.v_units_total.saturating_add(1);

    let err = recursion_verify::<WinterfellBackend>(rc_proof, &bad_pi, &opts)
        .expect_err("recursion_verify must fail when v_units_total is tampered");

    let _msg = format!("{err}");
}

#[test]
fn recursion_prove_rejects_wrong_children_root() {
    let program = build_tiny_program();
    let pi = build_public_inputs(&program);
    let opts = make_opts();

    let step = zk_lisp_proof_winterfell::prove::prove_step(&program, &pi, &opts)
        .expect("step proof must succeed");

    // Use an incorrect children_root to trigger builder error inside recursion_prove.
    let mut agg_pi = build_agg_pi_for_single_step(&step);
    agg_pi.children_root = [1u8; 32];

    let err = recursion_prove::<WinterfellBackend>(std::slice::from_ref(&step), &agg_pi, &opts)
        .expect_err("recursion_prove must fail when children_root is inconsistent");

    let msg = format!("{err}");
    assert!(
        msg.contains("children_root is inconsistent"),
        "error message must mention children_root inconsistency",
    );
}

#[test]
fn recursion_prove_rejects_wrong_v_units_total() {
    let program = build_tiny_program();
    let pi = build_public_inputs(&program);
    let opts = make_opts();

    let step = zk_lisp_proof_winterfell::prove::prove_step(&program, &pi, &opts)
        .expect("step proof must succeed");

    let mut agg_pi = build_agg_pi_for_single_step(&step);
    agg_pi.v_units_total = agg_pi.v_units_total.saturating_add(1); // mismatch

    let err = recursion_prove::<WinterfellBackend>(std::slice::from_ref(&step), &agg_pi, &opts)
        .expect_err("recursion_prove must fail when v_units_total mismatches transcripts");

    let msg = format!("{err}");
    assert!(
        msg.contains("AggAirPublicInputs.v_units_total must equal sum of child meta.v_units"),
        "error message must mention v_units_total mismatch",
    );
}

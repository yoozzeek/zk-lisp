// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Basic tests for the aggregation AIR (ZlAggAir) and
//! aggregation trace builder (build_agg_trace).

use std::panic;

use winterfell::crypto::{DefaultRandomCoin, Hasher, MerkleTree};
use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::matrix::ColMatrix;
use winterfell::{
    AcceptableOptions, Air, CompositionPoly, CompositionPolyTrace, DefaultConstraintCommitment,
    DefaultConstraintEvaluator, DefaultTraceLde, FieldExtension, PartitionOptions, Proof,
    ProofOptions, Prover, StarkDomain, Trace, TraceInfo, TracePolyTable, TraceTable,
};

use zk_lisp_compiler::builder::{Op, ProgramBuilder};
use zk_lisp_proof::ProverOptions;
use zk_lisp_proof::pi::PublicInputs as CorePublicInputs;
use zk_lisp_proof::pi::PublicInputsBuilder;
use zk_lisp_proof_winterfell::agg_air::{
    AggAirPublicInputs, AggFriProfile, AggProfileMeta, AggQueryProfile, ZlAggAir,
};
use zk_lisp_proof_winterfell::agg_child::{
    ZlChildCompact, ZlChildTranscript, children_root_from_compact,
};
use zk_lisp_proof_winterfell::agg_trace::{build_agg_trace, build_agg_trace_from_transcripts};
use zk_lisp_proof_winterfell::poseidon_hasher::PoseidonHasher;
use zk_lisp_proof_winterfell::zl_step::StepMeta;

/// Minimal prover wiring for
/// ZlAggAir used only in tests.
struct AggProver {
    options: ProofOptions,
    pub_inputs: AggAirPublicInputs,
}

impl AggProver {
    fn new(options: ProofOptions, pub_inputs: AggAirPublicInputs) -> Self {
        Self {
            options,
            pub_inputs,
        }
    }
}

impl Prover for AggProver {
    type BaseField = BE;
    type Air = ZlAggAir;
    type Trace = TraceTable<Self::BaseField>;
    type HashFn = PoseidonHasher<Self::BaseField>;
    type VC = MerkleTree<Self::HashFn>;
    type RandomCoin = DefaultRandomCoin<Self::HashFn>;
    type TraceLde<E: FieldElement<BaseField = Self::BaseField>> =
        DefaultTraceLde<E, Self::HashFn, Self::VC>;
    type ConstraintCommitment<E: FieldElement<BaseField = Self::BaseField>> =
        DefaultConstraintCommitment<E, Self::HashFn, Self::VC>;
    type ConstraintEvaluator<'a, E: FieldElement<BaseField = Self::BaseField>> =
        DefaultConstraintEvaluator<'a, Self::Air, E>;

    fn get_pub_inputs(&self, _trace: &Self::Trace) -> <Self::Air as Air>::PublicInputs {
        self.pub_inputs.clone()
    }

    fn options(&self) -> &ProofOptions {
        &self.options
    }

    fn new_trace_lde<E: FieldElement<BaseField = Self::BaseField>>(
        &self,
        trace_info: &TraceInfo,
        main_trace: &ColMatrix<Self::BaseField>,
        domain: &StarkDomain<Self::BaseField>,
        partition_option: PartitionOptions,
    ) -> (Self::TraceLde<E>, TracePolyTable<E>) {
        DefaultTraceLde::new(trace_info, main_trace, domain, partition_option)
    }

    fn build_constraint_commitment<E: FieldElement<BaseField = Self::BaseField>>(
        &self,
        composition_poly_trace: CompositionPolyTrace<E>,
        num_constraint_composition_columns: usize,
        domain: &StarkDomain<Self::BaseField>,
        partition_options: PartitionOptions,
    ) -> (Self::ConstraintCommitment<E>, CompositionPoly<E>) {
        DefaultConstraintCommitment::new(
            composition_poly_trace,
            num_constraint_composition_columns,
            domain,
            partition_options,
        )
    }

    fn new_evaluator<'a, E: FieldElement<BaseField = Self::BaseField>>(
        &self,
        air: &'a Self::Air,
        aux_rand_elements: Option<winterfell::AuxRandElements<E>>,
        composition_coefficients: winterfell::ConstraintCompositionCoefficients<E>,
    ) -> Self::ConstraintEvaluator<'a, E> {
        DefaultConstraintEvaluator::new(air, aux_rand_elements, composition_coefficients)
    }
}

fn make_wf_opts() -> ProofOptions {
    ProofOptions::new(
        16, // queries
        8,  // blowup
        0,  // grinding
        FieldExtension::None,
        2, // fri folding
        1, // max remainder degree
        winterfell::BatchingMethod::Linear,
        winterfell::BatchingMethod::Linear,
    )
}

fn make_children() -> Vec<ZlChildCompact> {
    let suite_id = [7u8; 32];

    // Two children with different m (base trace length)
    // but identical global STARK profile parameters
    // (rho, q, o, lambda, pi_len). This matches the
    // AggAirPublicInputs.profile_* contract.
    let meta1 = StepMeta::new(4, 8, 2, 2, 40, 1);
    let meta2 = StepMeta::new(8, 8, 2, 2, 40, 1);

    // For the initial aggregator skeleton we keep
    // trace roots trivial and equal to the public
    // `children_root` value used in tests (all zeros).
    let trace_root = [0u8; 32];

    let pi_core = CorePublicInputs::default();
    let rom_acc = [BE::ZERO; 3];
    let trace_roots = Vec::new();
    let constraint_root = [0u8; 32];
    let fri_roots = Vec::new();
    let pow_nonce = 0u64;

    let c1 = ZlChildCompact {
        suite_id,
        meta: meta1,
        pi_core: pi_core.clone(),
        rom_acc,
        step_digest: [1u8; 32],
        trace_root,
        trace_roots: trace_roots.clone(),
        constraint_root,
        fri_roots: fri_roots.clone(),
        pow_nonce,
        fs_challenges: None,
        merkle_proofs: None,
    };
    let c2 = ZlChildCompact {
        suite_id,
        meta: meta2,
        pi_core,
        rom_acc,
        step_digest: [2u8; 32],
        trace_root,
        trace_roots,
        constraint_root,
        fri_roots,
        pow_nonce,
        fs_challenges: None,
        merkle_proofs: None,
    };

    vec![c1, c2]
}

fn make_step_opts() -> ProverOptions {
    ProverOptions {
        min_security_bits: 40,
        blowup: 8,
        grind: 8,
        queries: 8,
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
fn agg_proof_roundtrip_ok() {
    let children = make_children();

    let m1 = children[0].meta.m;
    let m2 = children[1].meta.m;
    let v1 = children[0].meta.v_units;
    let v2 = children[1].meta.v_units;

    let children_root = children_root_from_compact(&children[0].suite_id, &children);

    let profile_meta = AggProfileMeta {
        m: children[0].meta.m,
        rho: children[0].meta.rho,
        q: children[0].meta.q,
        o: children[0].meta.o,
        lambda: children[0].meta.lambda,
        pi_len: children[0].meta.pi_len,
        v_units: children[0].meta.v_units,
    };

    let profile_fri = AggFriProfile {
        lde_blowup: 8,
        folding_factor: 2,
        redundancy: 1,
        num_layers: 0,
    };

    let profile_queries = AggQueryProfile {
        num_queries: children[0].meta.q,
        grinding_factor: 0,
    };

    let agg_pi = AggAirPublicInputs {
        children_root,
        v_units_total: v1 + v2,
        children_count: children.len() as u32,
        batch_id: [0u8; 32],
        profile_meta,
        profile_fri,
        profile_queries,
        suite_id: children[0].suite_id,
        children_ms: vec![m1, m2],
    };

    let agg_trace = build_agg_trace(&agg_pi, &children)
        .expect("agg trace build must succeed for consistent inputs");

    let opts = make_wf_opts();
    let prover = AggProver::new(opts.clone(), agg_pi.clone());

    // Prove and verify aggregation AIR.
    let proof: Proof = prover
        .prove(agg_trace.trace.clone())
        .expect("agg proof must be created");

    let acceptable = AcceptableOptions::MinConjecturedSecurity(40);

    winterfell::verify::<
        ZlAggAir,
        PoseidonHasher<BE>,
        DefaultRandomCoin<PoseidonHasher<BE>>,
        MerkleTree<PoseidonHasher<BE>>,
    >(proof, agg_pi, &acceptable)
    .expect("agg proof must verify");
}

#[test]
fn agg_build_rejects_wrong_v_units_total() {
    let children = make_children();

    let m1 = children[0].meta.m;
    let m2 = children[1].meta.m;
    let v1 = children[0].meta.v_units;
    let v2 = children[1].meta.v_units;

    let children_root = children_root_from_compact(&children[0].suite_id, &children);

    let profile_meta = AggProfileMeta {
        m: children[0].meta.m,
        rho: children[0].meta.rho,
        q: children[0].meta.q,
        o: children[0].meta.o,
        lambda: children[0].meta.lambda,
        pi_len: children[0].meta.pi_len,
        v_units: children[0].meta.v_units,
    };

    let profile_fri = AggFriProfile {
        lde_blowup: 8,
        folding_factor: 2,
        redundancy: 1,
        num_layers: 0,
    };

    let profile_queries = AggQueryProfile {
        num_queries: children[0].meta.q,
        grinding_factor: 0,
    };

    let agg_pi = AggAirPublicInputs {
        children_root,
        v_units_total: v1 + v2 + 1, // mismatch
        children_count: children.len() as u32,
        batch_id: [0u8; 32],
        profile_meta,
        profile_fri,
        profile_queries,
        suite_id: children[0].suite_id,
        children_ms: vec![m1, m2],
    };

    let err = build_agg_trace(&agg_pi, &children)
        .expect_err("agg trace build must fail when v_units_total mismatches");

    let msg = format!("{err}");
    assert!(msg.contains("v_units_total must equal sum of child meta.v_units"));
}

#[test]
fn agg_build_rejects_wrong_children_ms() {
    let children = make_children();

    let m1 = children[0].meta.m;
    let _m2 = children[1].meta.m;
    let v1 = children[0].meta.v_units;
    let v2 = children[1].meta.v_units;

    let children_root = children_root_from_compact(&children[0].suite_id, &children);

    // children_ms[1] mismatches meta.m for child 1
    let profile_meta = AggProfileMeta {
        m: children[0].meta.m,
        rho: children[0].meta.rho,
        q: children[0].meta.q,
        o: children[0].meta.o,
        lambda: children[0].meta.lambda,
        pi_len: children[0].meta.pi_len,
        v_units: children[0].meta.v_units,
    };

    let profile_fri = AggFriProfile {
        lde_blowup: 8,
        folding_factor: 2,
        redundancy: 1,
        num_layers: 0,
    };

    let profile_queries = AggQueryProfile {
        num_queries: children[0].meta.q,
        grinding_factor: 0,
    };

    let agg_pi = AggAirPublicInputs {
        children_root,
        v_units_total: v1 + v2,
        children_count: children.len() as u32,
        batch_id: [0u8; 32],
        profile_meta,
        profile_fri,
        profile_queries,
        suite_id: children[0].suite_id,
        children_ms: vec![m1, m1],
    };

    let err = build_agg_trace(&agg_pi, &children)
        .expect_err("agg trace build must fail when children_ms mismatches child meta.m");

    let msg = format!("{err}");
    assert!(msg.contains("children_ms entry does not match child meta.m"));
}

#[test]
fn agg_build_rejects_wrong_profile_meta() {
    let children = make_children();

    let m1 = children[0].meta.m;
    let m2 = children[1].meta.m;
    let v1 = children[0].meta.v_units;
    let v2 = children[1].meta.v_units;

    let children_root = children_root_from_compact(&children[0].suite_id, &children);

    // profile_meta.lambda mismatches child.meta.lambda
    let profile_meta = AggProfileMeta {
        m: children[0].meta.m,
        rho: children[0].meta.rho,
        q: children[0].meta.q,
        o: children[0].meta.o,
        lambda: children[0].meta.lambda + 1,
        pi_len: children[0].meta.pi_len,
        v_units: children[0].meta.v_units,
    };

    let profile_fri = AggFriProfile {
        lde_blowup: 8,
        folding_factor: 2,
        redundancy: 1,
        num_layers: 0,
    };

    let profile_queries = AggQueryProfile {
        num_queries: children[0].meta.q,
        grinding_factor: 0,
    };

    let agg_pi = AggAirPublicInputs {
        children_root,
        v_units_total: v1 + v2,
        children_count: children.len() as u32,
        batch_id: [0u8; 32],
        profile_meta,
        profile_fri,
        profile_queries,
        suite_id: children[0].suite_id,
        children_ms: vec![m1, m2],
    };

    let err = build_agg_trace(&agg_pi, &children)
        .expect_err("agg trace build must fail when profile_meta mismatches child StepMeta");

    let msg = format!("{err}");
    assert!(msg.contains("profile_meta is inconsistent with child StepMeta"));
}

#[test]
fn agg_build_rejects_mixed_suite_id() {
    let mut children = make_children();

    // Flip suite_id for the second child.
    children[1].suite_id = [9u8; 32];

    let m1 = children[0].meta.m;
    let m2 = children[1].meta.m;
    let v1 = children[0].meta.v_units;
    let v2 = children[1].meta.v_units;

    // children_root value is irrelevant here because the
    // suite_id consistency check fires first.
    let children_root = [0u8; 32];

    let profile_meta = AggProfileMeta {
        m: children[0].meta.m,
        rho: children[0].meta.rho,
        q: children[0].meta.q,
        o: children[0].meta.o,
        lambda: children[0].meta.lambda,
        pi_len: children[0].meta.pi_len,
        v_units: children[0].meta.v_units,
    };

    let profile_fri = AggFriProfile {
        lde_blowup: 8,
        folding_factor: 2,
        redundancy: 1,
        num_layers: 0,
    };

    let profile_queries = AggQueryProfile {
        num_queries: children[0].meta.q,
        grinding_factor: 0,
    };

    let agg_pi = AggAirPublicInputs {
        children_root,
        v_units_total: v1 + v2,
        children_count: children.len() as u32,
        batch_id: [0u8; 32],
        profile_meta,
        profile_fri,
        profile_queries,
        suite_id: [7u8; 32],
        children_ms: vec![m1, m2],
    };

    let err = build_agg_trace(&agg_pi, &children)
        .expect_err("agg trace build must fail when children have mixed suite_id");

    let msg = format!("{err}");
    assert!(msg.contains("suite_id must match suite_id of all children"));
}

#[test]
fn agg_merkle_binding_accepts_honest_child() {
    let program = build_step_program();
    let pi = build_step_public_inputs(&program);
    let opts = make_step_opts();

    let step = zk_lisp_proof_winterfell::prove::prove_step(&program, &pi, &opts)
        .expect("step proof must succeed");

    let child = ZlChildCompact::from_step(&step).expect("compact child must build");
    let children = vec![child.clone()];

    let children_root = children_root_from_compact(&child.suite_id, &children);

    let profile_meta = AggProfileMeta {
        m: child.meta.m,
        rho: child.meta.rho,
        q: child.meta.q,
        o: child.meta.o,
        lambda: child.meta.lambda,
        pi_len: child.meta.pi_len,
        v_units: child.meta.v_units,
    };

    let profile_fri = AggFriProfile {
        lde_blowup: 8,
        folding_factor: 2,
        redundancy: 1,
        num_layers: 0,
    };

    let profile_queries = AggQueryProfile {
        num_queries: child.meta.q,
        grinding_factor: 0,
    };

    let agg_pi = AggAirPublicInputs {
        children_root,
        v_units_total: child.meta.v_units,
        children_count: 1,
        batch_id: [0u8; 32],
        profile_meta,
        profile_fri,
        profile_queries,
        suite_id: child.suite_id,
        children_ms: vec![child.meta.m],
    };

    let agg_trace =
        build_agg_trace(&agg_pi, &children).expect("agg trace build must succeed for real child");

    // All Merkle error columns must be zero for an honest child.
    let cols = agg_trace.cols;
    let trace = &agg_trace.trace;
    for r in 0..trace.length() {
        assert_eq!(trace.get(cols.trace_root_err, r), BE::ZERO);
        assert_eq!(trace.get(cols.constraint_root_err, r), BE::ZERO);
    }

    // Prove and verify aggregation AIR with Merkle-bound child.
    let opts = make_wf_opts();
    let prover = AggProver::new(opts.clone(), agg_pi.clone());
    let proof: Proof = prover
        .prove(agg_trace.trace.clone())
        .expect("agg proof must be created for honest child");

    let acceptable = AcceptableOptions::MinConjecturedSecurity(40);

    winterfell::verify::<
        ZlAggAir,
        PoseidonHasher<BE>,
        DefaultRandomCoin<PoseidonHasher<BE>>,
        MerkleTree<PoseidonHasher<BE>>,
    >(proof, agg_pi, &acceptable)
    .expect("agg proof with Merkle binding must verify");
}

#[test]
fn agg_merkle_binding_rejects_tampered_trace_root() {
    let program = build_step_program();
    let pi = build_step_public_inputs(&program);
    let opts = make_step_opts();

    let step = zk_lisp_proof_winterfell::prove::prove_step(&program, &pi, &opts)
        .expect("step proof must succeed");

    let mut child = ZlChildCompact::from_step(&step).expect("compact child must build");

    // Corrupt the first trace root while keeping the aggregate
    // Blake3 root unchanged. This must be detected by Merkle
    // binding in the aggregator.
    if let Some(first) = child.trace_roots.first_mut() {
        first[0] ^= 1;
    }

    let children = vec![child.clone()];
    let children_root = children_root_from_compact(&child.suite_id, &children);

    let profile_meta = AggProfileMeta {
        m: child.meta.m,
        rho: child.meta.rho,
        q: child.meta.q,
        o: child.meta.o,
        lambda: child.meta.lambda,
        pi_len: child.meta.pi_len,
        v_units: child.meta.v_units,
    };

    let profile_fri = AggFriProfile {
        lde_blowup: 8,
        folding_factor: 2,
        redundancy: 1,
        num_layers: 0,
    };

    let profile_queries = AggQueryProfile {
        num_queries: child.meta.q,
        grinding_factor: 0,
    };

    let agg_pi = AggAirPublicInputs {
        children_root,
        v_units_total: child.meta.v_units,
        children_count: 1,
        batch_id: [0u8; 32],
        profile_meta,
        profile_fri,
        profile_queries,
        suite_id: child.suite_id,
        children_ms: vec![child.meta.m],
    };

    let agg_trace = build_agg_trace(&agg_pi, &children)
        .expect("agg trace build must succeed even for tampered child");

    let cols = agg_trace.cols;
    let trace = &agg_trace.trace;

    // Merkle error for trace root must be non-zero on the
    // first row of the child segment.
    assert_ne!(trace.get(cols.trace_root_err, 0), BE::ZERO);
}

#[test]
fn agg_fri_binding_accepts_honest_child_transcript() {
    let program = build_step_program();
    let pi = build_step_public_inputs(&program);
    let opts = make_step_opts();

    let step = zk_lisp_proof_winterfell::prove::prove_step(&program, &pi, &opts)
        .expect("step proof must succeed");

    let transcript =
        ZlChildTranscript::from_step(&step).expect("child transcript extraction must succeed");

    let child = transcript.compact.clone();
    let children = vec![child.clone()];
    let children_root = children_root_from_compact(&child.suite_id, &children);

    let profile_meta = AggProfileMeta {
        m: child.meta.m,
        rho: child.meta.rho,
        q: child.meta.q,
        o: child.meta.o,
        lambda: child.meta.lambda,
        pi_len: child.meta.pi_len,
        v_units: child.meta.v_units,
    };

    let profile_fri = AggFriProfile {
        lde_blowup: child.meta.rho as u32,
        folding_factor: 2,
        redundancy: 1,
        // We do not rely on num_layers here, but keeping it
        // consistent with transcript does not hurt.
        num_layers: transcript.fri_layers.len() as u8,
    };

    let profile_queries = AggQueryProfile {
        num_queries: child.meta.q,
        grinding_factor: 0,
    };

    let agg_pi = AggAirPublicInputs {
        children_root,
        v_units_total: child.meta.v_units,
        children_count: 1,
        batch_id: [0u8; 32],
        profile_meta,
        profile_fri,
        profile_queries,
        suite_id: child.suite_id,
        children_ms: vec![child.meta.m],
    };

    let agg_trace = build_agg_trace_from_transcripts(&agg_pi, &[transcript])
        .expect("agg trace build from transcripts must succeed for honest child");

    // Prove and verify aggregation AIR with a trace that
    // includes a minimal on-circuit FRI-folding sample.
    let opts = make_wf_opts();
    let prover = AggProver::new(opts.clone(), agg_pi.clone());
    let proof: Proof = prover
        .prove(agg_trace.trace.clone())
        .expect("agg proof must be created for honest FRI transcript");

    let acceptable = AcceptableOptions::MinConjecturedSecurity(40);

    winterfell::verify::<
        ZlAggAir,
        PoseidonHasher<BE>,
        DefaultRandomCoin<PoseidonHasher<BE>>,
        MerkleTree<PoseidonHasher<BE>>,
    >(proof, agg_pi, &acceptable)
    .expect("agg proof with FRI binding must verify");
}

#[test]
fn agg_fri_binding_rejects_tampered_fri_final() {
    let program = build_step_program();
    let pi = build_step_public_inputs(&program);
    let opts = make_step_opts();

    let step = zk_lisp_proof_winterfell::prove::prove_step(&program, &pi, &opts)
        .expect("step proof must succeed");

    let mut transcript =
        ZlChildTranscript::from_step(&step).expect("child transcript extraction must succeed");

    // Corrupt the FRI remainder polynomial so that
    // it no longer matches the recorded FRI layers.
    if let Some(c_last) = transcript.fri_final.coeffs.last_mut() {
        *c_last += BE::ONE;
    }

    let child = transcript.compact.clone();
    let children = vec![child.clone()];
    let children_root = children_root_from_compact(&child.suite_id, &children);

    let profile_meta = AggProfileMeta {
        m: child.meta.m,
        rho: child.meta.rho,
        q: child.meta.q,
        o: child.meta.o,
        lambda: child.meta.lambda,
        pi_len: child.meta.pi_len,
        v_units: child.meta.v_units,
    };

    let profile_fri = AggFriProfile {
        lde_blowup: child.meta.rho as u32,
        folding_factor: 2,
        redundancy: 1,
        num_layers: transcript.fri_layers.len() as u8,
    };

    let profile_queries = AggQueryProfile {
        num_queries: child.meta.q,
        grinding_factor: 0,
    };

    let agg_pi = AggAirPublicInputs {
        children_root,
        v_units_total: child.meta.v_units,
        children_count: 1,
        batch_id: [0u8; 32],
        profile_meta,
        profile_fri,
        profile_queries,
        suite_id: child.suite_id,
        children_ms: vec![child.meta.m],
    };

    let agg_trace = build_agg_trace_from_transcripts(&agg_pi, &[transcript])
        .expect("agg trace build from tampered transcript must still succeed");

    // Prove aggregation AIR and ensure that constraint evaluation fails
    // for the tampered FRI remainder. In debug/profile builds Winterfell
    // enforces this by panicking when a main transition constraint does
    // not evaluate to zero.
    let opts = make_wf_opts();
    let prover = AggProver::new(opts.clone(), agg_pi.clone());

    let result = panic::catch_unwind(|| {
        let _proof: Proof = prover
            .prove(agg_trace.trace.clone())
            .expect("agg proof construction unexpectedly succeeded for tampered FRI remainder");
    });

    assert!(
        result.is_err(),
        "agg prover must panic when FRI remainder is inconsistent with FRI layers",
    );
}

#[test]
fn agg_fri_binding_rejects_tampered_fri_layer_value() {
    let program = build_step_program();
    let pi = build_step_public_inputs(&program);
    let opts = make_step_opts();

    let step = zk_lisp_proof_winterfell::prove::prove_step(&program, &pi, &opts)
        .expect("step proof must succeed");

    let mut transcript =
        ZlChildTranscript::from_step(&step).expect("child transcript extraction must succeed");

    // Corrupt a single FRI layer-0 value while keeping the overall
    // transcript shape consistent. This should break DEEP vs FRI
    // layer-0 and FRI folding aggregates.
    if let Some(layer0) = transcript.fri_layers.get_mut(0) {
        if let Some(pair) = layer0.get_mut(0) {
            pair[0] += BE::ONE;
        }
    }

    let child = transcript.compact.clone();
    let children = vec![child.clone()];
    let children_root = children_root_from_compact(&child.suite_id, &children);

    let profile_meta = AggProfileMeta {
        m: child.meta.m,
        rho: child.meta.rho,
        q: child.meta.q,
        o: child.meta.o,
        lambda: child.meta.lambda,
        pi_len: child.meta.pi_len,
        v_units: child.meta.v_units,
    };

    let profile_fri = AggFriProfile {
        lde_blowup: child.meta.rho as u32,
        folding_factor: 2,
        redundancy: 1,
        num_layers: transcript.fri_layers.len() as u8,
    };

    let profile_queries = AggQueryProfile {
        num_queries: child.meta.q,
        grinding_factor: 0,
    };

    let agg_pi = AggAirPublicInputs {
        children_root,
        v_units_total: child.meta.v_units,
        children_count: 1,
        batch_id: [0u8; 32],
        profile_meta,
        profile_fri,
        profile_queries,
        suite_id: child.suite_id,
        children_ms: vec![child.meta.m],
    };

    let agg_trace = build_agg_trace_from_transcripts(&agg_pi, &[transcript])
        .expect("agg trace build from tampered transcript must still succeed");

    let opts = make_wf_opts();
    let prover = AggProver::new(opts.clone(), agg_pi.clone());

    let result = panic::catch_unwind(|| {
        let _proof: Proof = prover
            .prove(agg_trace.trace.clone())
            .expect("agg proof construction unexpectedly succeeded for tampered FRI layer");
    });

    assert!(
        result.is_err(),
        "agg prover must panic when FRI layer values are inconsistent with DEEP/FRI aggregates",
    );
}

#[test]
fn agg_builder_rejects_inconsistent_query_count() {
    let program = build_step_program();
    let pi = build_step_public_inputs(&program);
    let opts = make_step_opts();

    let step = zk_lisp_proof_winterfell::prove::prove_step(&program, &pi, &opts)
        .expect("step proof must succeed");

    let mut transcript =
        ZlChildTranscript::from_step(&step).expect("child transcript extraction must succeed");

    // Make transcript.num_queries inconsistent with FS query_positions
    // length so that aggregation helpers detect the mismatch.
    transcript.num_queries += 1;

    let child = transcript.compact.clone();
    let children = vec![child.clone()];
    let children_root = children_root_from_compact(&child.suite_id, &children);

    let profile_meta = AggProfileMeta {
        m: child.meta.m,
        rho: child.meta.rho,
        q: child.meta.q,
        o: child.meta.o,
        lambda: child.meta.lambda,
        pi_len: child.meta.pi_len,
        v_units: child.meta.v_units,
    };

    let profile_fri = AggFriProfile {
        lde_blowup: child.meta.rho as u32,
        folding_factor: 2,
        redundancy: 1,
        num_layers: transcript.fri_layers.len() as u8,
    };

    let profile_queries = AggQueryProfile {
        num_queries: child.meta.q,
        grinding_factor: 0,
    };

    let agg_pi = AggAirPublicInputs {
        children_root,
        v_units_total: child.meta.v_units,
        children_count: 1,
        batch_id: [0u8; 32],
        profile_meta,
        profile_fri,
        profile_queries,
        suite_id: child.suite_id,
        children_ms: vec![child.meta.m],
    };

    let result = build_agg_trace_from_transcripts(&agg_pi, &[transcript]);

    assert!(
        result.is_err(),
        "agg trace builder must reject transcripts with inconsistent num_queries",
    );
}

#[test]
fn agg_merkle_binding_rejects_tampered_trace_path() {
    let program = build_step_program();
    let pi = build_step_public_inputs(&program);
    let opts = make_step_opts();

    let step = zk_lisp_proof_winterfell::prove::prove_step(&program, &pi, &opts)
        .expect("step proof must succeed");

    let mut transcript =
        ZlChildTranscript::from_step(&step).expect("child transcript extraction must succeed");

    // Corrupt a single trace Merkle leaf so that Merkle binding
    // constraints detect an inconsistency with the trace root.
    if let Some(merkle) = &mut transcript.compact.merkle_proofs {
        if let Some(first_path) = merkle.trace_paths.get_mut(0) {
            first_path.leaf = PoseidonHasher::<BE>::hash(b"tampered_trace_leaf");
        }
    }

    let child = transcript.compact.clone();
    let children = vec![child.clone()];
    let children_root = children_root_from_compact(&child.suite_id, &children);

    let profile_meta = AggProfileMeta {
        m: child.meta.m,
        rho: child.meta.rho,
        q: child.meta.q,
        o: child.meta.o,
        lambda: child.meta.lambda,
        pi_len: child.meta.pi_len,
        v_units: child.meta.v_units,
    };

    let profile_fri = AggFriProfile {
        lde_blowup: child.meta.rho as u32,
        folding_factor: 2,
        redundancy: 1,
        num_layers: transcript.fri_layers.len() as u8,
    };

    let profile_queries = AggQueryProfile {
        num_queries: child.meta.q,
        grinding_factor: 0,
    };

    let agg_pi = AggAirPublicInputs {
        children_root,
        v_units_total: child.meta.v_units,
        children_count: 1,
        batch_id: [0u8; 32],
        profile_meta,
        profile_fri,
        profile_queries,
        suite_id: child.suite_id,
        children_ms: vec![child.meta.m],
    };

    let agg_trace = build_agg_trace_from_transcripts(&agg_pi, &[transcript])
        .expect("agg trace build from tampered transcript must still succeed");

    let opts = make_wf_opts();
    let prover = AggProver::new(opts.clone(), agg_pi.clone());

    let result = panic::catch_unwind(|| {
        let _proof: Proof = prover
            .prove(agg_trace.trace.clone())
            .expect("agg proof construction unexpectedly succeeded for tampered Merkle paths");
    });

    assert!(
        result.is_err(),
        "agg prover must panic when Merkle paths are inconsistent with commitment roots",
    );
}

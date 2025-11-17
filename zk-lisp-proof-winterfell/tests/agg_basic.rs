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

use winterfell::crypto::{DefaultRandomCoin, MerkleTree};
use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::matrix::ColMatrix;
use winterfell::{
    AcceptableOptions, Air, CompositionPoly, CompositionPolyTrace, DefaultConstraintCommitment,
    DefaultConstraintEvaluator, DefaultTraceLde, FieldExtension, PartitionOptions, Proof,
    ProofOptions, Prover, StarkDomain, TraceInfo, TracePolyTable, TraceTable,
};

use zk_lisp_proof::pi::PublicInputs as CorePublicInputs;
use zk_lisp_proof_winterfell::agg_air::{AggAirPublicInputs, ZlAggAir};
use zk_lisp_proof_winterfell::agg_child::{ZlChildCompact, children_root_from_compact};
use zk_lisp_proof_winterfell::agg_trace::build_agg_trace;
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

    // Two children with different m and v_units.
    let meta1 = StepMeta::new(4, 8, 2, 2, 40, 1);
    let meta2 = StepMeta::new(8, 8, 3, 2, 40, 1);

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

#[test]
fn agg_proof_roundtrip_ok() {
    let children = make_children();

    let m1 = children[0].meta.m;
    let m2 = children[1].meta.m;
    let v1 = children[0].meta.v_units;
    let v2 = children[1].meta.v_units;

    let children_root = children_root_from_compact(&children[0].suite_id, &children);

    let agg_pi = AggAirPublicInputs {
        suite_id: children[0].suite_id,
        children_root,
        v_units_total: v1 + v2,
        children_count: children.len() as u32,
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

    let agg_pi = AggAirPublicInputs {
        suite_id: children[0].suite_id,
        children_root,
        v_units_total: v1 + v2 + 1, // mismatch
        children_count: children.len() as u32,
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
    let agg_pi = AggAirPublicInputs {
        suite_id: children[0].suite_id,
        children_root,
        v_units_total: v1 + v2,
        children_count: children.len() as u32,
        children_ms: vec![m1, m1],
    };

    let err = build_agg_trace(&agg_pi, &children)
        .expect_err("agg trace build must fail when children_ms mismatches child meta.m");

    let msg = format!("{err}");
    assert!(msg.contains("children_ms entry does not match child meta.m"));
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

    let agg_pi = AggAirPublicInputs {
        suite_id: [7u8; 32],
        children_root,
        v_units_total: v1 + v2,
        children_count: children.len() as u32,
        children_ms: vec![m1, m2],
    };

    let err = build_agg_trace(&agg_pi, &children)
        .expect_err("agg trace build must fail when children have mixed suite_id");

    let msg = format!("{err}");
    assert!(msg.contains("suite_id must match suite_id of all children"));
}

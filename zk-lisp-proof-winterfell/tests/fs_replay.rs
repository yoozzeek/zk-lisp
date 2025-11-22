// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Smoke tests for FS replay against
//! real Winterfell step proofs.
//!
//! These tests exercise `replay_fs_from_step`
//! on a tiny zk-lisp program and enforce basic
//! invariants over the reconstructed Fiat–Shamir
//! challenges (OOD point, DEEP coeffs, FRI alphas
//! and query positions).

use winterfell::Air;
use winterfell::crypto::{DefaultRandomCoin, ElementHasher, RandomCoin};
use winterfell::math::FieldElement;
use winterfell::math::ToElements;
use winterfell::math::fields::f128::BaseElement as BE;
use zk_lisp_compiler::builder::{Op, ProgramBuilder};
use zk_lisp_proof::ProverOptions;
use zk_lisp_proof::pi::PublicInputsBuilder;
use zk_lisp_proof_winterfell::agg::fs::replay_fs_from_step;
use zk_lisp_proof_winterfell::poseidon::hasher::PoseidonHasher;
use zk_lisp_proof_winterfell::vm::air::ZkLispAir;

fn make_opts() -> ProverOptions {
    ProverOptions {
        min_security_bits: 40,
        blowup: 8,
        grind: 8,
        queries: 20,
        max_segment_rows: None,
    }
}

fn build_tiny_program() -> zk_lisp_compiler::Program {
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
fn fs_replay_smoke_invariants() {
    let program = build_tiny_program();
    let pi = build_public_inputs(&program);
    let opts = make_opts();

    let step = zk_lisp_proof_winterfell::prove::prove_step(&program, &pi, &opts)
        .expect("step proof must succeed");

    let fs = replay_fs_from_step(&step).expect("FS replay must succeed");

    let wf_proof = &step.proof.inner;
    let options = wf_proof.options();

    // Query positions must match
    // num_unique_queries and
    let num_unique = wf_proof.num_unique_queries as usize;
    if num_unique == 0 {
        assert!(fs.query_positions.is_empty());
    } else {
        assert_eq!(fs.query_positions.len(), num_unique);
        let lde_domain_size = wf_proof.lde_domain_size();
        for &idx in &fs.query_positions {
            assert!((idx as usize) < lde_domain_size);
        }
    }

    // OOD point must be present and non-zero.
    assert_eq!(fs.ood_points.len(), 1);
    assert_ne!(fs.ood_points[0], BE::ZERO);

    // DEEP coefficients must be non-empty.
    assert!(!fs.deep_coeffs.is_empty());

    // There must be exactly one FRI alpha per FRI commitment (including
    // the remainder commitment), matching the commitments parser.
    use zk_lisp_proof_winterfell::poseidon::hasher::PoseidonHasher;
    let trace_info = wf_proof.trace_info();
    let num_trace_segments = trace_info.num_segments();
    let fri_opts = options.to_fri_options();
    let lde_domain_size = wf_proof.lde_domain_size();
    let num_fri_layers = fri_opts.num_fri_layers(lde_domain_size);
    let (_trace_roots, _constraint_root, fri_roots) = wf_proof
        .commitments
        .clone()
        .parse::<PoseidonHasher<BE>>(num_trace_segments, num_fri_layers)
        .expect("commitments parse in fs_replay test");

    assert_eq!(fs.fri_alphas.len(), fri_roots.len());
}

#[test]
fn fs_replay_matches_reference_coin() {
    let program = build_tiny_program();
    let pi = build_public_inputs(&program);
    let opts = make_opts();

    let step = zk_lisp_proof_winterfell::prove::prove_step(&program, &pi, &opts)
        .expect("step proof must succeed");

    let fs = replay_fs_from_step(&step).expect("FS replay must succeed");

    let wf_proof = &step.proof.inner;

    // Rebuild AIR public inputs and
    // seed the public coin the same
    let pi_zl1 = &step.proof.pi;
    let air_pi = zk_lisp_proof_winterfell::AirPublicInputs {
        core: step.pi_core.clone(),
        segment_feature_mask: 0,
        rom_acc: step.rom_acc,
        pc_init: zk_lisp_proof_winterfell::utils::fe_from_bytes_fold(&pi_zl1.pc_init),
        ram_gp_unsorted_in: zk_lisp_proof_winterfell::utils::fe_from_bytes_fold(
            &pi_zl1.ram_gp_unsorted_in,
        ),
        ram_gp_unsorted_out: zk_lisp_proof_winterfell::utils::fe_from_bytes_fold(
            &pi_zl1.ram_gp_unsorted_out,
        ),
        ram_gp_sorted_in: zk_lisp_proof_winterfell::utils::fe_from_bytes_fold(
            &pi_zl1.ram_gp_sorted_in,
        ),
        ram_gp_sorted_out: zk_lisp_proof_winterfell::utils::fe_from_bytes_fold(
            &pi_zl1.ram_gp_sorted_out,
        ),
        rom_s_in: [
            zk_lisp_proof_winterfell::utils::fe_from_bytes_fold(&pi_zl1.rom_s_in_0),
            zk_lisp_proof_winterfell::utils::fe_from_bytes_fold(&pi_zl1.rom_s_in_1),
            zk_lisp_proof_winterfell::utils::fe_from_bytes_fold(&pi_zl1.rom_s_in_2),
        ],
        rom_s_out: [
            zk_lisp_proof_winterfell::utils::fe_from_bytes_fold(&pi_zl1.rom_s_out_0),
            zk_lisp_proof_winterfell::utils::fe_from_bytes_fold(&pi_zl1.rom_s_out_1),
            zk_lisp_proof_winterfell::utils::fe_from_bytes_fold(&pi_zl1.rom_s_out_2),
        ],
    };

    let mut seed_elems = wf_proof.context.to_elements();
    let mut pi_elems = air_pi.to_elements();
    seed_elems.append(&mut pi_elems);

    let mut coin = DefaultRandomCoin::<PoseidonHasher<BE>>::new(&seed_elems);

    // Instantiate AIR and parse commitments
    // into trace / constraint / FRI roots.
    let trace_info = wf_proof.trace_info().clone();
    let options = wf_proof.options().clone();
    let air = ZkLispAir::new(trace_info, air_pi, options.clone());

    let num_trace_segments = air.trace_info().num_segments();
    let lde_domain_size = wf_proof.lde_domain_size();
    let fri_opts = options.to_fri_options();
    let num_fri_layers = fri_opts.num_fri_layers(lde_domain_size);

    let commitments = wf_proof
        .commitments
        .clone()
        .parse::<PoseidonHasher<BE>>(num_trace_segments, num_fri_layers)
        .expect("commitments parse in reference FS coin");

    let (trace_roots_h, constraint_root_h, fri_roots_h) = commitments;
    assert!(!trace_roots_h.is_empty());

    // 1) Trace commitments and auxiliary randomness.
    coin.reseed(trace_roots_h[0]);

    if air.trace_info().is_multi_segment() {
        let _aux_rand = air
            .get_aux_rand_elements::<BE, DefaultRandomCoin<PoseidonHasher<BE>>>(&mut coin)
            .expect("aux rand in reference FS coin");

        coin.reseed(trace_roots_h[1]);
    }

    // 2) Constraint commitment and OOD point.
    coin.reseed(constraint_root_h);

    let _z_ood: BE = coin.draw().expect("draw OOD point in reference FS coin");

    // 3) OOD evaluations and reseeding with their hash.
    let main_width = air.trace_info().main_trace_width();
    let aux_width = air.trace_info().aux_segment_width();
    let constraint_frame_width = air.context().num_constraint_composition_columns();

    let (trace_ood_frame, quotient_ood_frame) = wf_proof
        .ood_frame
        .clone()
        .parse::<BE>(main_width, aux_width, constraint_frame_width)
        .expect("invalid OOD frame layout in reference FS coin");

    let mut current_row = trace_ood_frame.current_row().to_vec();
    current_row.extend_from_slice(quotient_ood_frame.current_row());

    let mut next_row = trace_ood_frame.next_row().to_vec();
    next_row.extend_from_slice(quotient_ood_frame.next_row());

    let mut ood_evals = current_row;
    ood_evals.extend_from_slice(&next_row);

    let ood_digest = PoseidonHasher::<BE>::hash_elements(&ood_evals);
    coin.reseed(ood_digest);

    // 4) DEEP composition coefficients (only for coin state evolution).
    let _deep = air
        .get_deep_composition_coefficients::<BE, DefaultRandomCoin<PoseidonHasher<BE>>>(&mut coin)
        .expect("deep coeffs in reference FS coin");

    // 5) FRI layer alphas.
    let mut fri_alphas_ref = Vec::with_capacity(fri_roots_h.len());
    let mut max_degree_plus_1 = air.trace_poly_degree() + 1;

    for (depth, root) in fri_roots_h.iter().enumerate() {
        coin.reseed(*root);
        let alpha: BE = coin.draw().expect("draw FRI alpha in reference FS coin");
        fri_alphas_ref.push(alpha);

        if depth != fri_roots_h.len() - 1
            && !max_degree_plus_1.is_multiple_of(fri_opts.folding_factor())
        {
            panic!("FRI degree truncation detected in reference FS coin");
        }
        max_degree_plus_1 /= fri_opts.folding_factor();
    }

    assert_eq!(fs.fri_alphas, fri_alphas_ref);

    // 6) Query positions via PoW nonce and draw_integers.
    let pow_nonce = wf_proof.pow_nonce;
    let grinding_factor = air.options().grinding_factor();

    assert!(
        coin.check_leading_zeros(pow_nonce) >= grinding_factor,
        "pow_nonce must satisfy grinding factor in reference FS coin",
    );

    let num_queries = air.options().num_queries();
    let lde_domain_size_air = air.lde_domain_size();
    let lde_domain_size_proof = wf_proof.lde_domain_size();
    assert_eq!(lde_domain_size_air, lde_domain_size_proof);

    let mut positions_ref = coin
        .draw_integers(num_queries, lde_domain_size_air, pow_nonce)
        .expect("draw query positions in reference FS coin");

    positions_ref.sort_unstable();
    positions_ref.dedup();

    let num_unique_queries = wf_proof.num_unique_queries as usize;
    assert_eq!(positions_ref.len(), num_unique_queries);

    let query_positions_ref: Vec<u32> = positions_ref.into_iter().map(|p| p as u32).collect();

    assert_eq!(fs.query_positions, query_positions_ref);
}

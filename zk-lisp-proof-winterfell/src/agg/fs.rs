// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Poseidon-based Fiat–Shamir helpers for zk-lisp child proofs.

use crate::AirPublicInputs;
use crate::agg::child::ZlFsChallenges;
use crate::poseidon::hasher::PoseidonHasher;
use crate::proof::step::StepProof;
use crate::vm::air::ZkLispAir;

use winterfell::Air;
use winterfell::crypto::{DefaultRandomCoin, ElementHasher, RandomCoin};
use winterfell::math::ToElements;
use winterfell::math::fields::f128::BaseElement as BE;
use zk_lisp_proof::error;

/// Replay Fiat–Shamir challenges for
/// a zk-lisp step proof by mirroring
/// Winterfell's verifier transcript
/// (DefaultRandomCoin + VerifierChannel).
///
/// This function derives the public coin seed
/// from the proof context and AIR public inputs,
/// then applies the same reseeding and draw sequence
/// as `winter_verifier::perform_verification` up to
/// the point where FRI verification starts.
/// The resulting `ZlFsChallenges` can be used by the
/// aggregation layer as a single source of randomness
/// consistent with both the original prover and verifier.
pub fn replay_fs_from_step(step: &StepProof) -> error::Result<ZlFsChallenges> {
    let wf_proof = &step.proof.inner;

    // Rebuild AIR public inputs for this proof instance.
    let pi_zl1 = &step.proof.pi;

    let air_pi = AirPublicInputs {
        core: step.pi_core.clone(),
        rom_acc: step.rom_acc,
        pc_init: crate::utils::fe_from_bytes_fold(&pi_zl1.pc_init),
        ram_gp_unsorted_in: crate::utils::fe_from_bytes_fold(&pi_zl1.ram_gp_unsorted_in),
        ram_gp_unsorted_out: crate::utils::fe_from_bytes_fold(&pi_zl1.ram_gp_unsorted_out),
        ram_gp_sorted_in: crate::utils::fe_from_bytes_fold(&pi_zl1.ram_gp_sorted_in),
        ram_gp_sorted_out: crate::utils::fe_from_bytes_fold(&pi_zl1.ram_gp_sorted_out),
        rom_s_in: [
            crate::utils::fe_from_bytes_fold(&pi_zl1.rom_s_in_0),
            crate::utils::fe_from_bytes_fold(&pi_zl1.rom_s_in_1),
            crate::utils::fe_from_bytes_fold(&pi_zl1.rom_s_in_2),
        ],
        rom_s_out: [
            crate::utils::fe_from_bytes_fold(&pi_zl1.rom_s_out_0),
            crate::utils::fe_from_bytes_fold(&pi_zl1.rom_s_out_1),
            crate::utils::fe_from_bytes_fold(&pi_zl1.rom_s_out_2),
        ],
    };

    // Seed for the public coin:
    // proof context elements + AIR public inputs,
    let mut seed_elems = wf_proof.context.to_elements();
    let mut pi_elems = air_pi.to_elements();
    seed_elems.append(&mut pi_elems);

    let mut coin = DefaultRandomCoin::<PoseidonHasher<BE>>::new(&seed_elems);

    // Instantiate AIR for this proof
    // instance so that auxiliary randomness
    let trace_info = wf_proof.trace_info().clone();
    let options = wf_proof.options().clone();
    let air = ZkLispAir::new(trace_info, air_pi, options.clone());

    // Parse commitments into
    // trace / constraint / FRI roots using the
    let num_trace_segments = air.trace_info().num_segments();
    let lde_domain_size = wf_proof.lde_domain_size();
    let fri_opts = options.to_fri_options();
    let num_fri_layers = fri_opts.num_fri_layers(lde_domain_size);

    let commitments = wf_proof
        .commitments
        .clone()
        .parse::<PoseidonHasher<BE>>(num_trace_segments, num_fri_layers)
        .map_err(|_| {
            error::Error::InvalidInput("invalid Winterfell commitments layout in FS replay")
        })?;

    let (trace_roots_h, constraint_root_h, fri_roots_h) = commitments;
    if trace_roots_h.is_empty() {
        return Err(error::Error::InvalidInput(
            "FS replay requires at least one trace commitment root",
        ));
    }

    // 1) Trace commitments and auxiliary randomness
    // ---------------------------------------------
    // Match winter_verifier::perform_verification:
    // reseed with main trace commitment, draw
    // auxiliary random elements if the trace is
    // multi-segment, then reseed with auxiliary
    // trace commitment.
    coin.reseed(trace_roots_h[0]);

    if air.trace_info().is_multi_segment() {
        if trace_roots_h.len() < 2 {
            return Err(error::Error::InvalidInput(
                "multi-segment trace must provide at least two trace commitments",
            ));
        }

        // Auxiliary randomness is not used
        // directly here but consumes
        let _aux_rand = air
            .get_aux_rand_elements::<BE, DefaultRandomCoin<PoseidonHasher<BE>>>(&mut coin)
            .map_err(|_| {
                error::Error::InvalidInput(
                    "failed to draw auxiliary random elements during FS replay",
                )
            })?;

        coin.reseed(trace_roots_h[1]);
    }

    // 2) Constraint commitment and OOD point
    // --------------------------------------
    coin.reseed(constraint_root_h);

    let z_ood: BE = coin
        .draw()
        .map_err(|_| error::Error::InvalidInput("failed to draw OOD point in FS replay"))?;

    // 3) OOD evaluations and reseeding with their hash
    // -----------------------------------------------
    let main_width = air.trace_info().main_trace_width();
    let aux_width = air.trace_info().aux_segment_width();
    let constraint_frame_width = air.context().num_constraint_composition_columns();

    let (trace_ood_frame, quotient_ood_frame) = wf_proof
        .ood_frame
        .clone()
        .parse::<BE>(main_width, aux_width, constraint_frame_width)
        .map_err(|_| error::Error::InvalidInput("invalid OOD frame layout in FS replay"))?;

    // Inline merge_ood_evaluations:
    // current(z) || quotient(z) || next(zg) || quotient(zg).
    let mut current_row = trace_ood_frame.current_row().to_vec();
    current_row.extend_from_slice(quotient_ood_frame.current_row());

    let mut next_row = trace_ood_frame.next_row().to_vec();
    next_row.extend_from_slice(quotient_ood_frame.next_row());

    let mut ood_evals = current_row;
    ood_evals.extend_from_slice(&next_row);

    let ood_digest = PoseidonHasher::<BE>::hash_elements(&ood_evals);
    coin.reseed(ood_digest);

    // 4) DEEP composition coefficients
    // --------------------------------
    let deep = air
        .get_deep_composition_coefficients::<BE, DefaultRandomCoin<PoseidonHasher<BE>>>(&mut coin)
        .map_err(|_| {
            error::Error::InvalidInput("failed to draw DEEP composition coefficients in FS replay")
        })?;

    let mut deep_coeffs = Vec::with_capacity(deep.trace.len() + deep.constraints.len());
    deep_coeffs.extend(deep.trace.iter().copied());
    deep_coeffs.extend(deep.constraints.iter().copied());

    // 5) FRI layer alphas
    // --------------------
    let mut fri_alphas = Vec::with_capacity(fri_roots_h.len());
    let mut max_degree_plus_1 = air.trace_poly_degree() + 1;

    for (depth, root) in fri_roots_h.iter().enumerate() {
        coin.reseed(*root);
        let alpha: BE = coin
            .draw()
            .map_err(|_| error::Error::InvalidInput("failed to draw FRI alpha in FS replay"))?;
        fri_alphas.push(alpha);

        if depth != fri_roots_h.len() - 1
            && !max_degree_plus_1.is_multiple_of(fri_opts.folding_factor())
        {
            return Err(error::Error::InvalidInput(
                "FRI degree truncation detected while replaying FS challenges",
            ));
        }
        max_degree_plus_1 /= fri_opts.folding_factor();
    }

    // 6) Query positions and PoW nonce
    // --------------------------------
    let pow_nonce = wf_proof.pow_nonce;
    let grinding_factor = air.options().grinding_factor();

    // Verify that the PoW nonce satisfies the grinding factor, just like
    // the verifier does.
    if coin.check_leading_zeros(pow_nonce) < grinding_factor {
        return Err(error::Error::InvalidInput(
            "pow_nonce does not satisfy grinding factor in FS replay",
        ));
    }

    let num_queries = air.options().num_queries();
    let lde_domain_size_air = air.lde_domain_size();
    let lde_domain_size_proof = wf_proof.lde_domain_size();

    if lde_domain_size_air != lde_domain_size_proof {
        return Err(error::Error::InvalidInput(
            "lde_domain_size mismatch between AIR and proof in FS replay",
        ));
    }

    let mut positions = coin
        .draw_integers(num_queries, lde_domain_size_air, pow_nonce)
        .map_err(|_| error::Error::InvalidInput("failed to draw query positions in FS replay"))?;

    positions.sort_unstable();
    positions.dedup();

    let num_unique_queries = wf_proof.num_unique_queries as usize;
    if positions.len() != num_unique_queries {
        return Err(error::Error::InvalidInput(
            "unique query positions count does not match proof.num_unique_queries",
        ));
    }

    let query_positions = positions.into_iter().map(|p| p as u32).collect();

    Ok(ZlFsChallenges {
        ood_points: vec![z_ood],
        deep_coeffs,
        fri_alphas,
        query_positions,
    })
}

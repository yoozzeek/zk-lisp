// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Poseidon-based Fiat–Shamir helpers for zk-lisp child proofs.
//!
//! These helpers define a minimal FS transcript over
//! `suite_id`, step digest and commitment roots which
//! will later be re-implemented inside `ZlAggAir` so
//! that STARK-in-STARK aggregation does not rely on the
//! host.

use crate::agg_child::ZlFsChallenges;
use crate::poseidon;
use crate::utils;

use std::collections::BTreeSet;
use winterfell::math::fields::f128::BaseElement as BE;

/// Derive Poseidon-based FS challenges for a child
/// step from its suite id, step digest, metadata,
/// domain size and FRI roots.
pub fn derive_fs_challenges(
    suite_id: &[u8; 32],
    step_digest: &[u8; 32],
    meta: &crate::zl_step::StepMeta,
    n: usize,
    q: usize,
    fri_roots: &[[u8; 32]],
) -> ZlFsChallenges {
    let seed_q = fs_seed_q(suite_id, step_digest, meta);
    let deep_coeffs = fs_deep_coeffs(suite_id, seed_q);
    let fri_alphas = fs_fri_alphas(suite_id, seed_q, fri_roots);
    let query_positions = fs_generate_indices(suite_id, seed_q, n, q);

    // Single OOD point derived from seed_q;
    // if future AIRs require multiple points,
    // this can be extended to a sequence.
    let z_ood = fs_ood_point(suite_id, seed_q);

    ZlFsChallenges {
        ood_points: vec![z_ood],
        deep_coeffs,
        fri_alphas,
        query_positions,
    }
}

/// Seed for query/FRI challenges derived
/// from the step digest and metadata.
fn fs_seed_q(suite_id: &[u8; 32], step_digest: &[u8; 32], meta: &crate::zl_step::StepMeta) -> BE {
    let mut meta_bytes = Vec::with_capacity(4 * 6 + 8);
    meta_bytes.extend_from_slice(&meta.m.to_le_bytes());
    meta_bytes.extend_from_slice(&meta.rho.to_le_bytes());
    meta_bytes.extend_from_slice(&meta.q.to_le_bytes());
    meta_bytes.extend_from_slice(&meta.o.to_le_bytes());
    meta_bytes.extend_from_slice(&meta.lambda.to_le_bytes());
    meta_bytes.extend_from_slice(&meta.pi_len.to_le_bytes());
    meta_bytes.extend_from_slice(&meta.v_units.to_le_bytes());

    let seed_meta = poseidon::poseidon_ro_parts(suite_id, "zkl/fs/meta", &[&meta_bytes[..]]);

    let seed_q = poseidon::poseidon_ro_parts(
        suite_id,
        "zkl/fs/seed_q",
        &[&utils::fe_to_bytes_fold(seed_meta)[..], step_digest],
    );

    seed_q
}

/// Derive DEEP/composition coefficients
/// (α, β, γ) from the seed.
fn fs_deep_coeffs(suite_id: &[u8; 32], seed_q: BE) -> Vec<BE> {
    let seed_b = utils::fe_to_bytes_fold(seed_q);

    let alpha = poseidon::poseidon_ro_parts(suite_id, "zkl/fs/alpha", &[&seed_b[..]]);
    let alpha_b = utils::fe_to_bytes_fold(alpha);

    let beta = poseidon::poseidon_ro_parts(suite_id, "zkl/fs/beta", &[&alpha_b[..]]);
    let beta_b = utils::fe_to_bytes_fold(beta);

    let gamma = poseidon::poseidon_ro_parts(suite_id, "zkl/fs/gamma", &[&beta_b[..]]);

    vec![alpha, beta, gamma]
}

/// Derive per-layer FRI folding challenges
/// from FRI commitment roots and the seed.
fn fs_fri_alphas(suite_id: &[u8; 32], seed_q: BE, fri_roots: &[[u8; 32]]) -> Vec<BE> {
    let mut alphas = Vec::with_capacity(fri_roots.len());
    let mut state = seed_q;

    for r in fri_roots {
        let sb = utils::fe_to_bytes_fold(state);
        let t = poseidon::poseidon_ro_parts(suite_id, "zkl/fs/fri/alpha_state", &[&sb[..], &r[..]]);

        let alpha = poseidon::poseidon_ro_parts(
            suite_id,
            "zkl/fs/fri/alpha",
            &[&utils::fe_to_bytes_fold(t)[..]],
        );

        alphas.push(alpha);
        state = t;
    }

    alphas
}

/// Derive a single OOD evaluation point from the seed.
fn fs_ood_point(suite_id: &[u8; 32], seed_q: BE) -> BE {
    let seed_b = utils::fe_to_bytes_fold(seed_q);
    poseidon::poseidon_ro_parts(suite_id, "zkl/fs/ood", &[&seed_b[..]])
}

/// Deterministically sample `q` distinct indices
/// without replacement from [0, n).
fn fs_generate_indices(suite_id: &[u8; 32], seed: BE, n: usize, q: usize) -> Vec<u32> {
    let mut out = Vec::with_capacity(q);
    let mut seen: BTreeSet<u32> = BTreeSet::new();
    let mut ctr: u64 = 0;

    if n == 0 {
        return out;
    }

    while out.len() < q {
        let t = poseidon::poseidon_hash_two_lanes(suite_id, seed, BE::from(ctr));
        let tb = utils::fe_to_bytes_fold(t);

        let mut le8 = [0u8; 8];
        le8.copy_from_slice(&tb[..8]);

        let v = u64::from_le_bytes(le8);
        let idx = (v % (n as u64)) as u32;

        ctr = ctr.wrapping_add(1);

        if seen.insert(idx) {
            out.push(idx);
        }
    }

    out
}

// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! IVC-level public inputs and digests for zk-lisp.
//!
//! This module defines a compact public input format for
//! incremental aggregation (`IvPublic`) plus helpers for
//! computing a Merkle-style execution root over step
//! digests and a Poseidon-based digest of the IVC proof
//! itself. These building blocks will be used by the
//! dedicated IVC AIR and trace in a separate module.

use crate::poseidon;
use crate::utils;

use winterfell::math::fields::f128::BaseElement as BE;
use zk_lisp_proof::ivc::{ExecRoot, IvDigest, IvPublic, StepDigest};

/// Compute an execution root over an optional previous
/// IVC digest and a multiset of 32-byte step digests.
///
/// Semantics:
/// - `prev_iv_digest` is interpreted as the digest of the
///   previous IVC step in the chain; when all bytes are zero
///   it is omitted;
/// - all non-zero digests (previous and child) are treated as
///   leaves of a Poseidon-based Merkle tree whose leaves are
///   obtained by folding each 32-byte digest into the base
///   field via [`utils::fold_bytes32_to_fe`];
/// - the Merkle root is computed over the digests sorted in
///   lexicographic byte order, so callers may pass digests in
///   any order and obtain a canonical `ExecRoot`.
///
/// Internal nodes are computed with
/// [`poseidon::poseidon_hash_two_lanes`] using the supplied
/// `suite_id` as the Poseidon suite selector. For a single
/// leaf the root is just that leaf's folded field element
/// mapped back via [`utils::fe_to_bytes_fold`].
pub fn exec_root_from_digests(
    suite_id: &[u8; 32],
    prev_iv_digest: &[u8; 32],
    digests: &[StepDigest],
) -> ExecRoot {
    // Collect non-zero digests into a scratch buffer so we
    // can sort them canonically before Merkle-ising.
    let mut items: Vec<[u8; 32]> = Vec::with_capacity(1 + digests.len());

    if prev_iv_digest.iter().any(|b| *b != 0) {
        items.push(*prev_iv_digest);
    }

    for d in digests {
        if d.iter().any(|b| *b != 0) {
            items.push(*d);
        }
    }

    if items.is_empty() {
        return [0u8; 32];
    }

    items.sort_unstable();

    // Classic binary Merkle
    // tree over field elements.
    let mut layer: Vec<BE> = items.iter().map(utils::fold_bytes32_to_fe).collect();

    while layer.len() > 1 {
        let mut next = Vec::with_capacity(layer.len().div_ceil(2));
        let mut i = 0usize;

        while i < layer.len() {
            let a = layer[i];
            let b = if i + 1 < layer.len() {
                layer[i + 1]
            } else {
                layer[i]
            };
            let h = poseidon::poseidon_hash_two_lanes(suite_id, a, b);

            next.push(h);
            i += 2;
        }

        layer = next;
    }

    utils::fe_to_bytes_fold(layer[0])
}

/// Compute a 32-byte digest of an IVC proof step
/// from its public inputs and the list of child
/// step digests it aggregates.
///
/// The digest is computed purely from public data
/// and does not depend on the internal AIR or trace
/// representation: callers must ensure that `pi` and
/// `step_digests` are consistent with the actual IVC
/// proof being encoded.
pub fn iv_digest(pi: &IvPublic, step_digests: &[StepDigest]) -> IvDigest {
    // suite_fe = RO2F("zkl/ivc/iv/suite", suite_id)
    let suite_fe = poseidon::ro_to_fe("zkl/ivc/iv/suite", &[&pi.suite_id[..]]);

    // meta_bytes = serialize(state_initial, state_final,
    // prev_iv_digest, exec_root, steps_count, v_units_total)
    let mut meta_bytes = Vec::with_capacity(32 * 4 + 4 + 8);
    meta_bytes.extend_from_slice(&pi.state_initial);
    meta_bytes.extend_from_slice(&pi.state_final);
    meta_bytes.extend_from_slice(&pi.prev_iv_digest);
    meta_bytes.extend_from_slice(&pi.exec_root);
    meta_bytes.extend_from_slice(&pi.steps_count.to_le_bytes());
    meta_bytes.extend_from_slice(&pi.v_units_total.to_le_bytes());

    let meta_ro = poseidon::ro_to_fe("zkl/ivc/iv/meta", &[&meta_bytes[..]]);
    let h_meta = poseidon::poseidon_hash_two_lanes(&pi.suite_id, meta_ro, BE::from(0u64));

    let mut h_steps = BE::from(0u64);

    if pi.prev_iv_digest.iter().any(|b| *b != 0) {
        let prev_f = utils::fold_bytes32_to_fe(&pi.prev_iv_digest);
        h_steps = poseidon::poseidon_hash_two_lanes(&pi.suite_id, h_steps, prev_f);
    }

    for d in step_digests {
        let df = utils::fold_bytes32_to_fe(d);
        h_steps = poseidon::poseidon_hash_two_lanes(&pi.suite_id, h_steps, df);
    }

    let c0 = poseidon::poseidon_hash_two_lanes(&pi.suite_id, suite_fe, h_meta);
    let h = poseidon::poseidon_hash_two_lanes(&pi.suite_id, c0, h_steps);

    utils::fe_to_bytes_fold(h)
}

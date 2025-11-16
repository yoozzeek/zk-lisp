// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Compact child representation for aggregation.
//!
//! `ZlChildCompact` is a lightweight summary of a zk-lisp
//! step proof suitable for use by a STARK-in-STARK
//! aggregation layer. It captures the suite id, per-proof
//! metadata, the step digest, and a compact commitment to
//! the underlying Winterfell trace via `trace_root`.

use crate::poseidon;
use crate::utils;
use crate::zl_step::{StepMeta, ZlStepProof};

use winterfell::math::fields::f128::BaseElement as BE;

/// Compact child structure derived from a `ZlStepProof`.
///
/// This initial version focuses on fields needed for
/// aggregation over work units and canonical child
/// identification via `step_digest`. It can be
/// extended later with additional commitment and
/// FRI data as the aggregation AIR evolves.
#[derive(Clone, Debug)]
pub struct ZlChildCompact {
    /// Poseidon suite identifier used by the child
    /// proof and its digest construction.
    pub suite_id: [u8; 32],

    /// Per-proof metadata echoing the proving
    /// profile (m, rho, q, o, lambda, pi_len,
    /// v_units).
    pub meta: StepMeta,

    /// 32-byte step digest computed from
    /// `zl1::format::Proof`.
    pub step_digest: [u8; 32],

    /// Folded trace/constraint/FRI commitment root
    /// derived from the inner Winterfell proof.
    ///
    /// In the initial aggregation skeleton this is
    /// used only to build simple consistency checks
    /// in the aggregator AIR; its semantics may be
    /// refined as the recursion layer evolves.
    pub trace_root: [u8; 32],
}

impl ZlChildCompact {
    /// Derive a compact child representation from
    /// a full step proof wrapper.
    pub fn from_step(step: &ZlStepProof) -> Self {
        let suite_id = step.proof.header.suite_id;
        let meta = step.proof.meta;
        let step_digest = step.digest();
        let trace_root = step.proof.commits.root_trace;

        Self {
            suite_id,
            meta,
            step_digest,
            trace_root,
        }
    }
}

/// Compute a canonical aggregation root
/// over a batch of compact children.
pub fn children_root_from_compact(suite_id: &[u8; 32], children: &[ZlChildCompact]) -> [u8; 32] {
    if children.is_empty() {
        return [0u8; 32];
    }

    let mut items: Vec<[u8; 32]> = Vec::with_capacity(children.len());

    for child in children {
        let d_fe = utils::fold_bytes32_to_fe(&child.step_digest);
        let t_fe = utils::fold_bytes32_to_fe(&child.trace_root);
        let leaf_fe = poseidon::poseidon_hash_two_lanes(suite_id, d_fe, t_fe);
        let leaf_bytes = utils::fe_to_bytes_fold(leaf_fe);

        items.push(leaf_bytes);
    }

    items.sort_unstable();

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

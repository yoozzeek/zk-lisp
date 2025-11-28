// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

use crate::proof::format;
use crate::{poseidon, utils};
use winterfell::math::fields::f128::BaseElement as BE;

/// Compute a 32-byte step digest from zl1 proof components.
///
pub fn step_digest(proof: &format::Proof) -> [u8; 32] {
    // suite_fe = RO2F("zkl/step/digest/suite", suite_id)
    let suite_fe = poseidon::ro_to_fe("zkl/step/digest/suite", &[&proof.header.suite_id]);

    // H_meta = Poseidon2(RO2F("zkl/step/digest/meta", meta_bytes), 0)
    let mut meta_bytes = Vec::with_capacity(4 * 6 + 8);
    meta_bytes.extend_from_slice(&proof.meta.m.to_le_bytes());
    meta_bytes.extend_from_slice(&proof.meta.rho.to_le_bytes());
    meta_bytes.extend_from_slice(&proof.meta.q.to_le_bytes());
    meta_bytes.extend_from_slice(&proof.meta.o.to_le_bytes());
    meta_bytes.extend_from_slice(&proof.meta.lambda.to_le_bytes());
    meta_bytes.extend_from_slice(&proof.meta.pi_len.to_le_bytes());
    meta_bytes.extend_from_slice(&proof.meta.v_units.to_le_bytes());

    let meta_ro = poseidon::ro_to_fe("zkl/step/digest/meta", &[&meta_bytes[..]]);
    let h_meta = poseidon::poseidon_hash_two_lanes(&proof.header.suite_id, meta_ro, BE::from(0u64));

    // H_pi = Poseidon2(RO2F("zkl/step/digest/pi", pi_bytes), 0)
    let mut pi_bytes = Vec::with_capacity(32 * 17 + 8 + 4 + 4);
    pi_bytes.extend_from_slice(&proof.pi.program_id);
    pi_bytes.extend_from_slice(&proof.pi.program_commitment);
    pi_bytes.extend_from_slice(&proof.pi.feature_mask.to_le_bytes());
    pi_bytes.extend_from_slice(&proof.pi.segment_index.to_le_bytes());
    pi_bytes.extend_from_slice(&proof.pi.segments_total.to_le_bytes());
    pi_bytes.extend_from_slice(&proof.pi.pc_init);
    pi_bytes.extend_from_slice(&proof.pi.state_in_hash);
    pi_bytes.extend_from_slice(&proof.pi.state_out_hash);
    pi_bytes.extend_from_slice(&proof.pi.ram_gp_unsorted_in);
    pi_bytes.extend_from_slice(&proof.pi.ram_gp_unsorted_out);
    pi_bytes.extend_from_slice(&proof.pi.ram_gp_sorted_in);
    pi_bytes.extend_from_slice(&proof.pi.ram_gp_sorted_out);
    pi_bytes.extend_from_slice(&proof.pi.rom_s_in_0);
    pi_bytes.extend_from_slice(&proof.pi.rom_s_in_1);
    pi_bytes.extend_from_slice(&proof.pi.rom_s_in_2);
    pi_bytes.extend_from_slice(&proof.pi.rom_s_out_0);
    pi_bytes.extend_from_slice(&proof.pi.rom_s_out_1);
    pi_bytes.extend_from_slice(&proof.pi.rom_s_out_2);

    let pi_ro = poseidon::ro_to_fe("zkl/step/digest/pi", &[&pi_bytes[..]]);
    let h_pi = poseidon::poseidon_hash_two_lanes(&proof.header.suite_id, pi_ro, BE::from(0u64));

    // H_roots = Poseidon2(root_trace_fe, 0)
    let rt_fe = utils::fold_bytes32_to_fe(&proof.commits.root_trace);
    let h_roots = poseidon::poseidon_hash_two_lanes(&proof.header.suite_id, rt_fe, BE::from(0u64));

    // StepDigest = fe_to_bytes_fold(Poseidon2(suite_fe, H_meta, H_pi, H_roots)
    // compressed via three 2-lane hashes).
    let c0 = poseidon::poseidon_hash_two_lanes(&proof.header.suite_id, suite_fe, h_meta);
    let c1 = poseidon::poseidon_hash_two_lanes(&proof.header.suite_id, c0, h_pi);
    let ch = poseidon::poseidon_hash_two_lanes(&proof.header.suite_id, c1, h_roots);

    utils::fe_to_bytes_fold(ch)
}

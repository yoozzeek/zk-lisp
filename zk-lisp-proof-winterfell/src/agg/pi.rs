// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

use crate::agg::child::{ZlChildCompact, ZlChildTranscript, children_root_from_compact};
use crate::proof::step::StepProof;
use crate::utils::fold_bytes32_to_fe;

use winterfell::math::ToElements;
use winterfell::math::fields::f128::BaseElement as BE;
use zk_lisp_proof::error;

/// Public inputs for the aggregation AIR.
#[derive(Clone, Debug)]
pub struct AggAirPublicInputs {
    /// Program identity and public-input digest
    /// (program + public main args) proved by the
    /// underlying step proofs.
    pub program_id: [u8; 32],
    pub program_commitment: [u8; 32],
    pub pi_digest: [u8; 32],

    /// Canonical aggregation root over compact
    /// children as defined in AGG_SPEC §2.1.
    pub children_root: [u8; 32],

    /// Global sum of child work units; the
    /// aggregator AIR enforces that the work
    pub v_units_total: u64,

    /// Number of children in the batch.
    pub children_count: u32,

    /// Aggregation batch identifier (optional
    /// from protocol perspective). This can
    pub batch_id: [u8; 32],

    /// Global zk-lisp STARK profile that all
    /// children are expected to share.
    pub profile_meta: AggProfileMeta,

    /// Global FRI profile shared by all children.
    pub profile_fri: AggFriProfile,

    /// Global FS query / PoW profile.
    pub profile_queries: AggQueryProfile,

    /// Helper field used by the current
    /// aggregation trace builder to check
    pub suite_id: [u8; 32],

    /// Helper field used by the trace builder
    /// to enforce shape invariants between
    /// public inputs and individual children.
    /// This will likely be phased out once
    /// the global profile constraints are in
    /// place.
    pub children_ms: Vec<u32>,

    /// Global VM state at the beginning and end
    /// of the aggregated prefix (including all
    pub vm_state_initial: [u8; 32],
    pub vm_state_final: [u8; 32],

    /// Global RAM grand-product accumulators for
    /// unsorted and sorted RAM tables at the
    pub ram_gp_unsorted_initial: [u8; 32],
    pub ram_gp_unsorted_final: [u8; 32],
    pub ram_gp_sorted_initial: [u8; 32],
    pub ram_gp_sorted_final: [u8; 32],

    /// Global ROM t=3 accumulator state at the
    /// beginning and end of the aggregated prefix.
    pub rom_s_initial: [[u8; 32]; 3],
    pub rom_s_final: [[u8; 32]; 3],
}

/// Global zk-lisp STARK profile shared by all
/// children in a batch. For now this simply
#[derive(Clone, Debug, Default)]
pub struct AggProfileMeta {
    pub m: u32,
    pub rho: u16,
    pub q: u16,
    pub o: u16,
    pub lambda: u16,
    pub pi_len: u32,
    pub v_units: u64,
}

/// Global FRI profile used by all
/// children in the aggregation.
#[derive(Clone, Debug, Default)]
pub struct AggFriProfile {
    pub lde_blowup: u32,
    pub folding_factor: u8,
    pub redundancy: u8,
    pub num_layers: u8,
}

/// Global query / PoW profile
/// shared by all children.
#[derive(Clone, Debug, Default)]
pub struct AggQueryProfile {
    pub num_queries: u16,
    pub grinding_factor: u32,
}

impl AggAirPublicInputs {
    /// Build aggregation public inputs for a single zk-lisp
    /// step proof by deriving a compact child view and child
    pub fn from_step_proof(step: &StepProof) -> error::Result<Self> {
        let compact = ZlChildCompact::from_step(step)?;
        let transcript = ZlChildTranscript::from_step(step)?;

        let core_pi = &compact.pi_core;
        let pi_digest = core_pi.digest();

        let children = vec![compact.clone()];
        let children_root = children_root_from_compact(&compact.suite_id, &children);

        let profile_meta = AggProfileMeta {
            m: compact.meta.m,
            rho: compact.meta.rho,
            q: compact.meta.q,
            o: compact.meta.o,
            lambda: compact.meta.lambda,
            pi_len: compact.meta.pi_len,
            v_units: compact.meta.v_units,
        };

        let profile_fri = AggFriProfile {
            lde_blowup: compact.meta.rho as u32,
            folding_factor: 2,
            redundancy: 1,
            num_layers: transcript.fri_layers.len() as u8,
        };

        let profile_queries = AggQueryProfile {
            num_queries: compact.meta.q,
            grinding_factor: 0,
        };

        Ok(AggAirPublicInputs {
            program_id: core_pi.program_id,
            program_commitment: core_pi.program_commitment,
            pi_digest,
            children_root,
            v_units_total: compact.meta.v_units,
            children_count: 1,
            batch_id: [0u8; 32],
            profile_meta,
            profile_fri,
            profile_queries,
            suite_id: compact.suite_id,
            children_ms: vec![compact.meta.m],
            vm_state_initial: compact.state_in_hash,
            vm_state_final: compact.state_out_hash,
            ram_gp_unsorted_initial: compact.ram_gp_unsorted_in,
            ram_gp_unsorted_final: compact.ram_gp_unsorted_out,
            ram_gp_sorted_initial: compact.ram_gp_sorted_in,
            ram_gp_sorted_final: compact.ram_gp_sorted_out,
            rom_s_initial: compact.rom_s_in,
            rom_s_final: compact.rom_s_out,
        })
    }
}

impl ToElements<BE> for AggAirPublicInputs {
    fn to_elements(&self) -> Vec<BE> {
        let mut out = Vec::with_capacity(32);

        out.push(fold_bytes32_to_fe(&self.program_id));
        out.push(fold_bytes32_to_fe(&self.program_commitment));
        out.push(fold_bytes32_to_fe(&self.pi_digest));
        out.push(fold_bytes32_to_fe(&self.children_root));
        out.push(fold_bytes32_to_fe(&self.batch_id));

        out.push(BE::from(self.profile_meta.m));
        out.push(BE::from(self.profile_meta.rho as u64));
        out.push(BE::from(self.profile_meta.q as u64));
        out.push(BE::from(self.profile_meta.o as u64));
        out.push(BE::from(self.profile_meta.lambda as u64));
        out.push(BE::from(self.profile_meta.pi_len));
        out.push(BE::from(self.profile_meta.v_units));
        out.push(BE::from(self.profile_fri.lde_blowup));
        out.push(BE::from(self.profile_fri.folding_factor as u64));
        out.push(BE::from(self.profile_fri.redundancy as u64));
        out.push(BE::from(self.profile_fri.num_layers as u64));
        out.push(BE::from(self.profile_queries.num_queries as u64));
        out.push(BE::from(self.profile_queries.grinding_factor));
        out.push(BE::from(self.children_count as u64));
        out.push(BE::from(self.v_units_total));

        // Fold global boundary bytes into field elements as
        // part of the aggregation FS seed so that any change
        out.push(fold_bytes32_to_fe(&self.vm_state_initial));
        out.push(fold_bytes32_to_fe(&self.vm_state_final));
        out.push(fold_bytes32_to_fe(&self.ram_gp_unsorted_initial));
        out.push(fold_bytes32_to_fe(&self.ram_gp_unsorted_final));
        out.push(fold_bytes32_to_fe(&self.ram_gp_sorted_initial));
        out.push(fold_bytes32_to_fe(&self.ram_gp_sorted_final));

        for lane in &self.rom_s_initial {
            out.push(fold_bytes32_to_fe(lane));
        }
        for lane in &self.rom_s_final {
            out.push(fold_bytes32_to_fe(lane));
        }

        out
    }
}

// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! zk-lisp step proof format (zl1) and Poseidon-based digest.

pub mod format {
    use crate::zl_step::StepMeta;

    use blake3::Hasher;
    use winterfell::Proof as WProof;
    use winterfell::crypto::Digest;
    use winterfell::math::fields::f128::BaseElement as BE;

    #[derive(Clone, Debug)]
    pub struct Header {
        /// Profile identifier (1 = zk-lisp Poseidon profile v1).
        pub profile_id: u8,
        /// Base field identifier (1 = f128).
        pub field_id: u8,
        /// Format version.
        pub version: u8,
        /// Poseidon suite identifier used by this proof.
        pub suite_id: [u8; 32],
        /// Blowup factor rho.
        pub rho: u16,
        /// FRI query count q.
        pub q: u16,
        /// FRI folding factor.
        pub fri_folding: u8,
        /// Field extension type (0 = none, 1 = quadratic, ...).
        pub ext: u8,
    }

    #[derive(Clone, Debug)]
    pub struct PublicInputs {
        pub program_id: [u8; 32],
        /// Blake3 commitment of the program as used by the
        /// base VM AIR.
        pub program_commitment: [u8; 32],
        /// Feature mask inferred from compiled ops.
        pub feature_mask: u64,
        /// Segment index within a multi-segment execution.
        pub segment_index: u32,
        /// Total number of segments; 1 for single-segment proofs.
        pub segments_total: u32,
        /// Program counter at the first map row of this segment.
        pub pc_init: [u8; 32],
        /// VM state hash at the beginning of this segment.
        ///
        pub state_in_hash: [u8; 32],
        /// VM state hash at the end of this segment.
        ///
        pub state_out_hash: [u8; 32],
        /// RAM grand-product accumulator at the first row of
        /// this segment for the unsorted RAM event stream.
        pub ram_gp_unsorted_in: [u8; 32],
        /// RAM grand-product accumulator at the last row of
        /// this segment for the unsorted RAM event stream.
        pub ram_gp_unsorted_out: [u8; 32],
        /// RAM grand-product accumulator at the first row of
        /// this segment for the sorted RAM table.
        pub ram_gp_sorted_in: [u8; 32],
        /// RAM grand-product accumulator at the last row of
        /// this segment for the sorted RAM table.
        pub ram_gp_sorted_out: [u8; 32],
        /// ROM t=3 state at the logical beginning of this
        /// segment. For single-segment proofs this is the
        pub rom_s_in_0: [u8; 32],
        pub rom_s_in_1: [u8; 32],
        pub rom_s_in_2: [u8; 32],
        /// ROM t=3 state at the logical end of this segment.
        /// For single-segment proofs this is the state on the
        pub rom_s_out_0: [u8; 32],
        pub rom_s_out_1: [u8; 32],
        pub rom_s_out_2: [u8; 32],
    }

    /// Commitment echo for the underlying Winterfell proof.
    ///
    #[derive(Clone, Debug)]
    pub struct Commitments {
        pub root_trace: [u8; 32],
    }

    /// Full zl1 step proof container.
    ///
    #[derive(Clone, Debug)]
    pub struct Proof {
        pub header: Header,
        pub pi: PublicInputs,
        pub commits: Commitments,
        pub meta: StepMeta,
        pub inner: WProof,
    }

    impl Proof {
        /// Construct a multi-segment zl1 proof with explicit segment indices.
        #[allow(clippy::too_many_arguments)]
        pub fn new_multi_segment(
            suite_id: [u8; 32],
            meta: StepMeta,
            core_pi: &zk_lisp_proof::pi::PublicInputs,
            segment_index: u32,
            segments_total: u32,
            pc_init: [u8; 32],
            state_in_hash: [u8; 32],
            state_out_hash: [u8; 32],
            ram_gp_unsorted_in: [u8; 32],
            ram_gp_unsorted_out: [u8; 32],
            ram_gp_sorted_in: [u8; 32],
            ram_gp_sorted_out: [u8; 32],
            rom_s_in_0: [u8; 32],
            rom_s_in_1: [u8; 32],
            rom_s_in_2: [u8; 32],
            rom_s_out_0: [u8; 32],
            rom_s_out_1: [u8; 32],
            rom_s_out_2: [u8; 32],
            wf_proof: WProof,
        ) -> zk_lisp_proof::error::Result<Self> {
            let mut p = Self::new_single_segment(
                suite_id,
                meta,
                core_pi,
                pc_init,
                state_in_hash,
                state_out_hash,
                ram_gp_unsorted_in,
                ram_gp_unsorted_out,
                ram_gp_sorted_in,
                ram_gp_sorted_out,
                rom_s_in_0,
                rom_s_in_1,
                rom_s_in_2,
                rom_s_out_0,
                rom_s_out_1,
                rom_s_out_2,
                wf_proof,
            )?;

            p.pi.segment_index = segment_index;
            p.pi.segments_total = segments_total;

            Ok(p)
        }
        /// Construct a single-segment zl1 proof from the
        /// suite id, per-proof metadata, backend-agnostic
        #[allow(clippy::too_many_arguments)]
        pub fn new_single_segment(
            suite_id: [u8; 32],
            meta: StepMeta,
            core_pi: &zk_lisp_proof::pi::PublicInputs,
            pc_init: [u8; 32],
            state_in_hash: [u8; 32],
            state_out_hash: [u8; 32],
            ram_gp_unsorted_in: [u8; 32],
            ram_gp_unsorted_out: [u8; 32],
            ram_gp_sorted_in: [u8; 32],
            ram_gp_sorted_out: [u8; 32],
            rom_s_in_0: [u8; 32],
            rom_s_in_1: [u8; 32],
            rom_s_in_2: [u8; 32],
            rom_s_out_0: [u8; 32],
            rom_s_out_1: [u8; 32],
            rom_s_out_2: [u8; 32],
            wf_proof: WProof,
        ) -> zk_lisp_proof::error::Result<Self> {
            // Header echoes the effective proving profile
            // under which the proof was generated.
            let header = Header {
                profile_id: 1,
                field_id: 1,
                version: 1,
                suite_id,
                rho: meta.rho,
                q: meta.q,
                fri_folding: 2,
                ext: 0,
            };

            // Backend-agnostic public inputs
            // provide a canonical semantic
            let program_id = core_pi.program_id;
            let program_commitment = core_pi.program_commitment;
            let feature_mask = core_pi.feature_mask;

            let pi = PublicInputs {
                program_id,
                program_commitment,
                feature_mask,
                segment_index: 0,
                segments_total: 1,
                pc_init,
                state_in_hash,
                state_out_hash,
                ram_gp_unsorted_in,
                ram_gp_unsorted_out,
                ram_gp_sorted_in,
                ram_gp_sorted_out,
                rom_s_in_0,
                rom_s_in_1,
                rom_s_in_2,
                rom_s_out_0,
                rom_s_out_1,
                rom_s_out_2,
            };

            // Derive a single commitment root
            // over the internal Winterfell commitments
            let num_trace_segments = wf_proof.trace_info().num_segments();
            let options = wf_proof.options();
            let fri_opts = options.to_fri_options();
            let lde_domain_size = wf_proof.lde_domain_size();
            let num_fri_layers = fri_opts.num_fri_layers(lde_domain_size);

            let commitments = wf_proof
                .commitments
                .clone()
                .parse::<crate::poseidon_hasher::PoseidonHasher<BE>>(
                    num_trace_segments,
                    num_fri_layers,
                )
                .map_err(|_| {
                    zk_lisp_proof::error::Error::InvalidInput(
                        "invalid Winterfell commitments layout in zl1::Proof",
                    )
                })?;

            let (trace_roots, constraint_root, fri_roots) = commitments;

            let mut h = Hasher::new();
            h.update(b"zkl/step/root_trace");
            h.update(&suite_id);

            for d in &trace_roots {
                h.update(&d.as_bytes());
            }

            h.update(&constraint_root.as_bytes());

            for d in &fri_roots {
                h.update(&d.as_bytes());
            }

            let digest = h.finalize();
            let mut root_trace = [0u8; 32];
            root_trace.copy_from_slice(digest.as_bytes());

            let commits = Commitments { root_trace };

            Ok(Self {
                header,
                pi,
                commits,
                meta,
                inner: wf_proof,
            })
        }
    }
}

pub mod digest {
    use crate::poseidon;
    use crate::utils;

    use super::format;
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
        let h_meta =
            poseidon::poseidon_hash_two_lanes(&proof.header.suite_id, meta_ro, BE::from(0u64));

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
        let h_roots =
            poseidon::poseidon_hash_two_lanes(&proof.header.suite_id, rt_fe, BE::from(0u64));

        // StepDigest = fe_to_bytes_fold(Poseidon2(suite_fe, H_meta, H_pi, H_roots)
        // compressed via three 2-lane hashes).
        let c0 = poseidon::poseidon_hash_two_lanes(&proof.header.suite_id, suite_fe, h_meta);
        let c1 = poseidon::poseidon_hash_two_lanes(&proof.header.suite_id, c0, h_pi);
        let ch = poseidon::poseidon_hash_two_lanes(&proof.header.suite_id, c1, h_roots);

        utils::fe_to_bytes_fold(ch)
    }
}

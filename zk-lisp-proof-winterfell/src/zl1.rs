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

    /// Step proof header echoing the proving profile under which the
    /// underlying Winterfell proof was generated.
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

    /// Minimal public input echo used at the step level for digest
    /// computation and future IVC wiring. This is intentionally
    /// narrower than the full AIR public inputs.
    #[derive(Clone, Debug)]
    pub struct PublicInputs {
        /// Deterministic identifier of the zk-lisp program.
        ///
        /// For now this is set equal to the Blake3
        /// `program_commitment`; it can be generalized to
        /// a separate logical id later without changing
        /// the rest of the layout.
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
        /// VM state hash at the beginning of this segment.
        ///
        /// This is a 32-byte digest derived from the initial
        /// register file and program counter at the map row
        /// of level 0 for single-segment proofs.
        pub state_in_hash: [u8; 32],
        /// VM state hash at the end of this segment.
        ///
        /// For single-segment proofs this is computed from the
        /// row where the final VM result is observed in the
        /// execution trace.
        pub state_out_hash: [u8; 32],
    }

    /// Commitment echo for the underlying Winterfell proof.
    ///
    /// At this stage we do not expose the internal trace/FRI
    /// Merkle roots used by Winterfell. Instead we derive a
    /// single 32-byte root deterministically from the suite id
    /// and the serialized Winterfell proof bytes under a fixed
    /// Blake3 domain. This value is then included into the
    /// step digest as a commitment to the base proof.
    #[derive(Clone, Debug)]
    pub struct Commitments {
        pub root_trace: [u8; 32],
    }

    /// Full zl1 step proof container.
    ///
    /// This structure ties together profile header, public
    /// inputs echo, commitment echo, per-proof metadata and
    /// the opaque Winterfell proof bytes.
    #[derive(Clone, Debug)]
    pub struct Proof {
        pub header: Header,
        pub pi: PublicInputs,
        pub commits: Commitments,
        pub meta: StepMeta,
        pub inner: WProof,
    }

    impl Proof {
        /// Construct a single-segment zl1 proof from the
        /// suite id, per-proof metadata, backend-agnostic
        /// public inputs and the underlying Winterfell proof.
        pub fn new_single_segment(
            suite_id: [u8; 32],
            meta: StepMeta,
            core_pi: &zk_lisp_proof::pi::PublicInputs,
            state_in_hash: [u8; 32],
            state_out_hash: [u8; 32],
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
            // program id and a VM-level
            // program commitment.
            let program_id = core_pi.program_id;
            let program_commitment = core_pi.program_commitment;
            let feature_mask = core_pi.feature_mask;

            let pi = PublicInputs {
                program_id,
                program_commitment,
                feature_mask,
                segment_index: 0,
                segments_total: 1,
                state_in_hash,
                state_out_hash,
            };

            // Derive a single commitment root
            // over the internal Winterfell commitments
            // (trace, constraint, FRI), domain-separated
            // from other uses of Blake3. This binds the
            // zl1 step to the full set of STARK
            // commitments without depending on the exact
            // serialization of the proof object.
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
    /// The digest is derived from:
    /// - the step metadata echo (`StepMeta`),
    /// - a compact public-input echo (`PublicInputs`), and
    /// - the commitment echo (`Commitments::root_trace`).
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
        let mut pi_bytes = Vec::with_capacity(32 * 4 + 8 + 4 + 4);
        pi_bytes.extend_from_slice(&proof.pi.program_id);
        pi_bytes.extend_from_slice(&proof.pi.program_commitment);
        pi_bytes.extend_from_slice(&proof.pi.feature_mask.to_le_bytes());
        pi_bytes.extend_from_slice(&proof.pi.segment_index.to_le_bytes());
        pi_bytes.extend_from_slice(&proof.pi.segments_total.to_le_bytes());
        pi_bytes.extend_from_slice(&proof.pi.state_in_hash);
        pi_bytes.extend_from_slice(&proof.pi.state_out_hash);

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

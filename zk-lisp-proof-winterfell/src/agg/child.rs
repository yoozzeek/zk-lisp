// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Compact child representation for aggregation.

use crate::agg::fs as fs_helpers;
use crate::poseidon;
use crate::poseidon::hasher::{PoseidonDigest, PoseidonHasher};
use crate::proof::step::{StepMeta, StepProof};
use crate::utils;

use blake3::Hasher as Blake3Hasher;
use winter_utils::{Deserializable, Serializable, SliceReader};
use winterfell::crypto::{Digest, ElementHasher, Hasher, MerkleTree};
use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;
use zk_lisp_proof::error;

/// Compact child structure derived from a `ZlStepProof`.
#[derive(Clone, Debug)]
pub struct ZlChildCompact {
    /// Poseidon suite identifier used by the child
    /// proof and its digest construction.
    pub suite_id: [u8; 32],

    /// Per-proof metadata echoing the proving
    /// profile (m, rho, q, o, lambda, pi_len,
    pub meta: StepMeta,

    /// Backend-agnostic public inputs
    /// used to build the child trace.
    pub pi_core: zk_lisp_proof::pi::PublicInputs,

    /// Final ROM accumulator lanes
    /// for the child step.
    pub rom_acc: [BE; 3],

    /// 32-byte step digest computed from
    /// `zl1::format::Proof`.
    pub step_digest: [u8; 32],

    /// Folded trace/constraint/FRI commitment root
    /// derived from the inner Winterfell proof.
    pub trace_root: [u8; 32],

    /// Segment index and total segment count as
    /// recorded in the zl1 step public inputs.
    pub segment_index: u32,
    pub segments_total: u32,

    /// VM state hash at the beginning and end of
    /// this segment, as exposed via zl1 public
    pub state_in_hash: [u8; 32],
    pub state_out_hash: [u8; 32],

    /// RAM grand-product accumulators at the
    /// boundaries of this segment for unsorted
    pub ram_gp_unsorted_in: [u8; 32],
    pub ram_gp_unsorted_out: [u8; 32],
    pub ram_gp_sorted_in: [u8; 32],
    pub ram_gp_sorted_out: [u8; 32],

    /// ROM t=3 state at the logical beginning and
    /// end of this segment.
    pub rom_s_in: [[u8; 32]; 3],
    pub rom_s_out: [[u8; 32]; 3],

    /// Per-trace-segment Merkle roots for the
    /// base execution trace as exposed by the
    pub trace_roots: Vec<[u8; 32]>,

    /// Merkle root of the constraint composition
    /// polynomial commitment used by the child.
    pub constraint_root: [u8; 32],

    /// Per-layer Merkle roots of the FRI
    /// commitments derived from the base proof.
    pub fri_roots: Vec<[u8; 32]>,

    /// Proof-of-work nonce used for query seed
    /// grinding in the underlying Winterfell proof.
    pub pow_nonce: u64,

    /// Fiat–Shamir challenges as seen by the
    /// child verifier. This will be populated from
    pub fs_challenges: Option<ZlFsChallenges>,

    /// Merkle authentication data for trace,
    /// constraint and FRI trees at all query
    pub merkle_proofs: Option<ZlMerkleProofs>,
}

/// Fiat–Shamir challenges needed to replay
/// zk-lisp AIR verification at the aggregator
#[derive(Clone, Debug)]
pub struct ZlFsChallenges {
    /// One or more OOD evaluation points used
    /// for DEEP composition. Most AIRs use a
    pub ood_points: Vec<BE>,

    /// Opaque list of DEEP/composition coefficients
    /// (α, β, γ, etc.) in the order expected by
    pub deep_coeffs: Vec<BE>,

    /// Per-layer FRI folding challenges.
    pub fri_alphas: Vec<BE>,

    /// Query positions in the LDE domain
    /// (indices in [0, n)).
    pub query_positions: Vec<u32>,
}

/// Simple Merkle path represented by a leaf digest
/// and a list of sibling digests from leaf to root.
#[derive(Clone, Debug)]
pub struct ZlMerklePath {
    pub leaf: PoseidonDigest,
    pub siblings: Vec<PoseidonDigest>,
}

/// Per-layer FRI Merkle proof for a single leaf
/// in the FRI commitment at a given layer.
#[derive(Clone, Debug)]
pub struct ZlFriLayerProof {
    /// Leaf index in the FRI layer commitment
    /// domain. For layer `d` this must equal
    pub idx: u32,
    /// Values committed in the leaf at `idx`;
    /// for folding factor 2 this is a pair of
    pub values: [BE; 2],
    /// Merkle authentication path from the leaf
    /// hash H(values) up to fri_roots[d].
    pub path: ZlMerklePath,
}

/// Collection of Merkle authentication data
/// for all trees touched by the verifier.
#[derive(Clone, Debug)]
pub struct ZlMerkleProofs {
    /// Per-query Merkle paths for main trace
    /// openings under `trace_roots`.
    pub trace_paths: Vec<ZlMerklePath>,

    /// Per-query Merkle paths for constraint
    /// /composition openings under
    pub constraint_paths: Vec<ZlMerklePath>,

    /// FRI Merkle proofs indexed as
    /// `fri_layers[layer][query]`.
    pub fri_layers: Vec<Vec<ZlFriLayerProof>>,
}

impl ZlChildCompact {
    /// Derive a compact child representation from
    /// a full step proof wrapper.
    pub fn from_step(step: &StepProof) -> error::Result<Self> {
        let suite_id = step.proof.header.suite_id;
        let meta = step.proof.meta;
        let pi_core = step.pi_core.clone();
        let rom_acc = step.rom_acc;
        let step_digest = step.digest();
        let trace_root = step.proof.commits.root_trace;

        let pi_zl1 = &step.proof.pi;
        let segment_index = pi_zl1.segment_index;
        let segments_total = pi_zl1.segments_total;
        let state_in_hash = pi_zl1.state_in_hash;
        let state_out_hash = pi_zl1.state_out_hash;
        let ram_gp_unsorted_in = pi_zl1.ram_gp_unsorted_in;
        let ram_gp_unsorted_out = pi_zl1.ram_gp_unsorted_out;
        let ram_gp_sorted_in = pi_zl1.ram_gp_sorted_in;
        let ram_gp_sorted_out = pi_zl1.ram_gp_sorted_out;
        let rom_s_in = [pi_zl1.rom_s_in_0, pi_zl1.rom_s_in_1, pi_zl1.rom_s_in_2];
        let rom_s_out = [pi_zl1.rom_s_out_0, pi_zl1.rom_s_out_1, pi_zl1.rom_s_out_2];

        let wf_proof = &step.proof.inner;
        let trace_info = wf_proof.trace_info();
        let num_trace_segments = trace_info.num_segments();
        let options = wf_proof.options();
        let fri_opts = options.to_fri_options();
        let lde_domain_size = wf_proof.lde_domain_size();
        let num_fri_layers = fri_opts.num_fri_layers(lde_domain_size);
        let num_queries = wf_proof.num_unique_queries as usize;

        let commitments = wf_proof
            .commitments
            .clone()
            .parse::<PoseidonHasher<BE>>(num_trace_segments, num_fri_layers)
            .map_err(|_| {
                error::Error::InvalidInput(
                    "invalid Winterfell commitments layout in ZlChildCompact",
                )
            })?;

        let (trace_roots_h, constraint_root_h, fri_roots_h) = commitments;

        let mut trace_roots = Vec::with_capacity(trace_roots_h.len());
        for d in trace_roots_h {
            let mut bytes = [0u8; 32];
            bytes.copy_from_slice(&d.as_bytes());
            trace_roots.push(bytes);
        }

        let mut constraint_root = [0u8; 32];
        constraint_root.copy_from_slice(&constraint_root_h.as_bytes());

        let mut fri_roots = Vec::with_capacity(fri_roots_h.len());
        for d in fri_roots_h {
            let mut bytes = [0u8; 32];
            bytes.copy_from_slice(&d.as_bytes());
            fri_roots.push(bytes);
        }

        let pow_nonce = wf_proof.pow_nonce;

        // Replay FS challenges exactly as seen by Winterfell verifier.
        // This provides a single source of randomness for aggregation
        let fs_challenges = if num_queries == 0 {
            None
        } else {
            Some(fs_helpers::replay_fs_from_step(step)?)
        };

        // Extract Merkle authentication data for trace,
        // constraint and FRI queries using the same
        let merkle_proofs = {
            if num_queries == 0 {
                None
            } else {
                let fs = fs_challenges.as_ref().ok_or(error::Error::InvalidInput(
                    "ZlChildCompact.fs_challenges must be present when num_queries > 0",
                ))?;

                if fs.query_positions.len() != num_queries {
                    return Err(error::Error::InvalidInput(
                        "ZlChildCompact.fs_challenges.query_positions length is inconsistent with num_queries",
                    ));
                }

                // Parse main-trace queries for the first
                // (and currently only) trace segment.
                let main_width = trace_info.main_trace_width();

                let (main_mproof, main_table) = wf_proof.trace_queries[0]
                    .clone()
                    .parse::<BE, PoseidonHasher<BE>, MerkleTree<PoseidonHasher<BE>>>(
                        lde_domain_size,
                        num_queries,
                        main_width,
                    )
                    .map_err(|_| {
                        error::Error::InvalidInput("invalid trace queries layout in ZlChildCompact")
                    })?;

                // Rebuild leaf digests for each queried
                // main-trace row using the same partitioning
                let partition_opts = options.partition_options();
                let partition_size_main =
                    partition_opts.partition_size::<BE>(trace_info.main_trace_width());

                let mut trace_leaves = Vec::with_capacity(num_queries);
                let mut trace_indexes = Vec::with_capacity(num_queries);

                // Each row in `main_table` is ordered consistently
                // with `fs.query_positions`, and the Merkle tree
                for (row, &pos) in main_table.rows().zip(fs.query_positions.iter()) {
                    let leaf = hash_row_poseidon(row, partition_size_main);
                    trace_leaves.push(leaf);

                    let idx = pos as usize;
                    if idx >= lde_domain_size {
                        return Err(error::Error::InvalidInput(
                            "ZlChildCompact.fs_challenges.query_positions contains index outside LDE domain",
                        ));
                    }

                    trace_indexes.push(idx);
                }

                let trace_openings = main_mproof
                    .into_openings(&trace_leaves, &trace_indexes)
                    .map_err(|_| {
                        error::Error::InvalidInput(
                            "failed to decompress trace Merkle multiproof in ZlChildCompact",
                        )
                    })?;

                let mut trace_paths = Vec::with_capacity(trace_openings.len());
                for (leaf, siblings) in trace_openings {
                    trace_paths.push(ZlMerklePath { leaf, siblings });
                }

                // Infer constraint frame width from the serialized
                // constraint queries and use it to parse the table
                let cq_clone = wf_proof.constraint_queries.clone();
                let cq_bytes = Serializable::to_bytes(&cq_clone);
                let mut reader = SliceReader::new(&cq_bytes);

                let values_bytes =
                    <Vec<u8> as Deserializable>::read_from(&mut reader).map_err(|_| {
                        error::Error::InvalidInput(
                            "failed to decode constraint query values in ZlChildCompact",
                        )
                    })?;

                // Skip paths bytes; `cq_clone.parse()` will re-parse them
                let _: Vec<u8> = Deserializable::read_from(&mut reader).map_err(|_| {
                    error::Error::InvalidInput(
                        "failed to decode constraint query paths in ZlChildCompact",
                    )
                })?;

                let total_value_bytes = values_bytes.len();
                let elem_bytes = BE::ELEMENT_BYTES;

                let denom =
                    num_queries
                        .checked_mul(elem_bytes)
                        .ok_or(error::Error::InvalidInput(
                            "overflow while computing constraint frame width in ZlChildCompact",
                        ))?;

                if denom == 0 || total_value_bytes % denom != 0 {
                    return Err(error::Error::InvalidInput(
                        "constraint_queries byte length is inconsistent with num_queries",
                    ));
                }

                let constraint_frame_width = total_value_bytes / denom;
                if constraint_frame_width == 0 {
                    return Err(error::Error::InvalidInput(
                        "constraint frame width inferred from queries must be non-zero",
                    ));
                }

                let (constraint_mproof, constraint_table) = cq_clone
                    .parse::<BE, PoseidonHasher<BE>, MerkleTree<PoseidonHasher<BE>>>(
                        lde_domain_size,
                        num_queries,
                        constraint_frame_width,
                    )
                    .map_err(|_| {
                        error::Error::InvalidInput(
                            "invalid constraint queries layout in ZlChildCompact",
                        )
                    })?;

                let partition_size_constraint =
                    partition_opts.partition_size::<BE>(constraint_frame_width);

                let mut constraint_leaves = Vec::with_capacity(num_queries);
                let mut constraint_indexes = Vec::with_capacity(num_queries);

                for (row, &pos) in constraint_table.rows().zip(fs.query_positions.iter()) {
                    let leaf = hash_row_poseidon(row, partition_size_constraint);
                    constraint_leaves.push(leaf);

                    let idx = pos as usize;
                    if idx >= lde_domain_size {
                        return Err(error::Error::InvalidInput(
                            "ZlChildCompact.fs_challenges.query_positions contains index outside LDE domain",
                        ));
                    }

                    constraint_indexes.push(idx);
                }

                let constraint_openings = constraint_mproof
                    .into_openings(&constraint_leaves, &constraint_indexes)
                    .map_err(|_| {
                        error::Error::InvalidInput(
                            "failed to decompress constraint Merkle multiproof in ZlChildCompact",
                        )
                    })?;

                let mut constraint_paths = Vec::with_capacity(constraint_openings.len());
                for (leaf, siblings) in constraint_openings {
                    constraint_paths.push(ZlMerklePath { leaf, siblings });
                }

                // FRI Merkle paths
                let folding = fri_opts.folding_factor();
                if folding != 2 {
                    return Err(error::Error::InvalidInput(
                        "ZlChildCompact currently supports only FRI folding factor 2",
                    ));
                }

                let num_fri_layers = fri_opts.num_fri_layers(lde_domain_size);
                let mut fri_layers_paths: Vec<Vec<ZlFriLayerProof>> = Vec::new();

                if num_fri_layers > 0 && num_queries > 0 {
                    // Parse FRI layers into per-query values and
                    // batch Merkle proofs using the same layout as
                    let fri_proof_clone = wf_proof.fri_proof.clone();
                    let (layer_queries, layer_proofs) = fri_proof_clone
                        .parse_layers::<BE, PoseidonHasher<BE>, MerkleTree<PoseidonHasher<BE>>>(
                            lde_domain_size,
                            folding,
                        )
                        .map_err(|_| {
                            error::Error::InvalidInput(
                                "invalid FRI layers layout in ZlChildCompact",
                            )
                        })?;

                    debug_assert_eq!(layer_queries.len(), num_fri_layers);
                    debug_assert_eq!(layer_proofs.len(), num_fri_layers);

                    // Reconstruct folded query positions for each
                    // FRI layer exactly as FriProver::build_proof
                    let mut positions: Vec<usize> =
                        fs.query_positions.iter().map(|&p| p as usize).collect();
                    let mut domain_size = lde_domain_size;

                    for (vals, mproof) in layer_queries.into_iter().zip(layer_proofs.into_iter()) {
                        if vals.is_empty() || folding == 0 {
                            fri_layers_paths.push(Vec::new());
                            domain_size /= folding;
                            positions = fold_positions_usize(&positions, domain_size, folding)?;
                            continue;
                        }

                        if vals.len() % folding != 0 {
                            return Err(error::Error::InvalidInput(
                                "FRI layer values length is inconsistent with folding factor in ZlChildCompact",
                            ));
                        }

                        // Fold positions for this layer
                        let folded_positions =
                            fold_positions_usize(&positions, domain_size, folding)?;

                        let q_count = vals.len() / folding;
                        if q_count != folded_positions.len() {
                            return Err(error::Error::InvalidInput(
                                "FRI folded positions count is inconsistent with layer queries in ZlChildCompact",
                            ));
                        }

                        // Hash per-query values into Merkle leaves using
                        // the same convention as FriProofLayer::parse.
                        let mut hashed_leaves = Vec::with_capacity(q_count);
                        let mut values_pairs = Vec::with_capacity(q_count);
                        for i in 0..q_count {
                            let base = i * folding;
                            let v0 = vals[base];
                            let v1 = vals[base + 1];
                            let pair = [v0, v1];
                            let leaf = PoseidonHasher::<BE>::hash_elements(&pair);
                            hashed_leaves.push(leaf);
                            values_pairs.push(pair);
                        }

                        // Decompress the batch proof into individual
                        // openings, preserving the same order as in
                        let openings = mproof
                            .into_openings(&hashed_leaves, &folded_positions)
                            .map_err(|_| {
                                error::Error::InvalidInput(
                                    "failed to decompress FRI Merkle multiproof in ZlChildCompact",
                                )
                            })?;

                        debug_assert_eq!(openings.len(), q_count);

                        let mut layer_paths = Vec::with_capacity(q_count);
                        for (((leaf, siblings), pair), &idx) in openings
                            .into_iter()
                            .zip(values_pairs.into_iter())
                            .zip(folded_positions.iter())
                        {
                            layer_paths.push(ZlFriLayerProof {
                                idx: idx as u32,
                                values: pair,
                                path: ZlMerklePath { leaf, siblings },
                            });
                        }

                        fri_layers_paths.push(layer_paths);

                        domain_size /= folding;
                        positions = folded_positions;
                    }
                }

                Some(ZlMerkleProofs {
                    trace_paths,
                    constraint_paths,
                    fri_layers: fri_layers_paths,
                })
            }
        };

        Ok(Self {
            suite_id,
            meta,
            pi_core,
            rom_acc,
            step_digest,
            trace_root,
            segment_index,
            segments_total,
            state_in_hash,
            state_out_hash,
            ram_gp_unsorted_in,
            ram_gp_unsorted_out,
            ram_gp_sorted_in,
            ram_gp_sorted_out,
            rom_s_in,
            rom_s_out,
            trace_roots,
            constraint_root,
            fri_roots,
            pow_nonce,
            fs_challenges,
            merkle_proofs,
        })
    }
}

/// Child transcript wrapper used as a starting
/// point for in-AIR verification design.
#[derive(Clone, Debug)]
pub struct ZlChildTranscript {
    /// Minimal compact view of the child proof.
    pub compact: ZlChildCompact,

    /// Per-trace-segment Merkle roots for the
    /// base execution trace as exposed by the
    pub trace_roots: Vec<[u8; 32]>,

    /// Merkle root of the constraint composition
    /// polynomial commitment used by the child.
    pub constraint_root: [u8; 32],

    /// Per-layer Merkle roots of the FRI
    /// commitments derived from the base proof.
    pub fri_roots: Vec<[u8; 32]>,

    /// Final FRI polynomial data parsed from
    /// the underlying Winterfell proof.
    pub fri_final: ZlFriFinal,

    /// Number of unique FS queries used by the
    /// child proof. This matches `num_unique_queries`
    pub num_queries: u8,

    /// Per-query main-trace openings for
    /// the base trace segment.
    pub trace_main_openings: Vec<Vec<BE>>,

    /// Per-query constraint composition
    /// openings at FS query positions.
    pub constraint_openings: Vec<Vec<BE>>,

    /// Per-layer FRI evaluations for the
    /// DEEP composition polynomial.
    pub fri_layers: Vec<Vec<[BE; 2]>>,

    /// OOD trace evaluations (main segment)
    /// at points z and z * g.
    pub ood_main_current: Vec<BE>,
    pub ood_main_next: Vec<BE>,

    /// OOD trace evaluations (aux segment)
    /// at points z and z * g. Empty when the
    pub ood_aux_current: Vec<BE>,
    pub ood_aux_next: Vec<BE>,

    /// OOD evaluations of the constraint
    /// composition polynomial at z and z * g.
    pub ood_quotient_current: Vec<BE>,
    pub ood_quotient_next: Vec<BE>,

    /// Trace and constraint widths needed to
    /// interpret OOD rows and constraint
    pub main_trace_width: u32,
    pub aux_trace_width: u32,
    pub constraint_frame_width: u32,
}

/// FRI remainder polynomial container used by
/// child transcripts. Coefficients are kept in
#[derive(Clone, Debug)]
pub struct ZlFriFinal {
    pub deg: u16,
    pub coeffs: Vec<BE>,
}

impl ZlChildTranscript {
    /// Construct a child transcript
    /// wrapper from a full step proof.
    pub fn from_step(step: &StepProof) -> error::Result<Self> {
        let compact = ZlChildCompact::from_step(step)?;

        let wf_proof = &step.proof.inner;
        let trace_info = wf_proof.trace_info();
        let options = wf_proof.options();
        let fri_opts = options.to_fri_options();
        let lde_domain_size = wf_proof.lde_domain_size();
        let num_fri_layers = fri_opts.num_fri_layers(lde_domain_size);

        let num_queries = wf_proof.num_unique_queries as usize;

        let trace_roots = compact.trace_roots.clone();
        let constraint_root = compact.constraint_root;
        let fri_roots = compact.fri_roots.clone();

        // Parse FRI remainder polynomial (final
        // layer) into base-field coefficients.
        let coeffs = wf_proof.fri_proof.parse_remainder::<BE>().map_err(|_| {
            error::Error::InvalidInput("invalid FRI remainder layout in ZlChildTranscript")
        })?;

        let mut deg_idx: usize = 0;
        for (i, c) in coeffs.iter().enumerate().rev() {
            if *c != BE::ZERO {
                deg_idx = i;
                break;
            }
        }

        let fri_final = ZlFriFinal {
            deg: deg_idx as u16,
            coeffs,
        };

        let main_width = trace_info.main_trace_width();
        let aux_width = trace_info.aux_segment_width();

        // Decode main-trace openings for each
        // unique query position from the first
        let mut trace_main_openings = Vec::new();

        if num_queries > 0 {
            let (main_proof, main_table) = wf_proof.trace_queries[0]
                .clone()
                .parse::<BE, PoseidonHasher<BE>, MerkleTree<PoseidonHasher<BE>>>(
                    lde_domain_size,
                    num_queries,
                    main_width,
                )
                .map_err(|_| {
                    error::Error::InvalidInput("invalid trace queries layout in ZlChildTranscript")
                })?;

            let _ = main_proof; // kept for future Merkle checks

            trace_main_openings = main_table.rows().map(|row| row.to_vec()).collect();
        }

        // Decode constraint composition openings at query positions
        // and reconstruct the constraint frame width in a backend-
        let (constraint_openings, constraint_frame_width) = if num_queries == 0 {
            (Vec::new(), 0u32)
        } else {
            let cq_clone = wf_proof.constraint_queries.clone();
            let cq_bytes = Serializable::to_bytes(&cq_clone);
            let mut reader = SliceReader::new(&cq_bytes);

            let values_bytes =
                <Vec<u8> as Deserializable>::read_from(&mut reader).map_err(|_| {
                    error::Error::InvalidInput(
                        "failed to decode constraint query values in ZlChildTranscript",
                    )
                })?;

            // Skip paths bytes; `cq_clone.parse()` will re-parse them
            let _: Vec<u8> = Deserializable::read_from(&mut reader).map_err(|_| {
                error::Error::InvalidInput(
                    "failed to decode constraint query paths in ZlChildTranscript",
                )
            })?;

            let total_value_bytes = values_bytes.len();
            let elem_bytes = BE::ELEMENT_BYTES;

            let denom = num_queries
                .checked_mul(elem_bytes)
                .ok_or(error::Error::InvalidInput(
                    "overflow while computing constraint frame width in ZlChildTranscript",
                ))?;

            if denom == 0 || total_value_bytes % denom != 0 {
                return Err(error::Error::InvalidInput(
                    "constraint_queries byte length is inconsistent with num_queries in ZlChildTranscript",
                ));
            }

            let frame_width = total_value_bytes / denom;
            if frame_width == 0 {
                return Err(error::Error::InvalidInput(
                    "constraint frame width inferred from queries must be non-zero in ZlChildTranscript",
                ));
            }

            let (constraint_mproof, constraint_table) = cq_clone
                .parse::<BE, PoseidonHasher<BE>, MerkleTree<PoseidonHasher<BE>>>(
                    lde_domain_size,
                    num_queries,
                    frame_width,
                )
                .map_err(|_| {
                    error::Error::InvalidInput(
                        "invalid constraint queries layout in ZlChildTranscript",
                    )
                })?;

            let _ = constraint_mproof; // reserved for future Merkle checks

            let openings = constraint_table.rows().map(|row| row.to_vec()).collect();
            (openings, frame_width as u32)
        };

        // Decode FRI per-layer query values for the
        // DEEP composition polynomial. For each layer
        let mut fri_layers: Vec<Vec<[BE; 2]>> = Vec::new();

        if num_queries > 0 && num_fri_layers > 0 {
            let folding = fri_opts.folding_factor();

            let fri_proof_clone = wf_proof.fri_proof.clone();
            let (layer_queries, _layer_proofs) = fri_proof_clone
                .parse_layers::<BE, PoseidonHasher<BE>, MerkleTree<PoseidonHasher<BE>>>(
                    lde_domain_size,
                    folding,
                )
                .map_err(|_| {
                    error::Error::InvalidInput("invalid FRI layers layout in ZlChildTranscript")
                })?;

            debug_assert_eq!(layer_queries.len(), num_fri_layers);

            for vals in layer_queries {
                if vals.is_empty() || folding == 0 {
                    continue;
                }

                debug_assert_eq!(vals.len() % folding, 0);

                let q_count = vals.len() / folding;
                let mut layer_pairs = Vec::with_capacity(q_count);

                for q in 0..q_count {
                    let base = q * folding;
                    let v0 = vals[base];
                    let v1 = if folding > 1 {
                        vals[base + 1]
                    } else {
                        vals[base]
                    };

                    layer_pairs.push([v0, v1]);
                }

                fri_layers.push(layer_pairs);
            }
        }

        // Decode OOD frames for trace and constraint composition.
        let (
            ood_main_current,
            ood_main_next,
            ood_aux_current,
            ood_aux_next,
            ood_quotient_current,
            ood_quotient_next,
        ) = if num_queries == 0 {
            (
                Vec::new(),
                Vec::new(),
                Vec::new(),
                Vec::new(),
                Vec::new(),
                Vec::new(),
            )
        } else {
            let (trace_ood_frame, quotient_ood_frame) = wf_proof
                .ood_frame
                .clone()
                .parse::<BE>(main_width, aux_width, constraint_frame_width as usize)
                .map_err(|_| {
                    error::Error::InvalidInput("invalid OOD frame layout in ZlChildTranscript")
                })?;

            let trace_ood_current = trace_ood_frame.current_row();
            let trace_ood_next = trace_ood_frame.next_row();

            if trace_ood_current.len() != main_width + aux_width
                || trace_ood_next.len() != main_width + aux_width
            {
                return Err(error::Error::InvalidInput(
                    "ZlChildTranscript OOD trace row length is inconsistent with trace widths",
                ));
            }

            let (main_curr, aux_curr) = trace_ood_current.split_at(main_width);
            let (main_next, aux_next) = trace_ood_next.split_at(main_width);

            let quotient_ood_current = quotient_ood_frame.current_row();
            let quotient_ood_next = quotient_ood_frame.next_row();

            if quotient_ood_current.len() != constraint_frame_width as usize
                || quotient_ood_next.len() != constraint_frame_width as usize
            {
                return Err(error::Error::InvalidInput(
                    "ZlChildTranscript OOD quotient row length is inconsistent with constraint frame width",
                ));
            }

            (
                main_curr.to_vec(),
                main_next.to_vec(),
                aux_curr.to_vec(),
                aux_next.to_vec(),
                quotient_ood_current.to_vec(),
                quotient_ood_next.to_vec(),
            )
        };

        Ok(Self {
            compact,
            trace_roots,
            constraint_root,
            fri_roots,
            fri_final,
            num_queries: wf_proof.num_unique_queries,
            trace_main_openings,
            constraint_openings,
            fri_layers,
            ood_main_current,
            ood_main_next,
            ood_aux_current,
            ood_aux_next,
            ood_quotient_current,
            ood_quotient_next,
            main_trace_width: main_width as u32,
            aux_trace_width: aux_width as u32,
            constraint_frame_width,
        })
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

/// Verify basic consistency of a child transcript
/// against its compact commitment view.
///
/// Besides recomputing the aggregated Blake3 root, this
/// also enforces basic shape invariants over openings and
/// FRI data so that obviously malformed transcripts are
/// rejected early instead of propagating further into
/// aggregation logic.
pub fn verify_child_transcript(tx: &ZlChildTranscript) -> error::Result<()> {
    // Recompute the Blake3 commitment root over
    // trace and FRI commitments and compare it
    let mut h = Blake3Hasher::new();
    h.update(b"zkl/step/root_trace");
    h.update(&tx.compact.suite_id);

    for r in &tx.trace_roots {
        h.update(r);
    }

    h.update(&tx.constraint_root);

    for r in &tx.fri_roots {
        h.update(r);
    }

    let digest = h.finalize();
    let mut root_trace = [0u8; 32];
    root_trace.copy_from_slice(digest.as_bytes());

    if root_trace != tx.compact.trace_root {
        return Err(error::Error::InvalidInput(
            "ZlChildTranscript commitments do not match compact trace_root",
        ));
    }

    // Enforce basic shape invariants for
    // openings and FRI layers. These checks
    // deliberately stay coarse and avoid
    // depending on backend internals.
    let num_q = tx.num_queries as usize;

    if num_q == 0 {
        if !tx.trace_main_openings.is_empty() {
            return Err(error::Error::InvalidInput(
                "ZlChildTranscript must not contain trace openings when num_queries is zero",
            ));
        }
        if !tx.constraint_openings.is_empty() {
            return Err(error::Error::InvalidInput(
                "ZlChildTranscript must not contain constraint openings when num_queries is zero",
            ));
        }
        if !tx.fri_layers.is_empty() {
            return Err(error::Error::InvalidInput(
                "ZlChildTranscript must not contain FRI layers when num_queries is zero",
            ));
        }
    } else {
        if tx.trace_main_openings.len() != num_q {
            return Err(error::Error::InvalidInput(
                "ZlChildTranscript.trace_main_openings length is inconsistent with num_queries",
            ));
        }

        for row in &tx.trace_main_openings {
            if row.is_empty() {
                return Err(error::Error::InvalidInput(
                    "ZlChildTranscript contains an empty trace opening row",
                ));
            }
        }

        if tx.constraint_openings.len() != num_q {
            return Err(error::Error::InvalidInput(
                "ZlChildTranscript.constraint_openings length is inconsistent with num_queries",
            ));
        }

        let c_width = tx.constraint_frame_width as usize;
        if c_width == 0 {
            return Err(error::Error::InvalidInput(
                "ZlChildTranscript.constraint_frame_width must be non-zero when num_queries is non-zero",
            ));
        }

        for row in &tx.constraint_openings {
            if row.is_empty() {
                return Err(error::Error::InvalidInput(
                    "ZlChildTranscript contains an empty constraint opening row",
                ));
            }
            if row.len() != c_width {
                return Err(error::Error::InvalidInput(
                    "ZlChildTranscript.constraint_openings row width is inconsistent with constraint_frame_width",
                ));
            }
        }

        if !tx.fri_layers.is_empty() {
            for layer in &tx.fri_layers {
                if layer.is_empty() {
                    return Err(error::Error::InvalidInput(
                        "ZlChildTranscript contains an empty FRI layer",
                    ));
                }
            }
        }
    }

    // FRI remainder polynomial must be
    // non-empty and its reported degree
    let coeffs_len = tx.fri_final.coeffs.len();
    if coeffs_len == 0 {
        return Err(error::Error::InvalidInput(
            "ZlChildTranscript.fri_final.coeffs must be non-empty",
        ));
    }

    let max_deg = coeffs_len.saturating_sub(1) as u16;
    if tx.fri_final.deg > max_deg {
        return Err(error::Error::InvalidInput(
            "ZlChildTranscript.fri_final.deg exceeds coeffs.len() - 1",
        ));
    }

    Ok(())
}

fn hash_row_poseidon(row: &[BE], partition_size: usize) -> PoseidonDigest {
    if partition_size == 0 {
        // Empty partition falls back to zero digest
        return PoseidonHasher::<BE>::hash(&[]);
    }

    let mut digests = Vec::with_capacity(row.len().div_ceil(partition_size));

    for chunk in row.chunks(partition_size) {
        let d = PoseidonHasher::<BE>::hash_elements(chunk);
        digests.push(d);
    }

    // Fold partitions with Poseidon hasher
    // in the same way as Winterfell verifier
    if digests.len() == 1 {
        digests[0]
    } else {
        PoseidonHasher::<BE>::merge_many(&digests)
    }
}

/// Recompute a binary Poseidon Merkle root from a leaf
/// digest, its sibling path and the leaf index.
pub fn merkle_root_from_leaf(
    leaf: &PoseidonDigest,
    mut idx: usize,
    siblings: &[PoseidonDigest],
) -> PoseidonDigest {
    let mut acc = *leaf;

    for sib in siblings {
        let pair = if idx & 1 == 0 {
            [acc, *sib]
        } else {
            [*sib, acc]
        };

        acc = PoseidonHasher::<BE>::merge(&pair);
        idx >>= 1;
    }

    acc
}

/// Fold query positions from a source domain of the
/// given size into a smaller domain by the specified
pub fn fold_positions_usize(
    positions: &[usize],
    source_domain_size: usize,
    folding_factor: usize,
) -> error::Result<Vec<usize>> {
    if folding_factor == 0 {
        return Err(error::Error::InvalidInput(
            "folding_factor must be non-zero in fold_positions_usize",
        ));
    }

    if source_domain_size == 0 || source_domain_size % folding_factor != 0 {
        return Err(error::Error::InvalidInput(
            "source_domain_size must be a positive multiple of folding_factor in fold_positions_usize",
        ));
    }

    let target_domain_size = source_domain_size / folding_factor;
    let mut result = Vec::new();

    for &pos in positions {
        let idx = pos % target_domain_size;
        if !result.contains(&idx) {
            result.push(idx);
        }
    }

    Ok(result)
}

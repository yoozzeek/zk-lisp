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

use crate::fs as fs_helpers;
use crate::poseidon;
use crate::poseidon_hasher::PoseidonHasher;
use crate::utils;
use crate::zl_step::{StepMeta, ZlStepProof};

use blake3::Hasher as Blake3Hasher;
use winterfell::crypto::{Digest, MerkleTree};
use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;
use zk_lisp_proof::error;

/// Compact child structure derived from a `ZlStepProof`.
///
/// This initial version focuses on fields needed for
/// aggregation over work units and canonical child
/// identification via `step_digest`. It is extended
/// with explicit commitment roots so that Merkle and
/// FRI checks can be performed inside aggregation logic
/// without re-reading the original Winterfell proof.
#[derive(Clone, Debug)]
pub struct ZlChildCompact {
    /// Poseidon suite identifier used by the child
    /// proof and its digest construction.
    pub suite_id: [u8; 32],

    /// Per-proof metadata echoing the proving
    /// profile (m, rho, q, o, lambda, pi_len,
    /// v_units).
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
    ///
    /// In the initial aggregation skeleton this is
    /// used only to build simple consistency checks
    /// in the aggregator AIR; its semantics may be
    /// refined as the recursion layer evolves.
    pub trace_root: [u8; 32],

    /// Per-trace-segment Merkle roots for the
    /// base execution trace as exposed by the
    /// underlying Winterfell proof.
    pub trace_roots: Vec<[u8; 32]>,

    /// Merkle root of the constraint composition
    /// polynomial commitment used by the child.
    pub constraint_root: [u8; 32],

    /// Per-layer Merkle roots of the FRI
    /// commitments derived from the base proof.
    pub fri_roots: Vec<[u8; 32]>,

    /// Proof-of-work nonce used for query seed
    /// grinding in the underlying Winterfell proof.
    /// This is needed to deterministically recompute
    /// query positions from the same public coin
    /// state during transcript-based verification.
    pub pow_nonce: u64,

    /// Fiat–Shamir challenges as seen by the
    /// child verifier. This will be populated from
    /// the Poseidon-based FS transcript once the
    /// replay logic is in place.
    pub fs_challenges: Option<ZlFsChallenges>,

    /// Merkle authentication data for trace,
    /// constraint and FRI trees at all query
    /// positions. This stays optional until the
    /// extraction from the underlying Winterfell
    /// proof is implemented.
    pub merkle_proofs: Option<ZlMerkleProofs>,
}

/// Fiat–Shamir challenges needed to replay
/// zk-lisp AIR verification at the aggregator
/// level.
#[derive(Clone, Debug)]
pub struct ZlFsChallenges {
    /// One or more OOD evaluation points used
    /// for DEEP composition. Most AIRs use a
    /// single point, but we keep this generic.
    pub ood_points: Vec<BE>,

    /// Opaque list of DEEP/composition coefficients
    /// (α, β, γ, etc.) in the order expected by
    /// the aggregation constraints.
    pub deep_coeffs: Vec<BE>,

    /// Per-layer FRI folding challenges.
    pub fri_alphas: Vec<BE>,

    /// Query positions in the LDE domain
    /// (indices in [0, n)).
    pub query_positions: Vec<u32>,
}

/// Simple Merkle path represented by a list of
/// sibling digests from leaf to root. Direction
/// at each level is derived from the leaf index
/// (stored separately) and is not encoded here.
#[derive(Clone, Debug)]
pub struct ZlMerklePath {
    pub siblings: Vec<[u8; 32]>,
}

/// Per-layer FRI Merkle proof for a single leaf
/// in the FRI commitment at a given layer.
///
/// For folding factor 2 each leaf carries two
/// evaluations (v0, v1) committed under the
/// corresponding FRI root at index `idx`.
#[derive(Clone, Debug)]
pub struct ZlFriLayerProof {
    /// Leaf index in the FRI layer commitment
    /// domain. For layer `d` this must equal
    /// the folded position `fold_positions_d[j]`.
    pub idx: u32,
    /// Values committed in the leaf at `idx`;
    /// for folding factor 2 this is a pair of
    /// evaluations for the corresponding coset.
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
    /// `constraint_root`.
    pub constraint_paths: Vec<ZlMerklePath>,

    /// FRI Merkle proofs indexed as
    /// `fri_layers[layer][query]`.
    pub fri_layers: Vec<Vec<ZlFriLayerProof>>,
}

impl ZlChildCompact {
    /// Derive a compact child representation from
    /// a full step proof wrapper.
    pub fn from_step(step: &ZlStepProof) -> error::Result<Self> {
        let suite_id = step.proof.header.suite_id;
        let meta = step.proof.meta;
        let pi_core = step.pi_core.clone();
        let rom_acc = step.rom_acc;
        let step_digest = step.digest();
        let trace_root = step.proof.commits.root_trace;

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
        // which is bit-for-bit consistent with the underlying child
        // proof transcript.
        let fs_challenges = if num_queries == 0 {
            None
        } else {
            Some(fs_helpers::replay_fs_from_step(step)?)
        };

        // Extract Merkle authentication data for trace,
        // constraint and FRI queries.
        //
        // NOTE: proper Merkle extraction requires replaying
        // Winterfell's FS coin exactly so that query
        // positions used in the proof match the indices
        // passed into batch Merkle multiproofs. Until this
        // replay is implemented, we leave Merkle proofs
        // empty to avoid constructing inconsistent
        // authentication data.
        let merkle_proofs = None;

        // Original WIP implementation for Merkle extraction kept
        // for future work. Once FS replay is wired to mirror
        // Winterfell exactly, this block can be re-enabled.
        // let merkle_proofs = {
        //     if num_queries == 0 {
        //         None
        //     } else {
        //         let fs = fs_challenges.as_ref().ok_or_else(|| {
        //             error::Error::InvalidInput(
        //                 "ZlChildCompact.fs_challenges must be present when num_queries > 0",
        //             )
        //         })?;
        //
        //         if fs.query_positions.len() != num_queries {
        //             return Err(error::Error::InvalidInput(
        //                 "ZlChildCompact.fs_challenges.query_positions length is inconsistent with num_queries",
        //             ));
        //         }
        //
        //         // Parse main-trace queries for the first
        //         // (and currently only) trace segment.
        //         let main_width = trace_info.main_trace_width();
        //
        //         let (main_mproof, main_table) = wf_proof.trace_queries[0]
        //             .clone()
        //             .parse::<BE, PoseidonHasher<BE>, MerkleTree<PoseidonHasher<BE>>>(
        //                 lde_domain_size,
        //                 num_queries,
        //                 main_width,
        //             )
        //             .map_err(|_| {
        //                 error::Error::InvalidInput("invalid trace queries layout in ZlChildCompact")
        //             })?;
        //
        //         // Rebuild leaf digests for each queried
        //         // main-trace row using the same partitioning
        //         // logic as Winterfell verifier.
        //         let partition_opts = options.partition_options();
        //         let partition_size_main =
        //             partition_opts.partition_size::<BE>(trace_info.main_trace_width());
        //
        //         let mut trace_leaves = Vec::with_capacity(num_queries);
        //         let mut trace_indexes = Vec::with_capacity(num_queries);
        //
        //         // Each row in `main_table` is ordered consistently
        //         // with `fs.query_positions`, and the Merkle tree
        //         // is built over the LDE domain [0, lde_domain_size).
        //         for (row, &pos) in main_table.rows().zip(fs.query_positions.iter()) {
        //             let leaf = hash_row_poseidon(row, partition_size_main);
        //             trace_leaves.push(leaf);
        //
        //             let idx = pos as usize;
        //             if idx >= lde_domain_size {
        //                 return Err(error::Error::InvalidInput(
        //                     "ZlChildCompact.fs_challenges.query_positions contains index outside LDE domain",
        //                 ));
        //             }
        //
        //             trace_indexes.push(idx);
        //         }
        //
        //         let trace_openings = main_mproof
        //             .into_openings(&trace_leaves, &trace_indexes)
        //             .map_err(|_| {
        //                 error::Error::InvalidInput(
        //                     "failed to decompress trace Merkle multiproof in ZlChildCompact",
        //                 )
        //             })?;
        //
        //         let mut trace_paths = Vec::with_capacity(trace_openings.len());
        //         for (_leaf, siblings) in trace_openings {
        //             let mut sib_bytes = Vec::with_capacity(siblings.len());
        //             for d in siblings {
        //                 let mut bytes = [0u8; 32];
        //                 bytes.copy_from_slice(&d.as_bytes());
        //                 sib_bytes.push(bytes);
        //             }
        //
        //             trace_paths.push(ZlMerklePath {
        //                 siblings: sib_bytes,
        //             });
        //         }
        //
        //         // Infer constraint frame width from the serialized
        //         // constraint queries and use it to parse the table
        //         // in the same way as Winterfell verifier.
        //         let cq_clone = wf_proof.constraint_queries.clone();
        //         let cq_bytes = Serializable::to_bytes(&cq_clone);
        //         let mut reader = SliceReader::new(&cq_bytes);
        //
        //         let values_bytes =
        //             <Vec<u8> as Deserializable>::read_from(&mut reader).map_err(|_| {
        //                 error::Error::InvalidInput(
        //                     "failed to decode constraint query values in ZlChildCompact",
        //                 )
        //             })?;
        //
        //         // skip paths bytes;
        //         // `cq_clone.parse()` will re-parse them
        //         let _: Vec<u8> = Deserializable::read_from(&mut reader).map_err(|_| {
        //             error::Error::InvalidInput(
        //                 "failed to decode constraint query paths in ZlChildCompact",
        //             )
        //         })?;
        //
        //         let total_value_bytes = values_bytes.len();
        //         let elem_bytes = BE::ELEMENT_BYTES;
        //
        //         let denom = num_queries.checked_mul(elem_bytes).ok_or_else(|| {
        //             error::Error::InvalidInput(
        //                 "overflow while computing constraint frame width in ZlChildCompact",
        //             )
        //         })?;
        //
        //         if denom == 0 || total_value_bytes % denom != 0 {
        //             return Err(error::Error::InvalidInput(
        //                 "constraint_queries byte length is inconsistent with num_queries",
        //             ));
        //         }
        //
        //         let constraint_frame_width = total_value_bytes / denom;
        //         if constraint_frame_width == 0 {
        //             return Err(error::Error::InvalidInput(
        //                 "constraint frame width inferred from queries must be non-zero",
        //             ));
        //         }
        //
        //         let (constraint_mproof, constraint_table) = cq_clone
        //             .parse::<BE, PoseidonHasher<BE>, MerkleTree<PoseidonHasher<BE>>>(
        //                 lde_domain_size,
        //                 num_queries,
        //                 constraint_frame_width,
        //             )
        //             .map_err(|_| {
        //                 error::Error::InvalidInput(
        //                     "invalid constraint queries layout in ZlChildCompact",
        //                 )
        //             })?;
        //
        //         let partition_size_constraint =
        //             partition_opts.partition_size::<BE>(constraint_frame_width);
        //
        //         let mut constraint_leaves = Vec::with_capacity(num_queries);
        //         let mut constraint_indexes = Vec::with_capacity(num_queries);
        //
        //         for (row, &pos) in constraint_table.rows().zip(fs.query_positions.iter()) {
        //             let leaf = hash_row_poseidon(row, partition_size_constraint);
        //             constraint_leaves.push(leaf);
        //
        //             let idx = pos as usize;
        //             if idx >= lde_domain_size {
        //                 return Err(error::Error::InvalidInput(
        //                     "ZlChildCompact.fs_challenges.query_positions contains index outside LDE domain",
        //                 ));
        //             }
        //
        //             constraint_indexes.push(idx);
        //         }
        //
        //         let constraint_openings = constraint_mproof
        //             .into_openings(&constraint_leaves, &constraint_indexes)
        //             .map_err(|_| {
        //                 error::Error::InvalidInput(
        //                     "failed to decompress constraint Merkle multiproof in ZlChildCompact",
        //                 )
        //             })?;
        //
        //         let mut constraint_paths = Vec::with_capacity(constraint_openings.len());
        //         for (_leaf, siblings) in constraint_openings {
        //             let mut sib_bytes = Vec::with_capacity(siblings.len());
        //             for d in siblings {
        //                 let mut bytes = [0u8; 32];
        //                 bytes.copy_from_slice(&d.as_bytes());
        //                 sib_bytes.push(bytes);
        //             }
        //
        //             constraint_paths.push(ZlMerklePath {
        //                 siblings: sib_bytes,
        //             });
        //         }
        //
        //         // FRI Merkle paths
        //         let folding = fri_opts.folding_factor();
        //         if folding != 2 {
        //             return Err(error::Error::InvalidInput(
        //                 "ZlChildCompact currently supports only FRI folding factor 2",
        //             ));
        //         }
        //
        //         let num_fri_layers = fri_opts.num_fri_layers(lde_domain_size);
        //         let mut fri_layers_paths: Vec<Vec<ZlFriLayerProof>> = Vec::new();
        //
        //         if num_fri_layers > 0 {
        //             let fri_proof_clone = wf_proof.fri_proof.clone();
        //             let (layer_values, layer_proofs) = fri_proof_clone
        //                 .parse_layers::<BE, PoseidonHasher<BE>, MerkleTree<PoseidonHasher<BE>>>(
        //                     lde_domain_size,
        //                     folding,
        //                 )
        //                 .map_err(|_| {
        //                     error::Error::InvalidInput(
        //                         "invalid FRI layers layout in ZlChildCompact",
        //                     )
        //                 })?;
        //
        //             debug_assert_eq!(layer_values.len(), num_fri_layers);
        //             debug_assert_eq!(layer_proofs.len(), num_fri_layers);
        //
        //             let mut positions: Vec<usize> =
        //                 fs.query_positions.iter().map(|&p| p as usize).collect();
        //             let mut domain_size = lde_domain_size;
        //
        //             for (vals, mproof) in layer_values.into_iter().zip(layer_proofs.into_iter()) {
        //                 let folded_positions = fri_fold_positions(&positions, domain_size, folding);
        //                 if folded_positions.is_empty() {
        //                     return Err(error::Error::InvalidInput(
        //                         "FRI folded positions must be non-empty when num_queries > 0",
        //                     ));
        //                 }
        //
        //                 if vals.len() != folded_positions.len() * folding {
        //                     return Err(error::Error::InvalidInput(
        //                         "FRI layer values length is inconsistent with folded positions",
        //                     ));
        //                 }
        //
        //                 let q_count = folded_positions.len();
        //                 let mut leaf_values: Vec<[BE; 2]> = Vec::with_capacity(q_count);
        //
        //                 for i in 0..q_count {
        //                     let base = i * folding;
        //                     let v0 = vals[base];
        //                     let v1 = vals[base + 1];
        //                     leaf_values.push([v0, v1]);
        //                 }
        //
        //                 let mut leaves = Vec::with_capacity(q_count);
        //                 for pair in &leaf_values {
        //                     let leaf = PoseidonHasher::<BE>::hash_elements(pair);
        //                     leaves.push(leaf);
        //                 }
        //
        //                 let indexes = folded_positions.clone();
        //                 let openings = mproof.into_openings(&leaves, &indexes).map_err(|_| {
        //                     error::Error::InvalidInput(
        //                         "failed to decompress FRI Merkle multiproof in ZlChildCompact",
        //                     )
        //                 })?;
        //
        //                 if openings.len() != q_count {
        //                     return Err(error::Error::InvalidInput(
        //                         "FRI openings length mismatch in ZlChildCompact",
        //                     ));
        //                 }
        //
        //                 let mut layer_proofs_out = Vec::with_capacity(q_count);
        //
        //                 for ((idx, pair), (_leaf, siblings)) in indexes
        //                     .into_iter()
        //                     .zip(leaf_values.into_iter())
        //                     .zip(openings.into_iter())
        //                 {
        //                     let mut sib_bytes = Vec::with_capacity(siblings.len());
        //                     for d in siblings {
        //                         let mut bytes = [0u8; 32];
        //                         bytes.copy_from_slice(&d.as_bytes());
        //                         sib_bytes.push(bytes);
        //                     }
        //
        //                     let path = ZlMerklePath {
        //                         siblings: sib_bytes,
        //                     };
        //                     layer_proofs_out.push(ZlFriLayerProof {
        //                         idx: idx as u32,
        //                         values: pair,
        //                         path,
        //                     });
        //                 }
        //
        //                 fri_layers_paths.push(layer_proofs_out);
        //
        //                 positions = folded_positions;
        //                 domain_size /= folding;
        //             }
        //         }
        //
        //         Some(ZlMerkleProofs {
        //             trace_paths,
        //             constraint_paths,
        //             fri_layers: fri_layers_paths,
        //         })
        //     }
        // };

        Ok(Self {
            suite_id,
            meta,
            pi_core,
            rom_acc,
            step_digest,
            trace_root,
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
    /// underlying Winterfell proof.
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
    /// in the underlying Winterfell proof context.
    pub num_queries: u8,

    /// Per-query main-trace openings for
    /// the base trace segment.
    pub trace_main_openings: Vec<Vec<BE>>,

    /// Per-layer FRI evaluations for the
    /// DEEP composition polynomial.
    pub fri_layers: Vec<Vec<[BE; 2]>>,
}

/// FRI remainder polynomial container used by
/// child transcripts. Coefficients are kept in
/// the base field to be directly usable by
/// aggregation logic.
#[derive(Clone, Debug)]
pub struct ZlFriFinal {
    pub deg: u16,
    pub coeffs: Vec<BE>,
}

impl ZlChildTranscript {
    /// Construct a child transcript
    /// wrapper from a full step proof.
    pub fn from_step(step: &ZlStepProof) -> error::Result<Self> {
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

        // Decode main-trace openings for each
        // unique query position from the first
        // (and currently only) trace segment.
        let main_width = trace_info.main_trace_width();
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

        // Decode FRI per-layer query values for the
        // DEEP composition polynomial. For each layer
        // `l`, we obtain a flat vector of length
        // `num_queries * folding_factor` and split it
        // into (v0, v1) pairs per query.
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

        Ok(Self {
            compact,
            trace_roots,
            constraint_root,
            fri_roots,
            fri_final,
            num_queries: wf_proof.num_unique_queries,
            trace_main_openings,
            fri_layers,
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
    // against the compact view embedded
    // into `ZlChildCompact`.
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
    // must not exceed coeffs.len() - 1.
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

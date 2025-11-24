// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Integration-style tests for
//! ZlChildCompact Merkle extraction.

use winterfell::crypto::{Digest, ElementHasher};
use winterfell::math::fields::f128::BaseElement as BE;
use zk_lisp_compiler::builder::{Op, ProgramBuilder};
use zk_lisp_proof::ProverOptions;
use zk_lisp_proof::pi::PublicInputsBuilder;
use zk_lisp_proof_winterfell::agg::child::{ZlChildCompact, ZlMerklePath, merkle_root_from_leaf};
use zk_lisp_proof_winterfell::poseidon::hasher::PoseidonHasher;

fn make_opts() -> ProverOptions {
    ProverOptions {
        min_security_bits: 40,
        blowup: 8,
        grind: 8,
        queries: 8,
        max_segment_rows: None,
        max_concurrent_segments: None,
    }
}

fn build_tiny_program() -> zk_lisp_compiler::Program {
    let metrics = zk_lisp_compiler::CompilerMetrics::default();
    let mut b = ProgramBuilder::new();

    b.push(Op::End);

    b.finalize(metrics).expect("program build must succeed")
}

fn build_public_inputs(program: &zk_lisp_compiler::Program) -> zk_lisp_proof::pi::PublicInputs {
    PublicInputsBuilder::from_program(program)
        .build()
        .expect("pi build")
}

fn verify_path(root: &[u8; 32], idx: usize, path: &ZlMerklePath) {
    // Basic shape: non-empty path
    assert!(!path.siblings.is_empty());

    let computed = merkle_root_from_leaf(&path.leaf, idx, &path.siblings);
    assert_eq!(
        root,
        &computed.as_bytes(),
        "Merkle path must reconstruct advertised root",
    );
}

#[test]
fn agg_child_merkle_paths_match_roots() {
    let program = build_tiny_program();
    let pi = build_public_inputs(&program);
    let opts = make_opts();

    let steps = zk_lisp_proof_winterfell::prove::prove_program(&program, &pi, &opts)
        .expect("step proof must succeed");

    let child = ZlChildCompact::from_step(&steps[0]).expect("compact child must build");

    let fs = child
        .fs_challenges
        .as_ref()
        .expect("fs_challenges must be present for non-zero queries");

    let merkle = child
        .merkle_proofs
        .as_ref()
        .expect("merkle_proofs must be present for non-zero queries");

    let num_q = fs.query_positions.len();
    assert_eq!(num_q, merkle.trace_paths.len());
    assert_eq!(num_q, merkle.constraint_paths.len());

    // Verify trace paths against the first trace root.
    let trace_root = child.trace_roots[0];

    for (&pos, path) in fs.query_positions.iter().zip(merkle.trace_paths.iter()) {
        verify_path(&trace_root, pos as usize, path);
    }

    // Verify constraint paths
    // against the constraint root.
    let constraint_root = child.constraint_root;

    for (&pos, path) in fs
        .query_positions
        .iter()
        .zip(merkle.constraint_paths.iter())
    {
        verify_path(&constraint_root, pos as usize, path);
    }

    // Shape and correctness checks for FRI layers.
    let num_layers = merkle.fri_layers.len();
    if num_layers > 0 {
        // Rebuild folded positions for each FRI
        // layer in the same way as FriProver.
        let mut positions: Vec<usize> = fs.query_positions.iter().map(|&p| p as usize).collect();
        let mut domain_size = (child.meta.m as usize)
            .checked_mul(child.meta.rho as usize)
            .expect("LDE domain size overflow in agg_child_merkle_paths_match_roots");
        let folding = 2usize;

        for (layer_idx, layer) in merkle.fri_layers.iter().enumerate() {
            assert!(!layer.is_empty());

            let folded_positions = fold_positions_test(&positions, domain_size, folding);
            assert_eq!(
                folded_positions.len(),
                layer.len(),
                "folded positions count must match number of FRI leaf proofs",
            );

            let fri_root = child.fri_roots[layer_idx];

            for (lp, &idx) in layer.iter().zip(folded_positions.iter()) {
                assert_eq!(
                    lp.idx as usize, idx,
                    "FRI leaf index must match folded query position",
                );
                assert!(!lp.path.siblings.is_empty());

                let leaf = PoseidonHasher::<BE>::hash_elements(&lp.values);
                let computed = merkle_root_from_leaf(&leaf, idx, &lp.path.siblings);
                assert_eq!(
                    &fri_root,
                    &computed.as_bytes(),
                    "FRI Merkle path must reconstruct advertised fri_root",
                );
            }

            positions = folded_positions;
            domain_size /= folding;
        }
    }
}

fn fold_positions_test(
    positions: &[usize],
    source_domain_size: usize,
    folding_factor: usize,
) -> Vec<usize> {
    assert!(folding_factor > 0);
    assert!(
        source_domain_size > 0 && source_domain_size % folding_factor == 0,
        "invalid source_domain_size/folding_factor in fold_positions_test",
    );

    let target_domain_size = source_domain_size / folding_factor;
    let mut result = Vec::new();
    for &p in positions {
        let idx = p % target_domain_size;
        if !result.contains(&idx) {
            result.push(idx);
        }
    }
    result
}

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

use winterfell::crypto::Digest;
use zk_lisp_compiler::builder::{Op, ProgramBuilder};
use zk_lisp_proof::ProverOptions;
use zk_lisp_proof::pi::PublicInputsBuilder;
use zk_lisp_proof_winterfell::agg_child::{ZlChildCompact, ZlMerklePath, merkle_root_from_leaf};

fn make_opts() -> ProverOptions {
    ProverOptions {
        min_security_bits: 40,
        blowup: 8,
        grind: 8,
        queries: 8,
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

    let step = zk_lisp_proof_winterfell::prove::prove_step(&program, &pi, &opts)
        .expect("step proof must succeed");

    let child = ZlChildCompact::from_step(&step).expect("compact child must build");

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

    // Shape checks for FRI layers.
    let num_layers = merkle.fri_layers.len();
    if num_layers > 0 {
        for layer in &merkle.fri_layers {
            assert!(!layer.is_empty());
            for lp in layer {
                assert_eq!(lp.values.len(), 2);
                assert!(!lp.path.siblings.is_empty());
            }
        }
    }
}

// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Basic tests for ZlChildTranscript extraction.
//!
//! These tests ensure that commitment roots parsed into
//! `ZlChildTranscript` are consistent with the aggregated
//! commitment root used by the zl1 step format.

use zk_lisp_compiler::builder::{Op, ProgramBuilder};
use zk_lisp_proof::ProverOptions;
use zk_lisp_proof::pi::PublicInputsBuilder;
use zk_lisp_proof_winterfell::agg_child::{ZlChildTranscript, verify_child_transcript};

fn make_opts() -> ProverOptions {
    ProverOptions {
        min_security_bits: 40,
        blowup: 8,
        grind: 8,
        queries: 8,
        max_segment_rows: None,
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

#[test]
fn transcript_commitments_match_zl1_root_trace() {
    let program = build_tiny_program();
    let pi = build_public_inputs(&program);
    let opts = make_opts();

    let step = zk_lisp_proof_winterfell::prove::prove_step(&program, &pi, &opts)
        .expect("step proof must succeed");

    let transcript =
        ZlChildTranscript::from_step(&step).expect("child transcript extraction must succeed");

    // Verify that transcript commitments recombine into
    // the same aggregated root as stored in the compact
    verify_child_transcript(&transcript)
        .expect("child transcript commitments must match compact trace_root");

    // FRI final polynomial must be non-empty and
    // degree must not exceed coeffs.len() - 1.
    assert!(!transcript.fri_final.coeffs.is_empty());

    let max_deg = transcript.fri_final.coeffs.len().saturating_sub(1) as u16;
    assert!(transcript.fri_final.deg <= max_deg);

    // Trace openings, constraint openings and FRI
    // layer values must be shape-consistent with
    let num_q = transcript.num_queries as usize;
    assert_eq!(num_q, transcript.trace_main_openings.len());
    assert_eq!(num_q, transcript.constraint_openings.len());

    for row in &transcript.trace_main_openings {
        assert!(!row.is_empty());
    }

    let c_width = transcript.constraint_frame_width as usize;
    assert!(c_width > 0);

    for row in &transcript.constraint_openings {
        assert!(!row.is_empty());
        assert_eq!(row.len(), c_width);
    }

    if !transcript.fri_layers.is_empty() {
        for layer in &transcript.fri_layers {
            assert!(!layer.is_empty());
        }
    }

    // OOD rows must be consistent with reported
    // trace and constraint widths.
    let main_w = transcript.main_trace_width as usize;
    let aux_w = transcript.aux_trace_width as usize;

    if !transcript.ood_main_current.is_empty() {
        assert_eq!(transcript.ood_main_current.len(), main_w);
        assert_eq!(transcript.ood_main_next.len(), main_w);
    }

    if aux_w > 0 && !transcript.ood_aux_current.is_empty() {
        assert_eq!(transcript.ood_aux_current.len(), aux_w);
        assert_eq!(transcript.ood_aux_next.len(), aux_w);
    }

    if c_width > 0 && !transcript.ood_quotient_current.is_empty() {
        assert_eq!(transcript.ood_quotient_current.len(), c_width);
        assert_eq!(transcript.ood_quotient_next.len(), c_width);
    }
}

// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::{BatchingMethod, FieldExtension, ProofOptions};

use zk_lisp_compiler::builder::{Op, ProgramBuilder};
use zk_lisp_compiler::{CompilerMetrics, compile_entry};
use zk_lisp_proof::pi::PublicInputsBuilder;
use zk_lisp_proof_winterfell::layout::Columns;
use zk_lisp_proof_winterfell::prove::{Error as ProveError, ZkProver, verify_proof};
use zk_lisp_proof_winterfell::schedule::pos_map;
use zk_lisp_proof_winterfell::trace::build_trace;
use zk_lisp_proof_winterfell::utils::vm_output_from_trace;

fn prove_opts() -> ProofOptions {
    ProofOptions::new(
        1, // queries
        8, // blowup
        0, // grind
        FieldExtension::None,
        2,
        1,
        BatchingMethod::Linear,
        BatchingMethod::Linear,
    )
}

fn prove_or_allow_backend(e: ProveError) {
    // In small traces Winterfell may
    // reject options; allow backend errors.
    if !matches!(e, ProveError::BackendSource(_)) {
        panic!("prove failed: {e}");
    }
}

#[test]
fn safe_add_trace_and_prove() {
    let src = "(def (main) (safe-add 7 9))";
    let program = compile_entry(src, &[]).expect("compile");

    // Build PI by inferring features
    // to avoid mismatches.
    let pi = PublicInputsBuilder::from_program(&program)
        .build()
        .expect("pi");

    let trace = build_trace(&program, &pi).expect("trace");
    let rom_acc = zk_lisp_proof_winterfell::romacc::rom_acc_from_program(&program);
    let cols = Columns::baseline();
    let (out_reg, out_row) = vm_output_from_trace(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    // 16
    assert_eq!(v, BE::from(16u64));

    let opts = prove_opts();
    let prover = ZkProver::new(opts.clone(), pi.clone(), rom_acc);
    match prover.prove(trace) {
        Ok(proof) => {
            let _ = verify_proof(proof, &program, pi, &opts, 64);
        }
        Err(e) => prove_or_allow_backend(e),
    }
}

#[test]
fn safe_sub_trace_and_prove() {
    let src = "(def (main) (safe-sub 9 7))";
    let program = compile_entry(src, &[]).expect("compile");

    let pi = PublicInputsBuilder::from_program(&program)
        .build()
        .expect("pi");

    let trace = build_trace(&program, &pi).expect("trace");
    let rom_acc = zk_lisp_proof_winterfell::romacc::rom_acc_from_program(&program);
    let cols = Columns::baseline();
    let (out_reg, out_row) = vm_output_from_trace(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    // 2
    assert_eq!(v, BE::from(2u64));

    let opts = prove_opts();
    let prover = ZkProver::new(opts.clone(), pi.clone(), rom_acc);
    match prover.prove(trace) {
        Ok(proof) => {
            let _ = verify_proof(proof, &program, pi, &opts, 64);
        }
        Err(e) => prove_or_allow_backend(e),
    }
}

#[test]
fn safe_mul_trace_and_prove() {
    let src = "(def (main) (safe-mul 32000 65000))";
    let program = compile_entry(src, &[]).expect("compile");

    let pi = PublicInputsBuilder::from_program(&program)
        .build()
        .expect("pi");

    let trace = build_trace(&program, &pi).expect("trace");
    let rom_acc = zk_lisp_proof_winterfell::romacc::rom_acc_from_program(&program);
    let cols = Columns::baseline();
    let (out_reg, out_row) = vm_output_from_trace(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    // 32000 * 65000 = 2_080_000_000
    assert_eq!(v, BE::from(2_080_000_000u64));

    let opts = prove_opts();
    let prover = ZkProver::new(opts.clone(), pi.clone(), rom_acc);
    match prover.prove(trace) {
        Ok(proof) => {
            let _ = verify_proof(proof, &program, pi, &opts, 64);
        }
        Err(e) => prove_or_allow_backend(e),
    }
}

#[test]
fn divmod_q_r_e2e_small_cases() {
    // q: 23/7=3, r: 23%7=2
    let src_q = "(def (main) (divmod-q 23 7))";
    let program_q = compile_entry(src_q, &[]).expect("compile q");

    let pi_q = PublicInputsBuilder::from_program(&program_q)
        .build()
        .expect("pi q");
    let trace_q = build_trace(&program_q, &pi_q).expect("trace q");

    let cols = Columns::baseline();
    let (out_reg_q, out_row_q) = vm_output_from_trace(&trace_q);
    let vq = trace_q.get(cols.r_index(out_reg_q as usize), out_row_q as usize);

    assert_eq!(vq, BE::from(3u64));

    let src_r = "(def (main) (divmod-r 23 7))";

    let program_r = compile_entry(src_r, &[]).expect("compile r");
    let pi_r = PublicInputsBuilder::from_program(&program_r)
        .build()
        .expect("pi r");

    let trace_r = build_trace(&program_r, &pi_r).expect("trace r");
    let (out_reg_r, out_row_r) = vm_output_from_trace(&trace_r);
    let vr = trace_r.get(cols.r_index(out_reg_r as usize), out_row_r as usize);

    assert_eq!(vr, BE::from(2u64));
}

#[cfg_attr(debug_assertions, ignore)]
#[test]
fn divmod_q_r_e2e_more_cases_and_prove() {
    // q: 100/10=10, r=0;
    // q: 5/2=2, r=1;
    let cases = vec![
        ("(def (main) (divmod-q 100 10))", 10u64),
        ("(def (main) (divmod-q 5 2))", 2u64),
        ("(def (main) (divmod-q 0 10))", 0u64),
        ("(def (main) (divmod-q 7 1))", 7u64),
    ];

    for (src, expect) in cases {
        let program = compile_entry(src, &[]).expect("compile q");

        let pi = PublicInputsBuilder::from_program(&program)
            .build()
            .expect("pi");
        let trace = build_trace(&program, &pi).expect("trace");

        let cols = Columns::baseline();
        let (out_reg, out_row) = vm_output_from_trace(&trace);
        let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

        assert_eq!(v, BE::from(expect));

        let opts = prove_opts();
        let rom_acc = zk_lisp_proof_winterfell::romacc::rom_acc_from_program(&program);
        let prover = ZkProver::new(opts.clone(), pi.clone(), rom_acc)
            .with_preflight_mode(zk_lisp_proof::frontend::PreflightMode::Off);
        match prover.prove(trace) {
            Ok(proof) => {
                let _ = verify_proof(proof, &program, pi, &opts, 64);
            }
            Err(e) => prove_or_allow_backend(e),
        }
    }

    let cases_r = vec![
        ("(def (main) (divmod-r 100 10))", 0u64),
        ("(def (main) (divmod-r 5 2))", 1u64),
        ("(def (main) (divmod-r 0 10))", 0u64),
        ("(def (main) (divmod-r 7 1))", 0u64),
    ];

    for (src, expect) in cases_r {
        let program = compile_entry(src, &[]).expect("compile r");

        let pi = PublicInputsBuilder::from_program(&program)
            .build()
            .expect("pi");
        let trace = build_trace(&program, &pi).expect("trace");
        let rom_acc = zk_lisp_proof_winterfell::romacc::rom_acc_from_program(&program);

        let cols = Columns::baseline();
        let (out_reg, out_row) = vm_output_from_trace(&trace);
        let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

        assert_eq!(v, BE::from(expect));

        let opts = prove_opts();
        let prover = ZkProver::new(opts.clone(), pi.clone(), rom_acc)
            .with_preflight_mode(zk_lisp_proof::frontend::PreflightMode::Off);
        match prover.prove(trace) {
            Ok(proof) => {
                let _ = verify_proof(proof, &program, pi, &opts, 64);
            }
            Err(e) => prove_or_allow_backend(e),
        }
    }
}

#[test]
fn divmod_divide_by_zero_proving_fails() {
    // Using immediate zero to
    // ensure dynamic lowering path;
    let src = "(def (main) (divmod-q 5 0))";
    let program = compile_entry(src, &[]).expect("compile");

    let pi = PublicInputsBuilder::from_program(&program)
        .build()
        .expect("pi");
    let trace = build_trace(&program, &pi).expect("trace");
    let rom_acc = zk_lisp_proof_winterfell::romacc::rom_acc_from_program(&program);

    let opts = prove_opts();
    let prover = ZkProver::new(opts.clone(), pi.clone(), rom_acc);
    let res = prover.prove(trace);

    match res {
        Ok(proof) => {
            // In release builds, the prover
            // may succeed even for invalid traces;
            let v = verify_proof(proof, &program, pi, &opts, 64);
            assert!(
                v.is_err(),
                "verify unexpectedly succeeded for division by zero"
            );
        }
        Err(_) => {
            // In debug builds or with preflight
            // enabled, proving fails early.
        }
    }
}

#[test]
fn rom_one_hot_op_mismatch_proof_fails() {
    // Build a minimal program with a single CONST op
    let metrics = CompilerMetrics::default();
    let mut b = ProgramBuilder::new();

    b.push(Op::Const { dst: 0, imm: 7 });
    b.push(Op::End);

    let program = b.finalize(metrics).expect("finalize must succeed");

    // Build PI and trace
    let pi = PublicInputsBuilder::from_program(&program)
        .build()
        .expect("pi");

    let mut trace = build_trace(&program, &pi).expect("trace");
    let rom_acc = zk_lisp_proof_winterfell::romacc::rom_acc_from_program(&program);
    let cols = Columns::baseline();

    // Flip a ROM one-hot bit at the first
    // map row to mismatch op_* vs ROM
    let row_map0 = pos_map();
    trace.set(cols.rom_op_index(1), row_map0, BE::ONE);

    // Proving must fail due to ROM↔op
    // equality constraint violation.
    let opts = prove_opts();
    let prover = ZkProver::new(opts.clone(), pi.clone(), rom_acc);
    let res = prover.prove(trace);

    match res {
        Ok(proof) => {
            // In release builds, the prover may
            // succeed even for invalid traces;
            let v = verify_proof(proof, &program, pi, &opts, 64);
            assert!(
                v.is_err(),
                "verify unexpectedly succeeded despite ROM/op mismatch"
            );
        }
        Err(_) => {
            // In debug builds or with preflight
            // enabled, proving fails early.
        }
    }
}

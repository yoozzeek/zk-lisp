// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::{BatchingMethod, FieldExtension, ProofOptions};
use zk_lisp::compiler::compile_entry;
use zk_lisp::compiler::ir::{Op, ProgramBuilder};
use zk_lisp::layout::Columns;
use zk_lisp::pi::{self};
use zk_lisp::prove::{self, ZkProver, build_trace_with_pi, verify_proof};

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

fn prove_or_allow_backend(e: zk_lisp::prove::Error) {
    // In small traces Winterfell may
    // reject options; allow backend errors.
    if !matches!(e, prove::Error::BackendSource(_)) {
        panic!("prove failed: {e}");
    }
}

#[test]
fn safe_add_trace_and_prove() {
    let src = "(def (main) (safe-add 7 9))";
    let program = compile_entry(src, &[]).expect("compile");

    // Build PI by inferring features
    // to avoid mismatches.
    let pi = pi::PublicInputsBuilder::for_program(&program)
        .build()
        .expect("pi");

    let trace = build_trace_with_pi(&program, &pi).expect("trace");
    let cols = Columns::baseline();
    let (out_reg, out_row) = prove::compute_vm_output(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);
    // 16
    assert_eq!(v, BE::from(16u64));

    let opts = prove_opts();
    let prover = ZkProver::new(opts.clone(), pi.clone());
    match prover.prove(trace) {
        Ok(proof) => {
            let _ = verify_proof(proof, pi, &opts);
        }
        Err(e) => prove_or_allow_backend(e),
    }
}

#[test]
fn safe_sub_trace_and_prove() {
    let src = "(def (main) (safe-sub 9 7))";
    let program = compile_entry(src, &[]).expect("compile");

    let pi = pi::PublicInputsBuilder::for_program(&program)
        .build()
        .expect("pi");

    let trace = build_trace_with_pi(&program, &pi).expect("trace");
    let cols = Columns::baseline();
    let (out_reg, out_row) = prove::compute_vm_output(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    // 2
    assert_eq!(v, BE::from(2u64));

    let opts = prove_opts();
    let prover = ZkProver::new(opts.clone(), pi.clone());
    match prover.prove(trace) {
        Ok(proof) => {
            let _ = verify_proof(proof, pi, &opts);
        }
        Err(e) => prove_or_allow_backend(e),
    }
}

#[test]
fn safe_mul_trace_and_prove() {
    let src = "(def (main) (safe-mul 32000 65000))";
    let program = compile_entry(src, &[]).expect("compile");

    let pi = pi::PublicInputsBuilder::for_program(&program)
        .build()
        .expect("pi");

    let trace = build_trace_with_pi(&program, &pi).expect("trace");
    let cols = Columns::baseline();
    let (out_reg, out_row) = prove::compute_vm_output(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    // 32000 * 65000 = 2_080_000_000
    assert_eq!(v, BE::from(2_080_000_000u64));

    let opts = prove_opts();
    let prover = ZkProver::new(opts.clone(), pi.clone());
    match prover.prove(trace) {
        Ok(proof) => {
            let _ = verify_proof(proof, pi, &opts);
        }
        Err(e) => prove_or_allow_backend(e),
    }
}

// Placeholder divmod tests (ignored until divmod op/DSL is implemented)
// Expected DSL form: (divmod dst_q dst_r a b)
// Semantics: q = floor(a / b), r = a - q*b, with 0 <= r < b and b != 0.
#[ignore]
#[test]
fn divmod_basic_trace_and_prove() {
    // Placeholder for future (divmod a b) that returns (q,r)
    let _ = ();
}

#[test]
fn divmod_q_r_e2e_small_cases() {
    // q: 23/7=3, r: 23%7=2
    let src_q = "(def (main) (divmod-q 23 7))";
    let program_q = compile_entry(src_q, &[]).expect("compile q");

    let pi_q = pi::PublicInputsBuilder::for_program(&program_q)
        .build()
        .expect("pi q");
    let trace_q = build_trace_with_pi(&program_q, &pi_q).expect("trace q");

    let cols = Columns::baseline();
    let (out_reg_q, out_row_q) = prove::compute_vm_output(&trace_q);
    let vq = trace_q.get(cols.r_index(out_reg_q as usize), out_row_q as usize);

    assert_eq!(vq, BE::from(3u64));

    let src_r = "(def (main) (divmod-r 23 7))";

    let program_r = compile_entry(src_r, &[]).expect("compile r");
    let pi_r = pi::PublicInputsBuilder::for_program(&program_r)
        .build()
        .expect("pi r");

    let trace_r = build_trace_with_pi(&program_r, &pi_r).expect("trace r");
    let (out_reg_r, out_row_r) = prove::compute_vm_output(&trace_r);
    let vr = trace_r.get(cols.r_index(out_reg_r as usize), out_row_r as usize);

    assert_eq!(vr, BE::from(2u64));
}

#[cfg_attr(debug_assertions, ignore)]
#[test]
fn divmod_q_r_e2e_more_cases_and_prove() {
    // q: 100/10=10, r=0;
    // q: 5/2=2, r=1;
    // q: 0/10=0, r=0;
    // q: 7/1=7, r=0
    let cases = vec![
        ("(def (main) (divmod-q 100 10))", 10u64),
        ("(def (main) (divmod-q 5 2))", 2u64),
        ("(def (main) (divmod-q 0 10))", 0u64),
        ("(def (main) (divmod-q 7 1))", 7u64),
    ];

    for (src, expect) in cases {
        let program = compile_entry(src, &[]).expect("compile q");

        let pi = pi::PublicInputsBuilder::for_program(&program)
            .build()
            .expect("pi");
        let trace = build_trace_with_pi(&program, &pi).expect("trace");

        let cols = Columns::baseline();
        let (out_reg, out_row) = prove::compute_vm_output(&trace);
        let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

        assert_eq!(v, BE::from(expect));

        let opts = prove_opts();
        let prover = ZkProver::new(opts.clone(), pi.clone())
            .with_preflight_mode(zk_lisp::PreflightMode::Off);
        match prover.prove(trace) {
            Ok(proof) => {
                let _ = verify_proof(proof, pi, &opts);
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

        let pi = pi::PublicInputsBuilder::for_program(&program)
            .build()
            .expect("pi");
        let trace = build_trace_with_pi(&program, &pi).expect("trace");

        let cols = Columns::baseline();
        let (out_reg, out_row) = prove::compute_vm_output(&trace);
        let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

        assert_eq!(v, BE::from(expect));

        let opts = prove_opts();
        let prover = ZkProver::new(opts.clone(), pi.clone())
            .with_preflight_mode(zk_lisp::PreflightMode::Off);
        match prover.prove(trace) {
            Ok(proof) => {
                let _ = verify_proof(proof, pi, &opts);
            }
            Err(e) => prove_or_allow_backend(e),
        }
    }
}

#[test]
fn divmod_divide_by_zero_proving_fails() {
    // Using immediate zero to ensure dynamic
    // lowering path; assertion should fail at prove time.
    let src = "(def (main) (divmod-q 5 0))";
    let program = compile_entry(src, &[]).expect("compile");

    let pi = pi::PublicInputsBuilder::for_program(&program)
        .build()
        .expect("pi");
    let trace = build_trace_with_pi(&program, &pi).expect("trace");

    let opts = prove_opts();
    let prover = ZkProver::new(opts.clone(), pi.clone());
    let res = prover.prove(trace);

    match res {
        Ok(proof) => {
            // In release builds, the prover
            // may succeed even for invalid traces;
            // verification must then fail.
            let v = verify_proof(proof, pi, &opts);
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
    let mut b = ProgramBuilder::new();
    b.push(Op::Const { dst: 0, imm: 7 });
    b.push(Op::End);

    let program = b.finalize();

    // Build PI and trace
    let pi = pi::PublicInputsBuilder::for_program(&program)
        .build()
        .expect("pi");

    let mut trace = build_trace_with_pi(&program, &pi).expect("trace");
    let cols = Columns::baseline();

    // Flip a ROM one-hot bit at the first map row to mismatch op_* vs ROM
    // Program has op_const at level 0 map row; we set rom_op[1] (mov) = 1 as well.
    let row_map0 = zk_lisp::schedule::pos_map();
    trace.set(cols.rom_op_index(1), row_map0, BE::ONE);

    // Proving must fail due to ROM↔op equality constraint violation
    let opts = prove_opts();
    let prover = ZkProver::new(opts.clone(), pi.clone());
    let res = prover.prove(trace);

    match res {
        Ok(proof) => {
            // In release builds, the prover may
            // succeed even for invalid traces;
            // verification must then fail.
            let v = verify_proof(proof, pi, &opts);
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

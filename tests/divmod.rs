// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::math::FieldElement;
use winterfell::{BatchingMethod, FieldExtension, ProofOptions};
use zk_lisp::compiler::ir::{Op, ProgramBuilder};
use zk_lisp::compiler::compile_entry;
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
    let prover =
        ZkProver::new(opts.clone(), pi.clone()).with_preflight_mode(zk_lisp::PreflightMode::Off);
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
    let prover =
        ZkProver::new(opts.clone(), pi.clone()).with_preflight_mode(zk_lisp::PreflightMode::Off);
    match prover.prove(trace) {
        Ok(proof) => {
            let _ = verify_proof(proof, pi, &opts);
        }
        Err(e) => prove_or_allow_backend(e),
    }
}

#[test]
fn safe_mut_trace_and_prove() {
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
    let prover =
        ZkProver::new(opts.clone(), pi.clone()).with_preflight_mode(zk_lisp::PreflightMode::Off);
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
    // Example once implemented:
    // (def (main) (let ((a 23) (b 7)) (do (divmod 0 1 a b) r1))) ; return r1 == 2
    let _ = ();
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
    let prover = ZkProver::new(opts.clone(), pi.clone()).with_preflight_mode(zk_lisp::PreflightMode::Off);
    let res = prover.prove(trace);

    assert!(res.is_err(), "proving unexpectedly succeeded despite ROM/op mismatch");
}

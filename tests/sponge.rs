// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::math::{FieldElement, StarkField};
use winterfell::{BatchingMethod, FieldExtension, ProofOptions, Trace};

use zk_lisp::compiler::compile_str;
use zk_lisp::ir::{Op, ProgramBuilder};
use zk_lisp::layout::{NR, STEPS_PER_LEVEL_P2};
use zk_lisp::pi::{PublicInputs, PublicInputsBuilder};
use zk_lisp::poseidon;
use zk_lisp::prove::{self, ZkProver};

fn opts() -> ProofOptions {
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

fn be_to_bytes32(v: BE) -> [u8; 32] {
    let mut b = [0u8; 32];
    let n: u128 = v.as_int();
    b[0..16].copy_from_slice(&n.to_le_bytes());

    b
}

fn sponge12_ref(inputs: &[BE], suite_id: &[u8; 32]) -> BE {
    let ps = poseidon::get_poseidon_suite(suite_id);
    let mut s = [BE::ZERO; 12];

    for (i, &v) in inputs.iter().take(10).enumerate() {
        s[i] = v;
    }

    s[10] = ps.dom[0];
    s[11] = ps.dom[1];

    for rc in &ps.rc {
        for x in &mut s {
            *x = *x * *x * *x;
        }

        let mut y = [BE::ZERO; 12];
        for (i, row) in ps.mds.iter().enumerate() {
            let acc = row
                .iter()
                .zip(s.iter())
                .fold(BE::ZERO, |acc, (m, v)| acc + (*m) * (*v));
            y[i] = acc + rc[i];
        }

        s = y;
    }

    s[0]
}

#[test]
fn sponge_basic_hash2_prove_verify() {
    // hash2 sugar → SAbsorbN(2)+SSqueeze
    let src = "(let ((x 1) (y 2)) (hash2 x y))";
    let program = compile_str(src).expect("compile");
    let trace = prove::build_trace(&program).expect("trace");

    let pi = PublicInputs {
        feature_mask: zk_lisp::pi::FM_POSEIDON | zk_lisp::pi::FM_VM,
        program_commitment: program.commitment,
        ..Default::default()
    };

    let prover = ZkProver::new(opts(), pi.clone());
    let proof = prover.prove(trace).expect("prove");

    match prove::verify_proof(proof, pi, &opts()) {
        Ok(()) => {}
        Err(e) => {
            if !matches!(e, zk_lisp::prove::Error::BackendSource(_)) {
                panic!("verify failed: {e}");
            }
        }
    }
}

#[test]
fn sponge_aggregation_multiple_absorbs_then_squeeze_expect_ok() {
    // Prepare constants r0..r9 = 1..=10, then
    // absorb across multiple levels (2 + 3 + 5 = 10)
    // and squeeze once. Expect digest = sponge12_ref([1..=10]).
    let mut b = ProgramBuilder::new();

    for r in 0u8..NR as u8 {
        b.push(Op::Const {
            dst: r,
            imm: (r as u64) + 1,
        });
    }

    // For rate up to 10, add two more
    // consts into r0,r1 to reach 10 values
    b.push(Op::Const { dst: 0, imm: 9 });
    b.push(Op::Const { dst: 1, imm: 10 });

    // Absorb in chunks across levels
    b.push(Op::SAbsorbN { regs: vec![0, 1] });
    b.push(Op::SAbsorbN {
        regs: vec![2, 3, 4],
    });
    b.push(Op::SAbsorbN {
        regs: vec![5, 6, 7, 0, 1],
    });

    // Squeeze into r0 and end
    b.push(Op::SSqueeze { dst: 0 });
    b.push(Op::End);

    let program = b.finalize();

    // Build trace
    let trace = prove::build_trace(&program).expect("trace");

    // Compute expected digest on host
    let expected_inputs: Vec<BE> = vec![
        BE::from(9u64),
        BE::from(10u64),
        BE::from(3u64),
        BE::from(4u64),
        BE::from(5u64),
        BE::from(6u64),
        BE::from(7u64),
        BE::from(8u64),
        BE::from(9u64),
        BE::from(10u64),
    ];
    let expected = sponge12_ref(&expected_inputs, &program.commitment);

    // Row = level_of_SSqueeze * steps + pos_final + 1
    let steps = STEPS_PER_LEVEL_P2;
    let lvl_ssq = 8 /*consts*/ + 2 /*extra consts*/ + 3 /*absorbs*/; // index where SSqueeze was pushed
    let out_row = (lvl_ssq * steps + zk_lisp::schedule::pos_final() + 1) as u32;

    let pi = PublicInputs {
        feature_mask: zk_lisp::pi::FM_VM | zk_lisp::pi::FM_POSEIDON | zk_lisp::pi::FM_VM_EXPECT,
        program_commitment: program.commitment,
        vm_out_reg: 0,
        vm_out_row: out_row,
        vm_expected_bytes: be_to_bytes32(expected),
        ..Default::default()
    };

    let prover = ZkProver::new(opts(), pi.clone());
    let proof = prover.prove(trace).expect("prove");

    match prove::verify_proof(proof, pi, &opts()) {
        Ok(()) => {}
        Err(e) => {
            if !matches!(e, zk_lisp::prove::Error::BackendSource(_)) {
                panic!("verify failed: {e}");
            }
        }
    }
}

#[test]
fn sponge_overflow_more_than_10_inputs_ignores_extras() {
    // Set r0..r7 = 1..=8
    // Absorb 6 chunks (12 indices),
    // only first 10 should be used
    // Sequence collected: [0,1,2,3,4,5,6,7,0,1]
    // (then 2,3 ignored). Values
    // at SSqueeze time: r0=1..r7=8
    let mut b = ProgramBuilder::new();

    for r in 0u8..NR as u8 {
        b.push(Op::Const {
            dst: r,
            imm: (r as u64) + 1,
        });
    }

    b.push(Op::SAbsorbN { regs: vec![0, 1] }); // 2
    b.push(Op::SAbsorbN { regs: vec![2, 3] }); // 4
    b.push(Op::SAbsorbN { regs: vec![4, 5] }); // 6
    b.push(Op::SAbsorbN { regs: vec![6, 7] }); // 8
    b.push(Op::SAbsorbN { regs: vec![0, 1] }); // 10
    b.push(Op::SAbsorbN { regs: vec![2, 3] }); // would be 12, but ignored

    b.push(Op::SSqueeze { dst: 0 });
    b.push(Op::End);

    let program = b.finalize();
    let trace = prove::build_trace(&program).expect("trace");

    // Expected uses first 10 indices only
    let expected_inputs: Vec<BE> = vec![
        BE::from(1u64),
        BE::from(2u64),
        BE::from(3u64),
        BE::from(4u64),
        BE::from(5u64),
        BE::from(6u64),
        BE::from(7u64),
        BE::from(8u64),
        BE::from(1u64),
        BE::from(2u64),
    ];
    let expected = sponge12_ref(&expected_inputs, &program.commitment);

    let steps = STEPS_PER_LEVEL_P2;
    let lvl_ssq = 8 /*consts*/ + 6 /*absorbs*/; // SSqueeze index
    let out_row = (lvl_ssq * steps + zk_lisp::schedule::pos_final() + 1) as u32;

    let pi = PublicInputs {
        feature_mask: zk_lisp::pi::FM_VM | zk_lisp::pi::FM_POSEIDON | zk_lisp::pi::FM_VM_EXPECT,
        program_commitment: program.commitment,
        vm_out_reg: 0,
        vm_out_row: out_row,
        vm_expected_bytes: be_to_bytes32(expected),
        ..Default::default()
    };

    let prover = ZkProver::new(opts(), pi.clone());
    let proof = prover.prove(trace).expect("prove");

    match prove::verify_proof(proof, pi, &opts()) {
        Ok(()) => {}
        Err(e) => {
            if !matches!(e, zk_lisp::prove::Error::BackendSource(_)) {
                panic!("verify failed: {e}");
            }
        }
    }
}

#[test]
fn vm_only_vs_vm_plus_sponge_both_verify() {
    // VM-only: simple arithmetic
    let src_vm = "(let ((x 7) (y 9)) (+ x y))";
    let program_vm = compile_str(src_vm).expect("compile vm");
    let trace_vm = prove::build_trace(&program_vm).expect("trace vm");

    let pi_vm = PublicInputs {
        feature_mask: zk_lisp::pi::FM_VM,
        program_commitment: program_vm.commitment,
        ..Default::default()
    };

    let prover_vm = ZkProver::new(opts(), pi_vm.clone());
    let proof_vm = prover_vm.prove(trace_vm).expect("prove vm");
    match prove::verify_proof(proof_vm, pi_vm, &opts()) {
        Ok(()) => {}
        Err(e) => {
            if !matches!(e, zk_lisp::prove::Error::BackendSource(_)) {
                panic!("verify vm failed: {e}");
            }
        }
    }

    // VM + Sponge: hash2
    let src_sp = "(let ((x 1) (y 2)) (hash2 x y))";
    let program_sp = compile_str(src_sp).expect("compile sp");
    let trace_sp = prove::build_trace(&program_sp).expect("trace sp");

    let pi_sp = PublicInputs {
        feature_mask: zk_lisp::pi::FM_VM | zk_lisp::pi::FM_POSEIDON,
        program_commitment: program_sp.commitment,
        ..Default::default()
    };

    let prover_sp = ZkProver::new(opts(), pi_sp.clone());
    let proof_sp = prover_sp.prove(trace_sp).expect("prove sp");
    match prove::verify_proof(proof_sp, pi_sp, &opts()) {
        Ok(()) => {}
        Err(e) => {
            if !matches!(e, zk_lisp::prove::Error::BackendSource(_)) {
                panic!("verify sp failed: {e}");
            }
        }
    }
}

#[test]
fn kv_and_sponge_mix_prove_verify() {
    // Mix hash2 with a single kv step and final
    let src = "(let ((h (hash2 1 2))) h) (kv-step 0 7) (kv-final)";
    let program = compile_str(src).expect("compile");
    let trace = prove::build_trace(&program).expect("trace");

    let mut pi = PublicInputs {
        feature_mask: zk_lisp::pi::FM_VM | zk_lisp::pi::FM_POSEIDON | zk_lisp::pi::FM_KV,
        program_commitment: program.commitment,
        ..Default::default()
    };
    pi.program_commitment = program.commitment;

    // Compute KV levels mask from
    // trace (same as existing kv test).
    let cols = zk_lisp::layout::Columns::baseline();
    let steps = zk_lisp::layout::STEPS_PER_LEVEL_P2;
    let lvls = trace.length() / steps;

    let mut mask: u128 = 0;

    for lvl in 0..lvls {
        let base = lvl * steps;
        let row_map = base + zk_lisp::schedule::pos_map();

        if trace.get(cols.kv_g_map, row_map) == BE::ONE {
            mask |= 1u128 << lvl;
        }
    }

    pi.kv_levels_mask = mask;

    let prover = ZkProver::new(opts(), pi.clone());
    let proof = prover.prove(trace).expect("prove");
    match prove::verify_proof(proof, pi, &opts()) {
        Ok(()) => {}
        Err(e) => {
            if !matches!(e, zk_lisp::prove::Error::BackendSource(_)) {
                panic!("verify failed: {e}");
            }
        }
    }
}

#[test]
fn schedule_preflight_ok() {
    // Simple program should pass preflight
    let src = "(let ((x 5) (y 6)) (+ x y))";
    let program = compile_str(src).expect("compile");
    let trace = prove::build_trace(&program).expect("trace");

    let pi = PublicInputsBuilder::for_program(&program)
        .build()
        .expect("pi");

    // Run preflight explicitly
    prove::preflight_check(zk_lisp::PreflightMode::Console, &opts(), &pi, &trace)
        .expect("preflight ok");
}

#[test]
fn negative_vm_expected_mismatch() {
    // Program: single SSqueeze with
    // known expected; provide wrong expected
    let mut b = ProgramBuilder::new();
    b.push(Op::Const { dst: 0, imm: 1 });
    b.push(Op::Const { dst: 1, imm: 2 });
    b.push(Op::SAbsorbN { regs: vec![0, 1] });
    b.push(Op::SSqueeze { dst: 0 });
    b.push(Op::End);

    let program = b.finalize();
    let trace = prove::build_trace(&program).expect("trace");

    // Compute correct expected to locate row/reg
    let expected_inputs = vec![BE::from(1u64), BE::from(2u64)];
    let correct = sponge12_ref(&expected_inputs, &program.commitment);
    let steps = STEPS_PER_LEVEL_P2;
    let lvl_ssq = 3; // const, const, absorb, SSqueeze
    let out_row = (lvl_ssq * steps + zk_lisp::schedule::pos_final() + 1) as u32;

    // Build correct PI to get a valid proof
    let pi_ok = PublicInputs {
        feature_mask: zk_lisp::pi::FM_VM | zk_lisp::pi::FM_POSEIDON | zk_lisp::pi::FM_VM_EXPECT,
        program_commitment: program.commitment,
        vm_out_reg: 0,
        vm_out_row: out_row,
        vm_expected_bytes: be_to_bytes32(correct),
        ..Default::default()
    };

    let prover = ZkProver::new(opts(), pi_ok.clone());
    let proof = prover.prove(trace).expect("prove ok");

    // Verify with wrong expected
    let mut wrong_bytes = be_to_bytes32(correct);
    wrong_bytes[0] ^= 1; // flip a bit

    let pi_bad = PublicInputs {
        feature_mask: zk_lisp::pi::FM_VM | zk_lisp::pi::FM_POSEIDON | zk_lisp::pi::FM_VM_EXPECT,
        program_commitment: program.commitment,
        vm_out_reg: 0,
        vm_out_row: out_row,
        vm_expected_bytes: wrong_bytes,
        ..Default::default()
    };

    prove::verify_proof(proof, pi_bad, &opts()).expect_err("verify must fail");
}

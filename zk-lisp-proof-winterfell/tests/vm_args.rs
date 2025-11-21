// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

use std::panic;
use winterfell::ProofOptions;
use winterfell::math::fields::f128::BaseElement as BE;

use zk_lisp_compiler::compile_entry;
use zk_lisp_proof::error::Error as CoreError;
use zk_lisp_proof::pi::{PublicInputsBuilder, VmArg};
use zk_lisp_proof_winterfell::prove::{self, ZkProver, verify_proof};
use zk_lisp_proof_winterfell::romacc;
use zk_lisp_proof_winterfell::utils::encode_main_args_to_slots;
use zk_lisp_proof_winterfell::vm::layout::{Columns, NR};
use zk_lisp_proof_winterfell::vm::schedule;
use zk_lisp_proof_winterfell::vm::trace::build_trace;

fn opts() -> ProofOptions {
    ProofOptions::new(
        64, // queries
        16, // blowup
        16, // grind
        winterfell::FieldExtension::None,
        2,
        1,
        winterfell::BatchingMethod::Linear,
        winterfell::BatchingMethod::Linear,
    )
}

#[test]
fn secret_arg_positive_verifies() {
    // (def (main) (assert (= (secret-arg 0) 3)))
    let src = r#"
(def (main)
  (assert (= (secret-arg 0) 3)))
"#;

    let program = compile_entry(src, &[]).expect("compile");

    let pi = PublicInputsBuilder::from_program(&program)
        .with_public_args(&[])
        .with_secret_args(&[VmArg::U64(3)])
        .build()
        .expect("pi");

    // Build trace and full proof
    let trace = build_trace(&program, &pi).expect("trace");
    let rom_acc = romacc::rom_acc_from_program(&program);

    let opts = opts();
    let prover = ZkProver::new(opts.clone(), pi.clone(), rom_acc);
    let proof = prover.prove(trace).expect("prove");

    // Verify must succeed with correct secret arg
    verify_proof(proof, &program, pi, &opts, 64).expect("verify");
}

#[test]
fn secret_arg_negative_fails_verify() {
    // Same program but wrong secret -> proof must fail
    let src = r#"
(def (main)
  (assert (= (secret-arg 0) 3)))
"#;

    let program = compile_entry(src, &[]).expect("compile");

    let pi = PublicInputsBuilder::from_program(&program)
        .with_public_args(&[])
        .with_secret_args(&[VmArg::U64(4)])
        .build()
        .expect("pi");

    let trace = build_trace(&program, &pi).expect("trace");
    let rom_acc = romacc::rom_acc_from_program(&program);
    let opts = opts();

    // In debug, prove() may panic due to
    // failed assertions; in release, prove() may
    // succeed but verify() must fail.
    let prove_res = panic::catch_unwind(|| {
        let prover = ZkProver::new(opts.clone(), pi.clone(), rom_acc);
        prover.prove(trace)
    });

    match prove_res {
        Ok(Ok(proof)) => {
            let err = verify_proof(proof, &program, pi, &opts, 64)
                .expect_err("must fail verify with wrong secret");
            match err {
                prove::Error::Backend(_)
                | prove::Error::BackendSource(_)
                | prove::Error::PublicInputs(_)
                | prove::Error::RecursionInvalid(_) => {}
            }
        }
        // Prove returned an error; acceptable failure mode
        Ok(Err(_)) => {}
        // Prove panicked; acceptable (typical in debug)
        Err(_) => {}
    }
}

#[test]
fn secret_arg_non_u64_rejected() {
    let src = r#"
(def (main)
  (assert (= (secret-arg 0) 3)))
"#;

    let program = compile_entry(src, &[]).expect("compile");

    // Provide non-u64 secret arg;
    // VM trace builder should reject
    let pi = PublicInputsBuilder::from_program(&program)
        .with_public_args(&[])
        .with_secret_args(&[VmArg::Bytes32([1u8; 32])])
        .build()
        .expect("pi");

    let err = build_trace(&program, &pi).expect_err("must reject non-u64 secret arg");

    let CoreError::InvalidInput(msg) = err;
    assert!(
        msg.contains("non-u64 secret arg"),
        "unexpected message: {msg}"
    );
}

#[test]
fn main_args_seed_tail_registers_at_level0_map() {
    // Simple program that does not
    // depend on args; we only inspect
    let src = "(def (main) 0)";
    let program = compile_entry(src, &[]).expect("compile");

    let main_args = [VmArg::U64(11), VmArg::U64(22)];
    let pi = PublicInputsBuilder::from_program(&program)
        .with_public_args(&[])
        .with_main_args(&main_args)
        .build()
        .expect("pi");

    let trace = build_trace(&program, &pi).expect("trace");
    let cols = Columns::baseline();
    let row0_map = schedule::pos_map();

    let tail_start = NR - main_args.len();

    assert_eq!(
        trace.get(cols.r_index(tail_start), row0_map),
        BE::from(11u64),
    );
    assert_eq!(
        trace.get(cols.r_index(tail_start + 1), row0_map),
        BE::from(22u64),
    );
}

#[test]
fn main_args_do_not_overwrite_secret_args_prefix() {
    // Use both secret_args and main_args and
    // ensure prefix registers come from secrets
    let src = "(def (main) 0)";
    let program = compile_entry(src, &[]).expect("compile");

    // Two secret args -> r0,r1
    let secret_args = [VmArg::U64(3), VmArg::U64(5)];
    // Two main_args -> r(8-2)=r6,r7
    let main_args = [VmArg::U64(11), VmArg::U64(13)];

    let pi = PublicInputsBuilder::from_program(&program)
        .with_public_args(&[])
        .with_secret_args(&secret_args)
        .with_main_args(&main_args)
        .build()
        .expect("pi");

    let trace = build_trace(&program, &pi).expect("trace");
    let cols = Columns::baseline();
    let row0_map = schedule::pos_map();

    // Secret prefix
    assert_eq!(trace.get(cols.r_index(0), row0_map), BE::from(3u64));
    assert_eq!(trace.get(cols.r_index(1), row0_map), BE::from(5u64));

    // Tail reserved for main_args
    let tail_start = NR - main_args.len();
    assert_eq!(
        trace.get(cols.r_index(tail_start), row0_map),
        BE::from(11u64),
    );
    assert_eq!(
        trace.get(cols.r_index(tail_start + 1), row0_map),
        BE::from(13u64),
    );
}

#[test]
fn main_args_overflow_register_file_rejected() {
    let src = "(def (main) 0)";
    let program = compile_entry(src, &[]).expect("compile");

    // Build more main_args slots than
    // registers by pushing NR+1 scalars.
    let mut many = Vec::new();
    for _ in 0..(NR + 1) {
        many.push(VmArg::U64(1));
    }

    let pi = PublicInputsBuilder::from_program(&program)
        .with_public_args(&[])
        .with_main_args(&many)
        .build()
        .expect("pi");

    let err = build_trace(&program, &pi).expect_err("must reject too many main_args");

    let CoreError::InvalidInput(msg) = err;
    assert!(
        msg.contains("too many main_args"),
        "unexpected message: {msg}"
    );
}

#[test]
fn main_args_u128_seed_tail_slots() {
    let src = "(def (main) 0)";
    let program = compile_entry(src, &[]).expect("compile");

    let main_args = [VmArg::U64(11), VmArg::U128(42u128 << 64 | 7u128)];

    let pi = PublicInputsBuilder::from_program(&program)
        .with_public_args(&[])
        .with_main_args(&main_args)
        .build()
        .expect("pi");

    let trace = build_trace(&program, &pi).expect("trace");
    let cols = Columns::baseline();
    let row0_map = schedule::pos_map();

    let slots = encode_main_args_to_slots(&main_args);
    let tail_start = NR - slots.len();

    for (j, expected) in slots.iter().enumerate() {
        let reg_idx = tail_start + j;
        assert_eq!(
            trace.get(cols.r_index(reg_idx), row0_map),
            *expected,
            "u128 mismatch at r{reg_idx}",
        );
    }
}

#[test]
fn main_args_bytes32_seed_tail_slots() {
    let src = "(def (main) 0)";
    let program = compile_entry(src, &[]).expect("compile");

    let main_args = [VmArg::U64(11), VmArg::Bytes32([3u8; 32])];

    let pi = PublicInputsBuilder::from_program(&program)
        .with_public_args(&[])
        .with_main_args(&main_args)
        .build()
        .expect("pi");

    let trace = build_trace(&program, &pi).expect("trace");
    let cols = Columns::baseline();
    let row0_map = schedule::pos_map();

    let slots = encode_main_args_to_slots(&main_args);
    let tail_start = NR - slots.len();

    for (j, expected) in slots.iter().enumerate() {
        let reg_idx = tail_start + j;
        assert_eq!(
            trace.get(cols.r_index(reg_idx), row0_map),
            *expected,
            "bytes32 mismatch at r{reg_idx}",
        );
    }
}

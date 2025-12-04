// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::{BatchingMethod, FieldExtension, ProofOptions};

use zk_lisp_compiler::compile_entry;
use zk_lisp_proof::frontend::PreflightMode;
use zk_lisp_proof::pi::{self, PublicInputsBuilder};
use zk_lisp_proof_winterfell::prove::ZkProver;
use zk_lisp_proof_winterfell::romacc;
use zk_lisp_proof_winterfell::vm::trace::build_trace;

fn init_tracing() {
    static INIT: std::sync::Once = std::sync::Once::new();
    INIT.call_once(|| {
        let filter = std::env::var("RUST_LOG").unwrap_or_else(|_| "info".to_string());
        let _ = tracing_subscriber::fmt()
            .with_env_filter(filter)
            .with_test_writer()
            .try_init();
    });
}

fn light_opts() -> ProofOptions {
    ProofOptions::new(
        32, // queries (as in ProverOptions::default)
        16, // blowup
        0,  // grind
        FieldExtension::None,
        2,
        1,
        BatchingMethod::Linear,
        BatchingMethod::Linear,
    )
}

/// 1. Poseidon + VM + Sponge degree smoke:
///    - Verifies that with VM + Poseidon + Sponge enabled
///      (hash2), degrees of PoseidonAir / VmCtrlAir / VmAlu
///      are sufficient and Winterfell does not panic inside
///      validate_transition_degrees().
#[test]
fn deg_poseidon_sponge_smoke() {
    init_tracing();

    // Small program: (hash2 x y).
    // We keep the (def (main) ...) shape to match other tests.
    let src = r#"
(def (main)
  (let ((x 1)
        (y 2))
    (hash2 x y)))"#;

    let program = compile_entry(src, &[]).expect("compile hash2");

    // Let builder infer correct features (VM + Poseidon + Sponge)
    let pi = PublicInputsBuilder::from_program(&program)
        .build()
        .expect("pi");

    // Assert that SPONGE is indeed enabled
    assert_ne!(pi.feature_mask & pi::FM_VM, 0);
    assert_ne!(pi.feature_mask & pi::FM_POSEIDON, 0);
    assert_ne!(pi.feature_mask & pi::FM_SPONGE, 0);

    // Single unified trace (no segmentation)
    let trace = build_trace(&program, &pi).expect("trace");

    // ROM accumulator:
    // only build it when program_commitment != 0
    let rom_acc = if pi.program_commitment.iter().any(|b| *b != 0) {
        romacc::rom_acc_from_program(&program)
    } else {
        [BE::ZERO; 3]
    };

    let opts = light_opts();

    // Disable preflight:
    // we care about the real Winterfell prove()
    // path and validate_transition_degrees
    // in DefaultConstraintEvaluator.
    let prover =
        ZkProver::new(opts.clone(), pi.clone(), rom_acc).with_preflight_mode(PreflightMode::Off);

    // If degrees are incorrect for Poseidon / CTRL / Sponge,
    // debug builds will panic here with
    // "transition constraint degrees didn't match".
    let _proof = prover
        .prove(trace)
        .expect("prove (deg_poseidon_sponge_smoke)");
}

/// 2. ALU high-degree gadgets (DivMod, Eq/assert) degree smoke:
///    - Uses front-end helpers divmod-q/divmod-r plus a simple assert
///      to run high-degree ALU gadgets through Winterfell.
#[test]
fn deg_alu_divmod_smoke() {
    init_tracing();

    // Example 1: divmod-q 23 7 -> 3
    let src_q = "(def (main) (divmod-q 23 7))";
    let program_q = compile_entry(src_q, &[]).expect("compile divmod-q");

    let pi_q = PublicInputsBuilder::from_program(&program_q)
        .build()
        .expect("pi_q");

    let trace_q = build_trace(&program_q, &pi_q).expect("trace_q");
    let rom_acc_q = if pi_q.program_commitment.iter().any(|b| *b != 0) {
        romacc::rom_acc_from_program(&program_q)
    } else {
        [BE::ZERO; 3]
    };

    let opts = light_opts();
    let prover_q = ZkProver::new(opts.clone(), pi_q.clone(), rom_acc_q)
        .with_preflight_mode(PreflightMode::Off);

    let _proof_q = prover_q
        .prove(trace_q)
        .expect("prove (deg_alu_divmod_smoke: divmod-q)");

    // Example 2: simple assert/eq, similar to
    // tests/if_and_assert.rs::assert_positive.
    let src_assert = r#"
(def (eq1 x y) (= x y))
(def (main)
  (let ((a 7) (b 7))
    (assert (eq1 a b))))"#;

    let program_a = compile_entry(src_assert, &[]).expect("compile assert+eq");

    let pi_a = PublicInputsBuilder::from_program(&program_a)
        .build()
        .expect("pi_a");

    let trace_a = build_trace(&program_a, &pi_a).expect("trace_a");
    let rom_acc_a = if pi_a.program_commitment.iter().any(|b| *b != 0) {
        romacc::rom_acc_from_program(&program_a)
    } else {
        [BE::ZERO; 3]
    };

    let prover_a = ZkProver::new(opts.clone(), pi_a.clone(), rom_acc_a)
        .with_preflight_mode(PreflightMode::Off);

    let _proof_a = prover_a
        .prove(trace_a)
        .expect("prove (deg_alu_divmod_smoke: assert/eq)");
}

/// 3. RAM store/load degree smoke:
///    - Simple program with a single store+load,
///      to run RamAir through a real Winterfell prove().
///    - Based on tests/ram.rs::store_same_addr_updates_value
///      and similar cases.
#[test]
fn deg_ram_store_load_smoke() {
    init_tracing();

    // Minimal program:
    //   (store 7 11)
    //   (load 7)
    let src = r#"
(def (main)
  (begin (store 7 11)
         (load 7)))"#;

    let program = compile_entry(src, &[]).expect("compile ram store/load");

    let pi = PublicInputsBuilder::from_program(&program)
        .build()
        .expect("pi");

    let trace = build_trace(&program, &pi).expect("trace");
    let rom_acc = if pi.program_commitment.iter().any(|b| *b != 0) {
        romacc::rom_acc_from_program(&program)
    } else {
        [BE::ZERO; 3]
    };

    let opts = light_opts();
    let prover =
        ZkProver::new(opts.clone(), pi.clone(), rom_acc).with_preflight_mode(PreflightMode::Off);

    // This call activates RamAir (unsorted/sorted GP, last_write, etc.).
    // If degrees are wrong (especially for gp_uns/gp_sorted/delta_clk)
    // Winterfell in debug will fail inside validate_transition_degrees().
    let _proof = prover
        .prove(trace)
        .expect("prove (deg_ram_store_load_smoke)");
}

/// 4. RAM multi-store / same-addr degree smoke:
///    - stresses RamAir constraints for:
///      * repeated writes to the same address (same-addr branches),
///      * interleaved writes to different addresses,
///      * loads after multiple writes.
#[test]
fn deg_ram_multi_store_smoke() {
    init_tracing();

    let src = r#"
(def (main)
  (begin
    ;; two writes to the same address
    ;; to hit same-addr / last-write paths.
    (store 7 11)
    (store 7 13)

    ;; interleave with a different address
    (store 8 5)

    ;; loads after multiple writes
    (load 7)
    (load 8)))"#;

    let program = compile_entry(src, &[]).expect("compile ram multi-store");

    let pi = PublicInputsBuilder::from_program(&program)
        .build()
        .expect("pi");

    let trace = build_trace(&program, &pi).expect("trace");
    let rom_acc = if pi.program_commitment.iter().any(|b| *b != 0) {
        romacc::rom_acc_from_program(&program)
    } else {
        [BE::ZERO; 3]
    };

    let opts = light_opts();
    let prover =
        ZkProver::new(opts.clone(), pi.clone(), rom_acc).with_preflight_mode(PreflightMode::Off);

    // This should exercise RamAir branches that
    // are not touched by a single store+load.
    let _proof = prover
        .prove(trace)
        .expect("prove (deg_ram_multi_store_smoke)");
}

#[test]
fn deg_alu_gadgets_smoke() {
    init_tracing();

    let src = r#"
(def (main)
  (begin
    ;; assert-bit on a constant 1
    (assert-bit 1)

    ;; 8-bit value inside a 32-bit range
    (assert-range 255 32)

    ;; mulwide-hi: 2^63 * 2 = 2^64 -> hi = 1
    (mulwide-hi 9223372036854775808 2)

    ;; mulwide-lo: 3 * 5 = 15 -> lo = 15
    (mulwide-lo 3 5)))"#;

    let program = compile_entry(src, &[]).expect("compile alu gadgets");

    let pi = PublicInputsBuilder::from_program(&program)
        .build()
        .expect("pi");

    let trace = build_trace(&program, &pi).expect("trace");
    let rom_acc = if pi.program_commitment.iter().any(|b| *b != 0) {
        romacc::rom_acc_from_program(&program)
    } else {
        [BE::ZERO; 3]
    };

    let opts = light_opts();
    let prover =
        ZkProver::new(opts.clone(), pi.clone(), rom_acc).with_preflight_mode(PreflightMode::Off);

    // If VmAluAir degrees for write / high-degree gadgets
    // are incorrect, debug builds will panic here with
    // "transition constraint degrees didn't match".
    let _proof = prover.prove(trace).expect("prove (deg_alu_gadgets_smoke)");
}

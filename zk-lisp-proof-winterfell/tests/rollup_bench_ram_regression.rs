// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

use std::{fs, path::Path};
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::math::{FieldElement, StarkField};
use winterfell::{Trace, TraceTable};
use zk_lisp_compiler as compiler;
use zk_lisp_compiler::{ArgRole, ScalarType};
use zk_lisp_proof::ProverOptions;
use zk_lisp_proof::frontend::{self, PreflightMode};
use zk_lisp_proof::pi::{PublicInputs, PublicInputsBuilder, VmArg};
use zk_lisp_proof_winterfell::WinterfellBackend;
use zk_lisp_proof_winterfell::vm::layout::{Columns, NR, STEPS_PER_LEVEL_P2};
use zk_lisp_proof_winterfell::vm::schedule;
use zk_lisp_proof_winterfell::vm::trace::build_trace;

/// Read `examples/rollup-bench.zlisp` from the workspace root.
fn rollup_bench_src() -> String {
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    let path = Path::new(manifest_dir).join("../examples/rollup-bench.zlisp");
    fs::read_to_string(&path).unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()))
}

/// Build the compiled program and PublicInputs for `rollup-bench`
/// in the same way the CLI does for:
///   zk-lisp prove examples/rollup-bench.zlisp --arg u64:10 --arg bytes32:0x01
fn build_rollup_bench_program_and_pi() -> (compiler::Program, PublicInputs) {
    let src = rollup_bench_src();

    // CLI-style public args:
    //   expected_fee_sum = 10 (u64)
    //   expected_root    = 0x01 (bytes32, little-endian in first byte)
    let expected_fee_sum = VmArg::U64(10);
    let mut root_bytes = [0u8; 32];
    root_bytes[0] = 1;
    let expected_root = VmArg::Bytes32(root_bytes);

    let public_args = vec![expected_fee_sum, expected_root];

    // Compile-time u64 view of public args, exactly like CLI `parse_public_args`:
    // - U64(v)     -> v
    // - Bytes32(b) -> LE u64 from b[0..8], requiring b[8..] == 0
    let mut public_u64 = Vec::with_capacity(public_args.len());
    for arg in &public_args {
        match arg {
            VmArg::U64(v) => public_u64.push(*v),
            VmArg::U128(v128) => {
                // Not used by rollup-bench, but keep semantics consistent with CLI.
                if *v128 > u64::MAX as u128 {
                    panic!("u128 public arg does not fit into 64 bits");
                }
                public_u64.push(*v128 as u64);
            }
            VmArg::Bytes32(bytes) => {
                // Same restriction as CLI: high bytes must be zero for now.
                assert!(
                    bytes[8..].iter().all(|b| *b == 0),
                    "bytes32 public arg must have bytes[8..32]=0"
                );
                let mut lo = [0u8; 8];
                lo.copy_from_slice(&bytes[0..8]);
                let v64 = u64::from_le_bytes(lo);
                public_u64.push(v64);
            }
        }
    }

    // Compile entry program with those u64 arguments.
    let program = compiler::compile_entry(&src, &public_u64)
        .expect("compile_entry(rollup-bench) must succeed");

    // Derive `main_args` from the typed schema in the same way
    // as CLI `build_pi_for_program`, but without secrets.
    let schema = program
        .type_schemas
        .fns
        .get("main")
        .expect("typed-fn main schema for rollup-bench.zlisp");

    assert_eq!(
        schema.args.len(),
        public_args.len(),
        "main typed schema arity mismatch: schema {} vs CLI {}",
        schema.args.len(),
        public_args.len()
    );

    let mut main_args: Vec<VmArg> = Vec::new();
    for (idx, ((role, ty), vmarg)) in schema.args.iter().zip(public_args.iter()).enumerate() {
        let pos = idx + 1;
        match role {
            ArgRole::Let => match (ty, vmarg) {
                (ScalarType::U64, VmArg::U64(_))
                | (ScalarType::U128, VmArg::U128(_))
                | (ScalarType::Bytes32, VmArg::Bytes32(_)) => {
                    main_args.push(vmarg.clone());
                }
                (ScalarType::U64, _) => {
                    panic!("main arg #{pos}: expected u64 VmArg for type 'u64'");
                }
                (ScalarType::U128, _) => {
                    panic!("main arg #{pos}: expected u128 VmArg for type 'u128'");
                }
                (ScalarType::Bytes32, _) => {
                    panic!("main arg #{pos}: expected bytes32 VmArg for type 'bytes32'");
                }
            },
            ArgRole::Const => {
                // rollup-bench's main uses only (let ...) args.
                panic!("unexpected ArgRole::Const at main arg #{pos}");
            }
        }
    }

    let pi = PublicInputsBuilder::from_program(&program)
        .with_public_args(&public_args)
        .with_main_args(&main_args)
        .build()
        .expect("PublicInputs build for rollup-bench");

    (program, pi)
}

/// Prover options matching typical CLI defaults for prove/verify:
/// queries=64, blowup=16, grind=16, security_bits=64 in debug.
/// We cap concurrency at 8 segments to mirror CLI usage.
fn prover_opts_rollup_bench() -> ProverOptions {
    ProverOptions {
        queries: 64,
        blowup: 16,
        grind: 16,
        min_security_bits: 64,
        max_segment_rows: None,
        max_concurrent_segments: Some(8),
    }
}

/// Scan the full unified trace for violations of the RAM
/// constraint:
///
///   s_on * (1 - s_w) * (s_val - last) == 0
///
/// where:
///   s_on   = ram_sorted
///   s_w    = ram_s_is_write
///   s_val  = ram_s_val
///   last   = ram_s_last_write
///
/// Returns all row indices where this evaluates non-zero.
fn scan_ram_read_vs_last(trace: &TraceTable<BE>, cols: &Columns) -> Vec<usize> {
    let mut bad = Vec::new();

    for row in 0..trace.length() {
        let s_on = trace.get(cols.ram_sorted, row);
        if s_on != BE::ONE {
            continue;
        }

        let s_w = trace.get(cols.ram_s_is_write, row);
        if s_w == BE::ONE {
            // Writes are allowed to differ from last_write.
            continue;
        }

        let s_val = trace.get(cols.ram_s_val, row);
        let last = trace.get(cols.ram_s_last_write, row);
        let diff = s_val - last;

        if diff != BE::ZERO {
            bad.push(row);
        }
    }

    bad
}

/// Dump detailed context around a RAM violation row:
/// - current/prev/next sorted rows
/// - full sorted chain for the offending address.
fn dump_ram_context(trace: &TraceTable<BE>, cols: &Columns, row: usize) {
    let len = trace.length();
    let pos = row % STEPS_PER_LEVEL_P2;
    let lvl = row / STEPS_PER_LEVEL_P2;

    let sorted = trace.get(cols.ram_sorted, row).as_int();
    let addr = trace.get(cols.ram_s_addr, row).as_int();
    let clk = trace.get(cols.ram_s_clk, row).as_int();
    let val = trace.get(cols.ram_s_val, row).as_int();
    let w = trace.get(cols.ram_s_is_write, row).as_int();
    let last = trace.get(cols.ram_s_last_write, row).as_int();
    let gp_uns = trace.get(cols.ram_gp_unsorted, row).as_int();
    let gp_s = trace.get(cols.ram_gp_sorted, row).as_int();

    println!("==== RAM read!=last diagnostic at row {row} (level={lvl}, pos={pos}) ====");
    println!(
        "cur:  S={} addr={} clk={} val={} w={} last={} gpU={} gpS={}",
        sorted, addr, clk, val, w, last, gp_uns, gp_s
    );

    if row > 0 {
        let prev = row - 1;
        println!(
            "prev: S={} addr={} clk={} val={} w={} last={} gpU={} gpS={}",
            trace.get(cols.ram_sorted, prev).as_int(),
            trace.get(cols.ram_s_addr, prev).as_int(),
            trace.get(cols.ram_s_clk, prev).as_int(),
            trace.get(cols.ram_s_val, prev).as_int(),
            trace.get(cols.ram_s_is_write, prev).as_int(),
            trace.get(cols.ram_s_last_write, prev).as_int(),
            trace.get(cols.ram_gp_unsorted, prev).as_int(),
            trace.get(cols.ram_gp_sorted, prev).as_int(),
        );
    }

    if row + 1 < len {
        let next = row + 1;
        println!(
            "next: S={} addr={} clk={} val={} w={} last={} gpU={} gpS={}",
            trace.get(cols.ram_sorted, next).as_int(),
            trace.get(cols.ram_s_addr, next).as_int(),
            trace.get(cols.ram_s_clk, next).as_int(),
            trace.get(cols.ram_s_val, next).as_int(),
            trace.get(cols.ram_s_is_write, next).as_int(),
            trace.get(cols.ram_s_last_write, next).as_int(),
            trace.get(cols.ram_gp_unsorted, next).as_int(),
            trace.get(cols.ram_gp_sorted, next).as_int(),
        );
    }

    // Full sorted chain for the offending address.
    println!("-- full sorted chain for addr={} --", addr);

    for r in 0..len {
        if trace.get(cols.ram_sorted, r) == BE::ONE
            && trace.get(cols.ram_s_addr, r) == trace.get(cols.ram_s_addr, row)
        {
            println!(
                "row {:4}: clk={:<4} val={:<4} w={} last={:<4}",
                r,
                trace.get(cols.ram_s_clk, r).as_int(),
                trace.get(cols.ram_s_val, r).as_int(),
                trace.get(cols.ram_s_is_write, r).as_int(),
                trace.get(cols.ram_s_last_write, r).as_int(),
            );
        }
    }
}

fn scan_assert_range_eq(trace: &TraceTable<BE>, cols: &Columns) -> Vec<usize> {
    let steps = STEPS_PER_LEVEL_P2;
    let mut bad = Vec::new();

    for row in 0..trace.length() {
        let pos = row % steps;
        if pos != schedule::pos_final() {
            continue;
        }

        let b_ar = trace.get(cols.op_assert_range, row);
        if b_ar == BE::ZERO {
            continue;
        }

        // Reconstruct c_val from selectors
        let mut c_val = BE::ZERO;
        for i in 0..NR {
            let sel_c = trace.get(cols.sel_c_index(i), row);
            let r_i = trace.get(cols.r_index(i), row);
            c_val += sel_c * r_i;
        }

        // Reconstruct dst0_cur from selectors
        let mut dst0_cur = BE::ZERO;
        for i in 0..NR {
            let sd0 = trace.get(cols.sel_dst0_index(i), row);
            let r_i = trace.get(cols.r_index(i), row);
            dst0_cur += sd0 * r_i;
        }

        // Sum bits from gadget_b
        let mut sum = BE::ZERO;
        let mut pow2 = BE::ONE;
        for i in 0..32 {
            let bi = trace.get(cols.gadget_b_index(i), row);
            sum += pow2 * bi;
            pow2 = pow2 + pow2;
        }

        let imm = trace.get(cols.imm, row);
        let mode64 = trace.get(cols.eq_inv, row); // reused as mode flag on range rows

        // Compute eq32 / eq64 and final eq_term exactly as in VmAluAir
        let mut p2_32 = BE::ONE;
        for _ in 0..32 {
            p2_32 = p2_32 + p2_32;
        }

        let eq32 = c_val - sum;
        let eq64 = c_val - (dst0_cur + sum * p2_32);
        let eq_term = imm * (mode64 * eq64 + (BE::ONE - mode64) * eq32);

        if eq_term != BE::ZERO {
            bad.push(row);
        }
    }

    bad
}

fn dump_assert_range_context(trace: &TraceTable<BE>, cols: &Columns, row: usize) {
    let steps = STEPS_PER_LEVEL_P2;
    let lvl = row / steps;
    let pos = row % steps;

    let b_ar = trace.get(cols.op_assert_range, row);
    let imm = trace.get(cols.imm, row);
    let mode64 = trace.get(cols.eq_inv, row);

    // c_val and dst0_cur
    let mut c_val = BE::ZERO;
    let mut dst0_cur = BE::ZERO;

    for i in 0..NR {
        let r_i = trace.get(cols.r_index(i), row);
        let sel_c = trace.get(cols.sel_c_index(i), row);
        let sel_d0 = trace.get(cols.sel_dst0_index(i), row);

        c_val += sel_c * r_i;
        dst0_cur += sel_d0 * r_i;
    }

    // Sum bits
    let mut sum = BE::ZERO;
    let mut pow2 = BE::ONE;

    for i in 0..32 {
        let bi = trace.get(cols.gadget_b_index(i), row);
        sum += pow2 * bi;
        pow2 = pow2 + pow2;
    }

    let mut p2_32 = BE::ONE;
    for _ in 0..32 {
        p2_32 = p2_32 + p2_32;
    }

    let eq32 = c_val - sum;
    let eq64 = c_val - (dst0_cur + sum * p2_32);
    let eq_term = imm * (mode64 * eq64 + (BE::ONE - mode64) * eq32);

    let c_int = c_val.as_int();
    let dst0_int = dst0_cur.as_int();
    let sum_int = sum.as_int();

    println!("==== AssertRange eq_term != 0 at row {row} (lvl={lvl}, pos={pos}) ====");
    println!(
        "flags: op_assert_range={} imm={} mode64={}",
        b_ar.as_int(),
        imm.as_int(),
        mode64.as_int(),
    );
    println!(
        "c_val={} dst0_cur={} sum_bits={} (lo={:#x}, hi={:#x})",
        c_int,
        dst0_int,
        sum_int,
        sum_int,
        sum_int << 32
    );
    println!(
        "eq32={} eq64={} eq_term={}",
        eq32.as_int(),
        eq64.as_int(),
        eq_term.as_int()
    );

    // Also show raw register file on this row for debugging
    for i in 0..NR {
        let ri = trace.get(cols.r_index(i), row).as_int();
        println!("  r[{i}] = {ri}");
    }
}

/// End‑to‑end diagnostic for rollup-bench RAM behavior:
/// 1. Build program + PI as CLI does (u64:10, bytes32:0x01).
/// 2. Build full unified trace and scan for read!=last_write violations.
/// 3. Dump detailed RAM context around the first violation.
/// 4. Run backend preflight with segment-aware AIR, expecting it to fail.
#[test]
fn ram_rollup_bench_preflight_and_ram_invariant_violation() {
    let (program, pi) = build_rollup_bench_program_and_pi();
    let opts = prover_opts_rollup_bench();

    // Build full trace once for diagnostics.
    let trace = build_trace(&program, &pi).expect("build_trace(rollup-bench)");

    let cols = Columns::baseline();
    assert_eq!(
        trace.width(),
        cols.width(0),
        "baseline Columns width must match trace width"
    );

    // Directly scan for violations of RamAir's
    //   s_on * (1 - s_w) * (s_val - last) == 0
    // invariant over the sorted RAM table.
    let bad_rows = scan_ram_read_vs_last(&trace, &cols);
    if !bad_rows.is_empty() {
        // Print a few offending rows for debugging
        for &row in bad_rows.iter().take(8) {
            dump_ram_context(&trace, &cols, row);
        }
    }

    assert!(
        bad_rows.is_empty(),
        "RAM read!=last_write invariant violated at rows: {:?}",
        bad_rows,
    );

    let bad_rows = scan_assert_range_eq(&trace, &cols);
    if !bad_rows.is_empty() {
        for &row in bad_rows.iter().take(8) {
            dump_assert_range_context(&trace, &cols, row);
        }

        panic!("assert-range eq_term violations at rows: {:?}", bad_rows);
    }

    // Run the full preflight pipeline that the CLI uses
    // (segment planner + segment-local AIR + preflight::run).
    frontend::preflight::<WinterfellBackend>(PreflightMode::Console, &opts, &program, &pi)
        .expect("preflight must succeed for rollup-bench after RAM fix");
}

// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use std::env;
use winterfell::ProofOptions;
use zk_lisp::compiler::compile_entry;
use zk_lisp::logging;
use zk_lisp::pi::PublicInputsBuilder;
use zk_lisp::prove::{ZkProver, verify_proof};

fn opts() -> ProofOptions {
    ProofOptions::new(
        1,
        8,
        0,
        winterfell::FieldExtension::None,
        2,
        1,
        winterfell::BatchingMethod::Linear,
        winterfell::BatchingMethod::Linear,
    )
}

fn parse_arg() -> Result<u64, String> {
    let mut it = env::args().skip(1);
    let s = it.next().ok_or_else(|| "missing <t:u64>".to_string())?;
    s.parse::<u64>()
        .map_err(|_| format!("invalid <t>: '{s}', expected u64"))
}

fn u128_to_bytes32(n: u128) -> [u8; 32] {
    let mut b = [0u8; 32];
    b[0..16].copy_from_slice(&n.to_le_bytes());

    b
}

fn main() {
    logging::init_with_level(None);
    tracing::info!(target = "examples.enum_fruit", "start");

    let t = match parse_arg() {
        Ok(v) => v,
        Err(msg) => {
            tracing::error!(
                target = "examples.enum_fruit",
                "usage: cargo run --example enum_fruit -- <t:u64>\\nerror: {msg}",
            );
            return;
        }
    };

    // Program: enum fruit, return:
    // predicate result (1 if in set, else 0).
    let src = r#"
        (deftype fruit () '(member apple orange banana))
        (def (main t)
          (fruit:is t))
    "#;
    let program = compile_entry(src, &[t]).expect("compile");

    // Expected = 1 (membership holds)
    // for t not in set verify must FAIL.
    let expected = u128_to_bytes32(1);

    let pi = PublicInputsBuilder::for_program(&program)
        .vm_args(&[t])
        .vm_expect_from_meta(&program, &expected)
        .build()
        .expect("pi");

    let trace = zk_lisp::prove::build_trace_with_pi(&program, &pi).expect("trace");

    tracing::info!(target = "examples.enum_fruit", "proving...");

    let opts = opts();
    let prover = ZkProver::new(opts.clone(), pi.clone());

    match prover.prove(trace) {
        Err(e) => tracing::error!(target = "examples.enum_fruit", "prove failed: {e}"),
        Ok(proof) => {
            tracing::info!(target = "examples.enum_fruit", "verifying...");
            match verify_proof(proof, pi, &opts) {
                Ok(()) => tracing::info!(target = "examples.enum_fruit", "OK"),
                Err(e) => tracing::error!(target = "examples.enum_fruit", "VERIFY FAILED: {e}"),
            }
        }
    }
}

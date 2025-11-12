// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use std::env;
use std::error::Error;
use winterfell::ProofOptions;
use winterfell::math::StarkField;
use winterfell::math::fields::f128::BaseElement as BE;
use zk_lisp::compiler::compile_entry;
use zk_lisp::poseidon::poseidon_hash_two_lanes;
use zk_lisp::prove::{self, ZkProver, verify_proof};

fn opts() -> ProofOptions {
    ProofOptions::new(
        64,
        8,
        0,
        winterfell::FieldExtension::None,
        2,
        1,
        winterfell::BatchingMethod::Linear,
        winterfell::BatchingMethod::Linear,
    )
}

fn parse_args() -> Result<(u64, u64, Option<String>), String> {
    let mut it = env::args().skip(1);
    let s = it.next().ok_or_else(|| "missing <secret>".to_string())?;
    let secret = s
        .parse::<u64>()
        .map_err(|_| format!("invalid <secret>: '{s}', expected u64"))?;
    let t = it.next().ok_or_else(|| "missing <salt>".to_string())?;
    let salt = t
        .parse::<u64>()
        .map_err(|_| format!("invalid <salt>: '{t}', expected u64"))?;

    // optional: 0xHEX expected digest (to demo failure)
    let expect_hex = it.next();

    Ok((secret, salt, expect_hex))
}

fn hex128_to_bytes32(hex: &str) -> Result<[u8; 32], String> {
    let s = hex.strip_prefix("0x").unwrap_or(hex);
    let n = u128::from_str_radix(s, 16).map_err(|e| format!("invalid hex: {e}"))?;

    let mut out = [0u8; 32];
    out[0..16].copy_from_slice(&n.to_le_bytes());

    Ok(out)
}

fn main() {
    println!("start");

    let (secret, salt, expect_hex) = match parse_args() {
        Ok(v) => v,
        Err(msg) => {
            println!(
                "usage: cargo run --example hash_lock -- <secret:u64> <salt:u64> [<expected_hex>]\nerror: {msg}"
            );
            return;
        }
    };

    println!("args: secret={secret}, salt={salt}");

    // Program: compute commit = Poseidon(secret, salt)
    let src = r"
        (def (main secret salt)
          (hash2 secret salt))
    ";

    // Build program with entry args
    let program = compile_entry(src, &[secret, salt]).expect("compile");

    let commit_hex = format!(
        "0x{}",
        program
            .commitment
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect::<String>()
    );
    println!("suite_id (commitment) = {commit_hex}");

    // Compute expected digest on host
    let expected = poseidon_hash_two_lanes(&program.commitment, BE::from(secret), BE::from(salt));

    // If user passed explicit expected,
    // use it (to demo verify failure on mismatch)
    let expected_bytes = if let Some(hex) = expect_hex {
        match hex128_to_bytes32(&hex) {
            Ok(b) => b,
            Err(e) => {
                println!("invalid expected_hex: {e}");
                return;
            }
        }
    } else {
        let mut b = [0u8; 32];
        let n: u128 = expected.as_int();
        b[0..16].copy_from_slice(&n.to_le_bytes());

        b
    };

    // Build PI via builder, but disable SPONGE explicitly
    // (we don't need sponge selector constraints for examples)
    let pi = zk_lisp::pi::PublicInputsBuilder::for_program(&program)
        .vm_args(&[secret, salt])
        .sponge(false)
        .vm_expect_from_meta(&program, &expected_bytes)
        .build()
        .expect("pi");

    let trace = prove::build_trace_with_pi(&program, &pi).expect("trace");

    println!("proving...");

    let opts = opts();
    let prover = ZkProver::new(opts.clone(), pi.clone());

    match prover.prove(trace) {
        Err(e) => {
            println!("prove failed: {e}");

            let mut s = e.source();
            while let Some(c) = s {
                println!("caused by: {c}");
                s = c.source();
            }
        }
        Ok(proof) => {
            println!("verifying...");
            match verify_proof(proof, pi, &opts) {
                Ok(()) => println!("OK"),
                Err(e) => {
                    println!("VERIFY FAILED: {e}");

                    let mut s = e.source();
                    while let Some(c) = s {
                        println!("caused by: {c}");
                        s = c.source();
                    }
                }
            }
        }
    }
}

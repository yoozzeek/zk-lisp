// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use std::env;
use std::error::Error;
use winterfell::{BatchingMethod, FieldExtension, ProofOptions};
use zk_lisp::pi;
use zk_lisp::prove::{self, ZkProver, verify_proof};

fn opts() -> ProofOptions {
    ProofOptions::new(
        64, // queries
        8,  // blowup
        0,  // grind
        FieldExtension::None,
        2, // FRI folding factor
        1, // FRI num queries per segment
        BatchingMethod::Linear,
        BatchingMethod::Linear,
    )
}

fn usage() {
    println!(
        "usage: cargo run --example merkle_airdrop_claim -- <addr:u64> <amount:u64> <path_pairs> <root_hex>\npath_pairs: d0:s0,d1:s1,... (e.g. 0:2,1:3); root_hex: 0x... (128-bit LE16)"
    );
}

fn parse_pairs(s: &str) -> Result<Vec<(u64, u64)>, String> {
    if s.trim().is_empty() {
        return Err("empty path".into());
    }

    let mut out = Vec::new();
    for (i, part) in s.split(',').enumerate() {
        let mut it = part.split(':');
        let d = it
            .next()
            .ok_or_else(|| format!("pair {i}: missing dir"))?
            .parse::<u64>()
            .map_err(|_| format!("pair {i}: invalid dir"))?;

        if d > 1 {
            return Err(format!("pair {i}: dir must be 0 or 1"));
        }

        let s = it
            .next()
            .ok_or_else(|| format!("pair {i}: missing sib"))?
            .parse::<u64>()
            .map_err(|_| format!("pair {i}: invalid sib"))?;

        out.push((d, s));
    }

    Ok(out)
}

fn parse_root_hex_to_bytes32(hex: &str) -> Result<[u8; 32], String> {
    let s = hex.strip_prefix("0x").unwrap_or(hex);
    let n = u128::from_str_radix(s, 16).map_err(|e| format!("invalid expected_root hex: {e}"))?;

    let mut out = [0u8; 32];
    out[0..16].copy_from_slice(&n.to_le_bytes());

    Ok(out)
}

fn build_program(
    addr: u64,
    amount: u64,
    path: &[(u64, u64)],
) -> Result<zk_lisp::compiler::ir::Program, zk_lisp::compiler::Error> {
    // Build parameter list:
    // (addr amount d0 s0 d1 s1 ...)
    let mut params = vec!["addr".to_string(), "amount".to_string()];
    for (i, _) in path.iter().enumerate() {
        params.push(format!("d{i}"));
        params.push(format!("s{i}"));
    }

    // Build path list literal:
    // ((d0 s0) (d1 s1) ...)
    let mut path_pairs = String::new();
    for (i, _) in path.iter().enumerate() {
        if !path_pairs.is_empty() {
            path_pairs.push(' ');
        }

        path_pairs.push_str(&format!("(d{i} s{i})"));
    }

    let src = format!(
        r#"
(def (main {})
  (let ((receipt (hash2 addr amount)))
    (load-ca receipt ({}))
    receipt))
"#,
        params.join(" "),
        path_pairs
    );

    // Build arguments vector in the same order
    let mut args: Vec<u64> = vec![addr, amount];
    for &(d, s) in path {
        args.push(d);
        args.push(s);
    }

    zk_lisp::compiler::compile_entry(&src, &args)
}

fn main() {
    println!("start");

    let mut it = env::args().skip(1);

    let addr = match it.next().and_then(|s| s.parse::<u64>().ok()) {
        Some(v) => v,
        None => {
            usage();
            return;
        }
    };
    let amount = match it.next().and_then(|s| s.parse::<u64>().ok()) {
        Some(v) => v,
        None => {
            usage();
            return;
        }
    };
    let pairs_s = match it.next() {
        Some(v) => v,
        None => {
            usage();
            return;
        }
    };
    let root_hex = match it.next() {
        Some(v) => v,
        None => {
            usage();
            return;
        }
    };

    let path = match parse_pairs(&pairs_s) {
        Ok(v) => v,
        Err(e) => {
            println!("{e}");
            return;
        }
    };
    let program = match build_program(addr, amount, &path) {
        Ok(p) => p,
        Err(e) => {
            println!("compile failed: {e}");
            return;
        }
    };

    // Bind Merkle root only
    let mut pi = pi::PublicInputsBuilder::for_program(&program)
        .sponge(false)
        .build()
        .expect("pi");

    let root_bytes = match parse_root_hex_to_bytes32(&root_hex) {
        Ok(b) => b,
        Err(e) => {
            println!("{e}");
            return;
        }
    };
    pi.cn_root = root_bytes;

    // Build trace and prove
    let trace = match prove::build_trace(&program) {
        Ok(t) => t,
        Err(e) => {
            println!("trace build failed: {e}");
            return;
        }
    };

    let prover = ZkProver::new(opts(), pi.clone());
    let proof = match prover.prove(trace) {
        Ok(p) => p,
        Err(e) => {
            println!("prove failed: {e}");

            if let Some(mut s) = e.source() {
                while let Some(c) = s.source() {
                    println!("caused by: {c}");
                    s = c;
                }
            }

            return;
        }
    };

    if let Err(e) = verify_proof(proof, pi, &opts()) {
        println!("verify failed: {e}");

        if let Some(mut s) = e.source() {
            while let Some(c) = s.source() {
                println!("caused by: {c}");
                s = c;
            }
        }

        return;
    }

    println!("OK: claim verified for addr={addr}, amount={amount}");
}

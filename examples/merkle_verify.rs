// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

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

fn main() {
    println!("start");

    // CLI: <leaf:u64> <path_pairs> <root_hex>
    let mut it = std::env::args().skip(1);
    let leaf: u64 = match it.next().and_then(|s| s.parse::<u64>().ok()) {
        Some(v) => v,
        None => {
            println!(
                "usage: cargo run --example merkle_verify -- <leaf:u64> <d0:s0,d1:s1,...> <root_hex>"
            );
            return;
        }
    };
    let pairs_s = match it.next() {
        Some(v) => v,
        None => {
            println!("missing path_pairs");
            return;
        }
    };
    let root_hex = match it.next() {
        Some(v) => v,
        None => {
            println!("missing root_hex");
            return;
        }
    };

    let pairs = match parse_pairs(&pairs_s) {
        Ok(v) => v,
        Err(e) => {
            println!("{e}");
            return;
        }
    };

    // Build program dynamically for pairs
    let mut params = vec!["leaf".to_string()];
    for (i, _) in pairs.iter().enumerate() {
        params.push(format!("d{i}"));
        params.push(format!("s{i}"));
    }

    let mut path_pairs = String::new();
    for (i, _) in pairs.iter().enumerate() {
        if !path_pairs.is_empty() {
            path_pairs.push(' ');
        }
        path_pairs.push_str(&format!("(d{i} s{i})"));
    }

    let src = format!(
        "(def (main {}) (load-ca leaf ({})))",
        params.join(" "),
        path_pairs
    );

    // args vector in same order
    let mut argv: Vec<u64> = vec![leaf];
    for &(d, s) in &pairs {
        argv.push(d);
        argv.push(s);
    }

    let program = match zk_lisp::compiler::compile_entry(&src, &argv) {
        Ok(p) => p,
        Err(e) => {
            println!("compile failed: {e}");
            return;
        }
    };

    // Build PI and set expected Merkle root
    let root_bytes = match parse_root_hex_to_bytes32(&root_hex) {
        Ok(b) => b,
        Err(e) => {
            println!("{e}");
            return;
        }
    };
    let mut pi = pi::PublicInputsBuilder::for_program(&program)
        .sponge(false)
        .build()
        .expect("pi");
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

            let mut s = e.source();
            while let Some(c) = s {
                println!("caused by: {c}");
                s = c.source();
            }

            return;
        }
    };

    if let Err(e) = verify_proof(proof, pi, &opts()) {
        println!("verify failed: {e}");

        let mut s = e.source();
        while let Some(c) = s {
            println!("caused by: {c}");
            s = c.source();
        }

        return;
    }

    println!("OK");
}

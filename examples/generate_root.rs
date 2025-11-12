// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use std::env;
use winterfell::math::{FieldElement, StarkField};
use winterfell::math::fields::f128::BaseElement as BE;

fn main() {
    println!("start");

    let mut it = env::args().skip(1);
    let mode = match it.next() {
        Some(m) => m,
        None => {
            println!("usage: airdrop <addr> <amount> <d:s,...> | verify <leaf> <d:s,...>");
            return;
        }
    };

    match mode.as_str() {
        "airdrop" => {
            let addr = match it.next().and_then(|s| s.parse::<u64>().ok()) {
                Some(v) => v,
                None => {
                    println!("missing <addr>");
                    return;
                }
            };
            let amount = match it.next().and_then(|s| s.parse::<u64>().ok()) {
                Some(v) => v,
                None => {
                    println!("missing <amount>");
                    return;
                }
            };
            let pairs_s = match it.next() {
                Some(v) => v,
                None => {
                    println!("missing <path_pairs>");
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

            let program = match build_airdrop_program(addr, amount, &pairs) {
                Ok(p) => p,
                Err(e) => {
                    println!("compile failed: {e}");
                    return;
                }
            };
            let root = compute_root_for_airdrop(&program.commitment, addr, amount, &pairs);
            let commit_hex = format!(
                "0x{}",
                program
                    .commitment
                    .iter()
                    .map(|b| format!("{b:02x}"))
                    .collect::<String>()
            );
            let root_hex = be_to_hex128(root);

            println!("commitment = {commit_hex}");
            println!("expected_root_hex = {root_hex}");
            println!("-- verify with:");
            println!(
                "cargo run --example merkle_airdrop_claim -- {addr} {amount} {pairs_s} {root_hex}"
            );
        }
        "verify" => {
            let leaf = match it.next().and_then(|s| s.parse::<u64>().ok()) {
                Some(v) => v,
                None => {
                    println!("missing <leaf>");
                    return;
                }
            };
            let pairs_s = match it.next() {
                Some(v) => v,
                None => {
                    println!("missing <path_pairs>");
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

            let program = match build_verify_program(leaf, &pairs) {
                Ok(p) => p,
                Err(e) => {
                    println!("compile failed: {e}");
                    return;
                }
            };
            let root = compute_root_for_leaf(&program.commitment, leaf, &pairs);
            let commit_hex = format!(
                "0x{}",
                program
                    .commitment
                    .iter()
                    .map(|b| format!("{b:02x}"))
                    .collect::<String>()
            );
            let root_hex = be_to_hex128(root);

            println!("commitment = {commit_hex}");
            println!("expected_root_hex = {root_hex}");
            println!("-- verify with:");
            println!("cargo run --example merkle_verify -- {leaf} {pairs_s} {root_hex}");
        }
        _ => {
            println!("unknown mode: {mode}. Use 'airdrop' or 'verify'");
        }
    }
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

fn be_to_hex128(v: BE) -> String {
    let n: u128 = v.as_int();
    format!("0x{n:032x}")
}

fn build_airdrop_program(
    addr: u64,
    amount: u64,
    pairs: &[(u64, u64)],
) -> Result<zk_lisp::compiler::ir::Program, zk_lisp::compiler::Error> {
    let mut params = vec!["addr".to_string(), "amount".to_string()];
    let mut pairs_src = String::new();

    for (i, _) in pairs.iter().enumerate() {
        params.push(format!("d{i}"));
        params.push(format!("s{i}"));

        if !pairs_src.is_empty() {
            pairs_src.push(' ');
        }

        pairs_src.push_str(&format!("(d{i} s{i})"));
    }

    let src = format!(
        r#"
(def (main {})
  (let ((r (hash2 addr amount)))
    (load-ca r ({})) r))"#,
        params.join(" "),
        pairs_src
    );

    let mut argv: Vec<u64> = vec![addr, amount];
    for &(d, s) in pairs {
        argv.push(d);
        argv.push(s);
    }

    zk_lisp::compiler::compile_entry(&src, &argv)
}

fn build_verify_program(
    leaf: u64,
    pairs: &[(u64, u64)],
) -> Result<zk_lisp::compiler::ir::Program, zk_lisp::compiler::Error> {
    let mut params = vec!["leaf".to_string()];
    let mut pairs_src = String::new();

    for (i, _) in pairs.iter().enumerate() {
        params.push(format!("d{i}"));
        params.push(format!("s{i}"));
        if !pairs_src.is_empty() {
            pairs_src.push(' ');
        }
        pairs_src.push_str(&format!("(d{i} s{i})"));
    }

    let src = format!(
        r#"(def (main {}) (load-ca leaf ({})))"#,
        params.join(" "),
        pairs_src
    );

    let mut argv: Vec<u64> = vec![leaf];
    for &(d, s) in pairs {
        argv.push(d);
        argv.push(s);
    }

    zk_lisp::compiler::compile_entry(&src, &argv)
}

fn compute_root_for_airdrop(
    commitment: &[u8; 32],
    addr: u64,
    amount: u64,
    pairs: &[(u64, u64)],
) -> BE {
    let mut acc =
        zk_lisp::poseidon::poseidon_hash_two_lanes(commitment, BE::from(addr), BE::from(amount));
    for &(d, s) in pairs {
        let dir = BE::from(d);
        let sib = BE::from(s);
        let left = (BE::ONE - dir) * acc + dir * sib;
        let right = (BE::ONE - dir) * sib + dir * acc;

        acc = zk_lisp::poseidon::poseidon_hash_two_lanes(commitment, left, right);
    }

    acc
}

fn compute_root_for_leaf(commitment: &[u8; 32], leaf: u64, pairs: &[(u64, u64)]) -> BE {
    let mut acc = BE::from(leaf);
    for &(d, s) in pairs {
        let dir = BE::from(d);
        let sib = BE::from(s);
        let left = (BE::ONE - dir) * acc + dir * sib;
        let right = (BE::ONE - dir) * sib + dir * acc;

        acc = zk_lisp::poseidon::poseidon_hash_two_lanes(commitment, left, right);
    }

    acc
}

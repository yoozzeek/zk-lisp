// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin

use std::env;
use winterfell::{BatchingMethod, FieldExtension, ProofOptions};
use zk_lisp::logging;
use zk_lisp::pi::{self};
use zk_lisp::prove::{self, ZkProver, verify_proof};
use std::error::Error;

fn opts() -> ProofOptions {
    ProofOptions::new(
        64,
        8,
        0,
        FieldExtension::None,
        2,
        1,
        BatchingMethod::Linear,
        BatchingMethod::Linear,
    )
}

fn parse_args() -> Result<(u64, u64, String), String> {
    let mut it = env::args().skip(1);

    let d = it.next().ok_or_else(|| "missing <dir:0|1>".to_string())?;
    let dir = d
        .parse::<u64>()
        .map_err(|_| format!("invalid dir: '{d}'"))?;
    if dir > 1 {
        return Err("dir must be 0 or 1".to_string());
    }

    let s = it
        .next()
        .ok_or_else(|| "missing <sibling:u64>".to_string())?;
    let sib = s
        .parse::<u64>()
        .map_err(|_| format!("invalid sibling: '{s}'"))?;

    let root_hex = it
        .next()
        .ok_or_else(|| "missing <expected_root_hex> (e.g. 0x1234)".to_string())?;

    Ok((dir, sib, root_hex))
}

fn parse_root_hex_to_bytes32(hex: &str) -> Result<[u8; 32], String> {
    let s = hex.strip_prefix("0x").unwrap_or(hex);
    let n = u128::from_str_radix(s, 16).map_err(|e| format!("invalid expected_root hex: {e}"))?;

    let mut out = [0u8; 32];
    out[0..16].copy_from_slice(&n.to_le_bytes());

    Ok(out)
}

fn main() {
    logging::init_with_level(None);
    tracing::info!(target = "examples.merkle_inclusion", "start");

    let (dir, sib, root_hex) = match parse_args() {
        Ok(v) => v,
        Err(msg) => {
            tracing::error!(
                target = "examples.merkle_inclusion",
                "usage: cargo run --example merkle_inclusion -- <dir:0|1> <sibling:u64> <expected_root_hex>\nerror: {msg}"
            );
            return;
        }
    };

    // Program: one KV step
    let src = r"
(def (main dir sib)
  (let ((x (kv-step dir sib)))
    (kv-final)))"
        .to_string();
    let program = zk_lisp::compiler::compile_entry(&src, &[dir, sib]).expect("compile");

    tracing::info!(
        target = "examples.merkle_inclusion",
        "commitment = 0x{}",
        program
            .commitment
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect::<String>()
    );

    // Build base PI via builder
    let pi_base = pi::PublicInputsBuilder::for_program(&program)
        .vm_args(&[dir, sib])
        .sponge(false)
        .build()
        .expect("pi");

    // Build trace with VM args and compute KV mask from trace
    let trace = prove::build_trace_with_pi(&program, &pi_base).expect("trace");
    let kv_mask = prove::compute_kv_levels_mask(&trace);

    // Final PI: add KV_EXPECT with provided root
    let root_bytes = match parse_root_hex_to_bytes32(&root_hex) {
        Ok(b) => b,
        Err(e) => {
            tracing::error!(target = "examples.merkle_inclusion", "{e}");
            return;
        }
    };

    let mut pi = pi_base.clone();
    pi.feature_mask |= pi::FM_KV_EXPECT;
    pi.kv_map_acc_bytes = [0u8; 32];
    pi.kv_fin_acc_bytes = root_bytes;
    pi.kv_levels_mask = kv_mask;

    let prover = ZkProver::new(opts(), pi.clone());
    let proof = match prover.prove(trace) {
        Ok(p) => p,
        Err(e) => {
            tracing::error!(target = "examples.merkle_inclusion", "prove failed: {e}");
            
            let mut s = e.source();
            while let Some(c) = s {
                tracing::error!(target = "examples.merkle_inclusion", "caused by: {}", c);
                s = c.source();
            }
            
            return;
        }
    };

    if let Err(e) = verify_proof(proof, pi, &opts()) {
        tracing::error!(target = "examples.merkle_inclusion", "verify failed: {e}");
        
        let mut s = e.source();
        while let Some(c) = s {
            tracing::error!(target = "examples.merkle_inclusion", "caused by: {}", c);
            s = c.source();
        }
        
        return;
    }

    tracing::info!(target = "examples.merkle_inclusion", "OK");
}

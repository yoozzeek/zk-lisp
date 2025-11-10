// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.

//! generate_root: host-side helper to compute commitment and expected root
//! for the merkle_inclusion example program with main+branching.
//!
//! Usage:
//!   cargo run --example generate_root -- <dir:0|1> <sibling:u64>
//! Prints:
//!   commitment and expected_root_hex suitable for merkle_inclusion

use std::env;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::math::{FieldElement, StarkField};
use zk_lisp::logging;

fn parse_args() -> Result<(u64, u64), String> {
    let mut it = env::args().skip(1);

    let d = it.next().ok_or_else(|| "missing <dir:0|1>".to_string())?;
    let dir = d
        .parse::<u64>()
        .map_err(|_| format!("invalid dir: '{d}'"))?;

    if dir > 1 {
        return Err("dir must be 0 or 1".into());
    }

    let s = it
        .next()
        .ok_or_else(|| "missing <sibling:u64>".to_string())?;
    let sib = s
        .parse::<u64>()
        .map_err(|_| format!("invalid sibling: '{s}'"))?;

    Ok((dir, sib))
}

fn main() {
    logging::init_with_level(None);

    let (dir, sib) = match parse_args() {
        Ok(v) => v,
        Err(msg) => {
            tracing::error!(
                target = "examples.generate_root",
                "usage: cargo run --example generate_root -- <dir:0|1> <sibling:u64>\nerror: {msg}"
            );
            return;
        }
    };

    // Program must match merkle_inclusion
    let src = r#"
(def (main dir sib)
  (let ((x (kv-step dir sib)))
    (kv-final)))
"#;
    // compile_entry to mirror merkle_inclusion
    let program = zk_lisp::compiler::compile_entry(src, &[dir, sib]).expect("compile");
    let suite_id = program.commitment;

    // Expected root for one KV step with acc0=0 and dynamic dir.
    // left = (1 - dir) * acc0 + dir * sib = dir * sib
    // right = (1 - dir) * sib + dir * acc0 = (1 - dir) * sib
    let d = BE::from(dir);
    let sib_fe = BE::from(sib);
    let left = (BE::ONE - d) * BE::ZERO + d * sib_fe;
    let right = (BE::ONE - d) * sib_fe + d * BE::ZERO;
    let h = zk_lisp::poseidon::poseidon_hash_two_lanes(&suite_id, left, right);
    let n: u128 = h.as_int();

    // Hex helpers
    let commit_hex = format!(
        "0x{}",
        suite_id
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect::<String>()
    );
    let root_hex = format!("0x{n:032x}");

    tracing::info!(
        target = "examples.generate_root",
        "commitment = {commit_hex}"
    );
    tracing::info!(
        target = "examples.generate_root",
        "expected_root_hex = {root_hex}"
    );
    tracing::info!(target = "examples.generate_root", "-- verify with:");
    tracing::info!(
        target = "examples.generate_root",
        "cargo run --example merkle_inclusion -- {dir} {sib} {root_hex}"
    );
}

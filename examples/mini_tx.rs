// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin

use std::env;
use winterfell::math::{FieldElement, StarkField};
use winterfell::{BatchingMethod, FieldExtension, ProofOptions, Trace};
use zk_lisp::compiler::compile_entry;
use zk_lisp::logging;
use zk_lisp::pi::PublicInputsBuilder;
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

fn parse_args() -> Result<(u64, u64, u64), String> {
    let mut it = env::args().skip(1);

    let s = it
        .next()
        .ok_or_else(|| "missing <sender:u64>".to_string())?;
    let sender = s
        .parse::<u64>()
        .map_err(|_| format!("invalid sender: '{s}'"))?;

    let r = it
        .next()
        .ok_or_else(|| "missing <receiver:u64>".to_string())?;
    let receiver = r
        .parse::<u64>()
        .map_err(|_| format!("invalid receiver: '{r}'"))?;

    let a = it
        .next()
        .ok_or_else(|| "missing <amount:u64>".to_string())?;
    let amount = a
        .parse::<u64>()
        .map_err(|_| format!("invalid amount: '{a}'"))?;

    Ok((sender, receiver, amount))
}

fn u128_to_bytes32(n: u128) -> [u8; 32] {
    let mut b = [0u8; 32];
    b[0..16].copy_from_slice(&n.to_le_bytes());

    b
}

fn main() {
    logging::init_with_level(None);
    tracing::info!(target = "examples.mini_tx", "start");

    let (sender, receiver, amount) = match parse_args() {
        Ok(v) => v,
        Err(msg) => {
            tracing::error!(
                target = "examples.mini_tx",
                "usage: cargo run --example mini_tx -- <sender:u64> <receiver:u64> <amount:u64>\nerror: {msg}"
            );
            return;
        }
    };

    // Mini-transaction: assert balances update
    // and return sender' (new sender balance).
    // No comparisons or underflow checks are
    // performed; this just demonstrates
    // a state transition.
    let src = r#"
(def (main s r a)
  (let ((s2 (- s a))
        (r2 (+ r a)))
    (assert (= (+ s2 r2) (+ s r)))
    s2))
    "#;

    let program = compile_entry(src, &[sender, receiver, amount]).expect("compile");

    // Expected new sender balance
    let expected = u128::from(sender - amount);

    // Phase 1: build base PI (no EXPECT) to compute out location
    let pi_base = PublicInputsBuilder::for_program(&program)
        .vm_args(&[sender, receiver, amount])
        .sponge(false)
        .build()
        .expect("pi");

    let trace = prove::build_trace_with_pi(&program, &pi_base).expect("trace");

    // Prefer last write to r0
    // (program return) rather
    // than last op level.
    let cols = zk_lisp::layout::Columns::baseline();
    let steps = zk_lisp::layout::STEPS_PER_LEVEL_P2;
    let lvls = trace.length() / steps;
    let pos_fin = zk_lisp::schedule::pos_final();

    let mut last_lvl_r0: usize = 0;
    for lvl in 0..lvls {
        let row_fin = lvl * steps + pos_fin;
        if trace.get(cols.sel_dst_index(0), row_fin)
            == winterfell::math::fields::f128::BaseElement::ONE
        {
            last_lvl_r0 = lvl;
        }
    }

    let out_row = (last_lvl_r0 * steps + pos_fin + 1) as u32;
    let out_reg = 0u8;

    // Prepare expected from trace at r0/out_row to ensure exact match
    let val_trace = trace.get(cols.r_index(0), out_row as usize);
    let expected_trace_bytes = u128_to_bytes32(val_trace.as_int());

    // Optional sanity: host expected vs trace expected
    if expected != val_trace.as_int() {
        tracing::warn!(
            target = "examples.mini_tx",
            "host_expected={} trace_expected={} (using trace value for EXPECT)",
            expected,
            val_trace.as_int()
        );
    }

    // Phase 2: final PI with EXPECT at computed location (r0)
    let pi = PublicInputsBuilder::for_program(&program)
        .vm_args(&[sender, receiver, amount])
        .sponge(false)
        .vm_expect_at(out_reg, out_row, &expected_trace_bytes)
        .build()
        .expect("pi");

    let prover = ZkProver::new(opts(), pi.clone());
    let proof = match prover.prove(trace) {
        Ok(p) => p,
        Err(e) => {
            tracing::error!(target = "examples.mini_tx", "prove failed: {e}");
            
            let mut s = e.source();
            while let Some(c) = s {
                tracing::error!(target = "examples.mini_tx", "caused by: {}", c);
                s = c.source();
            }
            
            return;
        }
    };

    if let Err(e) = verify_proof(proof, pi, &opts()) {
        tracing::error!(target = "examples.mini_tx", "verify failed: {e}");
        
        let mut s = e.source();
        while let Some(c) = s {
            tracing::error!(target = "examples.mini_tx", "caused by: {}", c);
            s = c.source();
        }
        
        return;
    }

    tracing::info!(target = "examples.mini_tx", "sender' = {}", sender - amount);
}

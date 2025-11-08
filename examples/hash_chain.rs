use std::env;
use winterfell::ProofOptions;
use winterfell::Trace;
use winterfell::math::FieldElement;
use winterfell::math::StarkField;
use winterfell::math::fields::f128::BaseElement as BE;
use zk_lisp::lisp::compile_entry;
use zk_lisp::logging;
use zk_lisp::pi::{self, PublicInputs};
use zk_lisp::poseidon::poseidon_hash_two_lanes;
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

fn parse_args() -> Result<(u64, u64, u64, Option<String>), String> {
    let mut it = env::args().skip(1);

    let a = it.next().ok_or_else(|| "missing <x>".to_string())?;
    let x = a
        .parse::<u64>()
        .map_err(|_| format!("invalid <x>: '{a}'"))?;
    let b = it.next().ok_or_else(|| "missing <y>".to_string())?;
    let y = b
        .parse::<u64>()
        .map_err(|_| format!("invalid <y>: '{b}'"))?;
    let c = it.next().ok_or_else(|| "missing <z>".to_string())?;
    let z = c
        .parse::<u64>()
        .map_err(|_| format!("invalid <z>: '{c}'"))?;

    let expect_hex = it.next();

    Ok((x, y, z, expect_hex))
}

fn hex128_to_bytes32(hex: &str) -> Result<[u8; 32], String> {
    let s = hex.strip_prefix("0x").unwrap_or(hex);
    let n = u128::from_str_radix(s, 16).map_err(|e| format!("invalid hex: {e}"))?;

    let mut out = [0u8; 32];
    out[0..16].copy_from_slice(&n.to_le_bytes());

    Ok(out)
}

fn main() {
    logging::init();
    tracing::info!(target = "examples.hash_chain", "start");

    let (x, y, z, expect_hex) = match parse_args() {
        Ok(v) => v,
        Err(msg) => {
            tracing::error!(
                target = "examples.hash_chain",
                "usage: cargo run --example hash_chain -- <x:u64> <y:u64> <z:u64> [<expected_hex>]\nerror: {msg}"
            );
            return;
        }
    };

    tracing::info!(target = "examples.hash_chain", "args: x={x}, y={y}, z={z}");

    // Program: two-level hash chain
    let src = r"
        (def (main x y z)
          (let ((h1 (hash2 x y))
                (h2 (hash2 h1 z)))
            h2))
    ";

    let program = compile_entry(src, &[x, y, z]).expect("compile");

    tracing::info!(
        target = "examples.hash_chain",
        "suite_id (commitment) = 0x{:02x?}",
        program.commitment
    );

    // Compute expected on host
    let h1 = poseidon_hash_two_lanes(&program.commitment, BE::from(x), BE::from(y));
    let expected = poseidon_hash_two_lanes(&program.commitment, h1, BE::from(z));

    let expected_bytes = if let Some(hex) = expect_hex {
        match hex128_to_bytes32(&hex) {
            Ok(b) => b,
            Err(e) => {
                tracing::error!(target = "examples.hash_chain", "invalid expected_hex: {e}");
                return;
            }
        }
    } else {
        let mut b = [0u8; 32];
        let n: u128 = expected.as_int();
        b[0..16].copy_from_slice(&n.to_le_bytes());

        b
    };

    // Build trace with VM args bound at level 0 map row via PI
    let mut pi = PublicInputs::default();
    pi.feature_mask = pi::FM_VM | pi::FM_VM_EXPECT;
    pi.program_commitment = program.commitment;
    pi.vm_args = vec![x, y, z];

    let trace = zk_lisp::prove::build_trace_with_pi(&program, &pi);

    // Detect output location (dst reg at last op final row)
    let cols = zk_lisp::layout::Columns::baseline();
    let steps = zk_lisp::layout::STEPS_PER_LEVEL_P2;
    let lvls = trace.length() / steps;
    let op_bits = [
        cols.op_const,
        cols.op_mov,
        cols.op_add,
        cols.op_sub,
        cols.op_mul,
        cols.op_neg,
        cols.op_eq,
        cols.op_select,
        cols.op_hash2,
        cols.op_assert,
    ];

    let mut last_op_lvl = 0usize;
    for lvl in (0..lvls).rev() {
        let base = lvl * steps;
        let row_map = base + zk_lisp::schedule::pos_map();

        if op_bits.iter().any(|&c| trace.get(c, row_map) == BE::ONE) {
            last_op_lvl = lvl;
            break;
        }
    }

    let base = last_op_lvl * steps;
    let row_fin = base + zk_lisp::schedule::pos_final();

    let mut out_reg = 0u8;

    for i in 0..zk_lisp::layout::NR {
        if trace.get(cols.sel_dst_index(i), row_fin) == BE::ONE {
            out_reg = i as u8;
            break;
        }
    }

    // Complete VM PI-binding
    pi.vm_out_reg = out_reg;
    pi.vm_out_row = (row_fin + 1) as u32;
    pi.vm_expected_bytes = expected_bytes;

    tracing::info!(target = "examples.hash_chain", "proving...");

    let opts = opts();
    let prover = ZkProver::new(opts.clone(), pi.clone());

    match prover.prove(trace) {
        Err(e) => {
            tracing::error!(target = "examples.hash_chain", "prove failed: {e}");
        }
        Ok(proof) => {
            tracing::info!(target = "examples.hash_chain", "verifying...");
            match verify_proof(proof, pi, &opts) {
                Ok(()) => tracing::info!(target = "examples.hash_chain", "OK"),
                Err(e) => tracing::error!(target = "examples.hash_chain", "VERIFY FAILED: {e}"),
            }
        }
    }
}

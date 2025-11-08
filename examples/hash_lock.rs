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
    logging::init();
    tracing::info!(target = "examples.hash_lock", "start");

    let (secret, salt, expect_hex) = match parse_args() {
        Ok(v) => v,
        Err(msg) => {
            tracing::error!(
                target = "examples.hash_lock",
                "usage: cargo run --example hash_lock -- <secret:u64> <salt:u64> [<expected_hex>]\nerror: {msg}"
            );
            return;
        }
    };

    tracing::info!(
        target = "examples.hash_lock",
        "args: secret={secret}, salt={salt}"
    );

    // Program: compute commit = Poseidon(secret, salt)
    let src = r"
        (def (main secret salt)
          (hash2 secret salt))
    ";

    // Build program with entry args
    let program = compile_entry(src, &[secret, salt]).expect("compile");

    tracing::info!(
        target = "examples.hash_lock",
        "suite_id (commitment) = 0x{:02x?}",
        program.commitment
    );

    // Compute expected digest on host
    let expected = poseidon_hash_two_lanes(&program.commitment, BE::from(secret), BE::from(salt));

    // If user passed explicit expected,
    // use it (to demo verify failure on mismatch)
    let expected_bytes = if let Some(hex) = expect_hex {
        match hex128_to_bytes32(&hex) {
            Ok(b) => b,
            Err(e) => {
                tracing::error!(target = "examples.hash_lock", "invalid expected_hex: {e}");
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
    pi.feature_mask = pi::FM_VM | pi::FM_VM_EXPECT; // VM + bind expected output
    pi.program_commitment = program.commitment;
    pi.vm_args = vec![secret, salt];

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

    tracing::info!(target = "examples.hash_lock", "proving...");

    let opts = opts();
    let prover = ZkProver::new(opts.clone(), pi.clone());

    match prover.prove(trace) {
        Err(e) => {
            tracing::error!(target = "examples.hash_lock", "prove failed: {e}");
        }
        Ok(proof) => {
            tracing::info!(target = "examples.hash_lock", "verifying...");
            match verify_proof(proof, pi, &opts) {
                Ok(()) => tracing::info!(target = "examples.hash_lock", "OK"),
                Err(e) => tracing::error!(target = "examples.hash_lock", "VERIFY FAILED: {e}"),
            }
        }
    }
}

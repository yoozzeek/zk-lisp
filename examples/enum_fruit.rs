use std::env;
use winterfell::ProofOptions;
use winterfell::Trace;
use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;
use zk_lisp::lisp::compile_entry;
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

    let s = it.next().ok_or_else(|| "missing <t:0|1|2>".to_string())?;
    match s.as_str() {
        "0" | "1" | "2" => Ok(s.parse::<u64>().unwrap()),
        _ => Err("expected 0,1,2".to_string()),
    }
}

fn u128_to_bytes32(n: u128) -> [u8; 32] {
    let mut b = [0u8; 32];
    b[0..16].copy_from_slice(&n.to_le_bytes());

    b
}

fn main() {
    logging::init();
    tracing::info!(target = "examples.enum_fruit", "start");

    let t = match parse_arg() {
        Ok(v) => v,
        Err(msg) => {
            tracing::error!(
                target = "examples.enum_fruit",
                "usage: cargo run --example enum_fruit -- <t:0|1|2>\nerror: {msg}",
            );
            return;
        }
    };

    // Program: enum fruit, assert membership, return tag
    let src = r#"
        (deftype fruit () '(member apple orange banana))
        (def (main t)
          (let ((ok (fruit:is t))
                (d (assert ok)))
            t))
    "#;
    let program = compile_entry(src, &[t]).expect("compile");

    // Expected = t (as FE in little-endian low 128 bits)
    let expected = u128_to_bytes32(t as u128);

    let pi = PublicInputsBuilder::for_program(&program)
        .vm_args(&[t])
        .vm_expect_from_meta(&program, &expected)
        .build()
        .expect("pi");

    let trace = zk_lisp::prove::build_trace_with_pi(&program, &pi);

    // Debug: print meta vs actual trace info
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
    let mut out_reg_scan = 0u8;
    for i in 0..zk_lisp::layout::NR {
        if trace.get(cols.sel_dst_index(i), row_fin) == BE::ONE {
            out_reg_scan = i as u8;
            break;
        }
    }
    let out_row_scan = (row_fin + 1) as u32;
    let val_scan = trace.get(cols.r_index(out_reg_scan as usize), out_row_scan as usize);
    // Also check select cond at this level
    let mut cond_reg = None;
    for i in 0..zk_lisp::layout::NR {
        if trace.get(cols.sel_c_index(i), row_fin) == BE::ONE { cond_reg = Some(i as u8); break; }
    }
    let cond_map = cond_reg.map(|r| trace.get(cols.r_index(r as usize), base + zk_lisp::schedule::pos_map()));
    let cond_nxt = cond_reg.map(|r| trace.get(cols.r_index(r as usize), out_row_scan as usize));

    // also inspect a/b sources
    let mut a_reg = None; let mut b_reg = None;
    for i in 0..zk_lisp::layout::NR { if trace.get(cols.sel_a_index(i), row_fin) == BE::ONE { a_reg = Some(i as u8); break; } }
    for i in 0..zk_lisp::layout::NR { if trace.get(cols.sel_b_index(i), row_fin) == BE::ONE { b_reg = Some(i as u8); break; } }
    let a_map = a_reg.map(|r| trace.get(cols.r_index(r as usize), base + zk_lisp::schedule::pos_map()));
    let b_map = b_reg.map(|r| trace.get(cols.r_index(r as usize), base + zk_lisp::schedule::pos_map()));

    tracing::info!(
        target = "examples.enum_fruit",
        "meta: out_reg={} out_row={} | scan: out_reg={} out_row={} val_scan={:?} cond_reg={:?} cond_map={:?} cond_next={:?} a_reg={:?} a_map={:?} b_reg={:?} b_map={:?}",
        program.meta.out_reg,
        program.meta.out_row,
        out_reg_scan,
        out_row_scan,
        val_scan,
        cond_reg,
        cond_map,
        cond_nxt,
        a_reg,
        a_map,
        b_reg,
        b_map
    );

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

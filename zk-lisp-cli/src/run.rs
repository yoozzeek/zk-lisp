// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

use crate::{CliError, PreflightArg, RunArgs};

use zk_lisp_compiler as compiler;
use zk_lisp_proof::frontend::PreflightMode;
use zk_lisp_proof::{ZkField, frontend};
use zk_lisp_proof_winterfell::WinterfellBackend;

pub fn cmd_run(
    args: RunArgs,
    json: bool,
    max_bytes: usize,
    pf: PreflightArg,
    security_bits: Option<u32>,
) -> Result<(), CliError> {
    let t_start = std::time::Instant::now();
    let src = crate::read_program(&args.path, max_bytes)?;

    let (public_vmargs, public_u64) = crate::parse_public_args(&args.args)?;
    let secret_vmargs = crate::parse_secret_args(&args.secrets)?;

    let program = compiler::compile_entry(&src, &public_u64)?;
    crate::validate_main_args_against_schema(&program, &public_vmargs)?;

    let pi = crate::build_pi_for_program(&program, &public_vmargs, &secret_vmargs)?;

    let pf_mode = crate::resolve_preflight_mode(pf);
    if !matches!(pf_mode, PreflightMode::Off) {
        let opts = crate::proof_opts(1, 8, 0, security_bits, None, None);
        frontend::preflight::<WinterfellBackend>(pf_mode, &opts, &program, &pi)
            .map_err(CliError::Prover)?;
    }

    let commitment_hex = format!("0x{}", hex::encode(program.program_id));

    // Compute VM output position
    // and value via backend.
    let run_res = frontend::run_vm::<WinterfellBackend>(&program, &pi).map_err(CliError::Prover)?;
    let out_reg = run_res.out_reg;
    let out_row = run_res.out_row;
    let val_u128: u128 = ZkField::to_u128(&run_res.value);
    let metrics = program.compiler_metrics;
    let elapsed_ms = t_start.elapsed().as_millis();

    if json {
        println!(
            "{}",
            serde_json::json!({
                "ok": true,
                "program_commitment": commitment_hex,
                "result_dec": val_u128.to_string(),
                "result_hex": format!("0x{:032x}", val_u128),
                "out_reg": out_reg,
                "out_row": out_row,
                "trace_len": run_res.trace_len,
                "time_ms": elapsed_ms,
                "compiler_metrics": {
                    "peak_live": metrics.peak_live,
                    "reuse_dst": metrics.reuse_dst,
                    "su_reorders": metrics.su_reorders,
                    "balanced_chains": metrics.balanced_chains,
                    "mov_elided": metrics.mov_elided
                }
            })
        );
    } else {
        let rows = run_res.trace_len;

        println!("Program commitment: {commitment_hex}");
        println!(
            "Result: {val_u128} (0x{val_u128:032x}), out_reg={out_reg}, out_row={out_row}, rows={rows}"
        );

        println!(
            "Compiler metrics: peak_live={} reuse_dst={} su_reorders={} balanced_chains={} mov_elided={}",
            metrics.peak_live,
            metrics.reuse_dst,
            metrics.su_reorders,
            metrics.balanced_chains,
            metrics.mov_elided
        );

        println!("Time: {elapsed_ms} ms");
    }

    Ok(())
}

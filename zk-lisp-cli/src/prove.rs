// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

use crate::{CliError, PreflightArg, ProveArgs};

use std::fs;
use std::path::PathBuf;
use zk_lisp_compiler as compiler;
use zk_lisp_proof::frontend::PreflightMode;
use zk_lisp_proof::recursion::RecursionArtifactCodec;
use zk_lisp_proof::{frontend, recursion};
use zk_lisp_proof_winterfell::WinterfellBackend;

pub fn cmd_prove(
    args: ProveArgs,
    json: bool,
    max_bytes: usize,
    pf: PreflightArg,
    security_bits: Option<u32>,
) -> Result<(), CliError> {
    if args.seed.is_some() {
        return Err(CliError::InvalidInput(
            "seed is not supported yet".to_string(),
        ));
    }

    let t_start = std::time::Instant::now();
    let src = crate::read_program(&args.path, max_bytes)?;

    let (public_vmargs, public_u64) = crate::parse_public_args(&args.args)?;
    let secret_vmargs = crate::parse_secret_args(&args.secrets)?;

    let program = compiler::compile_entry(&src, &public_u64)?;

    crate::validate_main_args_against_schema(&program, &public_vmargs)?;

    let pi = crate::build_pi_for_program(&program, &public_vmargs, &secret_vmargs)?;

    let opts = crate::proof_opts(
        args.queries,
        args.blowup,
        args.grind,
        security_bits,
        args.max_segment_rows,
        args.max_concurrent_segments,
    );
    let pf_mode = crate::resolve_preflight_mode(pf);

    if !matches!(pf_mode, PreflightMode::Off) {
        frontend::preflight::<WinterfellBackend>(pf_mode, &opts, &program, &pi)
            .map_err(CliError::Prover)?;
    }

    let (rc_proof, _rc_digest, rc_pi) =
        recursion::prove_chain::<WinterfellBackend>(&program, &pi, &opts)
            .map_err(CliError::Prover)?;

    let artifact_bytes = <WinterfellBackend as RecursionArtifactCodec>::encode(&rc_proof, &rc_pi)
        .map_err(CliError::Prover)?;

    let out_path = if let Some(path) = args.out {
        path
    } else {
        let file_name = proof_basename_from_program_path(&args.path).replace("proof_", "agg_");

        PathBuf::from(file_name)
    };

    fs::write(&out_path, &artifact_bytes).map_err(|e| CliError::IoPath {
        source: e,
        path: out_path.clone(),
    })?;

    let commitment_hex = format!("0x{}", hex::encode(program.program_id));
    let elapsed_ms = t_start.elapsed().as_millis();

    if !args.quiet {
        if json {
            println!(
                "{}",
                serde_json::json!({
                    "ok": true,
                    "program_commitment": commitment_hex,
                    "agg_proof_path": out_path.to_string_lossy(),
                    "agg_proof_bytes": artifact_bytes.len(),
                    "opts": {"queries": args.queries, "blowup": args.blowup, "grind": args.grind},
                    "time_ms": elapsed_ms,
                })
            );
        } else {
            println!("Program commitment: {commitment_hex}");
            println!(
                "Agg proof saved to {} (len={} bytes)",
                out_path.display(),
                artifact_bytes.len()
            );
            println!("Time: {elapsed_ms} ms");
        }
    }

    Ok(())
}

fn proof_basename_from_program_path(path: &std::path::Path) -> String {
    let stem = path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("program");

    let mut tag = String::new();
    for ch in stem.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' || ch == '-' {
            tag.push(ch);
        } else if ch.is_whitespace() {
            tag.push('_');
        }

        if tag.len() >= 32 {
            break;
        }
    }

    if tag.is_empty() {
        tag.push_str("program");
    }

    let ts = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);
    let ts_str = ts.to_string();

    let prefix = "proof_";
    let suffix_extra = 1 + ts_str.len() + 4; // "_" + ts + ".bin"
    let max_len = 64usize;

    let mut tag_trunc = tag.clone();
    if prefix.len() + tag_trunc.len() + suffix_extra > max_len {
        let allowed = max_len.saturating_sub(prefix.len() + suffix_extra);
        if allowed == 0 {
            tag_trunc.clear();
        } else if tag_trunc.len() > allowed {
            tag_trunc.truncate(allowed);
        }

        if tag_trunc.is_empty() {
            tag_trunc.push('x');
        }
    }

    format!("{prefix}{tag_trunc}_{ts_str}.bin")
}

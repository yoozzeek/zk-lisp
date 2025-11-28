// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

use crate::{CliError, VerifyArgs};

use std::fs;
use std::path::PathBuf;
use zk_lisp_compiler as compiler;
use zk_lisp_proof::recursion::RecursionArtifactCodec;
use zk_lisp_proof::{error, frontend};
use zk_lisp_proof_winterfell::{WinterfellBackend, prove};

pub fn cmd_verify(
    args: VerifyArgs,
    json: bool,
    max_bytes: usize,
    security_bits: Option<u32>,
) -> Result<(), CliError> {
    let t_start = std::time::Instant::now();
    let proof_path_str = args.proof.as_str();

    let artifact_bytes = {
        let meta = fs::metadata(proof_path_str).map_err(|e| CliError::IoPath {
            source: e,
            path: PathBuf::from(proof_path_str),
        })?;

        if meta.len() as usize > max_bytes {
            return Err(CliError::InvalidInput(format!(
                "agg proof file too large: {} bytes (limit {})",
                meta.len(),
                max_bytes
            )));
        }

        fs::read(proof_path_str).map_err(|e| CliError::IoPath {
            source: e,
            path: PathBuf::from(proof_path_str),
        })?
    };

    let src = crate::read_program(&args.path, max_bytes)?;
    let (public_vmargs, public_u64) = crate::parse_public_args(&args.args)?;

    let program = compiler::compile_entry(&src, &public_u64)?;

    crate::validate_main_args_against_schema(&program, &public_vmargs)?;

    let pi_cli = crate::build_pi_for_program(&program, &public_vmargs, &[])?;

    let (rc_proof, rc_pi) = <WinterfellBackend as RecursionArtifactCodec>::decode(&artifact_bytes)
        .map_err(CliError::Prover)?;

    if rc_pi.children_count == 0 {
        return Err(CliError::InvalidInput("agg proof has zero children".into()));
    }

    if rc_pi.program_id != pi_cli.program_id
        || rc_pi.program_commitment != pi_cli.program_commitment
    {
        let err = error::Error::InvalidInput(
            "agg proof program (program_id/program_commitment) does not match compiled program",
        );

        return Err(CliError::Verify(prove::Error::PublicInputs(err)));
    }

    let pi_digest_cli = pi_cli.digest();
    if rc_pi.pi_digest != pi_digest_cli {
        let err = error::Error::InvalidInput(
            "agg proof public inputs (main args) do not match CLI --arg",
        );

        return Err(CliError::Verify(prove::Error::PublicInputs(err)));
    }

    let opts = crate::proof_opts(
        args.queries,
        args.blowup,
        args.grind,
        security_bits,
        None,
        None,
    );
    frontend::recursion_verify::<WinterfellBackend>(rc_proof, &rc_pi, &opts)
        .map_err(CliError::Verify)?;

    let elapsed_ms = t_start.elapsed().as_millis();

    if json {
        println!("{}", serde_json::json!({"ok": true, "time_ms": elapsed_ms}));
    } else {
        println!("OK");
        println!("time: {elapsed_ms} ms");
    }

    Ok(())
}

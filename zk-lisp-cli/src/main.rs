// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Command-line interface for the zk-lisp prover.
//!
//! Provides subcommands to compile, run, prove and verify
//! zk-lisp programs using the configured STARK backend,
//! plus a minimal interactive REPL for experimentation.

#![forbid(unsafe_code)]

mod prove;
mod repl;
mod run;
mod verify;

use clap::{Parser, Subcommand};
use std::fs;
use std::io::{self};
use std::path::PathBuf;
use thiserror::Error;
use zk_lisp_compiler as compiler;
use zk_lisp_proof::frontend::PreflightMode;
use zk_lisp_proof::pi::{PublicInputs, PublicInputsBuilder, VmArg};
use zk_lisp_proof::{ProverOptions, error};
use zk_lisp_proof_winterfell::prove::Error as ProveError;

// Max file size for REPL
// operations (load/verify [PATH])
const REPL_MAX_BYTES: usize = 1_048_576; // 1 MiB

static INIT_LOGGING: std::sync::Once = std::sync::Once::new();

#[derive(Parser, Debug, Clone)]
#[command(
    name = "zk-lisp",
    about = r"# zk-lisp CLI
# Copyright (c) Andrei Kochergin. All rights reserved.

Lisp-like DSL and compiler for proving
program execution in zero-knowledge.",
    version
)]
struct Cli {
    /// Global JSON output
    #[arg(long, global = true, default_value_t = false)]
    json: bool,
    /// Global log level (trace|debug|info|warn|error)
    #[arg(
        long,
        global = true,
        default_value = "error",
        value_parser = ["trace", "debug", "info", "warn", "error"],
    )]
    log_level: String,
    /// Minimum conjectured security in bits for proofs (64 or 128).
    /// Defaults to 64 in debug builds and 128 in release builds.
    /// Can also be set via ZKL_SECURITY_BITS env var.
    #[arg(long, global = true, env = "ZKL_SECURITY_BITS")]
    security_bits: Option<u32>,
    /// Max input file size in bytes
    #[arg(long, global = true, default_value_t = 1_048_576)]
    max_bytes: usize,
    /// Preflight mode:
    /// off|console|json|auto (auto: console in debug, off in release)
    #[arg(long, global = true, default_value = "auto", value_enum)]
    preflight: PreflightArg,
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand, Debug, Clone)]
enum Command {
    /// Compile and execute a program, print result
    Run(RunArgs),
    /// Create a STARK proof for a program and args; prints proof hex
    Prove(ProveArgs),
    /// Verify a proof hex against a program and args
    Verify(VerifyArgs),
    /// Minimal interactive REPL
    Repl,
}

#[derive(clap::Args, Debug, Clone)]
struct RunArgs {
    /// Path to .zlisp file
    path: PathBuf,
    /// Arguments for main (repeat or comma-separated via --arg)
    ///
    /// Each argument is typed as `<kind>:<value>`, e.g.
    /// `u64:3`, `u64:0x10`. Currently only `u64` is
    /// supported for main; use --secret for other types.
    #[arg(long = "arg", value_delimiter = ',')]
    args: Vec<String>,
    /// Secret arguments for main (prove/run only).
    ///
    /// Each item is `<kind>:<value>` (u64|u128|bytes32).
    #[arg(long = "secret", value_delimiter = ',')]
    secrets: Vec<String>,
}

#[derive(clap::Args, Debug, Clone)]
struct ProveArgs {
    /// Path to .zlisp file
    path: PathBuf,
    /// Public arguments for main
    ///
    /// Each argument is typed as `<kind>:<value>`, e.g.
    /// `u64:3`, `u64:0x10`. Currently only `u64` is
    /// supported for main; use --secret for other types.
    #[arg(long = "arg", value_delimiter = ',')]
    args: Vec<String>,
    /// Secret arguments for main (prove only).
    ///
    /// Each item is `<kind>:<value>` (u64|u128|bytes32).
    #[arg(long = "secret", value_delimiter = ',')]
    secrets: Vec<String>,
    /// Number of FRI queries.
    #[arg(long, default_value_t = 64)]
    queries: u8,
    /// Blowup factor
    #[arg(long, default_value_t = 16)]
    blowup: u8,
    /// Grinding factor
    #[arg(long, default_value_t = 16)]
    grind: u32,
    /// Optional deterministic seed
    #[arg(long)]
    seed: Option<u64>,
    /// Write base STARK proof to file (binary);
    /// still prints preview to stdout unless --quiet
    #[arg(long)]
    out: Option<PathBuf>,
    /// Quiet mode (suppress non-essential output)
    #[arg(long, default_value_t = false)]
    quiet: bool,
    /// Override for the maximum number of base-trace
    /// rows per execution segment. When `None`, the
    /// backend's default policy is used.
    #[arg(long = "max-segment-rows")]
    max_segment_rows: Option<usize>,
    /// Upper bound on the number of child proofs
    /// (segments) that may be constructed in parallel.
    /// None means no parallelism.
    #[arg(long = "max-concurrent-segments")]
    max_concurrent_segments: Option<usize>,
}

#[derive(clap::Args, Debug, Clone)]
struct VerifyArgs {
    /// Proof file path
    proof: String,
    /// Path to .zlisp file
    path: PathBuf,
    /// Arguments for main must match
    /// the ones used for proof.
    ///
    /// Each argument is typed as `<kind>:<value>`;
    /// currently only `u64` is supported for main here.
    #[arg(long = "arg", value_delimiter = ',')]
    args: Vec<String>,
    /// Number of FRI queries
    #[arg(long, default_value_t = 64)]
    queries: u8,
    /// Blowup factor
    #[arg(long, default_value_t = 16)]
    blowup: u8,
    /// Grinding factor
    #[arg(long, default_value_t = 16)]
    grind: u32,
    /// Optional seed
    #[arg(long)]
    seed: Option<u64>,
}

#[derive(clap::ValueEnum, Debug, Clone, Copy)]
enum PreflightArg {
    Off,
    Console,
    Json,
    Auto,
}

#[derive(Error, Debug)]
enum CliError {
    #[error("invalid input: {0}")]
    InvalidInput(String),
    #[error("compile error: {0}")]
    Compile(#[from] compiler::Error),
    #[error("io error")]
    Io(#[from] io::Error),
    #[error("io error: {source}: {path}")]
    IoPath {
        #[source]
        source: io::Error,
        path: PathBuf,
    },
    #[error("prove error: {0}")]
    Prover(#[from] ProveError),
    #[error("verify error: {0}")]
    Verify(#[source] ProveError),
    #[error("build error")]
    Build(#[from] error::Error),
    #[error("hex error")]
    Hex(#[from] hex::FromHexError),
}

impl CliError {
    fn code(&self) -> i32 {
        match self {
            CliError::InvalidInput(_) => 2,
            CliError::Compile(_) => 3,
            CliError::Io(_) | CliError::IoPath { .. } => 5,
            CliError::Prover(_) => 6,
            CliError::Verify(_) => 7,
            CliError::Build(_) => 4,
            CliError::Hex(_) => 2,
        }
    }
}

fn normalize_security_bits(bits: Option<u32>) -> Result<Option<u32>, CliError> {
    match bits {
        None => Ok(None),
        Some(b) if b == 64 || b == 128 => Ok(Some(b)),
        Some(b) => Err(CliError::InvalidInput(format!(
            "invalid --security-bits={b}; expected 64 or 128",
        ))),
    }
}

fn proof_opts(
    queries: u8,
    blowup: u8,
    grind: u32,
    security_bits: Option<u32>,
    max_segment_rows: Option<usize>,
    max_concurrent_segments: Option<usize>,
) -> ProverOptions {
    let base = ProverOptions::default();
    let min_security_bits = security_bits.unwrap_or(base.min_security_bits);

    ProverOptions {
        queries,
        blowup,
        grind,
        min_security_bits,
        max_segment_rows,
        max_concurrent_segments,
    }
}

fn read_program(path: impl AsRef<std::path::Path>, max_bytes: usize) -> Result<String, CliError> {
    let path_ref = path.as_ref();
    let meta = fs::metadata(path_ref).map_err(|e| CliError::IoPath {
        source: e,
        path: path_ref.to_path_buf(),
    })?;

    if meta.len() as usize > max_bytes {
        return Err(CliError::InvalidInput(format!(
            "file too large: {} bytes (limit {})",
            meta.len(),
            max_bytes
        )));
    }

    let s = fs::read_to_string(path_ref).map_err(|e| CliError::IoPath {
        source: e,
        path: path_ref.to_path_buf(),
    })?;

    Ok(s)
}

fn build_pi_for_program(
    program: &compiler::Program,
    public_args: &[VmArg],
    secret_args: &[VmArg],
) -> Result<PublicInputs, CliError> {
    let main_args = if let Some(schema) = program.type_schemas.fns.get("main") {
        if schema.args.len() != public_args.len() {
            return Err(CliError::InvalidInput(format!(
                "main typed schema expects {} args, but CLI provided {}",
                schema.args.len(),
                public_args.len(),
            )));
        }

        let mut out = Vec::new();
        for (idx, ((role, ty), vmarg)) in schema.args.iter().zip(public_args).enumerate() {
            if matches!(role, compiler::ArgRole::Let) {
                let pos = idx + 1;
                match ty {
                    compiler::ScalarType::U64 => match vmarg {
                        VmArg::U64(_) => out.push(vmarg.clone()),
                        _ => {
                            return Err(CliError::InvalidInput(format!(
                                "main arg #{pos}: expected u64 value for type 'u64'",
                            )));
                        }
                    },
                    compiler::ScalarType::U128 => match vmarg {
                        VmArg::U128(_) => out.push(vmarg.clone()),
                        _ => {
                            return Err(CliError::InvalidInput(format!(
                                "main arg #{pos}: expected u128 value for type 'u128'",
                            )));
                        }
                    },
                    compiler::ScalarType::Bytes32 => match vmarg {
                        VmArg::Bytes32(_) => out.push(vmarg.clone()),
                        _ => {
                            return Err(CliError::InvalidInput(format!(
                                "main arg #{pos}: expected bytes32 value for type 'bytes32'",
                            )));
                        }
                    },
                }
            }
        }

        out
    } else {
        Vec::new()
    };

    // Build features from program ops and bind typed VM args.
    // Ensures Merkle/RAM/VM/POSEIDON/SPONGE flags are correct.
    PublicInputsBuilder::from_program(program)
        .with_public_args(public_args)
        .with_main_args(&main_args)
        .with_secret_args(secret_args)
        .build()
        .map_err(CliError::Build)
}

/// Validate that CLI-provided public arguments
/// for `main` are consistent with the optional
/// `typed-fn` schema.
///
/// Current policy:
/// - if no schema for `main` is present, no extra checks;
/// - arity of schema and CLI args must match;
/// - for `ArgRole::Const`, only `u64` is supported at CLI level
///   (both in schema type and actual value);
/// - for `ArgRole::Let`, the following types are supported
///   as runtime public inputs and CLI values:
///   `u64`, `u128`, `bytes32`.
fn validate_main_args_against_schema(
    program: &compiler::Program,
    public_args: &[VmArg],
) -> Result<(), CliError> {
    let Some(schema) = program.type_schemas.fns.get("main") else {
        return Ok(());
    };

    if schema.args.len() != public_args.len() {
        return Err(CliError::InvalidInput(format!(
            "main typed schema expects {} args, but CLI provided {}",
            schema.args.len(),
            public_args.len(),
        )));
    }

    for (idx, (role, ty)) in schema.args.iter().enumerate() {
        let pos = idx + 1;
        let vmarg = &public_args[idx];

        match role {
            compiler::ArgRole::Const => {
                // For now, const args must stay as u64 so
                // they can be passed to the compiler entry.
                if !matches!(ty, compiler::ScalarType::U64) {
                    let ty_str = match ty {
                        compiler::ScalarType::U64 => "u64",
                        compiler::ScalarType::U128 => "u128",
                        compiler::ScalarType::Bytes32 => "bytes32",
                    };

                    return Err(CliError::InvalidInput(format!(
                        "main arg #{pos}: const args of type '{ty_str}' are not supported for CLI public args; expected 'u64'",
                    )));
                }

                match vmarg {
                    VmArg::U64(_) => {}
                    _ => {
                        return Err(CliError::InvalidInput(format!(
                            "main arg #{pos}: const args currently support only u64 values",
                        )));
                    }
                }
            }
            compiler::ArgRole::Let => match ty {
                compiler::ScalarType::U64 => match vmarg {
                    VmArg::U64(_) => {}
                    _ => {
                        return Err(CliError::InvalidInput(format!(
                            "main arg #{pos}: expected u64 value for type 'u64'",
                        )));
                    }
                },
                compiler::ScalarType::U128 => match vmarg {
                    VmArg::U128(_) => {}
                    _ => {
                        return Err(CliError::InvalidInput(format!(
                            "main arg #{pos}: expected u128 value for type 'u128'",
                        )));
                    }
                },
                compiler::ScalarType::Bytes32 => match vmarg {
                    VmArg::Bytes32(_) => {}
                    _ => {
                        return Err(CliError::InvalidInput(format!(
                            "main arg #{pos}: expected bytes32 value for type 'bytes32'",
                        )));
                    }
                },
            },
        }
    }

    Ok(())
}

fn parse_u64_literal(s: &str) -> Result<u64, CliError> {
    let s = s.trim();
    if let Some(rest) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
        u64::from_str_radix(rest, 16)
            .map_err(|e| CliError::InvalidInput(format!("invalid u64 hex '{s}': {e}")))
    } else {
        s.parse::<u64>()
            .map_err(|e| CliError::InvalidInput(format!("invalid u64 '{s}': {e}")))
    }
}

fn parse_u128_literal(s: &str) -> Result<u128, CliError> {
    let s = s.trim();
    if let Some(rest) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
        u128::from_str_radix(rest, 16)
            .map_err(|e| CliError::InvalidInput(format!("invalid u128 hex '{s}': {e}")))
    } else {
        s.parse::<u128>()
            .map_err(|e| CliError::InvalidInput(format!("invalid u128 '{s}': {e}")))
    }
}

fn parse_bytes32_literal(s: &str) -> Result<[u8; 32], CliError> {
    let s = s.trim();
    let hex_str = s
        .strip_prefix("0x")
        .or_else(|| s.strip_prefix("0X"))
        .unwrap_or(s);

    let decoded = hex::decode(hex_str)?;
    if decoded.len() > 32 {
        return Err(CliError::InvalidInput(format!(
            "bytes32 literal too long: {} bytes (max 32)",
            decoded.len()
        )));
    }

    // Little-endian-style layout
    let mut out = [0u8; 32];
    out[..decoded.len()].copy_from_slice(&decoded);

    Ok(out)
}

fn parse_vm_arg(raw: &str) -> Result<VmArg, CliError> {
    let raw = raw.trim();
    let (ty, val) = raw.split_once(':').ok_or_else(|| {
        CliError::InvalidInput(format!(
            "invalid arg '{raw}': expected <type>:<value>, e.g. u64:3"
        ))
    })?;

    match ty {
        "u64" => Ok(VmArg::U64(parse_u64_literal(val)?)),
        "u128" => Ok(VmArg::U128(parse_u128_literal(val)?)),
        "bytes32" => Ok(VmArg::Bytes32(parse_bytes32_literal(val)?)),
        other => Err(CliError::InvalidInput(format!(
            "invalid arg type '{other}'; expected u64,u128,bytes32",
        ))),
    }
}

fn parse_public_args(raws: &[String]) -> Result<(Vec<VmArg>, Vec<u64>), CliError> {
    let mut vmargs = Vec::with_capacity(raws.len());
    let mut u64s = Vec::with_capacity(raws.len());

    for raw in raws {
        let arg = parse_vm_arg(raw)?;
        match arg {
            VmArg::U64(v) => {
                vmargs.push(VmArg::U64(v));
                u64s.push(v);
            }
            VmArg::U128(v128) => {
                // For now, compile-time entry supports only
                // 64-bit immediates. Allow u128 values that
                // fit into u64 and reject larger ones so we
                // never silently truncate.
                if v128 > u64::MAX as u128 {
                    return Err(CliError::InvalidInput(format!(
                        "u128 public arg '{raw}' does not fit into 64 bits; full 128-bit compile-time args are not supported yet",
                    )));
                }

                let v64 = v128 as u64;
                vmargs.push(VmArg::U128(v128));
                u64s.push(v64);
            }
            VmArg::Bytes32(bytes) => {
                // Map bytes32 to a u64 parameter for now by
                // requiring that high bytes are zero and using
                // the first 8 bytes as little-endian integer.
                if bytes[8..].iter().any(|b| *b != 0) {
                    return Err(CliError::InvalidInput(format!(
                        "bytes32 public arg '{raw}' must have bytes[8..32]=0 for now; full 32-byte compile-time args are not supported yet",
                    )));
                }

                let mut lo = [0u8; 8];
                lo.copy_from_slice(&bytes[0..8]);

                let v64 = u64::from_le_bytes(lo);
                vmargs.push(VmArg::Bytes32(bytes));
                u64s.push(v64);
            }
        }
    }

    Ok((vmargs, u64s))
}

fn parse_secret_args(raws: &[String]) -> Result<Vec<VmArg>, CliError> {
    let mut out = Vec::with_capacity(raws.len());
    for raw in raws {
        out.push(parse_vm_arg(raw)?);
    }

    Ok(out)
}

fn resolve_preflight_mode(p: PreflightArg) -> PreflightMode {
    match p {
        PreflightArg::Off => PreflightMode::Off,
        PreflightArg::Console => PreflightMode::Console,
        PreflightArg::Json => PreflightMode::Json,
        PreflightArg::Auto => {
            if cfg!(debug_assertions) {
                PreflightMode::Console
            } else {
                PreflightMode::Off
            }
        }
    }
}

fn init_logging(level: Option<&str>) {
    INIT_LOGGING.call_once(|| {
        if tracing::dispatcher::has_been_set() {
            return;
        }

        let env = match level {
            Some(l) if !l.is_empty() => l.to_string(),
            _ => std::env::var("RUST_LOG").unwrap_or_else(|_| "info".to_string()),
        };

        let filter = tracing_subscriber::EnvFilter::try_new(env.clone()).unwrap_or_else(|e| {
            eprintln!(
                r"
WARN: invalid RUST_LOG/log_level '{env}': {e};
falling back to 'info'"
            );
            tracing_subscriber::EnvFilter::new("info")
        });

        let _ = tracing_subscriber::fmt()
            .with_env_filter(filter)
            .with_target(true)
            .with_thread_ids(false)
            .with_thread_names(false)
            .compact()
            .try_init();
    });
}

fn try_main(cli: Cli) -> Result<(), CliError> {
    let security_bits = normalize_security_bits(cli.security_bits)?;

    match cli.command {
        Command::Run(args) => {
            run::cmd_run(args, cli.json, cli.max_bytes, cli.preflight, security_bits)
        }
        Command::Prove(args) => {
            prove::cmd_prove(args, cli.json, cli.max_bytes, cli.preflight, security_bits)
        }
        Command::Verify(args) => verify::cmd_verify(args, cli.json, cli.max_bytes, security_bits),
        Command::Repl => repl::cmd_repl(),
    }
}

fn main() {
    let cli = Cli::parse();
    init_logging(Some(&cli.log_level));

    let code = match try_main(cli.clone()) {
        Ok(()) => 0,
        Err(e) => {
            let code = e.code();
            if cli.json {
                println!(
                    "{}",
                    serde_json::json!({ "ok": false, "error": e.to_string(), "code": code })
                );
            } else {
                eprintln!("error: {e}");
            }

            code
        }
    };

    std::process::exit(code);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::repl::extract_docs;

    #[test]
    fn parse_vm_arg_u64_dec_and_hex() {
        let a = parse_vm_arg("u64:10").unwrap();
        assert!(matches!(a, VmArg::U64(10)));

        let b = parse_vm_arg("u64:0xa").unwrap();
        assert!(matches!(b, VmArg::U64(10)));
    }

    #[test]
    fn parse_vm_arg_u128_and_bytes32() {
        let a = parse_vm_arg("u128:340282366920938463463374607431768211455").unwrap();
        assert!(matches!(a, VmArg::U128(_)));

        let b = parse_vm_arg("bytes32:0x01ff").unwrap();
        match b {
            VmArg::Bytes32(arr) => {
                assert_eq!(arr[0], 0x01);
                assert_eq!(arr[1], 0xff);
            }
            _ => panic!("expected bytes32"),
        }
    }

    #[test]
    fn parse_public_args_u64_ok() {
        let (vmargs, u64s) = parse_public_args(&["u64:7".to_string()]).unwrap();
        assert_eq!(u64s, vec![7]);
        assert!(matches!(vmargs[0], VmArg::U64(7)));
    }

    #[test]
    fn parse_public_args_u128_fits_into_u64_ok() {
        let (vmargs, u64s) = parse_public_args(&["u128:7".to_string()]).unwrap();
        assert_eq!(u64s, vec![7]);
        assert!(matches!(vmargs[0], VmArg::U128(7)));
    }

    #[test]
    fn parse_public_args_bytes32_low_ok() {
        let (vmargs, u64s) =
            parse_public_args(&["bytes32:0x0100000000000000".to_string()]).unwrap();
        assert_eq!(u64s, vec![1]);

        match vmargs[0] {
            VmArg::Bytes32(arr) => {
                assert_eq!(arr[0], 0x01);
                assert!(arr[1..].iter().all(|b| *b == 0));
            }
            _ => panic!("expected bytes32"),
        }
    }

    #[test]
    fn parse_public_args_u128_overflow_fails() {
        let err = parse_public_args(&["u128:18446744073709551616".to_string()]).unwrap_err();
        let msg = err.to_string();
        assert!(msg.contains("does not fit into 64 bits"), "msg={msg}");
    }

    #[test]
    fn parse_public_args_bytes32_high_nonzero_fails() {
        let err = parse_public_args(&["bytes32:0x01000000000000000100".to_string()]).unwrap_err();
        let msg = err.to_string();
        assert!(msg.contains("must have bytes[8..32]=0"), "msg={msg}");
    }

    #[test]
    fn parse_vm_arg_invalid_type_fails() {
        let err = parse_vm_arg("foo:1").unwrap_err();
        let msg = err.to_string();
        assert!(msg.contains("invalid arg type"), "msg={msg}");
    }

    #[test]
    fn extract_docs_simple_def() {
        let src = ";; add two numbers\n(def (add2 x y) (+ x y))\n";
        let docs = extract_docs(src);
        assert_eq!(docs.len(), 1);
        assert_eq!(docs.get("add2").unwrap(), "add two numbers");
    }

    #[test]
    fn extract_docs_multiple_lines_and_blank() {
        let src = ";; first line\n;; second line\n;;\n(def foo 42)\n";
        let docs = extract_docs(src);
        let doc = docs.get("foo").unwrap();
        assert!(doc.contains("first line"));
        assert!(doc.contains("second line"));
    }
}

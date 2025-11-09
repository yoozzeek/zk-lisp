// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use clap::{Parser, Subcommand};
use std::fs;
use std::io::{self, Write};
use std::path::PathBuf;
use thiserror::Error;
use winterfell::math::StarkField;
use winterfell::{BatchingMethod, FieldExtension, Proof, ProofOptions, Trace};
use zk_lisp::{PreflightMode, compiler, error, prove};

#[derive(Parser, Debug, Clone)]
#[command(
    name = "zk-lisp",
    about = r"# zk-lisp CLI
# Copyright (c) Andrei Kochergin. All rights reserved.

Lisp dialect and compiler for running zero-knowledge (ZK)
programs, executable on an experimental virtual machine built
on top of the Winterfell STARK prover and verifier.",
    version
)]
struct Cli {
    /// Global JSON output
    #[arg(long, global = true, default_value_t = false)]
    json: bool,
    /// Global log level (trace|debug|info|warn|error)
    #[arg(long, global = true, default_value = "info")]
    log_level: String,
    /// Max input file size in bytes
    #[arg(long, global = true, default_value_t = 1_048_576)]
    max_bytes: usize,
    /// Preflight mode:
    /// off|console|json|auto (auto: console in debug, off in release)
    #[arg(long, global = true, default_value = "auto")]
    preflight: String,
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
    /// Arguments for main (repeat or comma-separated via --args)
    #[arg(long = "arg", value_delimiter = ',')]
    args: Vec<u64>,
}

#[derive(clap::Args, Debug, Clone)]
struct ProveArgs {
    /// Path to .zlisp file
    path: PathBuf,
    /// Arguments for main
    #[arg(long = "arg", value_delimiter = ',')]
    args: Vec<u64>,
    /// Number of FRI queries
    #[arg(long, default_value_t = 1)]
    queries: u8,
    /// Blowup factor
    #[arg(long, default_value_t = 8)]
    blowup: u8,
    /// Grinding factor
    #[arg(long, default_value_t = 0)]
    grind: u32,
    /// Optional deterministic seed
    #[arg(long)]
    seed: Option<u64>,
    /// Write proof to file (binary);
    /// still prints hex to stdout unless --quiet
    #[arg(long)]
    out: Option<PathBuf>,
    /// Quiet mode (suppress non-essential output)
    #[arg(long, default_value_t = false)]
    quiet: bool,
}

#[derive(clap::Args, Debug, Clone)]
struct VerifyArgs {
    /// Proof hex string or @path to binary proof file
    proof: String,
    /// Path to .zlisp file
    path: PathBuf,
    /// Arguments for main must match the ones
    /// used for proof (except secrets).
    #[arg(long = "arg", value_delimiter = ',')]
    args: Vec<u64>,

    /// Number of FRI queries (must match)
    #[arg(long, default_value_t = 1)]
    queries: u8,
    /// Blowup factor (must match)
    #[arg(long, default_value_t = 8)]
    blowup: u8,
    /// Grinding factor (must match)
    #[arg(long, default_value_t = 0)]
    grind: u32,
    /// Optional seed
    #[arg(long)]
    seed: Option<u64>,
}

#[derive(Error, Debug)]
enum CliError {
    #[error("invalid input: {0}")]
    InvalidInput(String),
    #[error("compile error")]
    Compile(#[from] compiler::Error),
    #[error("io error")]
    Io(#[from] io::Error),
    #[error("io error: {source}: {path}")]
    IoPath {
        #[source]
        source: io::Error,
        path: PathBuf,
    },
    #[error("prove error")]
    Prover(#[from] prove::Error),
    #[error("verify error")]
    Verify(prove::Error),
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

fn try_main(cli: Cli) -> Result<(), CliError> {
    match cli.command {
        Command::Run(args) => cmd_run(args, cli.json, cli.max_bytes, &cli.preflight),
        Command::Prove(args) => cmd_prove(args, cli.json, cli.max_bytes, &cli.preflight),
        Command::Verify(args) => cmd_verify(args, cli.json, cli.max_bytes),
        Command::Repl => cmd_repl(),
    }
}

fn proof_opts(queries: u8, blowup: u8, grind: u32) -> ProofOptions {
    ProofOptions::new(
        queries as usize,
        blowup as usize,
        grind,
        FieldExtension::None,
        2,
        1,
        BatchingMethod::Linear,
        BatchingMethod::Linear,
    )
}

fn read_program(path: &PathBuf, max_bytes: usize) -> Result<String, CliError> {
    let meta = fs::metadata(path).map_err(|e| CliError::IoPath {
        source: e,
        path: path.clone(),
    })?;

    if meta.len() as usize > max_bytes {
        return Err(CliError::InvalidInput(format!(
            "file too large: {} bytes (limit {})",
            meta.len(),
            max_bytes
        )));
    }

    let s = fs::read_to_string(path).map_err(|e| CliError::IoPath {
        source: e,
        path: path.clone(),
    })?;

    Ok(s)
}

fn build_pi_for_program(program: &zk_lisp::ir::Program, args: &[u64]) -> zk_lisp::pi::PublicInputs {
    use zk_lisp::ir::Op;
    let mut mask: u64 = 0;

    // VM is used by any ALU/select/eq/sponge op
    if program.ops.iter().any(|op| {
        matches!(
            op,
            Op::Const { .. }
                | Op::Mov { .. }
                | Op::Add { .. }
                | Op::Sub { .. }
                | Op::Mul { .. }
                | Op::Neg { .. }
                | Op::Eq { .. }
                | Op::Select { .. }
                | Op::Assert { .. }
                | Op::SAbsorb2 { .. }
                | Op::SSqueeze { .. }
        )
    }) {
        mask |= zk_lisp::pi::FM_VM;
    }

    // Poseidon when sponge ops or KV appear
    if program.ops.iter().any(|op| {
        matches!(
            op,
            Op::SAbsorb2 { .. } | Op::SSqueeze { .. } | Op::KvMap { .. } | Op::KvFinal
        )
    }) {
        mask |= zk_lisp::pi::FM_POSEIDON;
    }

    // Sponge feature when
    // SAbsorb2/SSqueeze appear.
    if program
        .ops
        .iter()
        .any(|op| matches!(op, Op::SAbsorb2 { .. } | Op::SSqueeze { .. }))
    {
        mask |= zk_lisp::pi::FM_SPONGE;
    }

    // KV when kv ops appear
    if program
        .ops
        .iter()
        .any(|op| matches!(op, Op::KvMap { .. } | Op::KvFinal))
    {
        mask |= zk_lisp::pi::FM_KV;
    }

    zk_lisp::pi::PublicInputs {
        feature_mask: mask,
        program_commitment: program.commitment,
        vm_args: args.to_vec(),
        ..Default::default()
    }
}

fn cmd_run(args: RunArgs, json: bool, max_bytes: usize, pf: &str) -> Result<(), CliError> {
    let src = read_program(&args.path, max_bytes)?;
    let program = compiler::compile_entry(&src, &args.args)?;

    let pi = build_pi_for_program(&program, &args.args);
    // Build trace with VM args
    let trace = prove::build_trace_with_pi(&program, &pi)?;

    let pf_mode = parse_preflight_mode(pf);
    if !matches!(pf_mode, PreflightMode::Off) {
        let opts = proof_opts(1, 8, 0);
        prove::preflight_check(pf_mode, &opts, &pi, &trace)?;
    }

    // Compute VM output position and value
    let (out_reg, out_row) = prove::compute_vm_output(&trace);
    let cols = zk_lisp::layout::Columns::baseline();
    let val = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    let val_u128: u128 = val.as_int();

    if json {
        println!(
            "{}",
            serde_json::json!({
                "ok": true,
                "result_dec": val_u128.to_string(),
                "result_hex": format!("0x{:032x}", val_u128),
                "out_reg": out_reg,
                "out_row": out_row,
                "trace_len": trace.length(),
            })
        );
    } else {
        let rows = trace.length();
        println!(
            "result: {val_u128} (0x{val_u128:032x}), out_reg={out_reg}, out_row={out_row}, rows={rows}"
        );
    }

    Ok(())
}

fn cmd_prove(args: ProveArgs, json: bool, max_bytes: usize, pf: &str) -> Result<(), CliError> {
    if args.seed.is_some() {
        return Err(CliError::InvalidInput(
            "seed is not supported yet".to_string(),
        ));
    }

    let src = read_program(&args.path, max_bytes)?;
    let program = compiler::compile_entry(&src, &args.args)?;

    let mut pi = build_pi_for_program(&program, &args.args);
    let trace = prove::build_trace_with_pi(&program, &pi)?;

    // Fill dynamic PI parts (kv mask)
    if (pi.feature_mask & zk_lisp::pi::FM_KV) != 0 {
        pi.kv_levels_mask = prove::compute_kv_levels_mask(&trace);
    }

    // VM output position
    let (out_reg, out_row) = prove::compute_vm_output(&trace);
    pi.vm_out_reg = out_reg;
    pi.vm_out_row = out_row;

    let opts = proof_opts(args.queries, args.blowup, args.grind);
    let pf_mode = parse_preflight_mode(pf);
    let prover = prove::ZkProver::new(opts.clone(), pi.clone()).with_preflight_mode(pf_mode);

    let proof = prover.prove(trace)?;

    // Serialize proof to bytes and hex
    let proof_bytes = proof_to_bytes(&proof)?;
    if let Some(path) = args.out {
        if let Err(e) = fs::write(&path, &proof_bytes) {
            return Err(CliError::IoPath { source: e, path });
        }
    }

    let proof_hex = hex::encode(&proof_bytes);

    if !args.quiet {
        if json {
            println!(
                "{}",
                serde_json::json!({
                    "ok": true,
                    "proof_hex": proof_hex,
                    "opts": {"queries": args.queries, "blowup": args.blowup, "grind": args.grind},
                    "commitment": format!("0x{:02x?}", program.commitment),
                })
            );
        } else {
            println!("proof(hex): {proof_hex}");
        }
    }

    Ok(())
}

fn cmd_verify(args: VerifyArgs, json: bool, max_bytes: usize) -> Result<(), CliError> {
    let proof_bytes = if let Some(path) = args.proof.strip_prefix('@') {
        let meta = fs::metadata(path).map_err(|e| CliError::IoPath {
            source: e,
            path: PathBuf::from(path),
        })?;
        if meta.len() as usize > max_bytes {
            return Err(CliError::InvalidInput(format!(
                "proof file too large: {} bytes (limit {})",
                meta.len(),
                max_bytes
            )));
        }

        fs::read(path).map_err(|e| CliError::IoPath {
            source: e,
            path: PathBuf::from(path),
        })?
    } else {
        let s = args.proof.strip_prefix("0x").unwrap_or(&args.proof);
        if s.len() / 2 > max_bytes {
            return Err(CliError::InvalidInput(format!(
                "proof hex too large: {} bytes (limit {})",
                s.len() / 2,
                max_bytes
            )));
        }

        hex::decode(s)?
    };

    let src = read_program(&args.path, max_bytes)?;
    let program = compiler::compile_entry(&src, &args.args)?;

    // Rebuild PI similarly to Prove
    let mut pi = build_pi_for_program(&program, &args.args);
    let trace = prove::build_trace_with_pi(&program, &pi)?;

    if (pi.feature_mask & zk_lisp::pi::FM_KV) != 0 {
        pi.kv_levels_mask = prove::compute_kv_levels_mask(&trace);
    }

    // VM output location
    let (out_reg, out_row) = prove::compute_vm_output(&trace);
    pi.vm_out_reg = out_reg;
    pi.vm_out_row = out_row;

    let proof = proof_from_bytes(&proof_bytes)?;

    let opts = proof_opts(args.queries, args.blowup, args.grind);
    prove::verify_proof(proof, pi, &opts).map_err(CliError::Verify)?;

    if json {
        println!(
            "{}",
            serde_json::json!({
                "ok": true,
                "opts": {
                    "queries": args.queries,
                    "blowup": args.blowup,
                    "grind": args.grind,
                }
            })
        );
    } else {
        println!("OK");
    }

    Ok(())
}

fn cmd_repl() -> Result<(), CliError> {
    zk_lisp::logging::init_with_level(None);

    println!(
        r"zk-lisp REPL Copyright (C) 2025  Andrei Kochergin

  Type :help for help. Ctrl-D to exit.

  This program comes with ABSOLUTELY NO WARRANTY;
  This is free software, and you are welcome to
  redistribute it under certain conditions;"
    );

    let mut _buf = String::new();
    let mut line = String::new();

    loop {
        print!("> ");

        io::stdout().flush().ok();
        line.clear();

        let n = io::stdin().read_line(&mut line)?;
        if n == 0 {
            // EOF
            break;
        }

        let s = line.trim();
        if s.is_empty() {
            continue;
        }
        if s == ":quit" || s == ":q" {
            break;
        }
        if s == ":help" {
            println!(
                r"Commands:
  :help       - this help
  :quit, :q   - exit
  :load PATH  - load file and set as current program
  :args a,b   - set args (comma-separated) for main
  expr        - evaluate expr in a (def (main) expr) context"
            );
            continue;
        }

        if let Some(rest) = s.strip_prefix(":load ") {
            match fs::read_to_string(rest) {
                Ok(src) => {
                    _buf = src;
                    println!("OK loaded {rest}");
                }
                Err(e) => println!("error: load failed: {e}"),
            }

            continue;
        }

        if let Some(rest) = s.strip_prefix(":args ") {
            let mut args = Vec::new();

            for part in rest.split(',') {
                if part.trim().is_empty() {
                    continue;
                }

                match part.trim().parse::<u64>() {
                    Ok(v) => args.push(v),
                    Err(e) => {
                        println!("error: bad arg '{part}': {e}");
                        args.clear();
                        break;
                    }
                }
            }

            if !args.is_empty() {
                println!("args set: {args:?}");
            }

            // store in env? keep simple: ephemeral per eval
            continue;
        }

        // Evaluate one-line expression by wrapping into (def (main) <expr>)
        let wrapped = format!("(def (main) {s})");
        match compiler::compile_entry(&wrapped, &[]) {
            Err(e) => println!("error: compile: {e}"),
            Ok(program) => {
                let pi = build_pi_for_program(&program, &[]);
                match prove::build_trace_with_pi(&program, &pi) {
                    Err(e) => println!("error: build trace: {e}"),
                    Ok(trace) => {
                        let (out_reg, out_row) = prove::compute_vm_output(&trace);
                        let cols = zk_lisp::layout::Columns::baseline();
                        let val = trace.get(cols.r_index(out_reg as usize), out_row as usize);
                        let v: u128 = val.as_int();

                        println!("= {v} (0x{v:032x})");
                    }
                }
            }
        }
    }

    Ok(())
}

fn proof_to_bytes(proof: &Proof) -> Result<Vec<u8>, CliError> {
    #[allow(clippy::let_and_return)]
    let bytes = proof.to_bytes();
    Ok(bytes)
}

fn proof_from_bytes(bytes: &[u8]) -> Result<Proof, CliError> {
    let p = Proof::from_bytes(bytes)
        .map_err(|e| CliError::InvalidInput(format!("invalid proof bytes: {e}")))?;
    Ok(p)
}

fn parse_preflight_mode(s: &str) -> PreflightMode {
    match s.to_ascii_lowercase().as_str() {
        "off" => PreflightMode::Off,
        "console" => PreflightMode::Console,
        "json" => PreflightMode::Json,
        _ => {
            // auto
            if cfg!(debug_assertions) {
                PreflightMode::Console
            } else {
                PreflightMode::Off
            }
        }
    }
}

fn main() {
    let cli = Cli::parse();
    zk_lisp::logging::init_with_level(Some(&cli.log_level));

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

// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp.
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

use base64::Engine;
use clap::{Parser, Subcommand};
use rustyline::{DefaultEditor, error::ReadlineError};
use std::collections::BTreeSet;
use std::fs;
use std::io::{self};
use std::path::PathBuf;
use thiserror::Error;

use zk_lisp_compiler as compiler;
use zk_lisp_proof::frontend::{self, PreflightMode};
use zk_lisp_proof::pi::{PublicInputs, PublicInputsBuilder};
use zk_lisp_proof::{ProverOptions, ZkField, error};
use zk_lisp_proof_winterfell::{WinterfellBackend, prove};

// Max file size for REPL
// operations (load/verify @PATH)
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
        default_value = "info",
        value_parser = ["trace","debug","info","warn","error"],
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
    #[arg(long, default_value_t = 64)]
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
    /// Proof base64 string or @path to binary proof file
    proof: String,
    /// Path to .zlisp file
    path: PathBuf,
    /// Arguments for main must match the ones
    /// used for proof (except secrets).
    #[arg(long = "arg", value_delimiter = ',')]
    args: Vec<u64>,

    /// Number of FRI queries
    #[arg(long, default_value_t = 64)]
    queries: u8,
    /// Blowup factor
    #[arg(long, default_value_t = 8)]
    blowup: u8,
    /// Grinding factor
    #[arg(long, default_value_t = 0)]
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
    #[error("prove error: {0}")]
    Prover(#[from] prove::Error),
    #[error("verify error: {0}")]
    Verify(#[source] prove::Error),
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

fn try_main(cli: Cli) -> Result<(), CliError> {
    let security_bits = normalize_security_bits(cli.security_bits)?;

    match cli.command {
        Command::Run(args) => cmd_run(args, cli.json, cli.max_bytes, cli.preflight, security_bits),
        Command::Prove(args) => {
            cmd_prove(args, cli.json, cli.max_bytes, cli.preflight, security_bits)
        }
        Command::Verify(args) => cmd_verify(args, cli.json, cli.max_bytes, security_bits),
        Command::Repl => cmd_repl(),
    }
}

fn proof_opts(queries: u8, blowup: u8, grind: u32, security_bits: Option<u32>) -> ProverOptions {
    let base = ProverOptions::default();
    let min_security_bits = security_bits.unwrap_or(base.min_security_bits);

    ProverOptions {
        queries,
        blowup,
        grind,
        min_security_bits,
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
    args: &[u64],
) -> Result<PublicInputs, CliError> {
    // Build features from program ops and bind VM args.
    // Ensures Merkle/RAM/VM/POSEIDON/SPONGE flags are correct.
    PublicInputsBuilder::from_program(program)
        .with_args(args)
        .build()
        .map_err(CliError::Build)
}

fn cmd_run(
    args: RunArgs,
    json: bool,
    max_bytes: usize,
    pf: PreflightArg,
    security_bits: Option<u32>,
) -> Result<(), CliError> {
    let src = read_program(&args.path, max_bytes)?;
    let program = compiler::compile_entry(&src, &args.args)?;
    let pi = build_pi_for_program(&program, &args.args)?;

    let pf_mode = resolve_preflight_mode(pf);
    if !matches!(pf_mode, PreflightMode::Off) {
        let opts = proof_opts(1, 8, 0, security_bits);
        frontend::preflight::<WinterfellBackend>(pf_mode, &opts, &program, &pi)
            .map_err(CliError::Prover)?;
    }

    // Compute VM output position
    // and value via backend.
    let run_res = frontend::run_vm::<WinterfellBackend>(&program, &pi).map_err(CliError::Prover)?;
    let out_reg = run_res.out_reg;
    let out_row = run_res.out_row;
    let val_u128: u128 = ZkField::to_u128(&run_res.value);
    let metrics = program.compiler_metrics;

    if json {
        println!(
            "{}",
            serde_json::json!({
                "ok": true,
                "result_dec": val_u128.to_string(),
                "result_hex": format!("0x{:032x}", val_u128),
                "out_reg": out_reg,
                "out_row": out_row,
                "trace_len": run_res.trace_len,
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
        println!(
            "result: {val_u128} (0x{val_u128:032x}), out_reg={out_reg}, out_row={out_row}, rows={rows}"
        );

        println!(
            "metrics: peak_live={} reuse_dst={} su_reorders={} balanced_chains={} mov_elided={}",
            metrics.peak_live,
            metrics.reuse_dst,
            metrics.su_reorders,
            metrics.balanced_chains,
            metrics.mov_elided
        );
    }

    Ok(())
}

fn cmd_prove(
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

    let src = read_program(&args.path, max_bytes)?;
    let program = compiler::compile_entry(&src, &args.args)?;
    let pi = build_pi_for_program(&program, &args.args)?;

    let opts = proof_opts(args.queries, args.blowup, args.grind, security_bits);
    let pf_mode = resolve_preflight_mode(pf);

    if !matches!(pf_mode, PreflightMode::Off) {
        frontend::preflight::<WinterfellBackend>(pf_mode, &opts, &program, &pi)
            .map_err(CliError::Prover)?;
    }

    let proof =
        frontend::prove::<WinterfellBackend>(&program, &pi, &opts).map_err(CliError::Prover)?;

    // Serialize proof to bytes
    let proof_bytes =
        frontend::encode_proof::<WinterfellBackend>(&proof).map_err(CliError::Prover)?;
    if let Some(path) = args.out {
        if let Err(e) = fs::write(&path, &proof_bytes) {
            return Err(CliError::IoPath { source: e, path });
        }
    }

    if !args.quiet {
        let proof_b64 = base64::engine::general_purpose::STANDARD.encode(&proof_bytes);

        if json {
            println!(
                "{}",
                serde_json::json!({
                    "ok": true,
                    "proof_b64": proof_b64,
                    "opts": {"queries": args.queries, "blowup": args.blowup, "grind": args.grind},
                    "commitment": format!("0x{:02x?}", program.commitment),
                })
            );
        } else {
            // Print a short preview
            // to avoid huge stdout.
            let preview = format!("{} (len={} bytes)", proof_b64, proof_bytes.len());
            println!("proof: {preview}");
        }
    }

    Ok(())
}

fn cmd_verify(
    args: VerifyArgs,
    json: bool,
    max_bytes: usize,
    security_bits: Option<u32>,
) -> Result<(), CliError> {
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
        // Base64 only
        let approx = (args.proof.len() / 4) * 3;
        if approx > max_bytes {
            return Err(CliError::InvalidInput(format!(
                "proof base64 too large: approx {approx} bytes (limit {max_bytes})"
            )));
        }

        base64::engine::general_purpose::STANDARD
            .decode(args.proof.as_bytes())
            .map_err(|e| CliError::InvalidInput(format!("invalid base64: {e}")))?
    };

    let src = read_program(&args.path, max_bytes)?;
    let program = compiler::compile_entry(&src, &args.args)?;

    // Rebuild PI similarly to Prove
    let pi = build_pi_for_program(&program, &args.args)?;
    let proof = frontend::decode_proof::<WinterfellBackend>(&proof_bytes)
        .map_err(|e| CliError::InvalidInput(format!("invalid proof encoding: {e}")))?;

    let opts = proof_opts(args.queries, args.blowup, args.grind, security_bits);
    frontend::verify::<WinterfellBackend>(proof, &program, &pi, &opts).map_err(CliError::Verify)?;

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

// Live session state
#[derive(Default, Clone)]
struct Session {
    base_src: String,   // from :load
    forms: Vec<String>, // live appended forms
    last_expr: Option<String>,
}

impl Session {
    fn reset(&mut self) {
        self.base_src.clear();
        self.forms.clear();
        self.last_expr = None;
    }

    fn add_form(&mut self, s: String) {
        self.forms.push(s);
    }

    fn combined_with_expr(&self, expr: &str) -> String {
        let mut out = String::new();
        if !self.base_src.trim().is_empty() {
            out.push_str(&self.base_src);
            out.push('\n');
        }

        if !self.forms.is_empty() {
            for f in &self.forms {
                out.push_str(f);
                if !f.ends_with('\n') {
                    out.push('\n');
                }
            }
        }

        // Allow bare symbol convenience:
        // turn "foo" into "(foo)"
        let trimmed = expr.trim();
        let expr_norm = if is_bare_symbol(trimmed) {
            format!("({trimmed})")
        } else {
            trimmed.to_string()
        };

        out.push_str(&format!("(def (main) {expr_norm})\n"));

        out
    }
}

fn cmd_repl() -> Result<(), CliError> {
    init_logging(None);

    println!(
        r"zk-lisp REPL Copyright (C) 2025  Andrei Kochergin

  Type :help for help. Ctrl-D to exit.

  This program comes with ABSOLUTELY NO WARRANTY;
  This is free software, and you are welcome to
  redistribute it under certain conditions;"
    );

    let mut session = Session::default();
    let mut rl =
        DefaultEditor::new().map_err(|e| CliError::InvalidInput(format!("repl init: {e}")))?;

    // History path: $HOME/.zk-lisp_history (fallback: ./.zk-lisp_history)
    let hist_path = std::env::var("HOME")
        .map(|h| format!("{h}/.zk-lisp_history"))
        .unwrap_or_else(|_| ".zk-lisp_history".into());
    let _ = rl.load_history(&hist_path);

    let mut acc = String::new();
    let mut need_more = false;

    loop {
        let prompt = if need_more { ".. " } else { "> " };
        let line = match rl.readline(prompt) {
            Ok(s) => s,
            Err(ReadlineError::Interrupted) => {
                // Ctrl-C: clear current buffer and continue
                acc.clear();
                need_more = false;
                continue;
            }
            Err(ReadlineError::Eof) => break,
            Err(e) => {
                println!("error: io: {e}");
                continue;
            }
        };

        // accumulate for multiline
        acc.push_str(&line);
        acc.push('\n');

        // enforce size cap to avoid runaway buffers
        if acc.len() > REPL_MAX_BYTES {
            println!("error: input too large (>{REPL_MAX_BYTES} bytes); buffer cleared");

            acc.clear();
            need_more = false;

            continue;
        }

        let bal = paren_balance(&acc);
        need_more = bal > 0;

        if need_more {
            continue;
        }

        // We have a full command or expr in acc
        let input_owned = acc.trim().to_string();
        acc.clear();

        let s = input_owned.as_str();
        if s.is_empty() {
            continue;
        }

        if s == ":quit" || s == ":q" {
            break;
        }

        if s == ":help" {
            println!(
                r"Commands:
  :help              - this help
  :quit, :q          - exit
  :load PATH         - load file into session (base)
  :reset             - clear session
  :docs               - list defined functions (best-effort)
  :prove [EXPR]      - build proof for EXPR (or last expr)
  :verify B64|@PATH  - verify proof against last expr and current session
  EXPR               - evaluate EXPR with current session defs
  (def ...)          - define function or constant form into session
  (deftype ...)      - define type helpers into session"
            );
            continue;
        }

        if let Some(rest) = s.strip_prefix(":load ") {
            let path = std::path::PathBuf::from(rest.trim());
            match read_program(&path, REPL_MAX_BYTES) {
                Ok(src) => {
                    session.base_src = src;
                    println!("OK loaded {}", path.display());
                }
                Err(e) => println!("error: load failed: {e}"),
            }

            let _ = rl.add_history_entry(s);
            let _ = rl.save_history(&hist_path);

            continue;
        }

        if s == ":reset" {
            session.reset();
            println!("OK reset");

            let _ = rl.clear_history();

            continue;
        }

        if s == ":docs" {
            let mut all = extract_def_names(&session.base_src);
            for f in &session.forms {
                for n in extract_def_names(f) {
                    all.insert(n);
                }
            }

            if all.is_empty() {
                println!("(none)");
            } else {
                for n in all {
                    println!("{n}");
                }
            }

            let _ = rl.add_history_entry(s);
            let _ = rl.save_history(&hist_path);

            continue;
        }

        // Build proof for expression
        if let Some(rest) = s.strip_prefix(":prove") {
            if let Some(msg) = diagnose_non_ascii(rest) {
                println!("error: {msg}");
                continue;
            }

            let expr = {
                let r = rest.trim();
                if r.is_empty() {
                    match &session.last_expr {
                        Some(e) => e.as_str(),
                        None => {
                            println!(
                                "error: no expression to prove; evaluate EXPR or use :prove EXPR"
                            );
                            continue;
                        }
                    }
                } else {
                    r
                }
            };

            let wrapped = session.combined_with_expr(expr);
            match compiler::compile_entry(&wrapped, &[]) {
                Err(e) => println!("error: compile: {e}"),
                Ok(program) => {
                    // Build PI
                    let pi = match build_pi_for_program(&program, &[]) {
                        Ok(p) => p,
                        Err(e) => {
                            println!("error: pi: {e}");
                            continue;
                        }
                    };

                    // cost metrics requires a trace length;
                    // reuse backend run.
                    let run_res = match frontend::run_vm::<WinterfellBackend>(&program, &pi) {
                        Ok(r) => r,
                        Err(e) => {
                            println!("error: run: {e}");
                            continue;
                        }
                    };

                    let rows = run_res.trace_len;
                    let cost = compute_cost(&program);
                    let metrics = program.compiler_metrics.clone();

                    println!(
                        "cost: rows={rows}, ops={}, sponge_absorb_calls={}, sponge_absorb_elems={}, squeeze_calls={}, merkle_steps={}",
                        cost.ops,
                        cost.sponge_absorb_calls,
                        cost.sponge_absorb_elems,
                        cost.squeeze_calls,
                        cost.merkle_steps
                    );

                    println!(
                        "metrics: peak_live={} reuse_dst={} su_reorders={} balanced_chains={} mov_elided={}",
                        metrics.peak_live,
                        metrics.reuse_dst,
                        metrics.su_reorders,
                        metrics.balanced_chains,
                        metrics.mov_elided
                    );

                    let opts = proof_opts(1, 8, 0, None);
                    match frontend::prove::<WinterfellBackend>(&program, &pi, &opts) {
                        Err(e) => println!("error: prove: {e}"),
                        Ok(proof) => match frontend::encode_proof::<WinterfellBackend>(&proof) {
                            Err(e) => println!("error: serialize proof: {e}"),
                            Ok(bytes) => {
                                let proof_b64 =
                                    base64::engine::general_purpose::STANDARD.encode(&bytes);
                                let preview = format!("{} (len={} bytes)", proof_b64, bytes.len());

                                println!("proof: {preview}");
                            }
                        },
                    }
                }
            }

            let _ = rl.add_history_entry(s);
            let _ = rl.save_history(&hist_path);

            continue;
        }

        // Verify proof for last expression
        if let Some(rest) = s.strip_prefix(":verify ") {
            let arg = rest.trim();
            if arg.is_empty() {
                println!("error: usage: :verify B64|@PATH");
                continue;
            }

            let bytes = if let Some(path) = arg.strip_prefix('@') {
                match fs::metadata(path) {
                    Ok(meta) => {
                        if meta.len() as usize > REPL_MAX_BYTES {
                            println!(
                                "error: proof file too large: {} bytes (limit {})",
                                meta.len(),
                                REPL_MAX_BYTES
                            );
                            continue;
                        }
                    }
                    Err(e) => {
                        println!("error: stat proof: {e}");
                        continue;
                    }
                }

                match fs::read(path) {
                    Ok(b) => b,
                    Err(e) => {
                        println!("error: read proof: {e}");
                        continue;
                    }
                }
            } else {
                // Bound base64 size before decoding
                let approx = (arg.len() / 4) * 3;
                if approx > REPL_MAX_BYTES {
                    println!("error: proof base64 too large: limit {REPL_MAX_BYTES} bytes");
                    continue;
                }

                match base64::engine::general_purpose::STANDARD.decode(arg) {
                    Ok(b) => b,
                    Err(e) => {
                        println!("error: invalid base64: {e}");
                        continue;
                    }
                }
            };

            let proof = match frontend::decode_proof::<WinterfellBackend>(&bytes) {
                Ok(p) => p,
                Err(e) => {
                    println!("error: parse proof: {e}");
                    continue;
                }
            };

            let expr = match &session.last_expr {
                Some(e) => e.clone(),
                None => {
                    println!("error: no prior expression; use :prove EXPR first or evaluate EXPR");
                    continue;
                }
            };
            let wrapped = session.combined_with_expr(&expr);
            let program = match compiler::compile_entry(&wrapped, &[]) {
                Ok(p) => p,
                Err(e) => {
                    println!("error: compile: {e}");
                    continue;
                }
            };

            let pi = match build_pi_for_program(&program, &[]) {
                Ok(p) => p,
                Err(e) => {
                    println!("error: pi: {e}");
                    continue;
                }
            };

            let opts = proof_opts(1, 8, 0, None);
            match frontend::verify::<WinterfellBackend>(proof, &program, &pi, &opts) {
                Ok(()) => println!("OK"),
                Err(e) => println!("verify error: {e}"),
            }

            let _ = rl.add_history_entry(s);
            let _ = rl.save_history(&hist_path);

            continue;
        }

        // Top-level def/deftype
        // are stored into session
        let st = s.trim_start();
        if st.starts_with("(def ") || st.starts_with("(deftype ") {
            if let Some(msg) = diagnose_non_ascii(s) {
                println!("error: {msg}");
                continue;
            }

            session.add_form(s.to_string());

            // try to print name for UX
            let names = extract_def_names(s);
            if names.is_empty() {
                println!("OK");
            } else {
                // show only first name
                // from this form.
                let first = names.into_iter().next().unwrap();
                println!("OK def {first}");
            }

            continue;
        }

        // Evaluate expression
        // using current session
        if let Some(msg) = diagnose_non_ascii(s) {
            println!("error: {msg}");
            continue;
        }

        let wrapped = session.combined_with_expr(s);
        match compiler::compile_entry(&wrapped, &[]) {
            Err(e) => println!("error: compile: {e}"),
            Ok(program) => {
                let pi = match build_pi_for_program(&program, &[]) {
                    Ok(p) => p,
                    Err(e) => {
                        println!("error: pi: {e}");
                        continue;
                    }
                };

                match frontend::run_vm::<WinterfellBackend>(&program, &pi) {
                    Err(e) => println!("error: run: {e}"),
                    Ok(run_res) => {
                        let v: u128 = ZkField::to_u128(&run_res.value);

                        println!("= {v} (0x{v:032x})");

                        // remember last expr for :prove/:verify
                        session.last_expr = Some(s.to_string());
                    }
                }
            }
        }

        // add to history after successful
        // processing of a full command/expression
        if !s.is_empty() {
            let _ = rl.add_history_entry(s);
            let _ = rl.save_history(&hist_path);
        }
    }

    // Save history on exit
    let _ = rl.save_history(&hist_path);

    Ok(())
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

// Helpers for UX
fn is_bare_symbol(s: &str) -> bool {
    let mut it = s.chars();
    match it.next() {
        Some(c0) if compiler::is_sym_start(c0) => {}
        _ => return false,
    }

    for c in it {
        if !compiler::is_sym_continue(c) {
            return false;
        }
    }

    true
}

fn paren_balance(s: &str) -> i32 {
    let mut bal = 0i32;
    let mut in_str = false;
    let mut prev_bslash = false;

    for ch in s.chars() {
        if in_str {
            if ch == '"' && !prev_bslash {
                in_str = false;
            }

            prev_bslash = ch == '\\' && !prev_bslash;

            continue;
        }

        match ch {
            '"' => in_str = true,
            '(' => bal += 1,
            ')' => bal -= 1,
            _ => {}
        }

        prev_bslash = false;
    }

    bal
}

fn diagnose_non_ascii(s: &str) -> Option<String> {
    // scan outside of string literals only
    let mut in_str = false;
    let mut prev_bslash = false;

    for (i, ch) in s.char_indices() {
        if in_str {
            if ch == '"' && !prev_bslash {
                in_str = false;
                prev_bslash = false;
                continue;
            }

            prev_bslash = ch == '\\' && !prev_bslash;

            continue;
        }

        if ch == '"' {
            in_str = true;
            prev_bslash = false;
            continue;
        }

        if ch.is_ascii() {
            continue;
        }

        // Suggestion for common problematic chars
        let suggestion = match ch {
            '\u{00A0}' => "Use regular space ' ' (U+0020) instead of non‑breaking space.",
            '\u{2018}' | '\u{2019}' => {
                "Use ASCII apostrophe ' (U+0027) for quote, or \" (U+0022) for strings."
            }
            '\u{201C}' | '\u{201D}' => "Use ASCII double quote \" (U+0022).",
            '\u{00D7}' => "Use * (U+002A) for multiplication.",
            '\u{2013}' | '\u{2014}' => "Use - (U+002D).",
            _ => "Switch keyboard layout to English (ASCII) and replace this character.",
        };

        return Some(format!(
            "non-ASCII character at position {}: ‘{}’ (U+{:04X}). {}",
            i + 1,
            ch,
            ch as u32,
            suggestion
        ));
    }

    None
}

fn extract_def_names(src: &str) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    let s = src;
    let bytes = s.as_bytes();
    let mut i = 0usize;

    while i + 4 <= bytes.len() {
        if &bytes[i..i + 4] == b"(def" {
            i += 4;

            // skip whitespace
            while i < bytes.len() && bytes[i].is_ascii_whitespace() {
                i += 1;
            }

            if i >= bytes.len() {
                break;
            }

            if bytes[i] == b'(' {
                // (def (name ...)
                i += 1;

                // skip whitespace
                while i < bytes.len() && bytes[i].is_ascii_whitespace() {
                    i += 1;
                }

                let start = i;
                while i < bytes.len() && !bytes[i].is_ascii_whitespace() && bytes[i] != b')' {
                    i += 1;
                }

                if i > start {
                    if let Ok(n) = std::str::from_utf8(&bytes[start..i]) {
                        names.insert(n.to_string());
                    }
                }
            } else {
                // (def name ...)
                let start = i;
                while i < bytes.len() && !bytes[i].is_ascii_whitespace() && bytes[i] != b')' {
                    i += 1;
                }

                if i > start {
                    if let Ok(n) = std::str::from_utf8(&bytes[start..i]) {
                        names.insert(n.to_string());
                    }
                }
            }
        } else {
            i += 1;
        }
    }

    names
}

#[derive(Default, Debug)]
struct Cost {
    ops: usize,
    sponge_absorb_calls: usize,
    sponge_absorb_elems: usize,
    squeeze_calls: usize,
    merkle_steps: usize,
}

fn compute_cost(program: &compiler::Program) -> Cost {
    use zk_lisp_compiler::builder::Op::*;

    let mut c = Cost {
        ops: program.ops.len(),
        ..Default::default()
    };

    for op in &program.ops {
        match op {
            SAbsorbN { regs } => {
                c.sponge_absorb_calls += 1;
                c.sponge_absorb_elems += regs.len();
            }
            SSqueeze { .. } => c.squeeze_calls += 1,
            MerkleStepFirst { .. } | MerkleStep { .. } | MerkleStepLast { .. } => {
                c.merkle_steps += 1
            }
            _ => {}
        }
    }

    c
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

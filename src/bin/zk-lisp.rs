#![allow(dead_code)]
#![allow(clippy::uninlined_format_args)]
use anyhow::{Context, Result, anyhow};
use clap::{Parser, Subcommand};
use std::fs;
use std::io::{self, Write};
use std::path::PathBuf;
use thiserror::Error;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::math::{FieldElement, StarkField};
use winterfell::{BatchingMethod, FieldExtension, Proof, ProofOptions, Trace};

#[derive(Parser, Debug, Clone)]
#[command(
    name = "zk-lisp",
    about = "zk-lisp CLI: run, prove, verify, repl",
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
enum CliExit {
    #[error("invalid input: {0}")]
    InvalidInput(String),
    #[error("compile error: {0}")]
    Compile(String),
    #[error("io error: {0}")]
    Io(String),
    #[error("prover error: {0}")]
    Prover(String),
    #[error("verify failed: {0}")]
    Verify(String),
}

impl CliExit {
    fn code(&self) -> i32 {
        match self {
            CliExit::InvalidInput(_) => 2,
            CliExit::Compile(_) => 3,
            CliExit::Io(_) => 5,
            CliExit::Prover(_) => 6,
            CliExit::Verify(_) => 7,
        }
    }
}

fn try_main(cli: Cli) -> Result<()> {
    match cli.command {
        Command::Run(args) => cmd_run(args, cli.json, cli.max_bytes),
        Command::Prove(args) => cmd_prove(args, cli.json, cli.max_bytes),
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

fn read_program(path: &PathBuf, max_bytes: usize) -> Result<String> {
    let meta = fs::metadata(path)
        .with_context(|| format!("stat file: {}", path.display()))
        .map_err(|e| CliExit::Io(e.to_string()))?;

    if meta.len() as usize > max_bytes {
        return Err(CliExit::InvalidInput(format!(
            "file too large: {} bytes (limit {})",
            meta.len(),
            max_bytes
        ))
        .into());
    }

    let s = fs::read_to_string(path)
        .with_context(|| format!("read file: {}", path.display()))
        .map_err(|e| CliExit::Io(e.to_string()))?;

    Ok(s)
}

fn build_pi_for_program(program: &zk_lisp::ir::Program, args: &[u64]) -> zk_lisp::pi::PublicInputs {
    use zk_lisp::ir::Op;
    let mut mask: u64 = 0;

    // VM is used by any ALU/select/eq/hash2 op
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
                | Op::Hash2 { .. }
        )
    }) {
        mask |= zk_lisp::pi::FM_VM;
    }

    // Poseidon when hash2 appears
    if program.ops.iter().any(|op| matches!(op, Op::Hash2 { .. })) {
        mask |= zk_lisp::pi::FM_POSEIDON;
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

fn detect_vm_output(trace: &winterfell::TraceTable<BE>) -> (u8, u32) {
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

    let mut last_op_lvl: usize = 0;
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

    (out_reg, (row_fin + 1) as u32)
}

fn cmd_run(args: RunArgs, json: bool, max_bytes: usize) -> Result<()> {
    let src = read_program(&args.path, max_bytes)?;
    let program = zk_lisp::compiler::compile_entry(&src, &args.args)
        .map_err(|e| CliExit::Compile(e.to_string()))?;

    let pi = build_pi_for_program(&program, &args.args);
    // Build trace with VM args (and possibly KV expectations later)
    let trace = zk_lisp::prove::build_trace_with_pi(&program, &pi);

    // Compute VM output position and value
    let (out_reg, out_row) = detect_vm_output(&trace);
    let cols = zk_lisp::layout::Columns::baseline();
    let val = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    let val_u128: u128 = val.as_int();

    if json {
        println!(
            "{}",
            serde_json::json!({
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
            r"result:
  {val_u128} (hex 0x{val_u128:032x}),
  out_reg={out_reg},
  out_row={out_row},
  rows={rows}"
        );
    }

    Ok(())
}

fn cmd_prove(args: ProveArgs, json: bool, max_bytes: usize) -> Result<()> {
    let src = read_program(&args.path, max_bytes)?;
    let program = zk_lisp::compiler::compile_entry(&src, &args.args)
        .map_err(|e| CliExit::Compile(e.to_string()))?;

    let mut pi = build_pi_for_program(&program, &args.args);
    let trace = zk_lisp::prove::build_trace_with_pi(&program, &pi);

    // Fill dynamic PI parts (kv mask, vm_out_* only if needed later)
    // kv_levels_mask
    if (pi.feature_mask & zk_lisp::pi::FM_KV) != 0 {
        let cols = zk_lisp::layout::Columns::baseline();
        let steps = zk_lisp::layout::STEPS_PER_LEVEL_P2;
        let lvls = trace.length() / steps;

        let mut mask: u128 = 0;

        for lvl in 0..lvls {
            let base = lvl * steps;
            let row_map = base + zk_lisp::schedule::pos_map();

            if trace.get(cols.kv_g_map, row_map) == BE::ONE {
                mask |= 1u128 << lvl;
            }
        }

        pi.kv_levels_mask = mask;
    }

    // VM output position (not setting VM_EXPECT here)
    let (out_reg, out_row) = detect_vm_output(&trace);
    pi.vm_out_reg = out_reg;
    pi.vm_out_row = out_row;

    let opts = proof_opts(args.queries, args.blowup, args.grind);
    let prover = zk_lisp::prove::ZkProver::new(opts.clone(), pi.clone());

    let proof = prover
        .prove(trace)
        .map_err(|e| CliExit::Prover(e.to_string()))?;

    // Serialize proof to bytes and hex
    let proof_bytes = proof_to_bytes(&proof)?;
    if let Some(path) = args.out {
        fs::write(&path, &proof_bytes)
            .with_context(|| format!("write proof: {}", path.display()))
            .map_err(|e| CliExit::Io(e.to_string()))?;
    }

    let proof_hex = hex::encode(&proof_bytes);

    if !args.quiet {
        if json {
            println!(
                "{}",
                serde_json::json!({
                    "proof_hex": proof_hex,
                    "opts": {"queries": args.queries, "blowup": args.blowup, "grind": args.grind},
                    "seed": args.seed,
                    "commitment": format!("0x{:02x?}", program.commitment),
                })
            );
        } else {
            println!("proof(hex): {proof_hex}");

            if let Some(s) = args.seed {
                println!("seed: {s} (note: currently not applied)");
            }
        }
    }

    Ok(())
}

fn cmd_verify(args: VerifyArgs, json: bool, max_bytes: usize) -> Result<()> {
    let proof_bytes = if let Some(path) = args.proof.strip_prefix('@') {
        fs::read(path)
            .with_context(|| format!("read proof file: {path}"))
            .map_err(|e| CliExit::Io(e.to_string()))?
    } else {
        let s = args.proof.strip_prefix("0x").unwrap_or(&args.proof);
        hex::decode(s).map_err(|e| CliExit::InvalidInput(format!("invalid proof hex: {e}")))?
    };

    let src = read_program(&args.path, max_bytes)?;
    let program = zk_lisp::compiler::compile_entry(&src, &args.args)
        .map_err(|e| CliExit::Compile(e.to_string()))?;

    // Rebuild PI similarly to Prove
    let mut pi = build_pi_for_program(&program, &args.args);
    let trace = zk_lisp::prove::build_trace_with_pi(&program, &pi);

    if (pi.feature_mask & zk_lisp::pi::FM_KV) != 0 {
        let cols = zk_lisp::layout::Columns::baseline();
        let steps = zk_lisp::layout::STEPS_PER_LEVEL_P2;
        let lvls = trace.length() / steps;

        let mut mask: u128 = 0;

        for lvl in 0..lvls {
            let base = lvl * steps;
            let row_map = base + zk_lisp::schedule::pos_map();

            if trace.get(cols.kv_g_map, row_map) == BE::ONE {
                mask |= 1u128 << lvl;
            }
        }

        pi.kv_levels_mask = mask;
    }

    // VM output location (even without VM_EXPECT)
    let (out_reg, out_row) = detect_vm_output(&trace);
    pi.vm_out_reg = out_reg;
    pi.vm_out_row = out_row;

    let proof = proof_from_bytes(&proof_bytes).map_err(|e| CliExit::InvalidInput(e.to_string()))?;

    let opts = proof_opts(args.queries, args.blowup, args.grind);
    zk_lisp::prove::verify_proof(proof, pi, &opts).map_err(|e| CliExit::Verify(e.to_string()))?;

    if json {
        println!(
            "{}",
            serde_json::json!({
                "ok": true,
                "opts": {
                    "queries": args.queries,
                    "blowup": args.blowup,
                    "grind": args.grind,
                },
                "seed": args.seed,
            })
        );
    } else {
        println!("OK");

        if let Some(s) = args.seed {
            println!("seed: {s} (note: currently not applied)");
        }
    }

    Ok(())
}

fn cmd_repl() -> Result<()> {
    zk_lisp::logging::init();

    println!("zk-lisp REPL. Type :help for help. Ctrl-D to exit.");

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
        match zk_lisp::compiler::compile_entry(&wrapped, &[]) {
            Err(e) => println!("error: compile: {e}"),
            Ok(program) => {
                let pi = build_pi_for_program(&program, &[]);
                let trace = zk_lisp::prove::build_trace_with_pi(&program, &pi);
                let (out_reg, out_row) = detect_vm_output(&trace);
                let cols = zk_lisp::layout::Columns::baseline();
                let val = trace.get(cols.r_index(out_reg as usize), out_row as usize);
                let v: u128 = val.as_int();

                println!("= {v} (0x{v:032x})");
            }
        }
    }

    Ok(())
}

// --- Proof (de)serialization helpers ---

fn proof_to_bytes(proof: &Proof) -> Result<Vec<u8>> {
    // Prefer winterfell's Serializable if available
    // Proof likely implements to_bytes(); try that first.
    #[allow(clippy::let_and_return)]
    let bytes = proof.to_bytes();
    Ok(bytes)
}

fn proof_from_bytes(bytes: &[u8]) -> Result<Proof> {
    let p = Proof::from_bytes(bytes).map_err(|_| anyhow!("invalid proof bytes"))?;
    Ok(p)
}

fn main() {
    let cli = Cli::parse();
    zk_lisp::logging::init();

    let _ = cli.log_level; // currently rely on RUST_LOG env; keep arg for future

    let code = match try_main(cli.clone()) {
        Ok(()) => 0,
        Err(e) => {
            if let Some(ce) = e.downcast_ref::<CliExit>() {
                let code = ce.code();
                if cli.json {
                    println!(
                        "{}",
                        serde_json::json!({ "ok": false, "error": ce.to_string(), "code": code })
                    );
                } else {
                    eprintln!("error: {ce}");
                }

                code
            } else {
                if cli.json {
                    println!(
                        "{}",
                        serde_json::json!({ "ok": false, "error": e.to_string(), "code": 1 })
                    );
                } else {
                    eprintln!("error: {e}");
                }

                1
            }
        }
    };

    std::process::exit(code);
}

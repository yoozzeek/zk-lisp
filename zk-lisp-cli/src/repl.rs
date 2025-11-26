// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

use base64::Engine;
use rustyline::DefaultEditor;
use rustyline::error::ReadlineError;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use zk_lisp_compiler as compiler;
use zk_lisp_proof::{ZkField, frontend, recursion};
use zk_lisp_proof_winterfell::WinterfellBackend;

use crate::{CliError, REPL_MAX_BYTES};

#[derive(Default, Debug)]
struct Cost {
    ops: usize,
    sponge_absorb_calls: usize,
    sponge_absorb_elems: usize,
    squeeze_calls: usize,
    merkle_steps: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DefKind {
    Var,
    Fn,
}

// Live session state
#[derive(Default, Clone)]
struct Session {
    base_src: String,   // from :load
    forms: Vec<String>, // live appended forms
    last_expr: Option<String>,
    docs: BTreeMap<String, String>,
}

impl Session {
    fn reset(&mut self) {
        self.base_src.clear();
        self.forms.clear();
        self.last_expr = None;
        self.docs.clear();
    }

    fn add_form(&mut self, s: String) {
        self.forms.push(s);
        self.recompute_docs();
    }

    fn recompute_docs(&mut self) {
        let mut merged = String::new();

        if !self.base_src.is_empty() {
            merged.push_str(&self.base_src);

            if !self.base_src.ends_with('\n') {
                merged.push('\n');
            }
        }

        for f in &self.forms {
            merged.push_str(f);

            if !f.ends_with('\n') {
                merged.push('\n');
            }
        }

        self.docs = extract_docs(&merged);
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

pub fn cmd_repl() -> Result<(), CliError> {
    crate::init_logging(None);

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
  :load [PATH]       - load file into session (base)
  :save [PATH]       - save current session to file
  :reset             - clear session
  :docs               - list defined functions (best-effort)
  :prove [EXPR]      - build proof for EXPR (or last expr)
  :verify [PATH]     - verify proof file against last expr and current session
  EXPR               - evaluate EXPR with current session defs
  (def ...)          - define function or constant form into session
  (deftype ...)      - define type helpers into session"
            );
            continue;
        }

        if let Some(rest) = s.strip_prefix(":load ") {
            let path = std::path::PathBuf::from(rest.trim());
            match crate::read_program(&path, REPL_MAX_BYTES) {
                Ok(src) => {
                    session.base_src = src;
                    session.recompute_docs();

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
            let mut kinds = extract_def_kinds(&session.base_src);

            for f in &session.forms {
                for n in extract_def_names(f) {
                    all.insert(n);
                }

                for (name, kind) in extract_def_kinds(f) {
                    kinds.insert(name, kind);
                }
            }

            if all.is_empty() {
                println!("(none)");
            } else {
                for n in all {
                    let kind_label = match kinds.get(&n) {
                        Some(DefKind::Fn) => "fn",
                        Some(DefKind::Var) => "var",
                        None => "def",
                    };

                    println!("{kind_label}: {n}");

                    if let Some(doc) = session.docs.get(&n) {
                        println!("docs:");

                        for line in doc.lines() {
                            println!("{line}");
                        }
                    } else {
                        println!("docs: (none)");
                    }

                    println!();
                }
            }

            let _ = rl.add_history_entry(s);
            let _ = rl.save_history(&hist_path);

            continue;
        }

        // Save current session to a file
        if let Some(rest) = s.strip_prefix(":save ") {
            let arg = rest.trim();

            if arg.is_empty() {
                println!("error: usage: :save PATH");
                continue;
            }

            let mut file_name = arg.to_string();

            // If user did not specify any
            // extension, append .zlisp.
            if !file_name.ends_with(".zlisp") && !file_name.contains('.') {
                file_name.push_str(".zlisp");
            }

            let mut out = String::new();

            if !session.base_src.trim().is_empty() {
                out.push_str(&session.base_src);
                if !session.base_src.ends_with('\n') {
                    out.push('\n');
                }
            }

            for f in &session.forms {
                out.push_str(f);
                if !f.ends_with('\n') {
                    out.push('\n');
                }
            }

            match fs::write(&file_name, out) {
                Ok(()) => println!("OK saved session to {file_name}"),
                Err(e) => println!("error: save session: {e}"),
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

            let t_start = std::time::Instant::now();
            let wrapped = session.combined_with_expr(expr);

            match compiler::compile_entry(&wrapped, &[]) {
                Err(e) => println!("error: compile: {e}"),
                Ok(program) => {
                    // Build PI (no external args in REPL yet)
                    let pi = match crate::build_pi_for_program(&program, &[], &[]) {
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

                    let opts = crate::proof_opts(64, 8, 0, None, None, None);
                    match recursion::prove_chain::<WinterfellBackend>(&program, &pi, &opts) {
                        Err(e) => println!("error: prove: {e}"),
                        Ok((rc_proof, _rc_digest, rc_pi)) => {
                            match <WinterfellBackend as recursion::RecursionArtifactCodec>::encode(
                                &rc_proof, &rc_pi,
                            ) {
                                Err(e) => println!("error: serialize agg proof: {e}"),
                                Ok(bytes) => {
                                    let file_name =
                                        proof_basename_from_expr(expr).replace("proof_", "agg_");
                                    let path = std::path::PathBuf::from(&file_name);

                                    match fs::write(&path, &bytes) {
                                        Err(e) => {
                                            println!("error: write proof file: {e}");
                                        }
                                        Ok(()) => {
                                            let proof_b64 =
                                                base64::engine::general_purpose::STANDARD
                                                    .encode(&bytes);
                                            let len_b64 = proof_b64.len();

                                            let preview_core = if len_b64 <= 128 {
                                                proof_b64
                                            } else {
                                                let head = &proof_b64[..64];
                                                let tail = &proof_b64[len_b64 - 64..];

                                                format!("{head}...{tail}")
                                            };

                                            println!("agg proof saved to {}", path.display());
                                            println!(
                                                "preview: {} (len={} bytes, b64_len={})",
                                                preview_core,
                                                bytes.len(),
                                                len_b64
                                            );
                                            println!(
                                                "hint: verify in REPL with `:verify {file_name}`"
                                            );
                                            println!(
                                                "hint: verify via CLI with `zk-lisp verify {file_name} <program.zlisp> --arg ...`"
                                            );

                                            let elapsed_ms = t_start.elapsed().as_millis();
                                            println!("time: {elapsed_ms} ms");

                                            // Remember last expression
                                            // for subsequent :verify
                                            session.last_expr = Some(expr.to_string());
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }

            let _ = rl.add_history_entry(s);
            let _ = rl.save_history(&hist_path);

            continue;
        }

        // Verify proof for last expression
        if let Some(rest) = s.strip_prefix(":verify ") {
            let path = rest.trim();
            if path.is_empty() {
                println!("error: usage: :verify PATH");
                continue;
            }

            let bytes = {
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
            };

            let (rc_proof, rc_pi) =
                match <WinterfellBackend as recursion::RecursionArtifactCodec>::decode(&bytes) {
                    Ok(pair) => pair,
                    Err(e) => {
                        println!("error: parse agg proof: {e}");
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

            let _pi = match crate::build_pi_for_program(&program, &[], &[]) {
                Ok(p) => p,
                Err(e) => {
                    println!("error: pi: {e}");
                    continue;
                }
            };

            let opts = crate::proof_opts(64, 8, 0, None, None, None);
            let t_start = std::time::Instant::now();

            match frontend::recursion_verify::<WinterfellBackend>(rc_proof, &rc_pi, &opts) {
                Ok(()) => {
                    let elapsed_ms = t_start.elapsed().as_millis();
                    println!("OK");
                    println!("time: {elapsed_ms} ms");
                }
                Err(e) => println!("verify error: {e}"),
            }

            let _ = rl.add_history_entry(s);
            let _ = rl.save_history(&hist_path);

            continue;
        }

        // Top-level def/deftype
        // are stored into session
        let st = s.trim_start();
        if st.starts_with("(def ") || st.starts_with("(deftype ") || st.starts_with("(typed-fn ") {
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

            let _ = rl.add_history_entry(s);
            let _ = rl.save_history(&hist_path);

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
                let pi = match crate::build_pi_for_program(&program, &[], &[]) {
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

fn extract_def_kinds(src: &str) -> BTreeMap<String, DefKind> {
    let mut kinds = BTreeMap::new();
    let bytes = src.as_bytes();
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

            let kind = if bytes[i] == b'(' {
                // (def (name ...)
                i += 1;
                while i < bytes.len() && bytes[i].is_ascii_whitespace() {
                    i += 1;
                }
                DefKind::Fn
            } else {
                DefKind::Var
            };

            let start = i;
            while i < bytes.len() && !bytes[i].is_ascii_whitespace() && bytes[i] != b')' {
                i += 1;
            }

            if i > start {
                if let Ok(n) = std::str::from_utf8(&bytes[start..i]) {
                    kinds.insert(n.to_string(), kind);
                }
            }
        } else {
            i += 1;
        }
    }

    kinds
}

pub fn extract_docs(src: &str) -> BTreeMap<String, String> {
    let mut docs = BTreeMap::new();
    let mut pending: Vec<String> = Vec::new();

    for line in src.lines() {
        let trimmed = line.trim_start();

        if trimmed.starts_with(";;") {
            // Treat any ";;" prefixed line as a doc-comment line
            let doc_line = trimmed.trim_start_matches(';').trim_start();
            pending.push(doc_line.to_string());

            continue;
        }

        if trimmed.is_empty() {
            // Allow blank lines inside a doc block
            if !pending.is_empty() {
                pending.push(String::new());
            }

            continue;
        }

        if trimmed.starts_with("(def ") {
            if !pending.is_empty() {
                let names = extract_def_names(line);

                if let Some(name) = names.into_iter().next() {
                    let joined = pending.join("\n");
                    let text = joined.trim().to_string();

                    if !text.is_empty() {
                        docs.insert(name, text);
                    }
                }

                pending.clear();
            }
        } else {
            // Any other non-empty, non-comment
            // line breaks the doc block.
            pending.clear();
        }
    }

    docs
}

fn proof_basename_from_expr(expr: &str) -> String {
    let raw_tag = proof_tag_from_expr(expr);
    let mut tag = String::new();

    for ch in raw_tag.chars() {
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
        tag.push_str("expr");
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

fn proof_tag_from_expr(expr: &str) -> String {
    let s = expr.trim_start();
    if let Some(rest) = s.strip_prefix('(') {
        let inner = rest.trim_start();
        let mut name = String::new();

        for ch in inner.chars() {
            if ch.is_whitespace() || ch == '(' || ch == ')' {
                break;
            }

            name.push(ch);
        }

        if !name.is_empty() {
            return name;
        }
    }

    "expr".to_string()
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

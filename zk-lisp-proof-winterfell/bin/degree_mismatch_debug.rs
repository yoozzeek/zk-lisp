// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

use std::fs;
use std::path::PathBuf;

use regex::Regex;
use thiserror::Error;
use zk_lisp_proof_winterfell::vm::layout::{NR, POSEIDON_ROUNDS, SPONGE_IDX_BITS};

#[derive(Debug, Error)]
#[error("{0}")]
struct CliError(String);

type Result<T> = std::result::Result<T, CliError>;

#[derive(Debug, Clone)]
struct PanicBlock {
    exp: Vec<i64>,
    act: Vec<i64>,
    panic_pos: usize,
}

#[derive(Debug, Clone)]
struct DegRange {
    module: String,
    start: usize,
    end: usize,
}

#[derive(Debug, Clone)]
struct VmCtrlLayout {
    len_ctrl: usize,
    len_roles: usize,
    len_tail: usize,
    sponge_extra: usize,
    num_lanes: usize,
}

#[derive(Debug, Clone)]
struct MismatchRecord {
    idx: usize,
    expected: i64,
    actual: i64,
    base_expected: Option<i64>,
    base_actual: Option<i64>,
    module: Option<String>,
    local: Option<usize>,
    lane: Option<usize>,
    kind: Option<String>,
}

#[derive(Debug, Clone)]
struct BaseMapping {
    min_val: i64,
    step: i64,
    ok: bool,
}

impl BaseMapping {
    fn empty() -> Self {
        BaseMapping {
            min_val: 0,
            step: 0,
            ok: false,
        }
    }

    fn from_vals(exp: &[i64]) -> BaseMapping {
        // Collect all unique positive
        // degree values and sort them.
        let mut vals: Vec<i64> = exp.iter().copied().filter(|&v| v > 0).collect();
        vals.sort();
        vals.dedup();

        if vals.is_empty() {
            // No positive degrees at all,
            // cannot infer anything.
            return BaseMapping::empty();
        }

        // Use the smallest positive degree
        // as the anchor point of the grid.
        let min_val = vals[0];

        // Build the set of all positive differences
        // between any two degrees. We deliberately
        // consider all pairs, not only neighbors,
        // because values from other modules may be
        // interleaved and destroy the structure if
        // we only look at neighbor differences.
        let mut diffs = std::collections::BTreeSet::<i64>::new();
        let n = vals.len();

        for i in 0..n {
            let vi = vals[i];
            for j in (i + 1)..n {
                let d = vals[j] - vi;
                if d > 1 {
                    // Ignore differences <= 1 as trivial/degenerate
                    diffs.insert(d);
                }
            }
        }

        if diffs.is_empty() {
            // No non-trivial positive
            // difference -> no meaningful grid.
            return BaseMapping {
                min_val,
                step: 0,
                ok: false,
            };
        }

        // Choose the step that maximizes the number
        // of values landing exactly on the
        // grid v = min_val + k * step, k >= 0.
        // In case of a tie, prefer the larger step
        // (important e.g. to prefer 4095 over its divisors).
        let mut best_step = 0i64;
        let mut best_count = 0usize;

        for step in diffs {
            if step <= 1 {
                continue;
            }

            let mut count = 0usize;
            for &v in &vals {
                if (v - min_val) % step == 0 {
                    count += 1;
                }
            }

            if count > best_count || (count == best_count && step > best_step) {
                best_step = step;
                best_count = count;
            }
        }

        // Heuristic: require at least this many
        // points to be explained by a
        // single arithmetic progression.
        const MIN_MATCHES: usize = 4;

        if best_step <= 1 || best_count < MIN_MATCHES {
            return BaseMapping {
                min_val,
                step: 0,
                ok: false,
            };
        }

        BaseMapping {
            min_val,
            step: best_step,
            ok: best_count >= MIN_MATCHES,
        }
    }

    // Map a degree value `v` to a 1-based base
    // index on the inferred grid. Returns `Some(idx)`
    // if `v` lies exactly on the grid, `None` otherwise
    // or when no reliable progression was found.
    fn base_from_eval(&self, v: i64) -> Option<i64> {
        if !self.ok || self.step <= 1 {
            return None;
        }

        if v < self.min_val {
            return None;
        }

        let num = v - self.min_val;
        if num % self.step != 0 {
            return None;
        }

        Some(1 + num / self.step)
    }
}

fn parse_int_list(raw_inner: &str) -> Result<Vec<i64>> {
    let inner_trimmed = raw_inner.trim();
    let wrapped = format!("[{}]", inner_trimmed);

    let vals: Vec<i64> = serde_json::from_str(&wrapped).map_err(|e| {
        CliError(format!(
            "failed to parse degree list as JSON: input='{}' error={}",
            inner_trimmed, e
        ))
    })?;

    Ok(vals)
}

fn parse_deg_ranges(raw_ranges: &str) -> Result<Vec<DegRange>> {
    // raw_ranges is of the form:
    //   [("vm_ctrl", 0, 91), ("vm_alu", 91, 107), ...]
    // which is valid Python list-of-tuples syntax. We map `(` and `)` to
    // `[` and `]` and then parse as JSON Vec<(String, usize, usize)>.
    let json_like = raw_ranges.replace('(', "[").replace(')', "]");

    let parsed: Vec<(String, usize, usize)> = serde_json::from_str(&json_like).map_err(|e| {
        CliError(format!(
            "failed to parse deg_ranges as JSON-like list-of-tuples: input='{}' error={}",
            raw_ranges, e
        ))
    })?;

    Ok(parsed
        .into_iter()
        .map(|(module, start, end)| DegRange { module, start, end })
        .collect())
}

fn find_all_panic_blocks(text: &str) -> Result<Vec<PanicBlock>> {
    let re = Regex::new(
        r"(?s)transition constraint degrees didn't match.*?expected:\s*\[(.*?)\]\s*actual:\s*\[(.*?)\]",
    )
    .map_err(|e| CliError(format!("invalid panic regex: {e}")))?;

    let mut blocks = Vec::new();

    for caps in re.captures_iter(text) {
        let full = caps
            .get(0)
            .ok_or_else(|| CliError("internal error: missing full match".to_string()))?;
        let panic_pos = full.start();

        let exp_inner = caps
            .get(1)
            .ok_or_else(|| CliError("missing expected degrees capture".to_string()))?
            .as_str();
        let act_inner = caps
            .get(2)
            .ok_or_else(|| CliError("missing actual degrees capture".to_string()))?
            .as_str();

        let exp = parse_int_list(exp_inner)?;
        let act = parse_int_list(act_inner)?;

        blocks.push(PanicBlock {
            exp,
            act,
            panic_pos,
        });
    }

    if blocks.is_empty() {
        return Err(CliError(
            "no `transition constraint degrees didn't match` found".to_string(),
        ));
    }

    Ok(blocks)
}

/// Select the most appropriate deg_ranges
/// block for a given panic.
///
/// Strategy (mirrors the Python script):
///   - Collect all 'deg_ranges: [...]' blocks
///     that appear BEFORE `panic_pos`.
///   - For each candidate compute
///     `max_end = max(end for (_, _, end) in ranges)`.
///   - Prefer the LAST candidate whose
///     coverage matches `exp_len` exactly.
///   - If none matches `exp_len`, fall back to
///     the last candidate and signal coverage
///     mismatch via the boolean flag.
fn find_deg_ranges_for_panic(
    text: &str,
    panic_pos: usize,
    exp_len: usize,
) -> Result<(Vec<DegRange>, bool)> {
    let re = Regex::new(r"deg_ranges:\s*(\[[^\]]*\])")
        .map_err(|e| CliError(format!("invalid deg_ranges regex: {e}")))?;

    let mut candidates: Vec<(usize, Vec<DegRange>, usize)> = Vec::new();

    for caps in re.captures_iter(text) {
        let full = caps
            .get(0)
            .ok_or_else(|| CliError("internal error: missing deg_ranges full match".to_string()))?;
        let start_pos = full.start();

        if start_pos >= panic_pos {
            break;
        }

        let ranges_str = caps
            .get(1)
            .ok_or_else(|| CliError("missing deg_ranges capture".to_string()))?
            .as_str();

        let ranges = parse_deg_ranges(ranges_str)?;
        if ranges.is_empty() {
            continue;
        }

        let max_end = ranges.iter().map(|r| r.end).max().unwrap_or(0);

        candidates.push((start_pos, ranges, max_end));
    }

    if candidates.is_empty() {
        return Ok((Vec::new(), false));
    }

    // Prefer a candidate whose
    // coverage matches exp_len.
    for (_pos, ranges, max_end) in candidates.iter().rev() {
        if *max_end == exp_len {
            return Ok((ranges.clone(), true));
        }
    }

    // Fallback: choose the last candidate
    // but mark coverage mismatch.
    let (_pos, ranges, max_end) = candidates.last().cloned().unwrap();

    Ok((ranges, max_end == exp_len))
}

fn analyze_one_panic(
    text: &str,
    path: &PathBuf,
    block_index: usize,
    total_blocks: usize,
    exp: &[i64],
    act: &[i64],
    panic_pos: usize,
) -> Result<()> {
    if exp.len() != act.len() {
        return Err(CliError(format!(
            "[panic #{}] len mismatch: expected={} actual={}",
            block_index,
            exp.len(),
            act.len()
        )));
    }

    let (deg_ranges, coverage_ok) = find_deg_ranges_for_panic(text, panic_pos, exp.len())?;

    if deg_ranges.is_empty() {
        return Err(CliError(format!(
            "[panic #{}] no deg_ranges found before panic; make sure vm::air::debug logging is enabled",
            block_index
        )));
    }

    let max_end = deg_ranges.iter().map(|r| r.end).max().unwrap_or(0);

    if !coverage_ok {
        println!(
            "[panic #{}] WARNING: deg_ranges coverage does not match expected length: max_end= {} len(exp)= {}",
            block_index,
            max_end,
            exp.len()
        );
    }

    let base_mapping = BaseMapping::from_vals(exp);

    let mut mismatches = Vec::new();
    for (i, (&ev, &av)) in exp.iter().zip(act.iter()).enumerate() {
        if ev != av {
            mismatches.push((i, ev, av));
        }
    }

    let mut module_map: Vec<MismatchRecord> = Vec::new();

    for (idx, ev, av) in mismatches.iter().copied() {
        let mut module: Option<String> = None;
        let mut local: Option<usize> = None;

        for r in &deg_ranges {
            if r.start <= idx && idx < r.end {
                module = Some(r.module.clone());
                local = Some(idx - r.start);
                break;
            }
        }

        let rec = MismatchRecord {
            idx,
            expected: ev,
            actual: av,
            base_expected: base_mapping.base_from_eval(ev),
            base_actual: base_mapping.base_from_eval(av),
            module,
            local,
            lane: None,
            kind: None,
        };

        module_map.push(rec);
    }

    // Locate vm_ctrl layout if present.
    let mut vm_ctrl_start: Option<usize> = None;
    let mut vm_ctrl_end: Option<usize> = None;

    for r in &deg_ranges {
        if r.module == "vm_ctrl" {
            match (vm_ctrl_start, vm_ctrl_end) {
                (None, None) => {
                    vm_ctrl_start = Some(r.start);
                    vm_ctrl_end = Some(r.end);
                }
                _ => {
                    return Err(CliError(format!(
                        "[panic #{}] multiple vm_ctrl ranges in deg_ranges; script assumes a single contiguous vm_ctrl block",
                        block_index
                    )));
                }
            }
        }
    }

    let vm_ctrl_layout: Option<VmCtrlLayout> = match (vm_ctrl_start, vm_ctrl_end) {
        (Some(s), Some(e)) => {
            let len_ctrl = e - s;
            let len_roles = 5 * NR + 5 + NR;
            let len_tail = 1 + 17 + 1 + 17 + 2;
            let sponge_extra = len_ctrl as isize - len_roles as isize - len_tail as isize;

            if sponge_extra < 0 {
                return Err(CliError(format!(
                    "[panic #{}] vm_ctrl layout mismatch: len_ctrl={}, len_roles={}, len_tail={}, sponge_extra={}",
                    block_index, len_ctrl, len_roles, len_tail, sponge_extra
                )));
            }

            let sponge_extra = sponge_extra as usize;
            if sponge_extra % (SPONGE_IDX_BITS + 1) != 0 {
                return Err(CliError(format!(
                    "[panic #{}] vm_ctrl sponge selector region size {} is not divisible by SPONGE_IDX_BITS+1={}",
                    block_index,
                    sponge_extra,
                    SPONGE_IDX_BITS + 1
                )));
            }

            let num_lanes = sponge_extra / (SPONGE_IDX_BITS + 1);

            Some(VmCtrlLayout {
                len_ctrl,
                len_roles,
                len_tail,
                sponge_extra,
                num_lanes,
            })
        }
        _ => None,
    };

    // Buckets for categorization
    let mut poseidon_bind: Vec<MismatchRecord> = Vec::new();
    let mut ctrl_sponge: Vec<MismatchRecord> = Vec::new();
    let mut ctrl_core: Vec<MismatchRecord> = Vec::new();
    let mut alu_high: Vec<MismatchRecord> = Vec::new();
    let mut ram_mism: Vec<MismatchRecord> = Vec::new();
    let mut rom_mism: Vec<MismatchRecord> = Vec::new();
    let mut other: Vec<MismatchRecord> = Vec::new();

    for mut rec in module_map {
        let module_name = rec.module.clone();
        let local = rec.local;

        if module_name.as_deref() == Some("poseidon") {
            if let Some(local_idx) = local {
                // base poseidon len: 12*R + 12
                let base_len = 12 * POSEIDON_ROUNDS + 12;
                if local_idx >= base_len {
                    let lane = local_idx - base_len;
                    rec.lane = Some(lane);
                    poseidon_bind.push(rec);
                } else {
                    other.push(rec);
                }

                continue;
            }
        }

        if module_name.as_deref() == Some("vm_ctrl") {
            if let (Some(local_idx), Some(layout)) = (local, vm_ctrl_layout.clone()) {
                let len_roles = layout.len_roles;
                let sponge_extra = layout.sponge_extra;

                if local_idx < len_roles {
                    ctrl_core.push(rec);
                } else if local_idx < len_roles + sponge_extra {
                    // Sponge selectors
                    let rel = local_idx - len_roles;
                    let lane = rel / (SPONGE_IDX_BITS + 1);
                    let pos = rel % (SPONGE_IDX_BITS + 1);

                    let kind = if pos < SPONGE_IDX_BITS {
                        format!("bit{}", pos)
                    } else {
                        "active".to_string()
                    };

                    rec.lane = Some(lane);
                    rec.kind = Some(kind);
                    ctrl_sponge.push(rec);
                } else {
                    ctrl_core.push(rec);
                }

                continue;
            }
        }

        if module_name.as_deref() == Some("vm_alu") && local.is_some() {
            alu_high.push(rec);
            continue;
        }

        if module_name.as_deref() == Some("ram") {
            ram_mism.push(rec);
            continue;
        }

        if module_name.as_deref() == Some("rom") {
            rom_mism.push(rec);
            continue;
        }

        other.push(rec);
    }

    println!("\n=== Panic #{}/{} ===", block_index, total_blocks);
    println!("path={} ", path.display());
    println!("len(exp)         = {}", exp.len());
    println!("total mismatches = {}", mismatches.len());

    // Format deg_ranges as a list of
    // (module, start, end) tuples for readability.
    let dr_repr: Vec<(String, usize, usize)> = deg_ranges
        .iter()
        .map(|r| (r.module.clone(), r.start, r.end))
        .collect();

    println!("deg_ranges       = {:?}", dr_repr);
    println!(
        "min_val= {} step= {} base_ok= {}",
        base_mapping.min_val, base_mapping.step, base_mapping.ok
    );

    if !base_mapping.ok {
        println!(
            "WARNING: base degree mapping is unreliable; base_* fields may be None or misleading"
        );
    }

    println!("\nPoseidon sponge binding mismatches:");
    for r in &poseidon_bind {
        println!(
            "  idx={}, lane={:?}, exp={} (base={:?}), act={} (base={:?})",
            r.idx, r.lane, r.expected, r.base_expected, r.actual, r.base_actual
        );
    }

    println!("\nVmCtrl sponge-selector mismatches:");
    for r in &ctrl_sponge {
        println!(
            "  idx={}, lane={:?}, {}, exp={} (base={:?}), act={} (base={:?})",
            r.idx,
            r.lane,
            r.kind.as_deref().unwrap_or("?"),
            r.expected,
            r.base_expected,
            r.actual,
            r.base_actual
        );
    }

    println!("\nVmCtrl core (roles/sums/op/rom/pc) mismatches:");
    for r in &ctrl_core {
        println!(
            "  idx={}, local={:?}, exp={} (base={:?}), act={} (base={:?})",
            r.idx, r.local, r.expected, r.base_expected, r.actual, r.base_actual
        );
    }

    println!("\nVmAlu high-degree mismatches:");
    for r in &alu_high {
        println!(
            "  idx={}, local={:?}, exp={} (base={:?}), act={} (base={:?})",
            r.idx, r.local, r.expected, r.base_expected, r.actual, r.base_actual
        );
    }

    println!("\nRAM mismatches:");
    for r in &ram_mism {
        println!("{}", shorten_debug(&format!("{:?}", r), 160));
    }

    println!("\nROM mismatches:");
    for r in &rom_mism {
        println!("{}", shorten_debug(&format!("{:?}", r), 160));
    }

    println!("\nOther mismatches:");
    for r in other.iter().take(80) {
        println!("{}", shorten_debug(&format!("{:?}", r), 160));
    }

    println!("\nSummary:");
    println!("  poseidon_bind mismatches : {}", poseidon_bind.len());
    println!("  vm_ctrl sponge mismatches: {}", ctrl_sponge.len());
    println!("  vm_ctrl core mismatches  : {}", ctrl_core.len());
    println!("  vm_alu high-degree       : {}", alu_high.len());
    println!("  ram mismatches           : {}", ram_mism.len());
    println!("  rom mismatches           : {}", rom_mism.len());
    println!("  other                    : {}", other.len());

    Ok(())
}

fn shorten_debug(s: &str, width: usize) -> String {
    // Rough equivalent of Python's textwrap.shorten
    // for debug output. Collapse whitespace, then
    // trim on word boundaries with an ellipsis.
    let collapsed = collapse_whitespace(s);
    if collapsed.len() <= width {
        return collapsed;
    }

    let placeholder = "...";
    if width <= placeholder.len() {
        return placeholder[..width].to_string();
    }

    let mut out = String::new();
    let mut current_len = 0usize;

    for (i, word) in collapsed.split_whitespace().enumerate() {
        let sep = if i == 0 { 0 } else { 1 }; // space separator
        let needed = current_len + sep + word.len() + placeholder.len();

        if needed > width {
            break;
        }

        if i > 0 {
            out.push(' ');
            current_len += 1;
        }

        out.push_str(word);
        current_len += word.len();
    }

    if out.is_empty() {
        // Fallback: hard cut.
        let cut = width.saturating_sub(placeholder.len());
        let mut base = collapsed.chars().take(cut).collect::<String>();
        base.push_str(placeholder);

        return base;
    }

    out.push_str(placeholder);
    out
}

fn collapse_whitespace(s: &str) -> String {
    let mut out = String::new();
    let mut in_ws = false;

    for ch in s.chars() {
        if ch.is_whitespace() {
            if !in_ws {
                out.push(' ');
                in_ws = true;
            }
        } else {
            in_ws = false;
            out.push(ch);
        }
    }

    out.trim().to_string()
}

fn analyze(path: &PathBuf) -> Result<()> {
    let text = fs::read_to_string(path).map_err(|e| {
        CliError(format!(
            "failed to read log file '{}': {}",
            path.display(),
            e
        ))
    })?;

    let panic_blocks = find_all_panic_blocks(&text)?;

    println!("path={}", path.display());
    println!("panic_blocks={}", panic_blocks.len());

    let total = panic_blocks.len();

    for (i, blk) in panic_blocks.into_iter().enumerate() {
        let block_index = i + 1;
        analyze_one_panic(
            &text,
            path,
            block_index,
            total,
            &blk.exp,
            &blk.act,
            blk.panic_pos,
        )?;
    }

    Ok(())
}

fn usage(bin: &str) -> String {
    format!("Usage: {} <path-to-debug-log>", bin)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 2 {
        eprintln!("{}", usage(&args[0]));
        std::process::exit(1);
    }

    let path = PathBuf::from(&args[1]);
    if let Err(e) = analyze(&path) {
        eprintln!("{}", e);
        std::process::exit(1);
    }
}

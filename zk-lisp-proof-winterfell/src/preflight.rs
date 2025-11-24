// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Backend-specific preflight diagnostics for zk-lisp.
//!
//! Evaluates AIR transition constraints over a trace, builds
//! rich [`PreflightReport`] snapshots and renders them as
//! console tables or JSON depending on [`PreflightMode`].

use crate::AirPublicInputs;
use crate::poseidon;
use crate::prove::Error;
use crate::vm::air::ZkLispAir;

use crate::vm::layout;
use comfy_table::{Cell, CellAlignment, ContentArrangement, Table, presets::ASCII_BORDERS_ONLY};
use serde::Serialize;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::math::{FieldElement, StarkField, polynom};
use winterfell::{Air, EvaluationFrame, ProofOptions, Trace, TraceInfo, TraceTable};
use zk_lisp_proof::frontend::PreflightMode;
use zk_lisp_proof::pi::PublicInputs;

#[derive(Debug, Clone, Serialize)]
pub struct PreflightReport {
    pub row: usize,
    pub constraint_idx: usize,
    pub constraint_val: String,
    pub pos: usize,
    pub gates_map: bool,
    pub gates_final: bool,
    pub rounds: Vec<bool>,
    pub lanes_cur: (String, String, String, String),
    pub lanes_next: (String, String, String, String),
    pub lanes_exp: Option<(String, String, String, String)>,
    pub ram: Option<RamSnap>,
    pub vm: Option<VmSnap>,
    pub peak_live: Option<u16>,
}

#[derive(Debug, Clone, Serialize)]
pub struct RamSnap {
    pub sorted: bool,
    pub addr_cur: String,
    pub addr_next: String,
    pub clk_cur: String,
    pub clk_next: String,
    pub val: String,
    pub is_write: String,
    pub last_cur: String,
    pub last_next: String,
    pub gp_unsorted_cur: String,
    pub gp_unsorted_next: String,
    pub gp_sorted_cur: String,
    pub gp_sorted_next: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct VmSnap {
    pub dst_reg: Option<usize>,
    pub a_val: String,
    pub b_val: String,
    pub c_val: String,
    pub lhs: String,
}

pub fn run(
    mode: PreflightMode,
    options: &ProofOptions,
    pub_inputs: &PublicInputs,
    trace: &TraceTable<BE>,
) -> Result<(), Error> {
    if matches!(mode, PreflightMode::Off) {
        return Ok(());
    }

    let ti = TraceInfo::new(trace.width(), trace.length());

    // Derive ROM accumulator lanes from the last
    // row of the trace to mirror prover behaviour.
    let mut rom_acc = [BE::ZERO; 3];
    let cols = layout::Columns::baseline();
    let last = trace.length().saturating_sub(1);

    if pub_inputs.program_commitment.iter().any(|b| *b != 0) && last > 0 {
        for (i, dst) in rom_acc.iter_mut().enumerate() {
            *dst = trace.get(cols.rom_s_index(i), last);
        }
    }

    let air_pi = AirPublicInputs {
        core: pub_inputs.clone(),
        segment_feature_mask: 0,
        rom_acc,
        pc_init: BE::ZERO,
        ram_gp_unsorted_in: BE::ZERO,
        ram_gp_unsorted_out: BE::ZERO,
        ram_gp_sorted_in: BE::ZERO,
        ram_gp_sorted_out: BE::ZERO,
        rom_s_in: [BE::ZERO; 3],
        rom_s_out: [BE::ZERO; 3],
    };

    let air = ZkLispAir::new(ti, air_pi, options.clone());
    let res_len = air.context().num_main_transition_constraints();
    let pc = air.get_periodic_column_values();

    // Extra: replicate Winterfell's periodic
    // poly eval at step 0 for debugging.
    if cfg!(debug_assertions) {
        let periodic_polys = air.get_periodic_column_polys();

        let mut periodic_poly_vals = vec![BE::ZERO; periodic_polys.len()];
        let x = BE::ONE; // step 0

        for (p, v) in periodic_polys.iter().zip(periodic_poly_vals.iter_mut()) {
            let num_cycles = air.trace_length() / p.len();
            let x_eval = x.exp((num_cycles as u32).into());
            *v = polynom::eval(p, x_eval);
        }

        // evaluate transition at step 0 using poly-evaluated periodic values
        let mut frame0 = EvaluationFrame::<BE>::new(trace.width());

        // fill current row
        for (c, dst) in frame0.current_mut().iter_mut().enumerate() {
            *dst = trace.get(c, 0);
        }

        // fill next row
        for (c, dst) in frame0.next_mut().iter_mut().enumerate() {
            *dst = trace.get(c, 1.min(trace.length() - 1));
        }

        let mut res0 = vec![BE::ZERO; res_len];
        air.evaluate_transition(&frame0, &periodic_poly_vals, &mut res0);

        let cols_dbg = layout::Columns::baseline();
        let sd0 = frame0.current()[cols_dbg.sel_dst0_index(0)];
        let p_map0 = periodic_poly_vals[0];
        let p_fin0 = periodic_poly_vals[1 + layout::POSEIDON_ROUNDS];
        let p_pad0 = periodic_poly_vals[1 + layout::POSEIDON_ROUNDS + 1];
        let p_last0 = periodic_poly_vals[1 + layout::POSEIDON_ROUNDS + 3];

        tracing::debug!(
            target = "proof.preflight",
            "[preflight poly step0] first 8: {:?}",
            &res0[0..res0.len().min(8)]
        );
        tracing::debug!(
            target = "proof.preflight",
            "[preflight poly step0] gates: p_map={p_map0:?} p_final={p_fin0:?} p_pad={p_pad0:?} p_last={p_last0:?} sd0={sd0:?}"
        );
    }

    let compilers_stats = &pub_inputs.compiler_stats;
    let mut frame = EvaluationFrame::<BE>::new(trace.width());
    let last_row = trace.length().saturating_sub(1);

    for r in 0..trace.length() {
        for c in 0..trace.width() {
            frame.current_mut()[c] = trace.get(c, r);

            let nxt = if r + 1 < trace.length() { r + 1 } else { r };
            frame.next_mut()[c] = trace.get(c, nxt);
        }

        // Skip transition exemption row (last row)
        if r == last_row {
            continue;
        }

        let mut res = vec![BE::ZERO; res_len];
        let pv: Vec<BE> = pc.iter().map(|col| col[r]).collect();

        air.evaluate_transition(&frame, &pv, &mut res);

        if let Some((i, v)) = res.iter().enumerate().find(|&(_, &x)| x != BE::ZERO) {
            // Build report
            let cols = layout::Columns::baseline();
            let pos = r % layout::STEPS_PER_LEVEL_P2;
            let g_map = b01(frame.current()[cols.g_map]);
            let g_final = b01(frame.current()[cols.g_final]);

            let rounds: Vec<bool> = (0..layout::POSEIDON_ROUNDS)
                .map(|j| b01(frame.current()[cols.g_r_index(j)]))
                .collect();

            let lanes_cur = (
                fe_s(frame.current()[cols.lane_l]),
                fe_s(frame.current()[cols.lane_r]),
                fe_s(frame.current()[cols.lane_c0]),
                fe_s(frame.current()[cols.lane_c1]),
            );
            let lanes_next = (
                fe_s(frame.next()[cols.lane_l]),
                fe_s(frame.next()[cols.lane_r]),
                fe_s(frame.next()[cols.lane_c0]),
                fe_s(frame.next()[cols.lane_c1]),
            );

            // Optional Poseidon expected next values;
            // first 2 rate lanes and 2 capacity lanes.
            let pose_constraints = 12 * layout::POSEIDON_ROUNDS;
            let lanes_exp = if i < pose_constraints {
                let j = i / 12;
                let ps = poseidon::get_poseidon_suite(&pub_inputs.program_id);
                let mm = ps.mds;
                let rc = ps.rc;

                // current state s
                let s: [BE; 12] = core::array::from_fn(|k| frame.current()[cols.lane_index(k)]);

                // s^3
                let s3 = s.map(|v| {
                    let v2 = v * v;
                    v2 * v
                });

                // y = MDS * s^3 + rc[j]
                let y: [BE; 12] = core::array::from_fn(|ri| {
                    let acc = (0..12).fold(BE::ZERO, |acc, c| acc + mm[ri][c] * s3[c]);
                    acc + rc[j][ri]
                });

                Some((fe_s(y[0]), fe_s(y[1]), fe_s(y[10]), fe_s(y[11])))
            } else {
                None
            };

            // RAM snapshot
            let cols = layout::Columns::baseline();
            let ram_snap = if cols.ram_sorted < trace.width() {
                Some(RamSnap {
                    sorted: frame.current()[cols.ram_sorted] == BE::ONE,
                    addr_cur: fe_s(frame.current()[cols.ram_s_addr]),
                    addr_next: fe_s(frame.next()[cols.ram_s_addr]),
                    clk_cur: fe_s(frame.current()[cols.ram_s_clk]),
                    clk_next: fe_s(frame.next()[cols.ram_s_clk]),
                    val: fe_s(frame.current()[cols.ram_s_val]),
                    is_write: fe_s(frame.current()[cols.ram_s_is_write]),
                    last_cur: fe_s(frame.current()[cols.ram_s_last_write]),
                    last_next: fe_s(frame.next()[cols.ram_s_last_write]),
                    gp_unsorted_cur: fe_s(frame.current()[cols.ram_gp_unsorted]),
                    gp_unsorted_next: fe_s(frame.next()[cols.ram_gp_unsorted]),
                    gp_sorted_cur: fe_s(frame.current()[cols.ram_gp_sorted]),
                    gp_sorted_next: fe_s(frame.next()[cols.ram_gp_sorted]),
                })
            } else {
                None
            };

            // VM write snapshot (only if write constraint area)
            let vm_snap = if (45..=52).contains(&i) {
                let wi = i - 45;
                let dst = frame.current()[cols.sel_dst0_index(wi)];

                let a_val = {
                    let mut a = BE::ZERO;
                    for k in 0..layout::NR {
                        a +=
                            frame.current()[cols.sel_a_index(k)] * frame.current()[cols.r_index(k)];
                    }

                    a
                };
                let b_val = {
                    let mut b = BE::ZERO;
                    for k in 0..layout::NR {
                        b +=
                            frame.current()[cols.sel_b_index(k)] * frame.current()[cols.r_index(k)];
                    }

                    b
                };
                let c_val = {
                    let mut c = BE::ZERO;
                    for k in 0..layout::NR {
                        c +=
                            frame.current()[cols.sel_c_index(k)] * frame.current()[cols.r_index(k)];
                    }

                    c
                };
                let b_const = frame.current()[cols.op_const];
                let b_mov = frame.current()[cols.op_mov];
                let b_add = frame.current()[cols.op_add];
                let b_sub = frame.current()[cols.op_sub];
                let b_mul = frame.current()[cols.op_mul];
                let b_neg = frame.current()[cols.op_neg];
                let b_sel = frame.current()[cols.op_select];
                let b_sponge = frame.current()[cols.op_sponge];
                let imm = frame.current()[cols.imm];

                let res_dbg = b_const * imm
                    + b_mov * a_val
                    + b_add * (a_val + b_val)
                    + b_sub * (a_val - b_val)
                    + b_mul * (a_val * b_val)
                    + b_neg * (BE::ZERO - a_val)
                    + b_sel * (c_val * a_val + (BE::ONE - c_val) * b_val)
                    + b_sponge * frame.current()[cols.lane_l];
                let lhs = frame.next()[cols.r_index(wi)]
                    - ((BE::ONE - dst) * frame.current()[cols.r_index(wi)] + dst * res_dbg);

                Some(VmSnap {
                    dst_reg: Some(wi),
                    a_val: fe_s(a_val),
                    b_val: fe_s(b_val),
                    c_val: fe_s(c_val),
                    lhs: fe_s(lhs),
                })
            } else if (144..=147).contains(&i) {
                // Sums snapshot
                let sum_dst0 = (0..layout::NR)
                    .map(|k| frame.current()[cols.sel_dst0_index(k)])
                    .fold(BE::ZERO, |acc, v| acc + v);
                let sum_a = (0..layout::NR)
                    .map(|k| frame.current()[cols.sel_a_index(k)])
                    .fold(BE::ZERO, |acc, v| acc + v);
                let sum_b = (0..layout::NR)
                    .map(|k| frame.current()[cols.sel_b_index(k)])
                    .fold(BE::ZERO, |acc, v| acc + v);
                let sum_c = (0..layout::NR)
                    .map(|k| frame.current()[cols.sel_c_index(k)])
                    .fold(BE::ZERO, |acc, v| acc + v);

                let b_const = frame.current()[cols.op_const];
                let b_mov = frame.current()[cols.op_mov];
                let b_add = frame.current()[cols.op_add];
                let b_sub = frame.current()[cols.op_sub];
                let b_mul = frame.current()[cols.op_mul];
                let b_neg = frame.current()[cols.op_neg];
                let b_eq = frame.current()[cols.op_eq];
                let b_sel = frame.current()[cols.op_select];
                let b_sponge = frame.current()[cols.op_sponge];
                let b_assert = frame.current()[cols.op_assert];

                let uses_a = b_mov + b_add + b_sub + b_mul + b_neg + b_eq + b_sel + b_sponge;
                let uses_b = b_add + b_sub + b_mul + b_eq + b_sel + b_sponge;
                let uses_c = b_sel + b_assert;
                let op_any = b_const
                    + b_mov
                    + b_add
                    + b_sub
                    + b_mul
                    + b_neg
                    + b_eq
                    + b_sel
                    + b_sponge
                    + b_assert;

                tracing::debug!(
                    target = "proof.preflight",
                    "[sums] sum_dst0={:?} sum_a={:?} sum_b={:?} sum_c={:?} uses_a={:?} uses_b={:?} uses_c={:?} op_any={:?}",
                    sum_dst0,
                    sum_a,
                    sum_b,
                    sum_c,
                    uses_a,
                    uses_b,
                    uses_c,
                    op_any
                );

                None
            } else {
                None
            };

            let report = PreflightReport {
                row: r,
                constraint_idx: i,
                constraint_val: fe_s(*v),
                pos,
                gates_map: g_map,
                gates_final: g_final,
                rounds,
                lanes_cur,
                lanes_next,
                lanes_exp,
                ram: ram_snap,
                vm: vm_snap,
                peak_live: Some(pub_inputs.compiler_stats.peak_live),
            };

            match mode {
                PreflightMode::Console => render_console(&report),
                PreflightMode::Json => match serde_json::to_string_pretty(&report) {
                    Ok(j) => println!("{j}"),
                    Err(e) => println!(
                        "{}",
                        serde_json::json!({
                            "ok": false,
                            "error": e.to_string()
                        })
                    ),
                },
                PreflightMode::Off => {}
            }

            return Err(Error::Backend(format!(
                "preflight: constraint {i} non-zero at row {r}: {v:?}"
            )));
        }
    }

    match mode {
        PreflightMode::Console => {
            let peak = pub_inputs.compiler_stats.peak_live;
            println!(
                "preflight: OK (rows={}, constraints={}, peak_live={}, reuse_dst={}, su_reorders={}, balanced_chains={}, mov_elided={})",
                trace.length(),
                res_len,
                peak,
                pub_inputs.compiler_stats.reuse_dst,
                pub_inputs.compiler_stats.su_reorders,
                pub_inputs.compiler_stats.balanced_chains,
                pub_inputs.compiler_stats.mov_elided,
            );
        }
        PreflightMode::Json => {
            println!(
                "{}",
                serde_json::json!({
                    "ok": true,
                    "rows": trace.length(),
                    "constraints": res_len,
                    "peak_live": compilers_stats.peak_live,
                    "reuse_dst": compilers_stats.reuse_dst,
                    "su_reorders": compilers_stats.su_reorders,
                    "balanced_chains": compilers_stats.balanced_chains,
                    "mov_elided": compilers_stats.mov_elided
                })
            );
        }
        PreflightMode::Off => {}
    }

    Ok(())
}

fn render_console(report: &PreflightReport) {
    let mut t = Table::new();
    t.load_preset(ASCII_BORDERS_ONLY)
        .set_content_arrangement(ContentArrangement::Dynamic)
        .set_header(vec![
            "row",
            "pos",
            "idx",
            "g_map",
            "g_fin",
            "rounds_nz",
            "lanes(cur)",
            "lanes(next)",
            "lanes(exp)",
            "ram",
            "vm",
        ]);

    let rounds_nz = report.rounds.iter().filter(|b| **b).count();
    let lanes_cur = format!(
        "{},{},{},{}",
        report.lanes_cur.0, report.lanes_cur.1, report.lanes_cur.2, report.lanes_cur.3
    );
    let lanes_next = format!(
        "{},{},{},{}",
        report.lanes_next.0, report.lanes_next.1, report.lanes_next.2, report.lanes_next.3
    );
    let lanes_exp = report
        .lanes_exp
        .as_ref()
        .map(|l| format!("{},{},{},{}", l.0, l.1, l.2, l.3))
        .unwrap_or_else(|| "-".into());

    let ram = if let Some(r) = &report.ram {
        format!(
            "S={} addr {}->{} clk {}->{} val={} w={} last {}->{} gpU {}->{} gpS {}->{}",
            if r.sorted { 1 } else { 0 },
            r.addr_cur,
            r.addr_next,
            r.clk_cur,
            r.clk_next,
            r.val,
            r.is_write,
            r.last_cur,
            r.last_next,
            r.gp_unsorted_cur,
            r.gp_unsorted_next,
            r.gp_sorted_cur,
            r.gp_sorted_next
        )
    } else {
        "-".into()
    };

    let vm = if let Some(vm) = &report.vm {
        format!(
            "dst={:?} a={} b={} c={} lhs={}",
            vm.dst_reg, vm.a_val, vm.b_val, vm.c_val, vm.lhs
        )
    } else {
        "-".into()
    };

    t.add_row(vec![
        Cell::new(format!("{}", report.row)).set_alignment(CellAlignment::Right),
        Cell::new(format!("{}", report.pos)).set_alignment(CellAlignment::Right),
        Cell::new(format!("{}", report.constraint_idx)).set_alignment(CellAlignment::Right),
        Cell::new(if report.gates_map { "1" } else { "0" }),
        Cell::new(if report.gates_final { "1" } else { "0" }),
        Cell::new(format!("{rounds_nz}")).set_alignment(CellAlignment::Right),
        Cell::new(lanes_cur),
        Cell::new(lanes_next),
        Cell::new(lanes_exp),
        Cell::new(ram),
        Cell::new(vm),
    ]);

    println!("{t}");
}

fn fe_s(x: BE) -> String {
    format!("{}", x.as_int())
}

fn b01(x: BE) -> bool {
    x == BE::ONE
}

// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use crate::air::ZkLispAir;
use crate::pi::{PublicInputs, be_from_le8};
use crate::prove::Error;
use crate::{layout, poseidon};

use comfy_table::{Cell, CellAlignment, ContentArrangement, Table, presets::ASCII_BORDERS_ONLY};
use serde::Serialize;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::math::{FieldElement, StarkField, polynom};
use winterfell::{Air, EvaluationFrame, ProofOptions, Trace, TraceInfo, TraceTable};

#[derive(Clone, Copy, Debug)]
#[allow(dead_code)]
pub enum PreflightMode {
    Off,
    Console,
    Json,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct PreflightReport {
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
    pub kv: Option<KvSnap>,
    pub vm: Option<VmSnap>,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct KvSnap {
    pub p_map: String,
    pub p_final: String,
    pub ver_cur: String,
    pub ver_next: String,
    pub acc_cur: String,
    pub acc_next: String,
    pub expect_enabled: bool,
    pub exp_map: String,
    pub exp_fin: String,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct VmSnap {
    pub dst_reg: Option<usize>,
    pub a_val: String,
    pub b_val: String,
    pub c_val: String,
    pub lhs: String,
}

pub(crate) fn run(
    mode: PreflightMode,
    options: &ProofOptions,
    pub_inputs: &PublicInputs,
    trace: &TraceTable<BE>,
) -> Result<(), Error> {
    if matches!(mode, PreflightMode::Off) {
        return Ok(());
    }

    let ti = TraceInfo::new(trace.width(), trace.length());
    let air = ZkLispAir::new(ti, pub_inputs.clone(), options.clone());
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

        for c in 0..trace.width() {
            frame0.current_mut()[c] = trace.get(c, 0);
            frame0.next_mut()[c] = trace.get(c, 1.min(trace.length() - 1));
        }

        let mut res0 = vec![BE::ZERO; res_len];
        air.evaluate_transition(&frame0, &periodic_poly_vals, &mut res0);

        let cols_dbg = layout::Columns::baseline();
        let sd0 = frame0.current()[cols_dbg.sel_dst_index(0)];
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

            let mut rounds = Vec::new();

            for j in 0..layout::POSEIDON_ROUNDS {
                rounds.push(b01(frame.current()[cols.g_r_index(j)]));
            }

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

            // Optional Poseidon expected next values
            let pose_constraints = 4 * layout::POSEIDON_ROUNDS;
            let lanes_exp = if i < pose_constraints {
                let j = i / 4;
                let mm = poseidon::derive_poseidon_mds_cauchy_4x4(&pub_inputs.program_commitment);
                let rc = poseidon::derive_poseidon_round_constants(&pub_inputs.program_commitment);
                let sl = frame.current()[cols.lane_l];
                let sr = frame.current()[cols.lane_r];
                let sc0 = frame.current()[cols.lane_c0];
                let sc1 = frame.current()[cols.lane_c1];
                let sl3 = sl * sl * sl;
                let sr3 = sr * sr * sr;
                let sc03 = sc0 * sc0 * sc0;
                let sc13 = sc1 * sc1 * sc1;
                let yl =
                    mm[0][0] * sl3 + mm[0][1] * sr3 + mm[0][2] * sc03 + mm[0][3] * sc13 + rc[j][0];
                let yr =
                    mm[1][0] * sl3 + mm[1][1] * sr3 + mm[1][2] * sc03 + mm[1][3] * sc13 + rc[j][1];
                let yc0 =
                    mm[2][0] * sl3 + mm[2][1] * sr3 + mm[2][2] * sc03 + mm[2][3] * sc13 + rc[j][2];
                let yc1 =
                    mm[3][0] * sl3 + mm[3][1] * sr3 + mm[3][2] * sc03 + mm[3][3] * sc13 + rc[j][3];

                Some((fe_s(yl), fe_s(yr), fe_s(yc0), fe_s(yc1)))
            } else {
                None
            };

            // KV snapshot
            let kv_snap = {
                let p_map = pc[0][r];
                let p_final = pc[1 + layout::POSEIDON_ROUNDS][r];
                let kv_ver = frame.current()[cols.kv_version];
                let kv_ver_next = frame.next()[cols.kv_version];
                let kv_acc_cur = frame.current()[cols.kv_acc];
                let kv_acc_next = frame.next()[cols.kv_acc];
                let exp_map = be_from_le8(&pub_inputs.kv_map_acc_bytes);
                let exp_fin = be_from_le8(&pub_inputs.kv_fin_acc_bytes);
                let exp_en = (pub_inputs.feature_mask & crate::pi::FM_KV_EXPECT) != 0;

                if (pub_inputs.feature_mask & crate::pi::FM_KV) != 0 {
                    Some(KvSnap {
                        p_map: fe_s(p_map),
                        p_final: fe_s(p_final),
                        ver_cur: fe_s(kv_ver),
                        ver_next: fe_s(kv_ver_next),
                        acc_cur: fe_s(kv_acc_cur),
                        acc_next: fe_s(kv_acc_next),
                        expect_enabled: exp_en,
                        exp_map: fe_s(exp_map),
                        exp_fin: fe_s(exp_fin),
                    })
                } else {
                    None
                }
            };

            // VM write snapshot (only if write constraint area)
            let vm_snap = if (45..=52).contains(&i) {
                let wi = i - 45;
                let dst = frame.current()[cols.sel_dst_index(wi)];
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
                let b_hash = frame.current()[cols.op_hash2];
                let imm = frame.current()[cols.imm];
                let res_dbg = b_const * imm
                    + b_mov * a_val
                    + b_add * (a_val + b_val)
                    + b_sub * (a_val - b_val)
                    + b_mul * (a_val * b_val)
                    + b_neg * (BE::ZERO - a_val)
                    + b_sel * (c_val * a_val + (BE::ONE - c_val) * b_val)
                    + b_hash * frame.current()[cols.lane_l];
                let lhs = frame.next()[cols.r_index(wi)]
                    - ((BE::ONE - dst) * frame.current()[cols.r_index(wi)] + dst * res_dbg);

                Some(VmSnap {
                    dst_reg: Some(wi),
                    a_val: fe_s(a_val),
                    b_val: fe_s(b_val),
                    c_val: fe_s(c_val),
                    lhs: fe_s(lhs),
                })
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
                kv: kv_snap,
                vm: vm_snap,
            };

            match mode {
                PreflightMode::Console => render_console(&report),
                PreflightMode::Json => println!(
                    "{}",
                    serde_json::to_string_pretty(&report).unwrap_or_default()
                ),
                PreflightMode::Off => {}
            }

            return Err(Error::Backend(format!(
                "preflight: constraint {i} non-zero at row {r}: {v:?}"
            )));
        }
    }

    match mode {
        PreflightMode::Console => {
            println!(
                "preflight: OK (rows={}, constraints={})",
                trace.length(),
                res_len
            );
        }
        PreflightMode::Json => {
            println!(
                "{}",
                serde_json::json!({
                    "ok": true,
                    "rows": trace.length(),
                    "constraints": res_len
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
            "kv",
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

    let kv = if let Some(kv) = &report.kv {
        format!(
            "p={} f={} ver {}->{} acc {}->{} exp_en={} map={} fin={}",
            kv.p_map,
            kv.p_final,
            kv.ver_cur,
            kv.ver_next,
            kv.acc_cur,
            kv.acc_next,
            kv.expect_enabled,
            kv.exp_map,
            kv.exp_fin
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
        Cell::new(kv),
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

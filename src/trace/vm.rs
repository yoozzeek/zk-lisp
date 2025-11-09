// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use crate::ir::Op;
use crate::layout::{Columns, NR, STEPS_PER_LEVEL_P2};
use crate::pi;
use crate::poseidon as poseidon_core;
use crate::schedule;
use crate::trace::poseidon;

use winterfell::TraceTable;
use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;

use super::TraceBuilder;

impl TraceBuilder {
    #[tracing::instrument(level = "info", skip(p))]
    pub fn build_from_program(p: &crate::ir::Program) -> crate::error::Result<TraceTable<BE>> {
        let levels = p.ops.len();
        let cols = Columns::baseline();
        let steps = STEPS_PER_LEVEL_P2;

        let total_levels = levels.next_power_of_two();
        let mut trace = Self::build_empty_levels(total_levels);

        // register state
        let mut regs = [BE::ZERO; NR];

        // Buffer absorbed registers
        // across levels until SSqueeze;
        // gather up to 10.
        let mut pending_regs: Vec<u8> = Vec::new();

        for (lvl, op) in p.ops.iter().enumerate() {
            // snapshot current regs and
            // compute next_regs for writes at final.
            let mut next_regs = regs;

            if lvl == 0 {
                // bind program commitment at first map row
                let row0_map = schedule::pos_map();
                let pc = pi::be_from_le8(&p.commitment);
                trace.set(cols.pi_prog, row0_map, pc);
            }

            let base = lvl * steps;
            let row_map = base + schedule::pos_map();
            let row_final = base + schedule::pos_final();

            // set Poseidon domain tags
            // at map row for all levels
            let suite = poseidon_core::get_poseidon_suite(&p.commitment);
            trace.set(cols.lane_c0, row_map, suite.dom[0]);
            trace.set(cols.lane_c1, row_map, suite.dom[1]);

            // carry register file into
            // the new level at map row.
            for (i, val) in regs.iter().enumerate().take(NR) {
                trace.set(cols.r_index(i), row_map, *val);
            }

            // zero decode/selectors for this map row
            for i in 0..NR {
                trace.set(cols.sel_dst_index(i), row_map, BE::ZERO);
                trace.set(cols.sel_a_index(i), row_map, BE::ZERO);
                trace.set(cols.sel_b_index(i), row_map, BE::ZERO);
                trace.set(cols.sel_c_index(i), row_map, BE::ZERO);
            }

            trace.set(cols.imm, row_map, BE::ZERO);
            trace.set(cols.eq_inv, row_map, BE::ZERO);

            // clear op bits
            let ops = [
                cols.op_const,
                cols.op_mov,
                cols.op_add,
                cols.op_sub,
                cols.op_mul,
                cols.op_neg,
                cols.op_eq,
                cols.op_select,
                cols.op_sponge,
                cols.op_assert,
            ];

            for &c in &ops {
                trace.set(c, row_map, BE::ZERO);
            }

            // Track per-level poseidon activity
            let mut pose_active = BE::ZERO;

            match *op {
                // ALU: write immediate to dst at final;
                // zero/clear decoders, set op bit
                // and dst selector on map.
                Op::Const { dst, imm } => {
                    trace.set(cols.op_const, row_map, BE::ONE);
                    set_sel(&mut trace, row_map, cols.sel_dst_start, dst);
                    trace.set(cols.imm, row_map, BE::from(imm));

                    // latch to final
                    trace.set(cols.op_const, row_final, BE::ONE);
                    set_sel(&mut trace, row_final, cols.sel_dst_start, dst);
                    trace.set(cols.imm, row_final, BE::from(imm));

                    next_regs[dst as usize] = BE::from(imm);
                }
                // ALU: dst = src at final;
                // selector "a" points to src
                Op::Mov { dst, src } => {
                    trace.set(cols.op_mov, row_map, BE::ONE);
                    set_sel(&mut trace, row_map, cols.sel_dst_start, dst);
                    set_sel(&mut trace, row_map, cols.sel_a_start, src);
                    trace.set(cols.op_mov, row_final, BE::ONE);
                    set_sel(&mut trace, row_final, cols.sel_dst_start, dst);
                    set_sel(&mut trace, row_final, cols.sel_a_start, src);

                    next_regs[dst as usize] = regs[src as usize];
                }
                // ALU: dst = a + b at final
                Op::Add { dst, a, b } => {
                    trace.set(cols.op_add, row_map, BE::ONE);
                    set_sel(&mut trace, row_map, cols.sel_dst_start, dst);
                    set_sel(&mut trace, row_map, cols.sel_a_start, a);
                    set_sel(&mut trace, row_map, cols.sel_b_start, b);

                    trace.set(cols.op_add, row_final, BE::ONE);
                    set_sel(&mut trace, row_final, cols.sel_dst_start, dst);
                    set_sel(&mut trace, row_final, cols.sel_a_start, a);
                    set_sel(&mut trace, row_final, cols.sel_b_start, b);

                    next_regs[dst as usize] = regs[a as usize] + regs[b as usize];
                }
                // ALU: dst = a - b at final
                Op::Sub { dst, a, b } => {
                    trace.set(cols.op_sub, row_map, BE::ONE);
                    set_sel(&mut trace, row_map, cols.sel_dst_start, dst);
                    set_sel(&mut trace, row_map, cols.sel_a_start, a);
                    set_sel(&mut trace, row_map, cols.sel_b_start, b);

                    trace.set(cols.op_sub, row_final, BE::ONE);
                    set_sel(&mut trace, row_final, cols.sel_dst_start, dst);
                    set_sel(&mut trace, row_final, cols.sel_a_start, a);
                    set_sel(&mut trace, row_final, cols.sel_b_start, b);

                    next_regs[dst as usize] = regs[a as usize] - regs[b as usize];
                }
                // ALU: dst = a * b at final
                Op::Mul { dst, a, b } => {
                    trace.set(cols.op_mul, row_map, BE::ONE);
                    set_sel(&mut trace, row_map, cols.sel_dst_start, dst);
                    set_sel(&mut trace, row_map, cols.sel_a_start, a);
                    set_sel(&mut trace, row_map, cols.sel_b_start, b);

                    trace.set(cols.op_mul, row_final, BE::ONE);
                    set_sel(&mut trace, row_final, cols.sel_dst_start, dst);
                    set_sel(&mut trace, row_final, cols.sel_a_start, a);
                    set_sel(&mut trace, row_final, cols.sel_b_start, b);

                    next_regs[dst as usize] = regs[a as usize] * regs[b as usize];
                }
                // ALU: dst = -a at final
                Op::Neg { dst, a } => {
                    trace.set(cols.op_neg, row_map, BE::ONE);
                    set_sel(&mut trace, row_map, cols.sel_dst_start, dst);
                    set_sel(&mut trace, row_map, cols.sel_a_start, a);

                    trace.set(cols.op_neg, row_final, BE::ONE);
                    set_sel(&mut trace, row_final, cols.sel_dst_start, dst);
                    set_sel(&mut trace, row_final, cols.sel_a_start, a);

                    next_regs[dst as usize] = BE::ZERO - regs[a as usize];
                }
                // ALU: dst = (a == b) ? 1 : 0 at final;
                // set eq_inv witness on map
                Op::Eq { dst, a, b } => {
                    trace.set(cols.op_eq, row_map, BE::ONE);
                    set_sel(&mut trace, row_map, cols.sel_dst_start, dst);
                    set_sel(&mut trace, row_map, cols.sel_a_start, a);
                    set_sel(&mut trace, row_map, cols.sel_b_start, b);

                    // latch op bit and selectors to final
                    trace.set(cols.op_eq, row_final, BE::ONE);
                    set_sel(&mut trace, row_final, cols.sel_dst_start, dst);
                    set_sel(&mut trace, row_final, cols.sel_a_start, a);
                    set_sel(&mut trace, row_final, cols.sel_b_start, b);

                    let diff = regs[a as usize] - regs[b as usize];
                    let w = if diff == BE::ZERO { BE::ONE } else { BE::ZERO };
                    let inv = if diff != BE::ZERO {
                        diff.inv()
                    } else {
                        BE::ZERO
                    };

                    trace.set(cols.eq_inv, row_map, inv);
                    trace.set(cols.eq_inv, row_final, inv);

                    next_regs[dst as usize] = w;
                }
                // ALU: dst = c ? a : b at final;
                // c must be boolean
                Op::Select { dst, c, a, b } => {
                    trace.set(cols.op_select, row_map, BE::ONE);
                    set_sel(&mut trace, row_map, cols.sel_dst_start, dst);
                    set_sel(&mut trace, row_map, cols.sel_c_start, c);
                    set_sel(&mut trace, row_map, cols.sel_a_start, a);
                    set_sel(&mut trace, row_map, cols.sel_b_start, b);

                    trace.set(cols.op_select, row_final, BE::ONE);
                    set_sel(&mut trace, row_final, cols.sel_dst_start, dst);
                    set_sel(&mut trace, row_final, cols.sel_c_start, c);
                    set_sel(&mut trace, row_final, cols.sel_a_start, a);
                    set_sel(&mut trace, row_final, cols.sel_b_start, b);

                    let cond = regs[c as usize];
                    next_regs[dst as usize] =
                        cond * regs[a as usize] + (BE::ONE - cond) * regs[b as usize];
                }
                Op::Assert { dst, c } => {
                    trace.set(cols.op_assert, row_map, BE::ONE);
                    set_sel(&mut trace, row_map, cols.sel_dst_start, dst);
                    set_sel(&mut trace, row_map, cols.sel_c_start, c);

                    trace.set(cols.op_assert, row_final, BE::ONE);
                    set_sel(&mut trace, row_final, cols.sel_dst_start, dst);
                    set_sel(&mut trace, row_final, cols.sel_c_start, c);

                    // write 1 at final
                    next_regs[dst as usize] = BE::ONE;
                }
                Op::SAbsorb2 { a, b } => {
                    // Treat as SAbsorbN with 2 regs;
                    // do not execute permutation now.
                    trace.set(cols.op_sponge, row_map, BE::ONE);
                    trace.set(cols.op_sponge, row_final, BE::ONE);

                    // Set sponge lane selectors
                    // for lanes 0..N-1.
                    trace.set(cols.sel_s_index(0, a as usize), row_map, BE::ONE);
                    trace.set(cols.sel_s_index(1, b as usize), row_map, BE::ONE);
                    trace.set(cols.sel_s_index(0, a as usize), row_final, BE::ONE);
                    trace.set(cols.sel_s_index(1, b as usize), row_final, BE::ONE);

                    // Accumulate regs for later
                    // permutation at SSqueeze.
                    if pending_regs.len() < 10 {
                        pending_regs.push(a);
                    }
                    if pending_regs.len() < 10 {
                        pending_regs.push(b);
                    }

                    // This level is inactive for Poseidon
                    pose_active = BE::ZERO;
                }
                Op::SSqueeze { dst } => {
                    // Execute one permutation
                    // absorbing all pending regs (<=10)
                    trace.set(cols.op_sponge, row_final, BE::ONE);
                    set_sel(&mut trace, row_final, cols.sel_dst_start, dst);

                    let mut inputs: Vec<BE> = Vec::with_capacity(pending_regs.len());
                    for &r in &pending_regs {
                        inputs.push(regs[r as usize]);
                    }

                    // If empty (no prior absorbs),
                    // treat as zeros to keep semantics.
                    pose_active = BE::ONE;
                    poseidon::apply_level_absorb(&mut trace, &p.commitment, lvl, &inputs);

                    let out = trace.get(cols.lane_index(0), row_final);
                    next_regs[dst as usize] = out;

                    pending_regs.clear();
                }
                Op::SAbsorbN { regs: ref rr } => {
                    // Mark sponge op at map/final,
                    // set selectors for provided regs.
                    trace.set(cols.op_sponge, row_map, BE::ONE);
                    trace.set(cols.op_sponge, row_final, BE::ONE);

                    for (i, &r) in rr.iter().enumerate() {
                        if i >= 10 {
                            break;
                        }

                        trace.set(cols.sel_s_index(i, r as usize), row_map, BE::ONE);
                        trace.set(cols.sel_s_index(i, r as usize), row_final, BE::ONE);

                        if pending_regs.len() < 10 {
                            pending_regs.push(r);
                        }
                    }

                    // No permutation at absorb rows
                    pose_active = BE::ZERO;
                }
                Op::KvMap { dir, sib_reg } => {
                    // KV map+final in one level
                    pose_active = BE::ONE;

                    trace.set(cols.kv_g_map, row_map, BE::ONE);
                    trace.set(cols.kv_dir, row_map, BE::from(dir as u64));

                    let sib = regs[sib_reg as usize];
                    trace.set(cols.kv_sib, row_map, sib);

                    // Select lanes and apply poseidon
                    let acc_cur = trace.get(cols.kv_acc, row_map);
                    let d = BE::from(dir as u64);
                    let left = (BE::ONE - d) * acc_cur + d * sib;
                    let right = (BE::ONE - d) * sib + d * acc_cur;

                    poseidon::apply_level_absorb(&mut trace, &p.commitment, lvl, &[left, right]);

                    // Mark final and set acc at/after final
                    trace.set(cols.kv_g_final, row_final, BE::ONE);

                    let out = trace.get(cols.lane_l, row_final);
                    for r in row_final..(base + steps) {
                        trace.set(cols.kv_acc, r, out);
                    }

                    // Set prev_acc at row after final
                    let row_next = row_final + 1;
                    if row_next < base + steps {
                        trace.set(cols.kv_prev_acc, row_next, out);
                    }

                    // Version: hold before/at final,
                    // bump after final
                    let ver = trace.get(cols.kv_version, row_map);

                    for r in base..=row_final {
                        trace.set(cols.kv_version, r, ver);
                    }

                    for r in (row_final + 1)..(base + steps) {
                        trace.set(cols.kv_version, r, ver + BE::ONE);
                    }
                }
                Op::KvFinal => {
                    // Only bump version at final
                    trace.set(cols.kv_g_final, row_final, BE::ONE);

                    let ver = trace.get(cols.kv_version, row_map);
                    for r in base..=row_final {
                        trace.set(cols.kv_version, r, ver)
                    }

                    for r in (row_final + 1)..(base + steps) {
                        trace.set(cols.kv_version, r, ver + BE::ONE);
                    }
                }
                Op::End => {}
            }

            // rows between map..=final:
            // keep old regs (pre-write state)
            for r in (row_map + 1)..=row_final {
                for (i, val) in regs.iter().enumerate().take(NR) {
                    trace.set(cols.r_index(i), r, *val);
                }
            }

            // after final within level: keep next_regs
            for r in (row_final + 1)..(base + steps) {
                for (i, val) in next_regs.iter().enumerate().take(NR) {
                    trace.set(cols.r_index(i), r, *val);
                }
            }

            // commit next_regs to regs for next level.
            // also set pose_active across the whole level
            for r in base..(base + steps) {
                trace.set(cols.pose_active, r, pose_active);
            }

            regs = next_regs;
        }

        // Ensure Poseidon domain tags are
        // present on map rows for all levels.
        let dom_all = poseidon_core::get_poseidon_suite(&p.commitment).dom;

        for lvl in 0..total_levels {
            let base = lvl * steps;
            let row_map = base + schedule::pos_map();
            trace.set(cols.lane_c0, row_map, dom_all[0]);
            trace.set(cols.lane_c1, row_map, dom_all[1]);
        }

        Ok(trace)
    }
}

#[inline]
fn set_sel(trace: &mut TraceTable<BE>, row: usize, sel_start: usize, idx: u8) {
    for i in 0..NR {
        trace.set(sel_start + i, row, BE::ZERO);
    }

    trace.set(sel_start + (idx as usize), row, BE::ONE);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::Op;
    use winterfell::Trace;
    // for length()

    #[test]
    fn alu_const_add() {
        let mut b = crate::ir::ProgramBuilder::new();
        b.push(Op::Const { dst: 0, imm: 7 });
        b.push(Op::Const { dst: 1, imm: 9 });
        b.push(Op::Add { dst: 2, a: 0, b: 1 });
        b.push(Op::End);

        let p = b.finalize();

        let trace = TraceBuilder::build_from_program(&p).unwrap();
        let cols = Columns::baseline();
        let steps = STEPS_PER_LEVEL_P2;

        // level 0: const r0=7
        let base0 = 0;
        let row0_map = base0 + schedule::pos_map();
        let row0_fin = base0 + schedule::pos_final();

        assert_eq!(trace.get(cols.op_const, row0_map), BE::ONE);
        assert_eq!(trace.get(cols.r_index(0), row0_fin + 1), BE::from(7u64));

        // level 1: const r1=9
        let base1 = steps;
        let row1_map = base1 + schedule::pos_map();
        let row1_fin = base1 + schedule::pos_final();

        assert_eq!(trace.get(cols.op_const, row1_map), BE::ONE);
        assert_eq!(trace.get(cols.r_index(1), row1_fin + 1), BE::from(9u64));

        // level 2: add r2=r0+r1=16
        let base2 = 2 * steps;
        let row2_map = base2 + schedule::pos_map();
        let row2_fin = base2 + schedule::pos_final();

        assert_eq!(trace.get(cols.op_add, row2_map), BE::ONE);
        assert_eq!(trace.get(cols.r_index(2), row2_fin + 1), BE::from(16u64));

        // total rows
        assert_eq!(trace.length(), 4 * steps);
    }

    #[test]
    fn alu_eq_and_select() {
        let mut b = crate::ir::ProgramBuilder::new();
        b.push(Op::Const { dst: 0, imm: 5 });
        b.push(Op::Const { dst: 1, imm: 5 });
        b.push(Op::Eq { dst: 2, a: 0, b: 1 }); // r2=1
        b.push(Op::Select {
            dst: 3,
            c: 2,
            a: 0,
            b: 1,
        }); // r3=r0 (both equal)

        b.push(Op::End);

        let p = b.finalize();

        let trace = TraceBuilder::build_from_program(&p).unwrap();
        let cols = Columns::baseline();
        let steps = STEPS_PER_LEVEL_P2;

        // level 2 EQ
        let base2 = 2 * steps;
        let row2_map = base2 + schedule::pos_map();
        let row2_fin = base2 + schedule::pos_final();

        assert_eq!(trace.get(cols.op_eq, row2_map), BE::ONE);
        assert_eq!(trace.get(cols.r_index(2), row2_fin + 1), BE::ONE);

        // level 3 SELECT
        let base3 = 3 * steps;
        let row3_map = base3 + schedule::pos_map();
        let row3_fin = base3 + schedule::pos_final();

        assert_eq!(trace.get(cols.op_select, row3_map), BE::ONE);
        assert_eq!(trace.get(cols.r_index(3), row3_fin + 1), BE::from(5u64));

        assert_eq!(trace.length(), 8 * steps);
    }

    #[test]
    fn sponge_absorb_squeeze_simple() {
        // Check that SAbsorb2+SSqueeze writes
        // Poseidon(left,right) into dst.
        let mut b = crate::ir::ProgramBuilder::new();
        b.push(Op::Const { dst: 0, imm: 1 });
        b.push(Op::Const { dst: 1, imm: 2 });
        b.push(Op::SAbsorb2 { a: 0, b: 1 });
        b.push(Op::SSqueeze { dst: 3 });
        b.push(Op::End);

        let p = b.finalize();

        let trace = TraceBuilder::build_from_program(&p).unwrap();
        let cols = Columns::baseline();
        let steps = STEPS_PER_LEVEL_P2;

        // Level 2 (SSqueeze) performs the write
        let base3 = 3 * steps;
        let row3_fin = base3 + schedule::pos_final();

        assert_eq!(trace.get(cols.op_sponge, row3_fin), BE::ONE);

        // Expected hash from inputs at absorb level
        let left = trace.get(cols.r_index(0), 2 * steps + schedule::pos_map());
        let right = trace.get(cols.r_index(1), 2 * steps + schedule::pos_map());
        let expected = poseidon_core::poseidon_hash_two_lanes(&p.commitment, left, right);

        assert_eq!(trace.get(cols.r_index(3), row3_fin + 1), expected);
    }

    #[test]
    fn program_commit_bound_at_level0() {
        let mut b = crate::ir::ProgramBuilder::new();
        b.push(Op::Const { dst: 0, imm: 1 });
        b.push(Op::End);

        let p = b.finalize();

        let trace = TraceBuilder::build_from_program(&p).unwrap();
        let cols = Columns::baseline();

        let row0_map = schedule::pos_map();
        let pc = pi::be_from_le8(&p.commitment);

        assert_eq!(trace.get(cols.pi_prog, row0_map), pc);
    }
}

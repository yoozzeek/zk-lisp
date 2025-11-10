// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use winterfell::TraceTable;
use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;

use crate::layout::{self, Columns, POSEIDON_ROUNDS};
use crate::{poseidon, schedule};

// Apply one Poseidon level at `level`
// absorbing up to 10 inputs. Map row:
// set lane[0..inputs.len()) = inputs, lane[10..12) = domain tags,
// rest of rate lanes are set to 0.
// Then apply R rounds and write final row.
pub fn apply_level_absorb(
    trace: &mut TraceTable<BE>,
    suite_id: &[u8; 32],
    level: usize,
    inputs: &[BE],
) {
    let cols = Columns::baseline();
    let steps = layout::STEPS_PER_LEVEL_P2;
    let base = level * steps;
    let row_map = base + schedule::pos_map();

    let suite = poseidon::get_poseidon_suite(suite_id);

    // map row
    let n = inputs.len().min(10);

    for (i, &v) in inputs.iter().take(10).enumerate() {
        trace.set(cols.lane_index(i), row_map, v);
    }

    if n < 10 {
        for i in n..10 {
            trace.set(cols.lane_index(i), row_map, BE::ZERO);
        }
    }

    trace.set(cols.lane_c0, row_map, suite.dom[0]);
    trace.set(cols.lane_c1, row_map, suite.dom[1]);

    // iterate rounds;
    // maintain full 12-lane state
    let mut s: [BE; 12] = core::array::from_fn(|i| trace.get(cols.lane_index(i), row_map));

    for (j, rcj) in suite.rc.iter().enumerate().take(POSEIDON_ROUNDS) {
        let r = base + 1 + j; // round row

        // set current state on round row (s_j)
        for (i, &val) in s.iter().enumerate() {
            trace.set(cols.lane_index(i), r, val);
        }

        // compute next state
        // s_{j+1}: y = MDS * s^3 + rc
        let s3 = s.map(|v| {
            let v2 = v * v;
            v2 * v
        });

        let y: [BE; 12] = core::array::from_fn(|i| {
            let acc = (0..12).fold(BE::ZERO, |acc, k| acc + suite.mds[i][k] * s3[k]);
            acc + rcj[i]
        });

        s = y;
    }

    // set final row to last state for convenience
    let row_fin = base + schedule::pos_final();
    for (i, &v) in s.iter().enumerate() {
        trace.set(cols.lane_index(i), row_fin, v);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::trace::TraceBuilder;

    fn sponge_ref(inputs: &[BE], suite_id: &[u8; 32]) -> BE {
        let ps = poseidon::get_poseidon_suite(suite_id);
        let mut s = [BE::ZERO; 12];

        for (i, &v) in inputs.iter().take(10).enumerate() {
            s[i] = v;
        }

        s[10] = ps.dom[0];
        s[11] = ps.dom[1];

        for rc in &ps.rc {
            for x in &mut s {
                *x = *x * *x * *x;
            }

            let mut y = [BE::ZERO; 12];
            for (i, row) in ps.mds.iter().enumerate() {
                let acc = row
                    .iter()
                    .zip(s.iter())
                    .fold(BE::ZERO, |acc, (m, v)| acc + (*m) * (*v));
                y[i] = acc + rc[i];
            }

            s = y;
        }

        s[0]
    }

    pub fn copy_level(trace: &mut TraceTable<BE>, src_level: usize, dst_level: usize) {
        let cols = Columns::baseline();
        let steps = layout::STEPS_PER_LEVEL_P2;

        let src_base = src_level * steps;
        let dst_base = dst_level * steps;

        // map row
        let src_map = src_base + schedule::pos_map();
        let dst_map = dst_base + schedule::pos_map();

        for i in 0..12 {
            let v = trace.get(cols.lane_index(i), src_map);
            trace.set(cols.lane_index(i), dst_map, v);
        }

        // rounds
        for j in 0..POSEIDON_ROUNDS {
            let src_r = src_base + 1 + j;
            let dst_r = dst_base + 1 + j;

            for i in 0..12 {
                let v = trace.get(cols.lane_index(i), src_r);
                trace.set(cols.lane_index(i), dst_r, v);
            }
        }

        // final row
        let src_fin = src_base + schedule::pos_final();
        let dst_fin = dst_base + schedule::pos_final();

        for i in 0..12 {
            let v = trace.get(cols.lane_index(i), src_fin);
            trace.set(cols.lane_index(i), dst_fin, v);
        }
    }

    #[test]
    fn absorb_0_2_10_match_reference() {
        let cols = Columns::baseline();
        let mut trace = TraceBuilder::build_empty_levels(1);
        let sid = [3u8; 32];
        let level = 0usize;

        // N=0
        apply_level_absorb(&mut trace, &sid, level, &[]);

        let fin = level * layout::STEPS_PER_LEVEL_P2 + schedule::pos_final();
        let out0 = trace.get(cols.lane_index(0), fin);
        assert_eq!(out0, sponge_ref(&[], &sid));

        // N=2
        let mut trace = TraceBuilder::build_empty_levels(1);
        apply_level_absorb(&mut trace, &sid, level, &[BE::from(1u64), BE::from(2u64)]);

        let fin = level * layout::STEPS_PER_LEVEL_P2 + schedule::pos_final();
        let out2 = trace.get(cols.lane_index(0), fin);
        assert_eq!(out2, sponge_ref(&[BE::from(1u64), BE::from(2u64)], &sid));

        // N=10
        let mut trace = TraceBuilder::build_empty_levels(1);
        let inputs: Vec<BE> = (0u64..10).map(BE::from).collect();
        apply_level_absorb(&mut trace, &sid, level, &inputs);

        let fin = level * layout::STEPS_PER_LEVEL_P2 + schedule::pos_final();
        let out10 = trace.get(cols.lane_index(0), fin);
        assert_eq!(out10, sponge_ref(&inputs, &sid));
    }

    #[test]
    fn copy_level_clones_rows() {
        let cols = Columns::baseline();
        let mut trace = TraceBuilder::build_empty_levels(2);
        let sid = [9u8; 32];

        // write level 0
        apply_level_absorb(&mut trace, &sid, 0, &[BE::from(5u64), BE::from(7u64)]);
        // copy to level 1
        copy_level(&mut trace, 0, 1);

        let steps = layout::STEPS_PER_LEVEL_P2;
        for pos in [schedule::pos_map(), 1, 2, schedule::pos_final()] {
            let r0 = pos;
            let r1 = steps + pos;

            for i in 0..12 {
                assert_eq!(
                    trace.get(cols.lane_index(i), r0),
                    trace.get(cols.lane_index(i), r1)
                );
            }
        }
    }
}

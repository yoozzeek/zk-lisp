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

/// Copy Poseidon lanes such as map, all rounds,
/// final from src_level to dst_level.
#[allow(dead_code)]
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

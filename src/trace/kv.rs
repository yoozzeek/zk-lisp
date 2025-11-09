// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use winterfell::Trace;
use winterfell::TraceTable;
use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;

use super::poseidon;
use crate::layout::{Columns, STEPS_PER_LEVEL_P2};
use crate::schedule;

pub enum KvEvent {
    Map { level: usize, dir: u32, sib: BE },
    Final { level: usize },
}

pub struct KvOverlayConfig {
    pub suite_id: [u8; 32],
    pub start_version: BE,
    pub acc0: BE,
}

impl KvOverlayConfig {
    pub fn new(start_version: u64, acc0: u64) -> Self {
        Self {
            start_version: BE::from(start_version),
            acc0: BE::from(acc0),
            suite_id: [0u8; 32],
        }
    }

    pub fn new_with_suite(start_version: u64, acc0: u64, suite_id: [u8; 32]) -> Self {
        Self {
            start_version: BE::from(start_version),
            acc0: BE::from(acc0),

            suite_id,
        }
    }
}

pub fn overlay_kv(trace: &mut TraceTable<BE>, events: &[KvEvent], cfg: KvOverlayConfig) {
    let cols = Columns::baseline();
    let steps = STEPS_PER_LEVEL_P2;
    let n_rows = trace.length();

    // initialize version/acc across all rows
    for r in 0..n_rows {
        trace.set(cols.kv_version, r, cfg.start_version);
    }

    for r in 0..n_rows {
        trace.set(cols.kv_acc, r, cfg.acc0);
    }

    for ev in events {
        match *ev {
            KvEvent::Map { level, dir, sib } => {
                let base = level * steps;
                let row_map = base + schedule::pos_map();
                let row_fin = base + schedule::pos_final();
                trace.set(cols.kv_g_map, row_map, BE::ONE);
                trace.set(cols.kv_g_final, row_fin, BE::ONE);

                // carry version across map..final
                let ver = trace.get(cols.kv_version, row_map);

                for r in base..=row_fin {
                    trace.set(cols.kv_version, r, ver);
                }

                for r in (row_fin + 1)..(base + steps) {
                    trace.set(cols.kv_version, r, ver + BE::ONE);
                }

                // lanes and acc
                let acc = trace.get(cols.kv_acc, row_map);
                let d = BE::from(dir as u64);
                trace.set(cols.kv_dir, row_map, d);
                trace.set(cols.kv_sib, row_map, sib);

                let left = (BE::ONE - d) * acc + d * sib;
                let right = (BE::ONE - d) * sib + d * acc;

                // Poseidon with provided suite_id
                poseidon::apply_level(trace, &cfg.suite_id, level, left, right);

                let out = trace.get(cols.lane_l, row_fin);
                for r in row_fin..(base + steps) {
                    trace.set(cols.kv_acc, r, out);
                }

                // prev_acc at row after final
                let row_next = row_fin + 1;
                if row_next < base + steps {
                    trace.set(cols.kv_prev_acc, row_next, out);
                }
            }
            KvEvent::Final { level } => {
                let base = level * steps;
                let row_fin = base + schedule::pos_final();
                let ver = trace.get(cols.kv_version, base + schedule::pos_map());

                for r in base..=row_fin {
                    trace.set(cols.kv_version, r, ver);
                }

                for r in (row_fin + 1)..(base + steps) {
                    trace.set(cols.kv_version, r, ver + BE::ONE);
                }

                trace.set(cols.kv_g_final, row_fin, BE::ONE);
            }
        }
    }
}

pub fn build_kv_multi_levels(levels: &[(u32, u32, u32)], cfg: KvOverlayConfig) -> TraceTable<BE> {
    let depth = levels.len();
    let cols = Columns::baseline();
    let width = cols.width(0);

    let mut trace = TraceTable::new(width, depth * STEPS_PER_LEVEL_P2);

    // zero + schedule
    for r in 0..trace.length() {
        for c in 0..width {
            trace.set(c, r, BE::ZERO);
        }
    }

    // tie gates for rows
    for lvl in 0..depth {
        let base = lvl * STEPS_PER_LEVEL_P2;
        let row_map = base + schedule::pos_map();
        let row_fin = base + schedule::pos_final();
        trace.set(cols.g_map, row_map, BE::ONE);
        trace.set(cols.g_final, row_fin, BE::ONE);

        for j in 0..crate::layout::POSEIDON_ROUNDS {
            trace.set(cols.g_r_index(j), base + 1 + j, BE::ONE);
        }
    }

    // events
    let mut events = Vec::with_capacity(depth * 2);
    for (lvl, (acc, sib, dir)) in levels.iter().enumerate() {
        // seed acc at map row for this level
        let row_map = lvl * STEPS_PER_LEVEL_P2 + schedule::pos_map();
        trace.set(cols.kv_acc, row_map, BE::from(*acc as u64));
        events.push(KvEvent::Map {
            level: lvl,
            dir: *dir,
            sib: BE::from(*sib as u64),
        });
    }

    overlay_kv(&mut trace, &events, cfg);

    trace
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn kv_single_level_dir0() {
        let cols = Columns::baseline();
        let steps = STEPS_PER_LEVEL_P2;

        let mut trace = crate::trace::TraceBuilder::build_empty_levels(1);

        // seed acc at level 0 map
        let row_map = schedule::pos_map();
        let row_fin = schedule::pos_final();
        trace.set(cols.kv_acc, row_map, BE::from(10u64));

        let events = vec![KvEvent::Map {
            level: 0,
            dir: 0,
            sib: BE::from(7u64),
        }];
        overlay_kv(&mut trace, &events, KvOverlayConfig::new(0, 10));

        // gates
        assert_eq!(trace.get(cols.kv_g_map, row_map), BE::ONE);
        assert_eq!(trace.get(cols.kv_g_final, row_fin), BE::ONE);

        // lanes at map
        let left = trace.get(cols.lane_l, row_map);
        let right = trace.get(cols.lane_r, row_map);
        assert_eq!(left, BE::from(10u64));
        assert_eq!(right, BE::from(7u64));

        // version stays till final, then bumps
        assert_eq!(trace.get(cols.kv_version, row_map), BE::from(0u64));
        assert_eq!(trace.get(cols.kv_version, row_fin), BE::from(0u64));
        assert_eq!(trace.get(cols.kv_version, steps - 1), BE::from(1u64));

        // acc equals lane_l at final and after
        let out = trace.get(cols.lane_l, row_fin);
        assert_eq!(trace.get(cols.kv_acc, row_fin), out);
        assert_eq!(trace.get(cols.kv_acc, steps - 1), out);
    }

    #[test]
    fn kv_single_level_dir1() {
        let cols = Columns::baseline();
        let steps = STEPS_PER_LEVEL_P2;

        let mut trace = crate::trace::TraceBuilder::build_empty_levels(1);

        let row_map = schedule::pos_map();
        let row_fin = schedule::pos_final();
        trace.set(cols.kv_acc, row_map, BE::from(11u64));

        let events = vec![KvEvent::Map {
            level: 0,
            dir: 1,
            sib: BE::from(3u64),
        }];
        overlay_kv(&mut trace, &events, KvOverlayConfig::new(5, 11));

        // gates
        assert_eq!(trace.get(cols.kv_g_map, row_map), BE::ONE);
        assert_eq!(trace.get(cols.kv_g_final, row_fin), BE::ONE);

        // lanes at map swapped
        let left = trace.get(cols.lane_l, row_map);
        let right = trace.get(cols.lane_r, row_map);
        assert_eq!(left, BE::from(3u64));
        assert_eq!(right, BE::from(11u64));

        // version
        assert_eq!(trace.get(cols.kv_version, row_map), BE::from(5u64));
        assert_eq!(trace.get(cols.kv_version, row_fin), BE::from(5u64));
        assert_eq!(trace.get(cols.kv_version, steps - 1), BE::from(6u64));

        // acc equals lane_l at final and after
        let out = trace.get(cols.lane_l, row_fin);
        assert_eq!(trace.get(cols.kv_acc, row_fin), out);
        assert_eq!(trace.get(cols.kv_acc, steps - 1), out);
    }
}

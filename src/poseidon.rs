// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use std::collections::HashMap;
use std::sync::{OnceLock, RwLock};
use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;

use crate::layout::POSEIDON_ROUNDS;
use crate::utils;

const DOM_POSEIDON_RC: &str = "zkl/poseidon2/rc";
const DOM_POSEIDON_DOM0: &str = "zkl/poseidon2/dom/c0";
const DOM_POSEIDON_DOM1: &str = "zkl/poseidon2/dom/c1";
const DOM_POSEIDON_MDS_X: &str = "zkl/poseidon2/mds/x";
const DOM_POSEIDON_MDS_Y: &str = "zkl/poseidon2/mds/y";

#[derive(Clone)]
pub struct PoseidonSuite {
    pub dom: [BE; 2],
    pub mds: [[BE; 4]; 4],
    pub rc: [[BE; 4]; POSEIDON_ROUNDS],
}

static POSEIDON_CACHE: OnceLock<RwLock<HashMap<[u8; 32], PoseidonSuite>>> = OnceLock::new();

pub fn get_poseidon_suite(suite_id: &[u8; 32]) -> PoseidonSuite {
    if let Some(found) = cache().read().ok().and_then(|m| m.get(suite_id).cloned()) {
        return found;
    }

    let dom = derive_poseidon_domain_tags(suite_id);
    let rc = derive_poseidon_round_constants(suite_id);
    let mds = derive_poseidon_mds_cauchy_4x4(suite_id);
    let suite = PoseidonSuite { dom, mds, rc };

    if let Ok(mut w) = cache().write() {
        w.insert(*suite_id, suite.clone());
    }

    suite
}

pub fn derive_poseidon_round_constants(suite_id: &[u8; 32]) -> [[BE; 4]; POSEIDON_ROUNDS] {
    let mut rc = [[BE::ZERO; 4]; POSEIDON_ROUNDS];
    for (r, lanes) in rc.iter_mut().enumerate() {
        for (lane, cell) in lanes.iter_mut().enumerate() {
            let r_b = [r as u8];
            let lane_b = [lane as u8];
            *cell = ro_from_slices(DOM_POSEIDON_RC, &[&suite_id[..], &r_b[..], &lane_b[..]]);
        }
    }

    rc
}

pub fn derive_poseidon_domain_tags(suite_id: &[u8; 32]) -> [BE; 2] {
    [
        ro_from_slices(DOM_POSEIDON_DOM0, &[&suite_id[..]]),
        ro_from_slices(DOM_POSEIDON_DOM1, &[&suite_id[..]]),
    ]
}

pub fn derive_poseidon_mds_cauchy_4x4(suite_id: &[u8; 32]) -> [[BE; 4]; 4] {
    fn derive_points(domain: &str, suite_id: &[u8; 32], n: usize) -> Vec<BE> {
        let mut pts = Vec::with_capacity(n);
        let mut ctr: u32 = 0;

        while pts.len() < n {
            let idx_b = [pts.len() as u8];
            let ctr_b = ctr.to_le_bytes();
            let cand = ro_from_slices(domain, &[&suite_id[..], &idx_b[..], &ctr_b[..]]);

            if cand != BE::ZERO && !pts.contains(&cand) {
                pts.push(cand);
            } else {
                ctr = ctr.wrapping_add(1);
            }
        }

        pts
    }

    let x = derive_points(DOM_POSEIDON_MDS_X, suite_id, 4);
    let mut y = derive_points(DOM_POSEIDON_MDS_Y, suite_id, 4);

    let mut adj_ctr: u32 = 0;
    loop {
        let mut ok = true;

        'outer: for xi in &x {
            for yj in &y {
                if *xi + *yj == BE::ZERO {
                    ok = false;
                    break 'outer;
                }
            }
        }

        if ok {
            break;
        }

        for (j, yj) in y.iter_mut().enumerate() {
            let j_b = [j as u8];
            let adj_b = adj_ctr.to_le_bytes();
            let cand = ro_from_slices(DOM_POSEIDON_MDS_Y, &[&suite_id[..], &j_b[..], &adj_b[..]]);

            *yj = if cand == BE::ZERO {
                BE::from(1u64)
            } else {
                cand
            };
        }

        adj_ctr = adj_ctr.wrapping_add(1);
    }

    let mut m = [[BE::ZERO; 4]; 4];
    for i in 0..4 {
        for (j, yj) in y.iter().enumerate().take(4) {
            let denom = x[i] + *yj;
            m[i][j] = denom.inv();
        }
    }

    m
}

pub fn poseidon_hash_two_lanes(suite_id: &[u8; 32], left: BE, right: BE) -> BE {
    let suite = get_poseidon_suite(suite_id);
    let mut state = [left, right, suite.dom[0], suite.dom[1]];

    for rc_r in suite.rc.iter() {
        let sl = state[0] * state[0] * state[0];
        let sr = state[1] * state[1] * state[1];
        let sc0 = state[2] * state[2] * state[2];
        let sc1 = state[3] * state[3] * state[3];

        let yl = suite.mds[0][0] * sl
            + suite.mds[0][1] * sr
            + suite.mds[0][2] * sc0
            + suite.mds[0][3] * sc1
            + rc_r[0];
        let yr = suite.mds[1][0] * sl
            + suite.mds[1][1] * sr
            + suite.mds[1][2] * sc0
            + suite.mds[1][3] * sc1
            + rc_r[1];
        let yc0 = suite.mds[2][0] * sl
            + suite.mds[2][1] * sr
            + suite.mds[2][2] * sc0
            + suite.mds[2][3] * sc1
            + rc_r[2];
        let yc1 = suite.mds[3][0] * sl
            + suite.mds[3][1] * sr
            + suite.mds[3][2] * sc0
            + suite.mds[3][3] * sc1
            + rc_r[3];

        state = [yl, yr, yc0, yc1];
    }

    state[0]
}

// Random-oracle-to-field:
// blake3(domain || parts...) folded into FE
fn ro_from_slices(domain: &str, parts: &[&[u8]]) -> BE {
    let mut h = blake3::Hasher::new();
    h.update(domain.as_bytes());

    for p in parts {
        h.update(p);
    }

    let digest = h.finalize();
    let bytes = digest.as_bytes();

    // fold low 16 bytes as LE u128
    // into field: lo + hi * 2^64.
    let mut le16 = [0u8; 16];
    le16.copy_from_slice(&bytes[0..16]);

    let val = u128::from_le_bytes(le16);
    let lo = (val & 0xFFFF_FFFF_FFFF_FFFFu128) as u64;
    let hi = (val >> 64) as u64;

    BE::from(lo) + BE::from(hi) * utils::pow2_64()
}

fn cache() -> &'static RwLock<HashMap<[u8; 32], PoseidonSuite>> {
    POSEIDON_CACHE.get_or_init(|| RwLock::new(HashMap::new()))
}

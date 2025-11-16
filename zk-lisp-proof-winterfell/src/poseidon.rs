// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Deterministic derivation of Poseidon2 parameters.
//!
//! Derives domain tags, MDS matrices and round constants for
//! the t=12 sponge and t=3 ROM hash, including a checked
//! mode used to validate suites during configuration.

use std::collections::HashMap;
use std::sync::{OnceLock, RwLock};
use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;

use crate::{layout::POSEIDON_ROUNDS, utils};

const DOM_POSEIDON_RC: &str = "zkl/poseidon2/rc";
const DOM_POSEIDON_DOM0: &str = "zkl/poseidon2/dom/c0";
const DOM_POSEIDON_DOM1: &str = "zkl/poseidon2/dom/c1";
const DOM_POSEIDON_MDS_X: &str = "zkl/poseidon2/mds/x";
const DOM_POSEIDON_MDS_Y: &str = "zkl/poseidon2/mds/y";

// Domains for ROM t=3 parameters
const DOM_ROM_RC: &str = "zkl/rom3/rc";
const DOM_ROM_MDS_X: &str = "zkl/rom3/mds/x";
const DOM_ROM_MDS_Y: &str = "zkl/rom3/mds/y";

#[derive(Clone)]
pub struct PoseidonSuite {
    pub dom: [BE; 2],
    pub mds: [[BE; 12]; 12],
    pub rc: Vec<[BE; 12]>, // length == rounds
}

#[derive(thiserror::Error, Debug)]
pub enum PoseidonError {
    #[error("poseidon: failed to derive valid 12x12 MDS for suite_id {0}")]
    MdsDerivation(String),
}

static POSEIDON_CACHE: OnceLock<RwLock<HashMap<[u8; 32], PoseidonSuite>>> = OnceLock::new();

/// Build Poseidon t=12 suite (r=10, c=2)
/// using conservative rounds by default.
pub fn get_poseidon_suite(suite_id: &[u8; 32]) -> PoseidonSuite {
    get_poseidon_suite_with_rounds(suite_id, POSEIDON_ROUNDS)
}

pub fn get_poseidon_suite_with_rounds(suite_id: &[u8; 32], rounds: usize) -> PoseidonSuite {
    if let Some(found) = cache().read().ok().and_then(|m| m.get(suite_id).cloned()) {
        return found;
    }

    let dom = derive_poseidon_domain_tags(suite_id);
    let mds = derive_poseidon_mds_cauchy_12x12(suite_id);
    let rc = derive_poseidon_round_constants_12(suite_id, rounds);
    let suite = PoseidonSuite { dom, mds, rc };

    if let Ok(mut w) = cache().write() {
        w.insert(*suite_id, suite.clone());
    }

    suite
}

/// Checked construction: attempt to
/// derive MDS with bounded fallback;
/// return Err on failure.
pub fn validate_poseidon_suite(suite_id: &[u8; 32]) -> Result<(), PoseidonError> {
    // Try deriving the MDS once in a checked mode;
    // DOM tags/RC are deterministic and infallible.
    let _ = try_derive_poseidon_mds_cauchy_12x12(suite_id)?;
    Ok(())
}

/// Unchecked derivation used internally
/// by suite builder; never returns Err,
/// but logs and performs a bounded deterministic
/// fallback search to avoid panics.
pub fn derive_poseidon_mds_cauchy_12x12(suite_id: &[u8; 32]) -> [[BE; 12]; 12] {
    try_derive_poseidon_mds_cauchy_12x12(suite_id).unwrap_or_else(|e| {
        tracing::error!(
            target="poseidon.mds",
            err=%e,
            "unchecked MDS derivation failed; returning identity to fail-closed in AIR",
        );

        // Identity will make constraints
        // inconsistent with the trace, causing failure.
        let mut m = [[BE::ZERO; 12]; 12];
        for (i, row) in m.iter_mut().enumerate() {
            row[i] = BE::ONE;
        }

        m
    })
}

/// Checked derivation that returns Err
/// if a valid MDS could not be derived
/// using a bounded search.
pub fn try_derive_poseidon_mds_cauchy_12x12(
    suite_id: &[u8; 32],
) -> Result<[[BE; 12]; 12], PoseidonError> {
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

    let x = derive_points(DOM_POSEIDON_MDS_X, suite_id, 12);
    let mut y = derive_points(DOM_POSEIDON_MDS_Y, suite_id, 12);

    let mut adj_ctr: u32 = 0;
    let mut attempts: u32 = 0;

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
        attempts = attempts.wrapping_add(1);

        if attempts > 1_000_000 {
            return Err(PoseidonError::MdsDerivation(format!("0x{suite_id:02x?}")));
        }
    }

    let mut m = [[BE::ZERO; 12]; 12];
    for (i, row) in m.iter_mut().enumerate() {
        for (j, cell) in row.iter_mut().enumerate() {
            let denom = x[i] + y[j];
            *cell = denom.inv();
        }
    }

    Ok(m)
}

pub fn derive_rom_round_constants_3(suite_id: &[u8; 32], rounds: usize) -> Vec<[BE; 3]> {
    let mut rc = vec![[BE::ZERO; 3]; rounds];
    for (r, row) in rc.iter_mut().enumerate() {
        let r_b = [r as u8];
        for (lane, cell) in row.iter_mut().enumerate() {
            let lane_b = [lane as u8];
            *cell = ro_from_slices(DOM_ROM_RC, &[&suite_id[..], &r_b[..], &lane_b[..]]);
        }
    }

    rc
}

pub fn derive_poseidon_round_constants_12(suite_id: &[u8; 32], rounds: usize) -> Vec<[BE; 12]> {
    let mut rc = vec![[BE::ZERO; 12]; rounds];
    for (r, row) in rc.iter_mut().enumerate() {
        let r_b = [r as u8];
        for (lane, cell) in row.iter_mut().enumerate() {
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

pub fn derive_rom_mds_cauchy_3x3(suite_id: &[u8; 32]) -> [[BE; 3]; 3] {
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

    let x = derive_points(DOM_ROM_MDS_X, suite_id, 3);
    let y = derive_points(DOM_ROM_MDS_Y, suite_id, 3);

    let mut m = [[BE::ZERO; 3]; 3];
    for (i, xi) in x.iter().enumerate().take(3) {
        for (j, yj) in y.iter().enumerate().take(3) {
            let denom = *xi + *yj;
            m[i][j] = denom.inv();
        }
    }

    m
}

// Legacy function for compatibility:
// compute hash via sponge
pub fn poseidon_hash_two_lanes(suite_id: &[u8; 32], left: BE, right: BE) -> BE {
    let suite = get_poseidon_suite(suite_id);
    let mut state = [
        left,
        right,
        BE::ZERO,
        BE::ZERO,
        BE::ZERO,
        BE::ZERO,
        BE::ZERO,
        BE::ZERO,
        BE::ZERO,
        BE::ZERO,
        suite.dom[0],
        suite.dom[1],
    ];

    for rc_r in suite.rc.iter() {
        // Apply S-box (cube all lanes)
        for lane in state.iter_mut() {
            *lane = *lane * *lane * *lane;
        }

        // Apply MDS + round constants
        let mut new_state = [BE::ZERO; 12];
        for (i, row) in suite.mds.iter().enumerate() {
            let acc = row
                .iter()
                .zip(state.iter())
                .fold(BE::ZERO, |acc, (m, s)| acc + (*m) * (*s));
            new_state[i] = acc + rc_r[i];
        }

        state = new_state;
    }

    state[0]
}

/// Public helper for domain-separated RO→field mapping.
///
/// Kept thin and explicit so higher-level modules
/// (e.g. IVC/digest code) can derive challenges and
/// binders under their own string domains without
/// re-implementing Blake3 plumbing.
pub fn ro_to_fe(domain: &str, parts: &[&[u8]]) -> BE {
    ro_from_slices(domain, parts)
}

// Local RO-to-field helper
fn ro_from_slices(domain: &str, parts: &[&[u8]]) -> BE {
    let mut h = blake3::Hasher::new();
    h.update(domain.as_bytes());

    for p in parts {
        h.update(p);
    }

    let digest = h.finalize();
    let bytes = digest.as_bytes();

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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mds_12x12_basic() {
        let sid = [42u8; 32];
        let m = derive_poseidon_mds_cauchy_12x12(&sid);
        assert_eq!(m.len(), 12);
        assert_eq!(m[0].len(), 12);
        assert!(m.iter().flatten().any(|v| *v != BE::ZERO));
    }

    #[test]
    fn rc_12_len_matches_rounds() {
        let sid = [7u8; 32];
        let rc = derive_poseidon_round_constants_12(&sid, POSEIDON_ROUNDS);
        assert_eq!(rc.len(), POSEIDON_ROUNDS);
        assert_ne!(rc[0][0], BE::ZERO);
        assert_ne!(rc[POSEIDON_ROUNDS - 1][11], BE::ZERO);
    }

    #[test]
    fn suite_determinism_and_cache() {
        let sid = [1u8; 32];
        let a = get_poseidon_suite(&sid);
        let b = get_poseidon_suite(&sid);
        assert_eq!(a.dom, b.dom);
        assert_eq!(a.mds, b.mds);
        assert_eq!(a.rc.len(), b.rc.len());
        // spot check
        assert_eq!(a.rc[0][0], b.rc[0][0]);
    }
}

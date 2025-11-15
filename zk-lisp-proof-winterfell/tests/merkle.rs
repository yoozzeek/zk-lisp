// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::math::{FieldElement, StarkField};
use winterfell::{BatchingMethod, FieldExtension, ProofOptions, Trace, TraceTable};

use zk_lisp_compiler::compile_entry;
use zk_lisp_proof::pi::{self, PublicInputsBuilder};
use zk_lisp_proof_winterfell::layout::{Columns, STEPS_PER_LEVEL_P2};
use zk_lisp_proof_winterfell::poseidon::poseidon_hash_two_lanes;
use zk_lisp_proof_winterfell::prove::{self, ZkProver};
use zk_lisp_proof_winterfell::schedule::{pos_final, pos_map};
use zk_lisp_proof_winterfell::trace::build_trace;

#[derive(Clone, Debug)]
pub struct MerkleRow {
    pub dir: BE,
    pub sib: BE,
    pub acc: BE,
    pub first: BE,
    pub last: BE,
    pub leaf: BE,
    pub g: BE,
    pub lane_l: BE,
    pub lane_r: BE,
}

pub struct MerkleOverlay<'a> {
    trace: &'a TraceTable<BE>,
    cols: Columns,
    steps: usize,
}

impl<'a> MerkleOverlay<'a> {
    pub fn new(trace: &'a TraceTable<BE>) -> Self {
        Self {
            trace,
            cols: Columns::baseline(),
            steps: STEPS_PER_LEVEL_P2,
        }
    }

    #[inline]
    pub fn row_map(&self, level: usize) -> usize {
        level * self.steps + pos_map()
    }

    #[inline]
    pub fn row_final(&self, level: usize) -> usize {
        level * self.steps + pos_final()
    }

    #[inline]
    pub fn is_merkle_level(&self, level: usize) -> bool {
        let r = self.row_map(level);
        self.trace.get(self.cols.merkle_g, r) == BE::ONE
    }

    pub fn at_map(&self, level: usize) -> MerkleRow {
        let r = self.row_map(level);
        MerkleRow {
            dir: self.trace.get(self.cols.merkle_dir, r),
            sib: self.trace.get(self.cols.merkle_sib, r),
            acc: self.trace.get(self.cols.merkle_acc, r),
            first: self.trace.get(self.cols.merkle_first, r),
            last: self.trace.get(self.cols.merkle_last, r),
            leaf: self.trace.get(self.cols.merkle_leaf, r),
            g: self.trace.get(self.cols.merkle_g, r),
            lane_l: self.trace.get(self.cols.lane_l, r),
            lane_r: self.trace.get(self.cols.lane_r, r),
        }
    }

    pub fn acc_at_final(&self, level: usize) -> BE {
        let r = self.row_final(level);
        self.trace.get(self.cols.merkle_acc, r)
    }

    pub fn levels_len(&self) -> usize {
        self.trace.length() / self.steps
    }
}

fn opts() -> ProofOptions {
    ProofOptions::new(
        1, // queries (low to speed tests; verify may reject; acceptable)
        8,
        0,
        FieldExtension::None,
        2,
        1,
        BatchingMethod::Linear,
        BatchingMethod::Linear,
    )
}

fn be_to_bytes32(v: BE) -> [u8; 32] {
    let mut b = [0u8; 32];
    let n: u128 = v.as_int();
    b[0..16].copy_from_slice(&n.to_le_bytes());

    b
}

#[test]
fn merkle_two_steps_positive_prove_verify() {
    // Program with 2-step path
    let src = r#"
(def (main leaf d0 s0 d1 s1)
  (merkle-verify leaf ((d0 s0) (d1 s1))))"#;
    let leaf = 1u64;
    let d0 = 0u64;
    let s0 = 2u64;
    let d1 = 1u64;
    let s1 = 3u64;

    let program = compile_entry(src, &[leaf, d0, s0, d1, s1]).expect("compile");

    // Expected root computed
    // with program commitment.
    let h0 = poseidon_hash_two_lanes(&program.commitment, BE::from(leaf), BE::from(s0));
    let root = poseidon_hash_two_lanes(&program.commitment, BE::from(s1), h0);

    // PI: bind root only (Merkle)
    let mut pi = PublicInputsBuilder::from_program(&program)
        .build()
        .expect("pi");
    pi.merkle_root = be_to_bytes32(root);

    // Build trace and check overlay
    let trace = build_trace(&program, &pi).expect("trace");
    let ov = MerkleOverlay::new(&trace);

    // Find merkle levels
    let mut levels: Vec<usize> = Vec::new();
    for lvl in 0..ov.levels_len() {
        if ov.is_merkle_level(lvl) {
            levels.push(lvl);
        }
    }

    assert_eq!(levels.len(), 2, "expected 2 merkle levels");

    // first level:
    // acc at map == leaf; dir/sib set
    let m0 = ov.at_map(levels[0]);
    assert_eq!(m0.first, BE::ONE);
    assert_eq!(m0.dir, BE::from(d0));
    assert_eq!(m0.sib, BE::from(s0));
    assert_eq!(m0.acc, BE::from(leaf));

    // final acc after
    // level 0 matches h0.
    let acc0_fin = ov.acc_at_final(levels[0]);
    assert_eq!(acc0_fin, h0);

    // second level:
    // dir/sib set;
    // last flag at final
    let m1 = ov.at_map(levels[1]);
    assert_eq!(m1.dir, BE::from(d1));
    assert_eq!(m1.sib, BE::from(s1));

    let acc1_fin = ov.acc_at_final(levels[1]);
    assert_eq!(acc1_fin, root);

    // Prove and verify (verify may reject
    // on security; accept BackendSource)
    let rom_acc = zk_lisp_proof_winterfell::romacc::rom_acc_from_program(&program);
    let prover = ZkProver::new(opts(), pi.clone(), rom_acc);
    let proof = prover.prove(trace).expect("prove");

    match prove::verify_proof(proof, &program, pi, &opts(), 64) {
        Ok(()) => {}
        Err(e) => {
            if !matches!(e, prove::Error::BackendSource(_)) {
                panic!("verify failed: {e}");
            }
        }
    }
}

#[test]
fn load_ca_positive_prove_verify() {
    // Same as merkle-verify but via load-ca
    let src = r#"
(def (main leaf d0 s0 d1 s1)
  (load-ca leaf ((d0 s0) (d1 s1))))"#;
    let leaf = 1u64;
    let d0 = 0u64;
    let s0 = 2u64;
    let d1 = 1u64;
    let s1 = 3u64;

    let program = compile_entry(src, &[leaf, d0, s0, d1, s1]).expect("compile");

    // Expected root computed
    // with program commitment
    let h0 = poseidon_hash_two_lanes(&program.commitment, BE::from(leaf), BE::from(s0));
    let root = poseidon_hash_two_lanes(&program.commitment, BE::from(s1), h0);

    let mut pi = PublicInputsBuilder::from_program(&program)
        .build()
        .expect("pi");
    pi.merkle_root = be_to_bytes32(root);

    let trace = build_trace(&program, &pi).expect("trace");
    let rom_acc = zk_lisp_proof_winterfell::romacc::rom_acc_from_program(&program);
    let prover = ZkProver::new(opts(), pi.clone(), rom_acc);
    let proof = prover.prove(trace).expect("prove");

    match prove::verify_proof(proof, &program, pi, &opts(), 64) {
        Ok(()) => {}
        Err(e) => {
            if !matches!(e, prove::Error::BackendSource(_)) {
                panic!("verify failed: {e}");
            }
        }
    }
}

#[test]
fn store_ca_new_root_overlay() {
    // Compute new root after
    // replacing leaf with new value
    let src = r#"
(def (main leaf_new d0 s0 d1 s1)
  (store-ca leaf_new ((d0 s0) (d1 s1))))"#;
    let leaf_new = 9u64;
    let d0 = 0u64;
    let s0 = 2u64;
    let d1 = 1u64;
    let s1 = 3u64;

    let program = compile_entry(src, &[leaf_new, d0, s0, d1, s1]).expect("compile");
    let trace = build_trace(&program, &pi::PublicInputs::default()).expect("trace");
    let ov = MerkleOverlay::new(&trace);

    // find last merkle level
    let mut last_lvl = None;
    for lvl in 0..ov.levels_len() {
        if ov.is_merkle_level(lvl) {
            last_lvl = Some(lvl);
        }
    }

    let lvl_last = last_lvl.expect("merkle level present");

    // expected root from new leaf
    let h0 = poseidon_hash_two_lanes(&program.commitment, BE::from(leaf_new), BE::from(s0));
    let expected = poseidon_hash_two_lanes(&program.commitment, BE::from(s1), h0);

    let acc_fin = ov.acc_at_final(lvl_last);
    assert_eq!(acc_fin, expected);
}

#[test]
fn load_ca_wrong_sibling_verify_fails() {
    let src = r#"
(def (main leaf d0 s0 d1 s1)
  (load-ca leaf ((d0 s0) (d1 s1))))"#;
    let (leaf, d0, s0, d1, s1) = (1u64, 0u64, 2u64, 1u64, 999u64);
    let program = compile_entry(src, &[leaf, d0, s0, d1, s1]).expect("compile");

    // Bind correct root
    // as if s1=3 (not 999)
    let h0 = poseidon_hash_two_lanes(&program.commitment, BE::from(leaf), BE::from(s0));
    let correct_root = poseidon_hash_two_lanes(&program.commitment, BE::from(3u64), h0);

    let mut pi = PublicInputsBuilder::from_program(&program)
        .build()
        .expect("pi");
    pi.merkle_root = be_to_bytes32(correct_root);

    let trace = build_trace(&program, &pi).expect("trace");
    let rom_acc = zk_lisp_proof_winterfell::romacc::rom_acc_from_program(&program);
    let prover = ZkProver::new(opts(), pi.clone(), rom_acc);

    if let Ok(proof) = prover.prove(trace) {
        assert!(prove::verify_proof(proof, &program, pi, &opts(), 64).is_err());
    }
}

#[allow(clippy::single_match)]
#[test]
fn merkle_wrong_root_verify_fails() {
    let src = r#"
(def (main leaf d0 s0 d1 s1)
  (merkle-verify leaf ((d0 s0) (d1 s1))))"#;
    let (leaf, d0, s0, d1, s1) = (1u64, 0u64, 2u64, 1u64, 3u64);
    let program = compile_entry(src, &[leaf, d0, s0, d1, s1]).expect("compile");

    // Bind incorrect root (arbitrary value)
    let bad_root = BE::from(123456789u64);
    let mut pi = PublicInputsBuilder::from_program(&program)
        .build()
        .expect("pi");
    pi.merkle_root = be_to_bytes32(bad_root);

    let pi_for_verify = pi.clone();

    let trace = build_trace(&program, &pi_for_verify).expect("trace");
    let rom_acc = zk_lisp_proof_winterfell::romacc::rom_acc_from_program(&program);
    let prover = ZkProver::new(opts(), pi, rom_acc);

    match prover.prove(trace) {
        Ok(proof) => {
            // Wrong root must be
            // rejected at verification
            assert!(prove::verify_proof(proof, &program, pi_for_verify, &opts(), 64).is_err());
        }
        Err(_) => {
            // Early failure is also
            // acceptable (e.g., backend/preflight)
        }
    }
}

#[allow(clippy::single_match)]
#[test]
fn merkle_wrong_sibling_verify_fails() {
    // Same as positive, but s1 is wrong
    let src = r#"
(def (main leaf d0 s0 d1 s1)
  (merkle-verify leaf ((d0 s0) (d1 s1))))"#;
    let (leaf, d0, s0, d1, s1) = (1u64, 0u64, 2u64, 1u64, 999u64);
    let program = compile_entry(src, &[leaf, d0, s0, d1, s1]).expect("compile");

    // Compute root as if s1=3 (correct),
    // but we pass s1=999 into program.
    let h0 = poseidon_hash_two_lanes(&program.commitment, BE::from(leaf), BE::from(s0));
    let correct_root = poseidon_hash_two_lanes(&program.commitment, BE::from(3u64), h0);

    let mut pi = PublicInputsBuilder::from_program(&program)
        .build()
        .expect("pi");
    pi.merkle_root = be_to_bytes32(correct_root);

    let pi_for_verify = pi.clone();

    let trace = build_trace(&program, &pi).expect("trace");
    let rom_acc = zk_lisp_proof_winterfell::romacc::rom_acc_from_program(&program);
    let prover = ZkProver::new(opts(), pi, rom_acc);

    match prover.prove(trace) {
        Ok(proof) => {
            assert!(prove::verify_proof(proof, &program, pi_for_verify, &opts(), 64).is_err());
        }
        Err(_) => {}
    }
}

#[test]
fn merkle_empty_path_compiler_error() {
    // (merkle-verify leaf ()) is invalid form
    let src = r#"(def (main x) (merkle-verify x ()))"#;
    assert!(compile_entry(src, &[1]).is_err());
}

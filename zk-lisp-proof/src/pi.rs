// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Public inputs and feature flags for zk-lisp proofs.
//!
//! [`PublicInputs`] capture the program commitment, VM
//! arguments, output location and feature mask inferred
//! from compiled ops, forming the common contract with AIR.

use crate::error::{Error, Result};

use blake3::Hasher;
use zk_lisp_compiler::builder::Op;
use zk_lisp_compiler::{CompilerMetrics, Program};

// Feature bits
pub const FM_POSEIDON: u64 = 1 << 0;
pub const FM_VM: u64 = 1 << 1;
pub const FM_VM_EXPECT: u64 = 1 << 4;
pub const FM_SPONGE: u64 = 1 << 5;
pub const FM_MERKLE: u64 = 1 << 6;
pub const FM_RAM: u64 = 1 << 7;

/// Typed VM argument value
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VmArg {
    U64(u64),
    U128(u128),
    Bytes32([u8; 32]),
}

#[derive(Clone, Copy, Debug, Default)]
pub struct FeaturesMap {
    pub poseidon: bool,
    pub vm: bool,
    pub vm_expect: bool,
    pub sponge: bool,
    pub merkle: bool,
    pub ram: bool,
}

impl FeaturesMap {
    pub fn from_mask(m: u64) -> Self {
        FeaturesMap {
            poseidon: (m & FM_POSEIDON) != 0,
            vm: (m & FM_VM) != 0,
            vm_expect: (m & FM_VM_EXPECT) != 0,
            sponge: (m & FM_SPONGE) != 0,
            merkle: (m & FM_MERKLE) != 0,
            ram: (m & FM_RAM) != 0,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct PublicInputs {
    /// Deterministic identifier
    /// of the program semantics.
    pub program_id: [u8; 32],

    /// Blake3 commitment of the program
    /// as used by the base VM AIR.
    pub program_commitment: [u8; 32],

    pub merkle_root: [u8; 32],

    /// Public VM arguments
    pub public_args: Vec<VmArg>,

    /// Runtime public arguments for `main`
    pub main_args: Vec<VmArg>,

    /// Secret VM arguments
    pub secret_args: Vec<VmArg>,

    pub vm_out_reg: u8,
    pub vm_out_row: u32,
    pub vm_expected_bytes: [u8; 32],

    pub feature_mask: u64,
    pub compiler_stats: CompilerMetrics,
}

impl PublicInputs {
    pub fn get_features(&self) -> FeaturesMap {
        FeaturesMap::from_mask(self.feature_mask)
    }

    pub fn validate_flags(&self) -> Result<()> {
        if self.program_id.iter().all(|b| *b == 0) {
            return Err(Error::InvalidInput(
                "program_id (Blake3 over canonical bytecode) must be non-zero",
            ));
        }
        if self.program_commitment.iter().all(|b| *b == 0) {
            return Err(Error::InvalidInput(
                "program_commitment (Blake3) must be non-zero",
            ));
        }
        if (self.feature_mask & FM_VM_EXPECT) != 0 && (self.feature_mask & FM_VM) == 0 {
            return Err(Error::InvalidInput("FM_VM_EXPECT requires FM_VM"));
        }

        Ok(())
    }

    pub fn digest(&self) -> [u8; 32] {
        let mut h = Hasher::new();
        h.update(b"zkl/pi/v1");
        h.update(&self.program_id);
        h.update(&self.program_commitment);
        h.update(&self.merkle_root);
        h.update(&self.feature_mask.to_le_bytes());

        // Stable encoding of main_args:
        // tag + little-endian bytes.
        h.update(&(self.main_args.len() as u32).to_le_bytes());

        for arg in &self.main_args {
            match arg {
                VmArg::U64(v) => {
                    h.update(&[0u8]);
                    h.update(&v.to_le_bytes());
                }
                VmArg::U128(v) => {
                    h.update(&[1u8]);
                    h.update(&v.to_le_bytes());
                }
                VmArg::Bytes32(bytes) => {
                    h.update(&[2u8]);
                    h.update(bytes);
                }
            }
        }

        let digest = h.finalize();
        let mut out = [0u8; 32];
        out.copy_from_slice(digest.as_bytes());

        out
    }
}

pub struct PublicInputsBuilder {
    pi: PublicInputs,
}

impl PublicInputsBuilder {
    pub fn from_program(program: &Program) -> Self {
        // The compiler exposes a single Blake3
        // commitment over the canonical bytecode
        let program_id = program.program_id;
        let mut builder = Self {
            pi: PublicInputs {
                program_id,
                program_commitment: program_id,
                compiler_stats: program.compiler_metrics.clone(),
                ..PublicInputs::default()
            },
        };

        // infer features from program ops
        builder.infer_features(program);

        builder
    }

    fn infer_features(&mut self, program: &Program) {
        use Op::*;

        let mut vm = false;
        let mut pose = false;

        for op in &program.ops {
            match *op {
                // ALU ops
                Const { .. }
                | Mov { .. }
                | Add { .. }
                | Sub { .. }
                | Mul { .. }
                | Neg { .. }
                | Eq { .. }
                | Select { .. }
                | Assert { .. }
                | AssertBit { .. }
                | AssertRange { .. }
                | AssertRangeLo { .. }
                | AssertRangeHi { .. }
                | DivMod { .. }
                | MulWide { .. }
                | DivMod128 { .. } => {
                    vm = true;
                }
                // RAM ops
                Load { .. } | Store { .. } => {
                    vm = true;
                    self.pi.feature_mask |= FM_RAM;
                }
                // Cryptographic ops
                SAbsorbN { .. } => {
                    vm = true;
                    pose = true;
                    self.pi.feature_mask |= FM_SPONGE;
                }
                SSqueeze { .. } => {
                    vm = true;
                    pose = true;
                    self.pi.feature_mask |= FM_SPONGE;
                }
                // Merkle ops
                MerkleStepFirst { .. } | MerkleStep { .. } | MerkleStepLast { .. } => {
                    pose = true;
                    self.pi.feature_mask |= FM_MERKLE;
                }
                End => {}
            }
        }

        if vm {
            self.pi.feature_mask |= FM_VM;
        }
        if pose {
            self.pi.feature_mask |= FM_POSEIDON;
        }
    }

    /// Attach typed public VM arguments.
    pub fn with_public_args(mut self, args: &[VmArg]) -> Self {
        self.pi.public_args = args.to_vec();
        self
    }

    /// Attach typed `main` arguments that are
    /// treated as runtime public inputs.
    pub fn with_main_args(mut self, args: &[VmArg]) -> Self {
        self.pi.main_args = args.to_vec();
        self
    }

    /// Attach typed secret VM arguments.
    pub fn with_secret_args(mut self, args: &[VmArg]) -> Self {
        self.pi.secret_args = args.to_vec();
        self.pi.feature_mask |= FM_VM;

        self
    }

    pub fn with_expect(mut self, expected: &[u8; 32]) -> Self {
        self.pi.vm_expected_bytes = *expected;
        self.pi.feature_mask |= FM_VM | FM_VM_EXPECT;

        self
    }

    pub fn build(self) -> Result<PublicInputs> {
        // basic validation and defaults
        if self.pi.program_id.iter().all(|b| *b == 0) {
            return Err(Error::InvalidInput(
                "program_id (Blake3 over canonical bytecode) must be non-zero",
            ));
        }
        if self.pi.program_commitment.iter().all(|b| *b == 0) {
            return Err(Error::InvalidInput(
                "program_commitment (Blake3) must be non-zero",
            ));
        }

        self.pi.validate_flags()?;

        Ok(self.pi)
    }
}

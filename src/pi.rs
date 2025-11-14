// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

//! Public inputs and features

use crate::commit::program_field_commitment;
use crate::error::{Error, Result};
use crate::{compiler, compiler::CompilerMetrics, utils};

use winterfell::math::fields::f128::BaseElement as BE;

// Feature bits
pub const FM_POSEIDON: u64 = 1 << 0;
pub const FM_VM: u64 = 1 << 1;
pub const FM_VM_EXPECT: u64 = 1 << 4;
pub const FM_SPONGE: u64 = 1 << 5;
pub const FM_MERKLE: u64 = 1 << 6;
pub const FM_RAM: u64 = 1 << 7;

#[derive(Clone, Copy, Debug, Default)]
pub struct FeaturesMap {
    pub poseidon: bool,
    pub vm: bool,
    pub vm_expect: bool,
    pub sponge: bool,
    pub merkle: bool,
    pub ram: bool,
}

#[derive(Clone, Debug, Default)]
pub struct PublicInputs {
    pub program_commitment: [u8; 32],
    pub merkle_root: [u8; 32],
    pub program_commitment_f0: BE,
    pub program_commitment_f1: BE,
    pub vm_args: Vec<u64>,
    pub vm_out_reg: u8,
    pub vm_out_row: u32,
    pub vm_expected_bytes: [u8; 32],

    pub feature_mask: u64,
    pub compiler_stats: CompilerMetrics,
}

pub struct PublicInputsBuilder {
    pi: PublicInputs,
}

impl PublicInputsBuilder {
    pub fn from_program(program: &compiler::Program) -> Self {
        let mut builder = Self {
            pi: PublicInputs {
                program_commitment: program.commitment,
                ..PublicInputs::default()
            },
        };

        // derive internal field-friendly
        // commitment from Blake3 digest.
        let fc = program_field_commitment(&program.commitment);
        builder.pi.program_commitment_f0 = fc[0];
        builder.pi.program_commitment_f1 = fc[1];

        // infer features from program ops
        builder.infer_features(program);

        builder.pi.vm_out_reg = program.out_reg;
        builder.pi.vm_out_row = program.out_row;

        builder
    }

    fn infer_features(&mut self, program: &compiler::Program) {
        use crate::compiler::builder::Op::*;

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

    pub fn with_args(mut self, args: &[u64]) -> Self {
        self.pi.vm_args = args.to_vec();
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
        if self.pi.program_commitment.iter().all(|b| *b == 0) {
            return Err(Error::InvalidInput(
                "program_commitment (Blake3) must be non-zero",
            ));
        }
        if self.pi.vm_args.len() > crate::layout::NR {
            return Err(Error::InvalidInput("too many vm_args for register file"));
        }

        self.pi.validate_flags()?;

        Ok(self.pi)
    }
}

impl PublicInputs {
    pub fn get_features(&self) -> FeaturesMap {
        let m = self.feature_mask;
        FeaturesMap {
            poseidon: (m & FM_POSEIDON) != 0,
            vm: (m & FM_VM) != 0,
            vm_expect: (m & FM_VM_EXPECT) != 0,
            sponge: (m & FM_SPONGE) != 0,
            merkle: (m & FM_MERKLE) != 0,
            ram: (m & FM_RAM) != 0,
        }
    }

    pub fn validate_flags(&self) -> Result<()> {
        if self.program_commitment.iter().all(|b| *b == 0) {
            return Err(Error::InvalidInput(
                "program_commitment (Blake3) must be non-zero",
            ));
        }
        if (self.feature_mask & FM_VM_EXPECT) != 0 && (self.feature_mask & FM_VM) == 0 {
            return Err(Error::InvalidInput("FM_VM_EXPECT requires FM_VM"));
        }
        if self.vm_args.len() > crate::layout::NR {
            return Err(Error::InvalidInput("too many vm_args for register file"));
        }

        Ok(())
    }
}

// PI encoding for Winterfell
impl winterfell::math::ToElements<BE> for PublicInputs {
    fn to_elements(&self) -> Vec<BE> {
        let out = vec![
            BE::from(self.feature_mask),
            utils::be_from_le8(&self.program_commitment),
            utils::be_from_le8(&self.merkle_root),
            self.program_commitment_f0,
            self.program_commitment_f1,
        ];

        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{air, layout};
    use winterfell::{Air, ProofOptions, TraceInfo};

    fn non_zero32(x: u8) -> [u8; 32] {
        [x; 32]
    }

    #[test]
    fn validate_prog_commit_non_zero_when_vm_or_poseidon() {
        let pi_vm = PublicInputs {
            feature_mask: FM_VM,
            ..Default::default()
        };
        assert!(pi_vm.validate_flags().is_err());

        let pi_pose = PublicInputs {
            feature_mask: FM_POSEIDON,
            ..Default::default()
        };
        assert!(pi_pose.validate_flags().is_err());

        let pi_ok = PublicInputs {
            feature_mask: FM_VM | FM_POSEIDON,
            program_commitment: non_zero32(1),
            ..Default::default()
        };
        pi_ok.validate_flags().expect("ok");
    }

    #[test]
    fn pi_feature_gating_counts() {
        let cols = layout::Columns::baseline();
        let width = cols.width(0);
        let steps = layout::STEPS_PER_LEVEL_P2;
        let info = TraceInfo::new(width, steps);
        let opts = ProofOptions::new(
            1,
            8,
            0,
            winterfell::FieldExtension::None,
            2,
            1,
            winterfell::BatchingMethod::Linear,
            winterfell::BatchingMethod::Linear,
        );

        let sched_asserts = 5 * layout::POSEIDON_ROUNDS + 6;

        // derive dynamic block lengths
        let pose_len = 12 * layout::POSEIDON_ROUNDS + 12; // rounds + holds

        // 5*NR role booleans (dst0,a,b,c,dst1)
        //   + 5 role sums
        //   + 1 select-cond
        //   + 17 op booleans
        //   + 1 one-hot
        //   + 17 rom-op equality
        //   + 2 PC constraints
        //   + NR no-overlap(dst0,dst1)
        let vm_ctrl_len_no_sponge = 5 * layout::NR + 5 + 1 + 17 + 1 + 17 + 2 + layout::NR; // 91

        // 8 carry + 8 writes
        //   + 2 eq ties + 2 divmod ties + 2 div128
        //   + 1 assert(c==1)
        //   + 1 assert-bit + 32 range bits
        //   + 1 range sum + 1 mulwide
        //   + 2 RAM (shadow + active_addr)
        let vm_alu_len = 8 + 8 + 2 + 2 + 2 + 1 + 1 + 32 + 1 + 1; // 58

        // Case A: Poseidon only
        let pi_pose = PublicInputs {
            feature_mask: FM_POSEIDON,
            ..Default::default()
        };

        let air_pose = air::ZkLispAir::new(info.clone(), pi_pose, opts.clone());
        assert_eq!(
            air_pose.context().num_main_transition_constraints(),
            pose_len
        );
        assert_eq!(air_pose.get_assertions().len(), sched_asserts);

        // Case B: VM only
        let pi_vm = PublicInputs {
            feature_mask: FM_VM,
            ..Default::default()
        };

        let air_vm = air::ZkLispAir::new(info.clone(), pi_vm, opts.clone());
        assert_eq!(
            air_vm.context().num_main_transition_constraints(),
            vm_ctrl_len_no_sponge + vm_alu_len
        );
        assert_eq!(air_vm.get_assertions().len(), sched_asserts + 1);

        // Case C: VM + Poseidon
        let pi_all = PublicInputs {
            feature_mask: FM_POSEIDON | FM_VM,
            ..Default::default()
        };

        let air_all = air::ZkLispAir::new(info, pi_all, opts);
        assert_eq!(
            air_all.context().num_main_transition_constraints(),
            pose_len + (vm_ctrl_len_no_sponge + vm_alu_len)
        );
        assert_eq!(air_all.get_assertions().len(), sched_asserts + 1);
    }
}

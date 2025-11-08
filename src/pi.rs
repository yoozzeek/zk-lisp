// Public inputs and features

use crate::error::{Error, Result};
use winterfell::math::fields::f128::BaseElement as BE;

// Feature bits
pub const FM_POSEIDON: u64 = 1 << 0;
pub const FM_VM: u64 = 1 << 1;
pub const FM_KV: u64 = 1 << 2;
pub const FM_KV_EXPECT: u64 = 1 << 3;

#[derive(Clone, Debug, Default)]
pub struct PublicInputs {
    pub feature_mask: u64,
    pub program_commitment: [u8; 32],
    pub kv_map_acc_bytes: [u8; 32],
    pub kv_fin_acc_bytes: [u8; 32],
    pub cn_root: [u8; 32],
    pub kv_levels_mask: u128,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct FeaturesMap {
    pub poseidon: bool,
    pub vm: bool,
    pub kv: bool,
    pub kv_expect: bool,
}

impl PublicInputs {
    pub fn get_features(&self) -> FeaturesMap {
        let m = self.feature_mask;
        FeaturesMap {
            poseidon: (m & FM_POSEIDON) != 0,
            vm: (m & FM_VM) != 0,
            kv: (m & FM_KV) != 0,
            kv_expect: (m & FM_KV_EXPECT) != 0,
        }
    }

    pub fn validate_flags(&self) -> Result<()> {
        if (self.feature_mask & FM_KV_EXPECT) != 0 && (self.feature_mask & FM_KV) == 0 {
            return Err(Error::InvalidInput("FM_KV_EXPECT requires FM_KV"));
        }

        if (self.feature_mask & FM_KV) == 0 && self.kv_levels_mask != 0 {
            return Err(Error::InvalidInput(
                "kv_levels_mask must be zero when FM_KV is disabled",
            ));
        }

        if ((self.feature_mask & FM_VM) != 0 || (self.feature_mask & FM_POSEIDON) != 0)
            && self.program_commitment.iter().all(|b| *b == 0)
        {
            return Err(Error::InvalidInput(
                "program_commitment must be non-zero when VM or POSEIDON is enabled",
            ));
        }

        Ok(())
    }
}

// PI encoding for Winterfell
impl winterfell::math::ToElements<BE> for PublicInputs {
    fn to_elements(&self) -> Vec<BE> {
        // encode kv_levels_mask into
        // one field element (lo + hi*2^64)
        let lo = (self.kv_levels_mask & 0xFFFF_FFFF_FFFF_FFFFu128) as u64;
        let hi = (self.kv_levels_mask >> 64) as u64;
        let kv_mask_fe = BE::from(lo) + BE::from(hi) * pow2_64_fe();

        let out = vec![
            BE::from(self.feature_mask),
            be_from_le8(&self.program_commitment),
            be_from_le8(&self.kv_map_acc_bytes),
            be_from_le8(&self.kv_fin_acc_bytes),
            be_from_le8(&self.cn_root),
            kv_mask_fe,
        ];

        out
    }
}

pub fn be_from_le8(bytes32: &[u8; 32]) -> BE {
    // fold first 16 bytes (LE) into
    // a field element: lo + hi * 2^64.
    let mut lo = [0u8; 8];
    let mut hi = [0u8; 8];
    lo.copy_from_slice(&bytes32[0..8]);
    hi.copy_from_slice(&bytes32[8..16]);

    BE::from(u64::from_le_bytes(lo)) + BE::from(u64::from_le_bytes(hi)) * pow2_64_fe()
}

#[inline]
fn pow2_64_fe() -> BE {
    let mut acc = BE::from(1u64);
    let two = BE::from(2u64);
    for _ in 0..64 {
        acc *= two;
    }

    acc
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
    fn validate_expect_requires_kv() {
        let pi = PublicInputs {
            feature_mask: FM_KV_EXPECT,
            ..Default::default()
        };
        let err = pi
            .validate_flags()
            .expect_err("EXPECT without KV must error");

        let Error::InvalidInput(msg) = err;
        assert!(msg.contains("FM_KV_EXPECT requires FM_KV"));
    }

    #[test]
    fn validate_expect_with_zero_accs_allowed() {
        let pi = PublicInputs {
            feature_mask: FM_KV | FM_KV_EXPECT,
            ..Default::default()
        };

        // Zero expected accs are allowed:
        // 0 is a valid field value
        pi.validate_flags().expect("ok with zero accs");
    }

    #[test]
    fn validate_kv_levels_mask_requires_kv() {
        let mut pi = PublicInputs {
            feature_mask: 0,
            ..Default::default()
        };
        pi.kv_levels_mask = 1;

        let err = pi
            .validate_flags()
            .expect_err("kv_levels_mask without KV must error");

        let Error::InvalidInput(msg) = err;
        assert!(msg.contains("kv_levels_mask must be zero"));
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

        // Case A: Poseidon only
        let pi_pose = PublicInputs {
            feature_mask: FM_POSEIDON,
            ..Default::default()
        };

        let air_pose = air::ZkLispAir::new(info.clone(), pi_pose, opts.clone());
        assert_eq!(
            air_pose.context().num_main_transition_constraints(),
            4 * layout::POSEIDON_ROUNDS
        );
        assert_eq!(air_pose.get_assertions().len(), sched_asserts);

        // Case B: VM only
        let pi_vm = PublicInputs {
            feature_mask: FM_VM,
            ..Default::default()
        };

        let air_vm = air::ZkLispAir::new(info.clone(), pi_vm, opts.clone());
        // vm_ctrl (48) + vm_alu (19) = 67
        assert_eq!(air_vm.context().num_main_transition_constraints(), 67);
        assert_eq!(air_vm.get_assertions().len(), sched_asserts + 1);

        // Case C: all features
        let pi_all = PublicInputs {
            feature_mask: FM_POSEIDON | FM_VM | FM_KV,
            ..Default::default()
        };

        let air_all = air::ZkLispAir::new(info, pi_all, opts);
        // poseidon (4*R) + vm(67) + kv(6)
        assert_eq!(
            air_all.context().num_main_transition_constraints(),
            4 * layout::POSEIDON_ROUNDS + 67 + 6
        );
        assert_eq!(air_all.get_assertions().len(), sched_asserts + 1);
    }
}

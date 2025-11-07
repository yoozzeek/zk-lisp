// Public inputs and features

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
}

// PI encoding for Winterfell
impl winterfell::math::ToElements<BE> for PublicInputs {
    fn to_elements(&self) -> Vec<BE> {
        let out = vec![
            BE::from(self.feature_mask),
            be_from_le8(&self.program_commitment),
            be_from_le8(&self.kv_map_acc_bytes),
            be_from_le8(&self.kv_fin_acc_bytes),
            be_from_le8(&self.cn_root),
        ];
        out
    }
}

fn be_from_le8(bytes32: &[u8; 32]) -> BE {
    let mut le = [0u8; 8];
    le.copy_from_slice(&bytes32[0..8]);

    BE::from(u64::from_le_bytes(le))
}

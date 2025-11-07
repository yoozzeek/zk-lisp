use winterfell::math::fields::f128::BaseElement as BE;

pub const POSEIDON_ROUNDS: usize = 8;
pub const STEPS_PER_LEVEL_P2: usize = 16;

#[derive(Clone, Debug)]
pub struct Columns {
    // Poseidon lanes
    pub lane_l: usize,
    pub lane_r: usize,
    pub lane_c0: usize,
    pub lane_c1: usize,

    // Schedule gates
    pub g_map: usize,
    pub g_final: usize,
    pub g_r_start: usize, // start index for g_r[0..POSEIDON_ROUNDS)

    // Generic activity mask for padding rows
    pub mask: usize,

    width: usize,
}

impl Columns {
    pub fn baseline() -> Self {
        let lane_l = 0;
        let lane_r = 1;
        let lane_c0 = 2;
        let lane_c1 = 3;

        let g_map = 4;
        let g_final = 5;
        let g_r_start = 6;
        let mask = g_r_start + POSEIDON_ROUNDS;

        let width = mask + 1;

        Self {
            lane_l,
            lane_r,
            lane_c0,
            lane_c1,
            g_map,
            g_final,
            g_r_start,
            mask,
            width,
        }
    }

    pub fn g_r_index(&self, j: usize) -> usize {
        debug_assert!(j < POSEIDON_ROUNDS);

        self.g_r_start + j
    }

    pub fn width(&self, _feature_mask: u64) -> usize {
        // Will add feature-based columns here
        self.width
    }
}

#[inline]
pub fn fe_u32(v: u32) -> BE {
    BE::from(v as u64)
}

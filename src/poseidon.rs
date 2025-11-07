use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;

use crate::layout::POSEIDON_ROUNDS;

pub fn round_constants() -> [[BE; 4]; POSEIDON_ROUNDS] {
    [[BE::ZERO; 4]; POSEIDON_ROUNDS]
}

pub fn mds_matrix() -> [[BE; 4]; 4] {
    let mut m = [[BE::ZERO; 4]; 4];
    m[0][0] = BE::ONE;
    m[1][1] = BE::ONE;
    m[2][2] = BE::ONE;
    m[3][3] = BE::ONE;

    m
}

pub fn domain_tags() -> [BE; 2] {
    [BE::ONE, BE::from(2u64)]
}

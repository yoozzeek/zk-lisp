use winterfell::math::StarkField;
use winterfell::{ProofOptions, Trace};
use zk_lisp::lisp::compile_str;
use zk_lisp::pi::{self, PublicInputs, be_from_le8};
use zk_lisp::poseidon::poseidon_hash_two_lanes;
use zk_lisp::prove::{ZkProver, build_trace, verify_proof};

#[test]
fn kv_membership_prove_verify() {
    // Single kv step + final; initial acc defaults to 0 so map/final acc stay 0.
    let src = "(kv-step 0 7) (kv-final)";
    let program = compile_str(src).expect("compile");
    let trace = build_trace(&program);

    // A) Without EXPECT
    let mut pi = PublicInputs::default();
    pi.feature_mask = pi::FM_POSEIDON | pi::FM_VM | pi::FM_KV;
    pi.program_commitment = program.commitment;

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

    // Compute KV levels mask from
    // the trace and include in PI.
    let cols = zk_lisp::layout::Columns::baseline();
    let steps = zk_lisp::layout::STEPS_PER_LEVEL_P2;
    let lvls = trace.length() / steps;

    let mut mask: u128 = 0;

    for lvl in 0..lvls {
        let base = lvl * steps;
        let row_map = base + zk_lisp::schedule::pos_map();

        if trace.get(cols.kv_g_map, row_map)
            == <winterfell::math::fields::f128::BaseElement as winterfell::math::FieldElement>::ONE
        {
            mask |= 1u128 << lvl;
        }
    }

    pi.kv_levels_mask = mask;

    let prover = ZkProver::new(opts.clone(), pi.clone());
    let proof = prover.prove(trace.clone()).expect("prove");

    verify_proof(proof, pi, &opts).expect("verify");

    // B) With EXPECT: compute expected map/final
    // acc from the actual Poseidon params
    // map acc is initial acc (0),
    // final acc is Poseidon(0, 7)
    let mut fin_bytes = [0u8; 32];
    {
        let fin = poseidon_hash_two_lanes(
            &program.commitment,
            be_from_le8(&[0u8; 32]),
            be_from_le8(&{
                let mut b = [0u8; 32];
                b[0] = 7u8;
                b
            }),
        );

        // encode full 128-bit field element
        // into first 16 bytes (LE)
        let v = fin.as_int();
        fin_bytes[0..16].copy_from_slice(&v.to_le_bytes());
    }

    let mut pi2 = PublicInputs {
        feature_mask: pi::FM_POSEIDON | pi::FM_VM | pi::FM_KV | pi::FM_KV_EXPECT,
        program_commitment: program.commitment,
        kv_map_acc_bytes: [0u8; 32],
        kv_fin_acc_bytes: fin_bytes,
        ..Default::default()
    };

    // Compute and set kv_levels_mask for EXPECT assertions
    let cols = zk_lisp::layout::Columns::baseline();
    let steps = zk_lisp::layout::STEPS_PER_LEVEL_P2;
    let lvls = trace.length() / steps;

    let mut mask2: u128 = 0;

    for lvl in 0..lvls {
        let base = lvl * steps;
        let row_map = base + zk_lisp::schedule::pos_map();

        if trace.get(cols.kv_g_map, row_map)
            == <winterfell::math::fields::f128::BaseElement as winterfell::math::FieldElement>::ONE
        {
            mask2 |= 1u128 << lvl;
        }
    }

    pi2.kv_levels_mask = mask2;

    let prover2 = ZkProver::new(opts.clone(), pi2.clone());
    let proof2 = prover2.prove(trace).expect("prove");

    verify_proof(proof2, pi2, &opts).expect("verify");
}

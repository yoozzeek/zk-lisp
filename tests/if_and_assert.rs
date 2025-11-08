use winterfell::ProofOptions;
use zk_lisp::lisp::compile_str;
use zk_lisp::pi::{self, PublicInputs};
use zk_lisp::prove::{ZkProver, build_trace, verify_proof};

#[test]
fn assert_positive() {
    let src = "(def (eq1 x y) (= x y)) (let ((a 7) (b 7)) (assert (eq1 a b)))";
    let program = compile_str(src).expect("compile");
    let trace = build_trace(&program);

    let mut pi = PublicInputs::default();
    pi.feature_mask = pi::FM_VM;
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

    let prover = ZkProver::new(opts.clone(), pi.clone());
    let proof = prover.prove(trace).expect("prove");

    verify_proof(proof, pi, &opts).expect("verify");
}

#[test]
fn if_positive() {
    let src = "(if 1 5 9)";
    let program = compile_str(src).expect("compile");
    let trace = build_trace(&program);

    let mut pi = PublicInputs::default();
    pi.feature_mask = pi::FM_VM;
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

    let prover = ZkProver::new(opts.clone(), pi.clone());
    let proof = prover.prove(trace).expect("prove");

    verify_proof(proof, pi, &opts).expect("verify");
}

#[test]
fn assert_negative_fails() {
    // assert(false) must fail
    let src = "(let ((a 5) (b 6)) (assert (= a b)))";
    let program = compile_str(src).expect("compile");
    let trace = build_trace(&program);

    let mut pi = PublicInputs::default();
    pi.feature_mask = pi::FM_VM;
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

    let prover = ZkProver::new(opts.clone(), pi.clone());

    match prover.prove(trace) {
        Err(_) => {
            // In debug, preflight should fail — this is OK
        }
        Ok(proof) => {
            // In release, proving may succeed, 
            // but verification must fail.
            verify_proof(proof, pi, &opts).expect_err("verify must fail");
        }
    }
}

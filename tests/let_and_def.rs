use winterfell::ProofOptions;
use zk_lisp::lisp::compile_str;
use zk_lisp::pi::{self, PublicInputs};
use zk_lisp::prove::{ZkProver, build_trace, verify_proof};

fn opts() -> ProofOptions {
    ProofOptions::new(
        1,
        8,
        0,
        winterfell::FieldExtension::None,
        2,
        1,
        winterfell::BatchingMethod::Linear,
        winterfell::BatchingMethod::Linear,
    )
}

#[test]
fn let_nested_and_shadowing_positive() {
    // Two independent let scenarios
    // cover nested binds and shadowing
    let src = r"
        (let ((x 2) (y 3))
            (let ((z (+ x y)))
                (assert (= z 5))))
        (let ((x 2))
            (let ((x 3))
                (assert (= x 3))))
    ";

    let program = compile_str(src).expect("compile");
    let trace = build_trace(&program);

    let mut pi = PublicInputs::default();
    pi.feature_mask = pi::FM_VM;
    pi.program_commitment = program.commitment;

    let opts = opts();
    let prover = ZkProver::new(opts.clone(), pi.clone());
    let proof = prover.prove(trace).expect("prove");

    verify_proof(proof, pi, &opts).expect("verify");
}

#[test]
fn def_function_and_call_positive() {
    // Define and call a function
    let src = r"
        (def (add2 a b) (+ a b))
        (assert (= (add2 7 8) 15))
    ";

    let program = compile_str(src).expect("compile");
    let trace = build_trace(&program);

    let mut pi = PublicInputs::default();
    pi.feature_mask = pi::FM_VM;
    pi.program_commitment = program.commitment;

    let opts = opts();
    let prover = ZkProver::new(opts.clone(), pi.clone());
    let proof = prover.prove(trace).expect("prove");

    verify_proof(proof, pi, &opts).expect("verify");
}

#[test]
fn def_call_wrong_arity_errors() {
    // Wrong number of args in function
    // call must be a compile-time error.
    let src_missing = r"
        (def (add2 a b) (+ a b))
        (add2 7)
    ";
    let err1 = compile_str(src_missing).expect_err("compile must fail");
    let msg1 = err1.to_string();

    assert!(msg1.contains("expects 2"));

    let src_extra = r"
        (def (add2 a b) (+ a b))
        (add2 7 8 9)
    ";
    let err2 = compile_str(src_extra).expect_err("compile must fail");
    let msg2 = err2.to_string();

    assert!(msg2.contains("expects 2"));
}

#[test]
fn recursion_direct_errors() {
    // Direct recursion must be detected
    // and rejected at compile time.
    let src = r"
        (def (f x) (f x))
        (f 1)
    ";
    let err = compile_str(src).expect_err("compile must fail");
    let msg = err.to_string();

    assert!(msg.to_lowercase().contains("recursion"));
}

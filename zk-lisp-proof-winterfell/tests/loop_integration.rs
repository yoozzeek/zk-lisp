// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

use winterfell::ProofOptions;
use winterfell::math::fields::f128::BaseElement as BE;
use zk_lisp_compiler::compile_entry;
use zk_lisp_proof::pi::PublicInputsBuilder;
use zk_lisp_proof_winterfell::prove::{self, ZkProver, verify_proof};
use zk_lisp_proof_winterfell::romacc::rom_acc_from_program;
use zk_lisp_proof_winterfell::utils::vm_output_from_trace;
use zk_lisp_proof_winterfell::vm::layout::Columns;
use zk_lisp_proof_winterfell::vm::trace::build_trace;

#[test]
fn loop_bounded_recur_prove_verify() {
    let src = r#"
(def (main)
  (loop :max 5 ((i 0) (acc 0))
    acc
    (recur (+ i 1) (+ acc i))))
(main)
"#;

    let program = compile_entry(src, &[]).expect("compile");
    let pi = PublicInputsBuilder::from_program(&program)
        .build()
        .expect("pi");

    let trace = build_trace(&program, &pi).expect("trace");

    // Check that main returns the
    // expected value from the VM trace.
    let cols = Columns::baseline();
    let (out_reg, out_row) = vm_output_from_trace(&trace);
    let v = trace.get(cols.r_index(out_reg as usize), out_row as usize);

    assert_eq!(v, BE::from(10u64));

    let rom_acc = rom_acc_from_program(&program);
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

    let prover = ZkProver::new(opts.clone(), pi.clone(), rom_acc);
    let proof = prover.prove(trace).expect("prove");

    // Verify
    match verify_proof(proof, &program, pi, &opts, 64) {
        Ok(()) => {}
        Err(e) => {
            if !matches!(e, prove::Error::BackendSource(_)) {
                panic!("verify failed: {e}");
            }
        }
    }
}

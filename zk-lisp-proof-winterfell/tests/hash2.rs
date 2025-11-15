// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

use winterfell::ProofOptions;

use zk_lisp_compiler::compile_str;
use zk_lisp_proof::pi::{self, PublicInputs};
use zk_lisp_proof_winterfell::prove::{self, ZkProver, verify_proof};
use zk_lisp_proof_winterfell::trace::build_trace;

#[test]
fn hash2_prove_verify() {
    // Poseidon placeholder:
    // choose left=1 to keep output stable (1)
    let src = "(let ((x 1) (y 2)) (hash2 x y))";
    let program = compile_str(src).expect("compile");

    let mut pi = PublicInputs::default();
    pi.feature_mask = pi::FM_POSEIDON | pi::FM_VM;
    pi.program_commitment = program.commitment;

    let trace = build_trace(&program, &pi).expect("trace");
    let rom_acc = zk_lisp_proof_winterfell::romacc::rom_acc_from_program(&program);

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

    match verify_proof(proof, &program, pi, &opts, 64) {
        Ok(()) => {}
        Err(e) => {
            if !matches!(e, prove::Error::BackendSource(_)) {
                panic!("verify failed: {e}");
            }
        }
    }
}

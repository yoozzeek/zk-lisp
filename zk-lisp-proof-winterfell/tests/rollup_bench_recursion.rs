// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

use std::{fs, path::Path};
use winterfell::Trace;
use winterfell::crypto::{DefaultRandomCoin, MerkleTree};
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::math::{FieldElement, StarkField};
use winterfell::matrix::ColMatrix;
use winterfell::{
    AcceptableOptions, Air, CompositionPoly, CompositionPolyTrace, DefaultConstraintCommitment,
    DefaultConstraintEvaluator, DefaultTraceLde, FieldExtension, PartitionOptions, Proof,
    ProofOptions, Prover as WProver, StarkDomain, TraceInfo, TracePolyTable, TraceTable,
};
use zk_lisp_compiler as compiler;
use zk_lisp_compiler::{ArgRole, ScalarType};
use zk_lisp_proof::ProverOptions;
use zk_lisp_proof::frontend::{self, PreflightMode};
use zk_lisp_proof::pi::{PublicInputs, PublicInputsBuilder, VmArg};
use zk_lisp_proof::recursion::{self, RecursionArtifactCodec};
use zk_lisp_proof::segment::SegmentPlanner;
use zk_lisp_proof_winterfell::WinterfellBackend;
use zk_lisp_proof_winterfell::agg::child::{ZlChildTranscript, verify_child_transcript};
use zk_lisp_proof_winterfell::agg::layout::AggColumns;
use zk_lisp_proof_winterfell::agg::pi::AggAirPublicInputs;
use zk_lisp_proof_winterfell::agg::trace::build_agg_trace_from_transcripts;
use zk_lisp_proof_winterfell::prove;

use zk_lisp_proof_winterfell::agg::air::ZlAggAir;
use zk_lisp_proof_winterfell::poseidon::hasher::PoseidonHasher;

/// Minimal Winterfell prover for `ZlAggAir`, it's a copy of `AggProver` from `agg_basic.rs`
struct AggProver {
    options: ProofOptions,
    pub_inputs: AggAirPublicInputs,
}

impl AggProver {
    fn new(options: ProofOptions, pub_inputs: AggAirPublicInputs) -> Self {
        Self {
            options,
            pub_inputs,
        }
    }
}

impl WProver for AggProver {
    type BaseField = BE;
    type Air = ZlAggAir;
    type Trace = TraceTable<Self::BaseField>;
    type HashFn = PoseidonHasher<Self::BaseField>;
    type VC = MerkleTree<Self::HashFn>;
    type RandomCoin = DefaultRandomCoin<Self::HashFn>;
    type TraceLde<E: FieldElement<BaseField = Self::BaseField>> =
        DefaultTraceLde<E, Self::HashFn, Self::VC>;
    type ConstraintCommitment<E: FieldElement<BaseField = Self::BaseField>> =
        DefaultConstraintCommitment<E, Self::HashFn, Self::VC>;
    type ConstraintEvaluator<'a, E: FieldElement<BaseField = Self::BaseField>> =
        DefaultConstraintEvaluator<'a, Self::Air, E>;

    fn get_pub_inputs(&self, _trace: &Self::Trace) -> <Self::Air as Air>::PublicInputs {
        self.pub_inputs.clone()
    }

    fn options(&self) -> &ProofOptions {
        &self.options
    }

    fn new_trace_lde<E: FieldElement<BaseField = Self::BaseField>>(
        &self,
        trace_info: &TraceInfo,
        main_trace: &ColMatrix<Self::BaseField>,
        domain: &StarkDomain<Self::BaseField>,
        partition_option: PartitionOptions,
    ) -> (Self::TraceLde<E>, TracePolyTable<E>) {
        DefaultTraceLde::new(trace_info, main_trace, domain, partition_option)
    }

    fn new_evaluator<'a, E: FieldElement<BaseField = Self::BaseField>>(
        &self,
        air: &'a Self::Air,
        aux_rand_elements: Option<winterfell::AuxRandElements<E>>,
        composition_coefficients: winterfell::ConstraintCompositionCoefficients<E>,
    ) -> Self::ConstraintEvaluator<'a, E> {
        DefaultConstraintEvaluator::new(air, aux_rand_elements, composition_coefficients)
    }

    fn build_constraint_commitment<E: FieldElement<BaseField = Self::BaseField>>(
        &self,
        composition_poly_trace: CompositionPolyTrace<E>,
        num_constraint_composition_columns: usize,
        domain: &StarkDomain<Self::BaseField>,
        partition_options: PartitionOptions,
    ) -> (Self::ConstraintCommitment<E>, CompositionPoly<E>) {
        DefaultConstraintCommitment::new(
            composition_poly_trace,
            num_constraint_composition_columns,
            domain,
            partition_options,
        )
    }
}

/// Read `examples/rollup-bench.zlisp` from the workspace root.
fn rollup_bench_src() -> String {
    // Same trick as in rollup_bench_regression.rs
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    let path = Path::new(manifest_dir).join("../examples/rollup-bench.zlisp");
    fs::read_to_string(&path).unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()))
}

/// Build compiled Program + PublicInputs for rollup-bench
/// exactly like CLI:
///
///   zk-lisp prove examples/rollup-bench.zlisp \
///     --arg u64:10 --arg bytes32:0x01
fn build_rollup_bench_program_and_pi() -> (compiler::Program, PublicInputs) {
    let src = rollup_bench_src();

    // CLI-style public args:
    //   expected_fee_sum = 10 (u64)
    //   expected_root    = 0x01 (bytes32, little-endian)
    let expected_fee_sum = VmArg::U64(10);
    let mut root_bytes = [0u8; 32];
    root_bytes[0] = 1;

    let expected_root = VmArg::Bytes32(root_bytes);

    let public_args = vec![expected_fee_sum, expected_root];

    // Compile-time u64 view of public args, mirroring CLI parse_public_args:
    // - U64(v)     -> v
    // - U128(v128) -> v128 as u64 (must fit)
    // - Bytes32(b) -> LE u64 from b[0..8], requiring b[8..] == 0
    let mut public_u64 = Vec::with_capacity(public_args.len());

    for arg in &public_args {
        match arg {
            VmArg::U64(v) => public_u64.push(*v),
            VmArg::U128(v128) => {
                if *v128 > u64::MAX as u128 {
                    panic!("u128 public arg does not fit into 64 bits");
                }

                public_u64.push(*v128 as u64);
            }
            VmArg::Bytes32(bytes) => {
                assert!(
                    bytes[8..].iter().all(|b| *b == 0),
                    "bytes32 public arg must have bytes[8..32]=0 (CLI restriction)"
                );
                let mut lo = [0u8; 8];
                lo.copy_from_slice(&bytes[0..8]);

                let v64 = u64::from_le_bytes(lo);
                public_u64.push(v64);
            }
        }
    }

    // Compile entry program with those u64 arguments.
    let program = compiler::compile_entry(&src, &public_u64)
        .expect("compile_entry(rollup-bench) must succeed");

    // Derive `main_args` from typed schema exactly like CLI build_pi_for_program.
    let schema = program
        .type_schemas
        .fns
        .get("main")
        .expect("typed-fn main schema for rollup-bench.zlisp");

    assert_eq!(
        schema.args.len(),
        public_args.len(),
        "main typed schema arity mismatch: schema {} vs CLI {}",
        schema.args.len(),
        public_args.len(),
    );

    let mut main_args: Vec<VmArg> = Vec::new();
    for (idx, ((role, ty), vmarg)) in schema.args.iter().zip(public_args.iter()).enumerate() {
        let pos = idx + 1;
        match role {
            ArgRole::Let => match (ty, vmarg) {
                (ScalarType::U64, VmArg::U64(_))
                | (ScalarType::U128, VmArg::U128(_))
                | (ScalarType::Bytes32, VmArg::Bytes32(_)) => {
                    main_args.push(vmarg.clone());
                }
                (ScalarType::U64, _) => {
                    panic!("main arg #{pos}: expected u64 VmArg for type 'u64'");
                }
                (ScalarType::U128, _) => {
                    panic!("main arg #{pos}: expected u128 VmArg for type 'u128'");
                }
                (ScalarType::Bytes32, _) => {
                    panic!("main arg #{pos}: expected bytes32 VmArg for type 'bytes32'");
                }
            },
            ArgRole::Const => {
                // rollup-bench main uses only (let ...) args;
                // const args are not expected here.
                panic!("unexpected ArgRole::Const at main arg #{pos}");
            }
        }
    }

    let pi = PublicInputsBuilder::from_program(&program)
        .with_public_args(&public_args)
        .with_main_args(&main_args)
        // no secrets for rollup-bench
        .build()
        .expect("PublicInputs build for rollup-bench");

    (program, pi)
}

/// Prover options matching typical CLI defaults for rollup-bench:
/// queries=64, blowup=16, grind=16, security_bits=64.
fn prover_opts_rollup_bench() -> ProverOptions {
    ProverOptions {
        queries: 64,
        blowup: 16,
        grind: 16,
        min_security_bits: 64,
        max_segment_rows: None,
        max_concurrent_segments: Some(8),
    }
}

fn prover_opts_rollup_bench_128() -> ProverOptions {
    ProverOptions {
        queries: 64,
        blowup: 16,
        grind: 16,
        min_security_bits: 128,
        max_segment_rows: None,
        max_concurrent_segments: Some(8),
    }
}

/// Build step-proofs, transcripts, and AggAirPublicInputs
/// for rollup-bench in the same way as RecursionBackend (build_public + prove).
fn build_steps_transcripts_and_agg_pi(
    program: &compiler::Program,
    pi: &PublicInputs,
    opts: &ProverOptions,
) -> (
    Vec<zk_lisp_proof_winterfell::proof::step::StepProof>,
    Vec<ZlChildTranscript>,
    AggAirPublicInputs,
) {
    // Step 1: step-proofs as in prove_chain
    let steps =
        prove::prove_program(program, pi, opts).expect("prove_program(rollup-bench) must succeed");

    assert!(
        steps.len() > 1,
        "rollup-bench is expected to produce multiple segments/steps"
    );

    // Step 2: AggAirPublicInputs via the same builder as recursion::prove_chain
    let agg_pi = <WinterfellBackend as recursion::RecursionPublicBuilder>::build_public(
        program, pi, &steps, opts,
    )
    .expect("build_public(AggAirPublicInputs) for rollup-bench");

    // Step 3: Transcripts for each step (as in RecursionBackend::prove)
    let mut transcripts = Vec::with_capacity(steps.len());
    for step in &steps {
        let tx = ZlChildTranscript::from_step(step)
            .expect("ZlChildTranscript::from_step(step) for rollup-bench");

        // sanity: check the compact view and transcript for consistency
        verify_child_transcript(&tx).expect("verify_child_transcript(rollup-bench step)");
        transcripts.push(tx);
    }

    (steps, transcripts, agg_pi)
}

/// Scan AggTrace and print which chain errors are non-zero.
/// This will help to understand whether the VM/RAM/ROM
/// chain or the Merkle/FRI/DEEP chain is broken.
fn debug_agg_trace_chain_errors(agg_pi: &AggAirPublicInputs, transcripts: &[ZlChildTranscript]) {
    let agg = build_agg_trace_from_transcripts(agg_pi, transcripts)
        .expect("build_agg_trace_from_transcripts(rollup-bench)");
    let trace = &agg.trace;
    let cols: &AggColumns = &agg.cols;
    let n = trace.length();

    let mut bad_vm = Vec::new();
    let mut bad_ram_u = Vec::new();
    let mut bad_ram_s = Vec::new();
    let mut bad_rom0 = Vec::new();
    let mut bad_rom1 = Vec::new();
    let mut bad_rom2 = Vec::new();
    let mut bad_trace_root = Vec::new();
    let mut bad_constraint_root = Vec::new();
    let mut bad_deep = Vec::new();
    let mut bad_fri_l1 = Vec::new();
    let mut bad_fri_path = Vec::new();
    let mut bad_fri_paths = Vec::new();

    for r in 0..n {
        let vm_err = trace.get(cols.vm_chain_err, r);
        let ram_u_err = trace.get(cols.ram_u_chain_err, r);
        let ram_s_err = trace.get(cols.ram_s_chain_err, r);
        let rom0_err = trace.get(cols.rom_chain_err_0, r);
        let rom1_err = trace.get(cols.rom_chain_err_1, r);
        let rom2_err = trace.get(cols.rom_chain_err_2, r);

        let tr_err = trace.get(cols.trace_root_err, r);
        let cc_err = trace.get(cols.constraint_root_err, r);
        let deep_err = trace.get(cols.comp_sum, r);
        let fri_l1_err = trace.get(cols.alpha_div_zm_sum, r);
        let fri_path_err = trace.get(cols.map_l0_sum, r);
        let fri_paths_err = trace.get(cols.final_llast_sum, r);

        if vm_err != BE::ZERO {
            bad_vm.push((r, vm_err.as_int()));
        }
        if ram_u_err != BE::ZERO {
            bad_ram_u.push((r, ram_u_err.as_int()));
        }
        if ram_s_err != BE::ZERO {
            bad_ram_s.push((r, ram_s_err.as_int()));
        }
        if rom0_err != BE::ZERO {
            bad_rom0.push((r, rom0_err.as_int()));
        }
        if rom1_err != BE::ZERO {
            bad_rom1.push((r, rom1_err.as_int()));
        }
        if rom2_err != BE::ZERO {
            bad_rom2.push((r, rom2_err.as_int()));
        }

        if tr_err != BE::ZERO {
            bad_trace_root.push((r, tr_err.as_int()));
        }
        if cc_err != BE::ZERO {
            bad_constraint_root.push((r, cc_err.as_int()));
        }
        if deep_err != BE::ZERO {
            bad_deep.push((r, deep_err.as_int()));
        }
        if fri_l1_err != BE::ZERO {
            bad_fri_l1.push((r, fri_l1_err.as_int()));
        }
        if fri_path_err != BE::ZERO {
            bad_fri_path.push((r, fri_path_err.as_int()));
        }
        if fri_paths_err != BE::ZERO {
            bad_fri_paths.push((r, fri_paths_err.as_int()));
        }
    }

    println!("=== AggTrace chain diagnostics for rollup-bench ===");
    println!("rows = {}", n);
    println!("vm_chain_err != 0 at {:?}", bad_vm);
    println!("ram_u_chain_err != 0 at {:?}", bad_ram_u);
    println!("ram_s_chain_err != 0 at {:?}", bad_ram_s);
    println!("rom_chain_err_0 != 0 at {:?}", bad_rom0);
    println!("rom_chain_err_1 != 0 at {:?}", bad_rom1);
    println!("rom_chain_err_2 != 0 at {:?}", bad_rom2);
    println!("trace_root_err != 0 at {:?}", bad_trace_root);
    println!("constraint_root_err != 0 at {:?}", bad_constraint_root);
    println!("comp_sum (DEEP) != 0 at {:?}", bad_deep);
    println!("alpha_div_zm_sum (FRI L1 agg) != 0 at {:?}", bad_fri_l1);
    println!("map_l0_sum (FRI path agg) != 0 at {:?}", bad_fri_path);
    println!(
        "final_llast_sum (FRI paths agg) != 0 at {:?}",
        bad_fri_paths
    );
}

/// End-to-end recursion pipeline for rollup-bench, mirroring:
///
///   zk-lisp prove  examples/rollup-bench.zlisp --arg u64:10 --arg bytes32:0x01
///   zk-lisp verify <agg-proof>.bin  examples/rollup-bench.zlisp --arg u64:10 --arg bytes32:0x01
///
/// Steps:
/// 1. Build Program + PI exactly like CLI.
/// 2. (Optional) run preflight to ensure base AIR is satisfied.
/// 3. Build step proofs + aggregation via recursion_prove::<WinterfellBackend>.
/// 4. Encode recursion artifact via RecursionArtifactCodec (CLI prove path).
/// 5. Decode artifact and run recursion_verify::<WinterfellBackend> (CLI verify path).
#[test]
#[ignore]
fn recursion_rollup_bench_roundtrip_like_cli() {
    let (program, pi) = build_rollup_bench_program_and_pi();
    let opts = prover_opts_rollup_bench();

    // Sanity: base-level preflight should pass
    frontend::preflight::<WinterfellBackend>(PreflightMode::Off, &opts, &program, &pi)
        .expect("preflight OFF should be a no-op");

    // 1) Full recursion pipeline: prove_chain (builds step proofs + agg proof)
    let (rc_proof, rc_digest, rc_pi) =
        recursion::prove_chain::<WinterfellBackend>(&program, &pi, &opts)
            .expect("recursion::prove_chain(rollup-bench) must succeed");

    // We won't use rc_digest here yet, but it's important that
    // it stays stable relative to AggAirPublicInputs.
    assert!(
        rc_digest.iter().any(|b| *b != 0),
        "recursion digest for rollup-bench must be non-zero"
    );

    // 2) We encode the artifact in the same way as the CLI prove
    let artifact_bytes = <WinterfellBackend as RecursionArtifactCodec>::encode(&rc_proof, &rc_pi)
        .expect("encode recursion artifact for rollup-bench");

    // 3) We decode it in the same way as CLI verify
    let (rc_proof_dec, rc_pi_dec) =
        <WinterfellBackend as RecursionArtifactCodec>::decode(&artifact_bytes)
            .expect("decode recursion artifact for rollup-bench");

    // Quick sanity checks to ensure encode/decode
    // haven't changed the binding to the program/PI.
    assert_eq!(
        rc_pi_dec.program_id, rc_pi.program_id,
        "program_id must survive encode/decode"
    );
    assert_eq!(
        rc_pi_dec.program_commitment, rc_pi.program_commitment,
        "program_commitment must survive encode/decode"
    );
    assert_eq!(
        rc_pi_dec.pi_digest, rc_pi.pi_digest,
        "pi_digest must survive encode/decode"
    );

    // 4) The final check of the aggregation proof is the same
    // as what the CLI zk-lisp verify fails on for rollup-bench.
    frontend::recursion_verify::<WinterfellBackend>(rc_proof_dec, &rc_pi_dec, &opts)
        .expect("recursion_verify(rollup-bench) must succeed like CLI verify");
}

/// Aggregator diagnostics for rollup-bench:
/// plotting steps and AggTrace and checking
/// which chain errors are non-zero.
#[test]
#[ignore]
fn recursion_rollup_bench_agg_diag() {
    let (program, pi) = build_rollup_bench_program_and_pi();
    let opts = prover_opts_rollup_bench();

    let (_steps, transcripts, agg_pi) = build_steps_transcripts_and_agg_pi(&program, &pi, &opts);

    debug_agg_trace_chain_errors(&agg_pi, &transcripts);
}

#[test]
#[ignore]
fn recursion_rollup_bench_roundtrip_like_cli_128_bits() {
    let (program, pi) = build_rollup_bench_program_and_pi();
    let opts = prover_opts_rollup_bench_128();

    // 1) Build the recursion-proof chain in the same way as CLI `prove`
    let (rc_proof, rc_digest, rc_pi) =
        recursion::prove_chain::<WinterfellBackend>(&program, &pi, &opts)
            .expect("recursion::prove_chain(rollup-bench, 128 bits) must succeed");

    assert!(
        rc_digest.iter().any(|b| *b != 0),
        "recursion digest for rollup-bench (128 bits) must be non-zero"
    );

    // 2) Encode the recursion artifact in the same way as CLI `prove` does
    let artifact_bytes = <WinterfellBackend as RecursionArtifactCodec>::encode(&rc_proof, &rc_pi)
        .expect("encode recursion artifact for rollup-bench (128 bits)");

    // 3) Decode it in the same way as CLI `verify` does
    let (rc_proof_dec, rc_pi_dec) =
        <WinterfellBackend as RecursionArtifactCodec>::decode(&artifact_bytes)
            .expect("decode recursion artifact for rollup-bench (128 bits)");

    // Sanity: encode/decode must not break the binding to program/PI
    assert_eq!(
        rc_pi_dec.program_id, rc_pi.program_id,
        "program_id must survive encode/decode (128 bits)",
    );
    assert_eq!(
        rc_pi_dec.program_commitment, rc_pi.program_commitment,
        "program_commitment must survive encode/decode (128 bits)",
    );
    assert_eq!(
        rc_pi_dec.pi_digest, rc_pi.pi_digest,
        "pi_digest must survive encode/decode (128 bits)",
    );

    assert_agg_pi_equal(&rc_pi_dec, &rc_pi);

    // 4) Final aggregation-proof check — equivalent to `zk-lisp verify`;
    // We expect the same result as CLI `verify`.
    frontend::recursion_verify::<WinterfellBackend>(rc_proof_dec, &rc_pi_dec, &opts)
        .expect("recursion_verify(rollup-bench, 128 bits) must succeed like CLI verify");
}

/// Full diagnostics of all 24 transition constraints of `ZlAggAir`
/// on the aggregation trace. Uses the same logic as
/// `ZlAggAir::evaluate_transition`, but written out explicitly.
fn debug_agg_transition_constraint_violations(
    agg_pi: &AggAirPublicInputs,
    transcripts: &[ZlChildTranscript],
) {
    let agg = build_agg_trace_from_transcripts(agg_pi, transcripts)
        .expect("build_agg_trace_from_transcripts(rollup-bench, 128 bits)");
    let trace = &agg.trace;
    let cols: &AggColumns = &agg.cols;
    let n = trace.length();

    // For each constraint C0..C23 collect all violations:
    // bad[i] = list of (row, value) where constraint i != 0.
    let mut bad: Vec<Vec<(usize, BE)>> = vec![Vec::new(); 24];

    for r in 0..n {
        let next_r = (r + 1) % n;

        // periodic is_last: 1 only on the last row, 0 everywhere else
        let is_last = if r + 1 == n { BE::ONE } else { BE::ZERO };
        let not_last = BE::ONE - is_last;

        // Snapshot current and next values of all used columns
        let ok = trace.get(cols.ok, r);
        let v_acc = trace.get(cols.v_units_acc, r);
        let v_acc_next = trace.get(cols.v_units_acc, next_r);
        let v_child = trace.get(cols.v_units_child, r);
        let seg_first = trace.get(cols.seg_first, r);
        let trace_root_err = trace.get(cols.trace_root_err, r);
        let constraint_root_err = trace.get(cols.constraint_root_err, r);
        let child_count_acc = trace.get(cols.child_count_acc, r);
        let child_count_acc_next = trace.get(cols.child_count_acc, next_r);

        let r_chal = trace.get(cols.r, r);
        let r_next = trace.get(cols.r, next_r);
        let alpha = trace.get(cols.alpha, r);
        let alpha_next = trace.get(cols.alpha, next_r);
        let beta = trace.get(cols.beta, r);
        let beta_next = trace.get(cols.beta, next_r);
        let gamma = trace.get(cols.gamma, r);
        let gamma_next = trace.get(cols.gamma, next_r);

        let v0_sum = trace.get(cols.v0_sum, r);
        let v0_sum_next = trace.get(cols.v0_sum, next_r);
        let v1_sum = trace.get(cols.v1_sum, r);
        let v1_sum_next = trace.get(cols.v1_sum, next_r);
        let vnext_sum = trace.get(cols.vnext_sum, r);
        let vnext_sum_next = trace.get(cols.vnext_sum, next_r);

        let fri_v0_child = trace.get(cols.fri_v0_child, r);
        let fri_v1_child = trace.get(cols.fri_v1_child, r);
        let fri_vnext_child = trace.get(cols.fri_vnext_child, r);
        let fri_alpha_child = trace.get(cols.fri_alpha_child, r);
        let fri_x0_child = trace.get(cols.fri_x0_child, r);
        let fri_x1_child = trace.get(cols.fri_x1_child, r);
        let fri_q1_child = trace.get(cols.fri_q1_child, r);

        let comp_sum = trace.get(cols.comp_sum, r);
        let fri_layer1_agg = trace.get(cols.alpha_div_zm_sum, r);
        let fri_path_agg = trace.get(cols.map_l0_sum, r);
        let fri_paths_agg = trace.get(cols.final_llast_sum, r);

        let vm_chain_err = trace.get(cols.vm_chain_err, r);
        let ram_u_chain_err = trace.get(cols.ram_u_chain_err, r);
        let ram_s_chain_err = trace.get(cols.ram_s_chain_err, r);
        let rom_chain_err_0 = trace.get(cols.rom_chain_err_0, r);
        let rom_chain_err_1 = trace.get(cols.rom_chain_err_1, r);
        let rom_chain_err_2 = trace.get(cols.rom_chain_err_2, r);

        let mut c = [BE::ZERO; 24];

        // C0: ok == 0
        c[0] = ok;

        // C1: v_units_acc chain (increment on seg_first, otherwise constant) on non-last rows
        c[1] = not_last * (v_acc_next - (v_acc + v_child * seg_first));

        // C2: trace_root_err == 0
        c[2] = trace_root_err;

        // C3: constraint_root_err == 0
        c[3] = constraint_root_err;

        // C4–C7: r, alpha, beta, gamma must stay constant
        // along the trace (via not_last * (next - cur)).
        c[4] = not_last * (r_next - r_chal);
        c[5] = not_last * (alpha_next - alpha);
        c[6] = not_last * (beta_next - beta);
        c[7] = not_last * (gamma_next - gamma);

        // C8–C10: v0_sum, v1_sum, vnext_sum must
        // also stay constant along the trace.
        c[8] = not_last * (v0_sum_next - v0_sum);
        c[9] = not_last * (v1_sum_next - v1_sum);
        c[10] = not_last * (vnext_sum_next - vnext_sum);

        // C11: child_count_acc increments by 1 on seg_first rows.
        c[11] = not_last * (child_count_acc_next - (child_count_acc + seg_first));

        // C12: FRI binary folding: (x1 - x0) * vnext == v1*(alpha - x0) - v0*(alpha - x1)
        let x_diff = fri_x1_child - fri_x0_child;
        let lhs = fri_vnext_child * x_diff;
        let rhs = fri_v1_child * (fri_alpha_child - fri_x0_child)
            - fri_v0_child * (fri_alpha_child - fri_x1_child);
        c[12] = lhs - rhs;

        // C13: vnext_child == fri_q1_child
        c[13] = fri_vnext_child - fri_q1_child;

        // C14: comp_sum == 0 (DEEP vs FRI L0 aggregate error must vanish)
        c[14] = comp_sum;

        // C15: fri_layer1_agg == 0 (FRI layer-1 aggregate error must vanish)
        c[15] = fri_layer1_agg;

        // C16: fri_path_agg == 0 (local FRI path aggregate error must vanish)
        c[16] = fri_path_agg;

        // C17: fri_paths_agg == 0 (global aggregate over all FRI paths must vanish)
        c[17] = fri_paths_agg;

        // C18–C23: global VM/RAM/ROM boundary chains
        c[18] = vm_chain_err;
        c[19] = ram_u_chain_err;
        c[20] = ram_s_chain_err;
        c[21] = rom_chain_err_0;
        c[22] = rom_chain_err_1;
        c[23] = rom_chain_err_2;

        for (i, val) in c.into_iter().enumerate() {
            if val != BE::ZERO {
                bad[i].push((r, val));
            }
        }
    }

    println!("=== AggAir transition constraints diagnostics (rollup-bench) ===");
    println!("rows = {}", n);
    for (i, rows) in bad.iter().enumerate() {
        println!("C{i} != 0 at {:?}", rows);
    }
}

fn assert_agg_pi_equal(actual: &AggAirPublicInputs, expected: &AggAirPublicInputs) {
    assert_eq!(
        actual.program_id, expected.program_id,
        "AggAirPublicInputs.program_id mismatch after encode/decode",
    );
    assert_eq!(
        actual.program_commitment, expected.program_commitment,
        "AggAirPublicInputs.program_commitment mismatch after encode/decode",
    );
    assert_eq!(
        actual.pi_digest, expected.pi_digest,
        "AggAirPublicInputs.pi_digest mismatch after encode/decode",
    );
    assert_eq!(
        actual.children_root, expected.children_root,
        "AggAirPublicInputs.children_root mismatch after encode/decode",
    );
    assert_eq!(
        actual.v_units_total, expected.v_units_total,
        "AggAirPublicInputs.v_units_total mismatch after encode/decode",
    );
    assert_eq!(
        actual.children_count, expected.children_count,
        "AggAirPublicInputs.children_count mismatch after encode/decode",
    );
    assert_eq!(
        actual.batch_id, expected.batch_id,
        "AggAirPublicInputs.batch_id mismatch after encode/decode",
    );

    // profile_meta
    assert_eq!(
        actual.profile_meta.m, expected.profile_meta.m,
        "AggAirPublicInputs.profile_meta.m mismatch after encode/decode",
    );
    assert_eq!(
        actual.profile_meta.rho, expected.profile_meta.rho,
        "AggAirPublicInputs.profile_meta.rho mismatch after encode/decode",
    );
    assert_eq!(
        actual.profile_meta.q, expected.profile_meta.q,
        "AggAirPublicInputs.profile_meta.q mismatch after encode/decode",
    );
    assert_eq!(
        actual.profile_meta.o, expected.profile_meta.o,
        "AggAirPublicInputs.profile_meta.o mismatch after encode/decode",
    );
    assert_eq!(
        actual.profile_meta.lambda, expected.profile_meta.lambda,
        "AggAirPublicInputs.profile_meta.lambda mismatch after encode/decode",
    );
    assert_eq!(
        actual.profile_meta.pi_len, expected.profile_meta.pi_len,
        "AggAirPublicInputs.profile_meta.pi_len mismatch after encode/decode",
    );
    assert_eq!(
        actual.profile_meta.v_units, expected.profile_meta.v_units,
        "AggAirPublicInputs.profile_meta.v_units mismatch after encode/decode",
    );

    // profile_fri
    assert_eq!(
        actual.profile_fri.lde_blowup, expected.profile_fri.lde_blowup,
        "AggAirPublicInputs.profile_fri.lde_blowup mismatch after encode/decode",
    );
    assert_eq!(
        actual.profile_fri.folding_factor, expected.profile_fri.folding_factor,
        "AggAirPublicInputs.profile_fri.folding_factor mismatch after encode/decode",
    );
    assert_eq!(
        actual.profile_fri.redundancy, expected.profile_fri.redundancy,
        "AggAirPublicInputs.profile_fri.redundancy mismatch after encode/decode",
    );
    assert_eq!(
        actual.profile_fri.num_layers, expected.profile_fri.num_layers,
        "AggAirPublicInputs.profile_fri.num_layers mismatch after encode/decode",
    );

    // profile_queries
    assert_eq!(
        actual.profile_queries.num_queries, expected.profile_queries.num_queries,
        "AggAirPublicInputs.profile_queries.num_queries mismatch after encode/decode",
    );
    assert_eq!(
        actual.profile_queries.grinding_factor, expected.profile_queries.grinding_factor,
        "AggAirPublicInputs.profile_queries.grinding_factor mismatch after encode/decode",
    );

    // suite & children_ms
    assert_eq!(
        actual.suite_id, expected.suite_id,
        "AggAirPublicInputs.suite_id mismatch after encode/decode",
    );
    assert_eq!(
        actual.children_ms, expected.children_ms,
        "AggAirPublicInputs.children_ms mismatch after encode/decode",
    );

    // VM / RAM / ROM boundaries
    assert_eq!(
        actual.vm_state_initial, expected.vm_state_initial,
        "AggAirPublicInputs.vm_state_initial mismatch after encode/decode",
    );
    assert_eq!(
        actual.vm_state_final, expected.vm_state_final,
        "AggAirPublicInputs.vm_state_final mismatch after encode/decode",
    );
    assert_eq!(
        actual.ram_gp_unsorted_initial, expected.ram_gp_unsorted_initial,
        "AggAirPublicInputs.ram_gp_unsorted_initial mismatch after encode/decode",
    );
    assert_eq!(
        actual.ram_gp_unsorted_final, expected.ram_gp_unsorted_final,
        "AggAirPublicInputs.ram_gp_unsorted_final mismatch after encode/decode",
    );
    assert_eq!(
        actual.ram_gp_sorted_initial, expected.ram_gp_sorted_initial,
        "AggAirPublicInputs.ram_gp_sorted_initial mismatch after encode/decode",
    );
    assert_eq!(
        actual.ram_gp_sorted_final, expected.ram_gp_sorted_final,
        "AggAirPublicInputs.ram_gp_sorted_final mismatch after encode/decode",
    );
    assert_eq!(
        actual.rom_s_initial, expected.rom_s_initial,
        "AggAirPublicInputs.rom_s_initial mismatch after encode/decode",
    );
    assert_eq!(
        actual.rom_s_final, expected.rom_s_final,
        "AggAirPublicInputs.rom_s_final mismatch after encode/decode",
    );
}

/// Diagnostics for `ZlAggAir` on rollup-bench at `min_security_bits=128`.
///
/// Build step proofs and transcripts with the same options
/// as CLI `prove` in release, and inspect which
/// `ZlAggAir` transition constraints fail to vanish.
#[test]
#[ignore]
fn recursion_rollup_bench_agg_diag_128_bits() {
    let (program, pi) = build_rollup_bench_program_and_pi();
    let opts = prover_opts_rollup_bench_128();

    let (_steps, transcripts, agg_pi) = build_steps_transcripts_and_agg_pi(&program, &pi, &opts);

    debug_agg_transition_constraint_violations(&agg_pi, &transcripts);
}

/// Pure aggregation roundtrip for rollup-bench: build an `AggTrace` and run
/// `ZlAggAir` through Winterfell (prove + verify) with the same parameters
/// as the recursion backend. This isolates problems from the recursion layer
/// into a standalone aggregator.
#[test]
#[ignore]
fn recursion_rollup_bench_agg_roundtrip_128_bits() {
    let (program, pi) = build_rollup_bench_program_and_pi();
    let opts = prover_opts_rollup_bench_128();

    // Diagnostics: which ALU opcodes are
    // actually used on the targeted segment.
    scan_alu_usage_for_segment(&program, &pi, &opts);

    // Steps and transcripts constructed
    // exactly as in the recursion backend.
    let (_steps, transcripts, agg_pi) = build_steps_transcripts_and_agg_pi(&program, &pi, &opts);

    // Build aggregation trace from transcripts.
    let agg = build_agg_trace_from_transcripts(&agg_pi, &transcripts)
        .expect("build_agg_trace_from_transcripts(rollup-bench, 128 bits)");
    let trace = agg.trace;
    let trace_width = trace.width();
    let trace_length = trace.length();

    // Mirror the logic of `prove_agg_proof`
    // when constructing `ProofOptions`.
    let min_bits = opts.min_security_bits;
    let blowup = opts.blowup as usize;
    let grind = opts.grind;
    let agg_queries = opts.queries.max(16) as usize;

    let field_extension = if min_bits >= 128 {
        FieldExtension::Quadratic
    } else {
        FieldExtension::None
    };

    let (num_partitions, hash_rate) =
        zk_lisp_proof_winterfell::utils::select_partitions_for_trace(trace_width, trace_length);

    let base_opts = ProofOptions::new(
        agg_queries,
        blowup,
        grind,
        field_extension,
        2,
        1,
        winterfell::BatchingMethod::Linear,
        winterfell::BatchingMethod::Linear,
    );

    // Sanity-check security bits exactly as in `prove_agg_proof`
    if min_bits >= 64 {
        let bits = prove::estimate_conjectured_security_bits(&base_opts);
        assert!(
            bits >= min_bits,
            "agg options do not meet requested security: estimated_bits={bits}, min_bits={min_bits}",
        );
    }

    let wf_opts = base_opts.with_partitions(num_partitions, hash_rate);

    let prover = AggProver::new(wf_opts.clone(), agg_pi.clone());

    // 1) Try to construct an aggregation proof
    let proof: Proof = prover
        .prove(trace.clone())
        .expect("agg proof for rollup-bench must be created");

    // 2) Verify it directly via `winterfell::verify`
    let acceptable = AcceptableOptions::MinConjecturedSecurity(min_bits);

    winterfell::verify::<
        ZlAggAir,
        PoseidonHasher<BE>,
        DefaultRandomCoin<PoseidonHasher<BE>>,
        MerkleTree<PoseidonHasher<BE>>,
    >(proof, agg_pi, &acceptable)
    .expect("agg proof for rollup-bench must verify in pure Winterfell roundtrip");
}

fn scan_alu_usage_for_segment(
    program: &compiler::Program,
    pi: &PublicInputs,
    opts: &ProverOptions,
) {
    // 1) Build the full execution trace for the program
    let full = zk_lisp_proof_winterfell::vm::trace::build_trace(program, pi).expect("full trace");

    // 2) Take the same `Segment` that `prove_program` / `segment_planner` use
    let segments =
        zk_lisp_proof_winterfell::segment_planner::WinterfellSegmentPlanner::plan_segments(
            program, pi, opts,
        )
        .expect("segments");
    assert!(!segments.is_empty());

    // For diagnostics, inspect the second segment in the chain
    let seg = &segments[1];

    let cols = zk_lisp_proof_winterfell::vm::layout::Columns::baseline();
    let mut used = std::collections::BTreeMap::new();

    for row in seg.r_start..seg.r_end {
        macro_rules! mark {
            ($name:ident, $col:expr) => {
                if full.get($col, row) != BE::ZERO {
                    used.insert(stringify!($name), true);
                }
            };
        }

        mark!(op_const, cols.op_const);
        mark!(op_mov, cols.op_mov);
        mark!(op_add, cols.op_add);
        mark!(op_sub, cols.op_sub);
        mark!(op_mul, cols.op_mul);
        mark!(op_neg, cols.op_neg);
        mark!(op_eq, cols.op_eq);
        mark!(op_select, cols.op_select);
        mark!(op_sponge, cols.op_sponge);
        mark!(op_assert, cols.op_assert);
        mark!(op_assert_bit, cols.op_assert_bit);
        mark!(op_assert_range, cols.op_assert_range);
        mark!(op_divmod, cols.op_divmod);
        mark!(op_mulwide, cols.op_mulwide);
        mark!(op_div128, cols.op_div128);
        mark!(op_load, cols.op_load);
        mark!(op_store, cols.op_store);
    }

    println!("ALU ops used on segment {:?}: {used:?}", seg);
}

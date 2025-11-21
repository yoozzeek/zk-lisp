// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.

use zk_lisp_compiler::builder::{Op, ProgramBuilder};
use zk_lisp_proof::ProverOptions;
use zk_lisp_proof::pi::PublicInputsBuilder;
use zk_lisp_proof_winterfell::agg_air::AggAirPublicInputs;
use zk_lisp_proof_winterfell::agg_child::{ZlChildCompact, children_root_from_compact};
use zk_lisp_proof_winterfell::agg_trace::build_agg_trace;

fn init_tracing() {
    static INIT: std::sync::Once = std::sync::Once::new();
    INIT.call_once(|| {
        let filter = std::env::var("RUST_LOG").unwrap_or_else(|_| "info".to_string());
        let _ = tracing_subscriber::fmt()
            .with_env_filter(filter)
            .with_test_writer()
            .try_init();
    });
}

fn make_opts() -> ProverOptions {
    ProverOptions {
        min_security_bits: 40,
        blowup: 8,
        grind: 8,
        queries: 8,
    }
}

fn build_large_program_for_multiseg() -> zk_lisp_compiler::Program {
    // Create a program large enough to exceed one segment
    // (see WinterfellSegmentPlanner::MAX_SEGMENT_ROWS and STEPS_PER_LEVEL_P2).
    let metrics = zk_lisp_compiler::CompilerMetrics::default();
    let mut b = ProgramBuilder::new();

    // Construct target_levels = (MAX_SEGMENT_ROWS / STEPS_PER_LEVEL_P2) + 1
    // We reuse the same op per level; padding to next power-of-two
    // will push total rows above the per-segment cap.
    // STEPS_PER_LEVEL_P2 = 32.
    // Use env override ZKL_MAX_SEGMENT_ROWS when present
    // so tests can force multi-seg without huge programs.
    let steps_per_level = zk_lisp_proof_winterfell::layout::STEPS_PER_LEVEL_P2;
    let max_rows = std::env::var("ZKL_MAX_SEGMENT_ROWS")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(1 << 16);
    let target_levels = (max_rows / steps_per_level) + 1;

    for _ in 0..target_levels {
        b.push(Op::Const { dst: 0, imm: 1 });
    }

    b.push(Op::End);

    b.finalize(metrics).expect("program build must succeed")
}

#[test]
fn agg_multiseg_positive_builds_trace() {
    init_tracing();
    let program = build_large_program_for_multiseg();
    let pi = PublicInputsBuilder::from_program(&program)
        .build()
        .expect("pi build");
    let opts = make_opts();

    // Build multi-segment step proofs
    let steps = zk_lisp_proof_winterfell::prove::prove_program_steps(&program, &pi, &opts)
        .expect("prove_program_steps must succeed and produce multiple segments");
    assert!(steps.len() > 1, "expected multi-segment output");

    // Compact children and compute children_root
    let children: Vec<ZlChildCompact> = steps
        .iter()
        .map(|s| ZlChildCompact::from_step(s).expect("child compact"))
        .collect();

    let suite_id = children[0].suite_id;
    let children_root = children_root_from_compact(&suite_id, &children);

    // Global boundaries from the first/last child
    let first = &children[0];
    let last = &children[children.len() - 1];

    // Sum v_units and collect m's
    let v_sum: u64 = children.iter().map(|c| c.meta.v_units).sum();
    let children_ms: Vec<u32> = children.iter().map(|c| c.meta.m).collect();

    let agg_pi = AggAirPublicInputs {
        children_root,
        v_units_total: v_sum,
        children_count: children.len() as u32,
        batch_id: [0u8; 32],
        profile_meta: zk_lisp_proof_winterfell::agg_air::AggProfileMeta {
            m: first.meta.m,
            rho: first.meta.rho,
            q: first.meta.q,
            o: first.meta.o,
            lambda: first.meta.lambda,
            pi_len: first.meta.pi_len,
            v_units: first.meta.v_units, // unused in checks beyond to_elements
        },
        profile_fri: zk_lisp_proof_winterfell::agg_air::AggFriProfile::default(),
        profile_queries: zk_lisp_proof_winterfell::agg_air::AggQueryProfile {
            num_queries: first.meta.q,
            grinding_factor: 0,
        },
        suite_id,
        children_ms,
        vm_state_initial: first.state_in_hash,
        vm_state_final: last.state_out_hash,
        ram_gp_unsorted_initial: first.ram_gp_unsorted_in,
        ram_gp_unsorted_final: last.ram_gp_unsorted_out,
        ram_gp_sorted_initial: first.ram_gp_sorted_in,
        ram_gp_sorted_final: last.ram_gp_sorted_out,
        rom_s_initial: first.rom_s_in,
        rom_s_final: last.rom_s_out,
    };

    // Build aggregation trace (compact path) — should succeed
    let _agg_trace = build_agg_trace(&agg_pi, &children)
        .expect("agg trace must build for honest multiseg batch");
}

#[test]
fn agg_multiseg_negative_invalid_index_rejected() {
    init_tracing();
    let program = build_large_program_for_multiseg();
    let pi = PublicInputsBuilder::from_program(&program)
        .build()
        .expect("pi build");
    let opts = make_opts();

    let steps = zk_lisp_proof_winterfell::prove::prove_program_steps(&program, &pi, &opts)
        .expect("prove_program_steps must succeed");
    assert!(steps.len() > 1);

    let mut children: Vec<ZlChildCompact> = steps
        .iter()
        .map(|s| ZlChildCompact::from_step(s).expect("child compact"))
        .collect();

    // Tamper one child: set segment_index out of range
    children[0].segment_index = children[0].segments_total; // invalid

    let suite_id = children[1].suite_id;
    let children_root = children_root_from_compact(&suite_id, &children);

    // Minimal agg_pi (values unused due to early sanity failure)
    let agg_pi = AggAirPublicInputs {
        children_root,
        v_units_total: children.iter().map(|c| c.meta.v_units).sum(),
        children_count: children.len() as u32,
        batch_id: [0u8; 32],
        profile_meta: Default::default(),
        profile_fri: Default::default(),
        profile_queries: Default::default(),
        suite_id,
        children_ms: children.iter().map(|c| c.meta.m).collect(),
        vm_state_initial: children[0].state_in_hash,
        vm_state_final: children.last().unwrap().state_out_hash,
        ram_gp_unsorted_initial: children[0].ram_gp_unsorted_in,
        ram_gp_unsorted_final: children.last().unwrap().ram_gp_unsorted_out,
        ram_gp_sorted_initial: children[0].ram_gp_sorted_in,
        ram_gp_sorted_final: children.last().unwrap().ram_gp_sorted_out,
        rom_s_initial: children[0].rom_s_in,
        rom_s_final: children.last().unwrap().rom_s_out,
    };

    let err = build_agg_trace(&agg_pi, &children)
        .expect_err("agg trace must fail for invalid segment_index");
    match err {
        zk_lisp_proof::error::Error::InvalidInput(msg) => {
            assert!(msg.contains("segment_index"));
        }
    }
}

#[test]
fn agg_multiseg_negative_missing_segment_rejected() {
    init_tracing();
    let program = build_large_program_for_multiseg();
    let pi = PublicInputsBuilder::from_program(&program)
        .build()
        .expect("pi build");
    let opts = make_opts();

    let steps = zk_lisp_proof_winterfell::prove::prove_program_steps(&program, &pi, &opts)
        .expect("prove_program_steps must succeed");

    let mut children: Vec<ZlChildCompact> = steps
        .iter()
        .map(|s| ZlChildCompact::from_step(s).expect("child compact"))
        .collect();
    assert!(children.len() > 1);

    // Drop the last segment — chain is incomplete
    children.pop();

    let suite_id = children[0].suite_id;
    let children_root = children_root_from_compact(&suite_id, &children);

    let agg_pi = AggAirPublicInputs {
        children_root,
        v_units_total: children.iter().map(|c| c.meta.v_units).sum(),
        children_count: children.len() as u32,
        batch_id: [0u8; 32],
        profile_meta: Default::default(),
        profile_fri: Default::default(),
        profile_queries: Default::default(),
        suite_id,
        children_ms: children.iter().map(|c| c.meta.m).collect(),
        vm_state_initial: children[0].state_in_hash,
        vm_state_final: children.last().unwrap().state_out_hash,
        ram_gp_unsorted_initial: children[0].ram_gp_unsorted_in,
        ram_gp_unsorted_final: children.last().unwrap().ram_gp_unsorted_out,
        ram_gp_sorted_initial: children[0].ram_gp_sorted_in,
        ram_gp_sorted_final: children.last().unwrap().ram_gp_sorted_out,
        rom_s_initial: children[0].rom_s_in,
        rom_s_final: children.last().unwrap().rom_s_out,
    };

    let err = build_agg_trace(&agg_pi, &children)
        .expect_err("agg trace must fail for missing segment in chain");
    match err {
        zk_lisp_proof::error::Error::InvalidInput(msg) => {
            assert!(msg.contains("complete contiguous segment chain"));
        }
    }
}

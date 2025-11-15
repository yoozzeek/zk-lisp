// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

use winterfell::math::FieldElement;
use winterfell::math::ToElements;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::{Air, BatchingMethod, FieldExtension, ProofOptions, TraceInfo};

use zk_lisp_proof::pi::{FM_VM, PublicInputs, VmArg};
use zk_lisp_proof_winterfell::AirPublicInputs;
use zk_lisp_proof_winterfell::air::ZkLispAir;
use zk_lisp_proof_winterfell::layout::{Columns, NR, STEPS_PER_LEVEL_P2};
use zk_lisp_proof_winterfell::schedule;
use zk_lisp_proof_winterfell::utils::encode_main_args_to_slots;

#[test]
fn air_public_inputs_encode_main_args_at_tail() {
    let core = PublicInputs {
        main_args: vec![VmArg::U64(5), VmArg::U64(7)],
        ..Default::default()
    };

    let api = AirPublicInputs {
        core: core.clone(),
        rom_acc: [BE::ZERO; 3],
    };

    let els = api.to_elements();

    // 5 base elements + slots for main_args
    let slots = encode_main_args_to_slots(&core.main_args);
    assert_eq!(els.len(), 5 + slots.len());

    assert_eq!(els[5], BE::from(5u64));
    assert_eq!(els[6], BE::from(7u64));
}

#[test]
fn zk_lisp_air_adds_main_args_boundary_assertions() {
    // core PI with VM feature and two main_args
    let mut core = PublicInputs::default();
    core.feature_mask |= FM_VM;
    core.main_args = vec![VmArg::U64(10), VmArg::U64(20)];

    let air_pi = AirPublicInputs {
        core: core.clone(),
        rom_acc: [BE::ZERO; 3],
    };

    let cols = Columns::baseline();
    let width = cols.width(core.feature_mask);

    // One level, length = STEPS_PER_LEVEL_P2
    let trace_len = STEPS_PER_LEVEL_P2;
    let trace_info = TraceInfo::new(width, trace_len);

    let opts = ProofOptions::new(
        1,
        8,
        0,
        FieldExtension::None,
        2,
        1,
        BatchingMethod::Linear,
        BatchingMethod::Linear,
    );

    let air: ZkLispAir = <ZkLispAir as Air>::new(trace_info, air_pi, opts);
    let assertions = <ZkLispAir as Air>::get_assertions(&air);

    // Assertions are per-slot rather than per-arg
    let slots = encode_main_args_to_slots(&core.main_args);
    let tail_start = NR - slots.len();
    let row0_map = schedule::pos_map();

    for (j, expected) in slots.iter().enumerate() {
        let reg_idx = tail_start + j;
        let col = cols.r_index(reg_idx);

        let found = assertions
            .iter()
            .any(|a| a.column() == col && a.first_step() == row0_map && a.values()[0] == *expected);

        assert!(found, "no assertion for r{reg_idx} at row {row0_map}");
    }
}

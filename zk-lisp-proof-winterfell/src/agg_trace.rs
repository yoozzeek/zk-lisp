// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Aggregation trace builder for ZlAggAir.
//!
//! This module constructs a minimal aggregation trace over
//! `AggColumns` from a batch of `ZlChildCompact` instances
//! and public inputs. The initial implementation focuses on
//! enforcing a global work accumulator consistent with
//! `AggAirPublicInputs::v_units_total`.

use crate::agg_air::AggAirPublicInputs;
use crate::agg_child::{ZlChildCompact, children_root_from_compact};
use crate::agg_layout::AggColumns;

use winterfell::TraceTable;
use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;
use zk_lisp_proof::error;

/// Helper structure bundling an aggregation trace with
/// its column layout.
#[derive(Debug)]
pub struct AggTrace {
    pub trace: TraceTable<BE>,
    pub cols: AggColumns,
}

impl AggTrace {
    #[inline]
    pub fn new(trace: TraceTable<BE>, cols: AggColumns) -> Self {
        Self { trace, cols }
    }
}

/// Build an aggregation trace from compact child proofs
/// and aggregation public inputs.
///
/// Invariants enforced here:
/// - `children` must be non-empty;
/// - `agg_pi.children_count == children.len()`;
/// - `agg_pi.children_ms.len() == children.len()`;
/// - for all `i`, `agg_pi.children_ms[i] == children[i].meta.m`;
/// - `agg_pi.v_units_total` equals the sum of `children[i].meta.v_units`.
///
/// The trace layout:
/// - child segments are concatenated in order;
/// - each child `j` with base trace length `m_j` occupies `m_j` rows;
/// - on the first row of each child segment we set `seg_first = 1`
///   and `v_units_child = meta.v_units`;
/// - on all other rows `seg_first = 0` and `v_units_child = 0`;
/// - the global accumulator `v_units_acc` is updated only on
///   rows where `seg_first == 1` and remains constant elsewhere.
pub fn build_agg_trace(
    agg_pi: &AggAirPublicInputs,
    children: &[ZlChildCompact],
) -> error::Result<AggTrace> {
    if children.is_empty() {
        return Err(error::Error::InvalidInput(
            "AggTrace requires at least one child proof",
        ));
    }

    let cols = AggColumns::baseline();
    let n_children = children.len();

    // Basic shape checks against public inputs.
    if agg_pi.children_count != n_children as u32 {
        return Err(error::Error::InvalidInput(
            "AggAirPublicInputs.children_count must match number of children",
        ));
    }
    if agg_pi.children_ms.len() != n_children {
        return Err(error::Error::InvalidInput(
            "AggAirPublicInputs.children_ms length must match number of children",
        ));
    }

    // Enforce suite_id consistency
    // across children and public inputs.
    for child in children {
        if child.suite_id != agg_pi.suite_id {
            return Err(error::Error::InvalidInput(
                "AggAirPublicInputs.suite_id must match suite_id of all children",
            ));
        }
    }

    // Enforce canonical children_root
    let children_root_expected = children_root_from_compact(&agg_pi.suite_id, children);
    if children_root_expected != agg_pi.children_root {
        return Err(error::Error::InvalidInput(
            "AggAirPublicInputs.children_root is inconsistent with child commitments",
        ));
    }

    // Enforce per-child m and aggregate v_units.
    let mut base_rows: usize = 0;
    let mut v_units_sum: u64 = 0;

    for (i, child) in children.iter().enumerate() {
        let m = agg_pi.children_ms[i];
        if m == 0 {
            return Err(error::Error::InvalidInput(
                "AggAirPublicInputs.children_ms entries must be non-zero",
            ));
        }

        if m != child.meta.m {
            return Err(error::Error::InvalidInput(
                "AggAirPublicInputs.children_ms entry does not match child meta.m",
            ));
        }

        base_rows = base_rows
            .checked_add(m as usize)
            .ok_or(error::Error::InvalidInput(
                "AggTrace length overflow when summing children_ms",
            ))?;

        v_units_sum =
            v_units_sum
                .checked_add(child.meta.v_units)
                .ok_or(error::Error::InvalidInput(
                    "AggAirPublicInputs.v_units_total overflow when summing child meta.v_units",
                ))?;
    }

    if agg_pi.v_units_total != v_units_sum {
        return Err(error::Error::InvalidInput(
            "AggAirPublicInputs.v_units_total must equal sum of child meta.v_units",
        ));
    }

    if base_rows == 0 {
        return Err(error::Error::InvalidInput(
            "AggTrace requires a positive total number of rows",
        ));
    }

    let n_rows = base_rows.next_power_of_two();

    let mut trace = TraceTable::new(cols.width(), n_rows);

    let mut row = 0usize;
    let mut v_acc = BE::from(0u64);

    for (i, child) in children.iter().enumerate() {
        let m = agg_pi.children_ms[i] as usize;
        let v_child_fe = BE::from(child.meta.v_units);

        for r in 0..m {
            let cur_row = row + r;
            let is_first = r == 0;

            // seg_first flag
            trace.set(
                cols.seg_first,
                cur_row,
                if is_first { BE::ONE } else { BE::ZERO },
            );

            // v_units_child: only on the
            // first row of the segment.
            if is_first {
                trace.set(cols.v_units_child, cur_row, v_child_fe);
                trace.set(cols.v_units_acc, cur_row, v_acc);
                trace.set(cols.trace_root_err, cur_row, BE::ZERO);

                v_acc += v_child_fe;
            } else {
                trace.set(cols.v_units_child, cur_row, BE::ZERO);
                trace.set(cols.v_units_acc, cur_row, v_acc);
                trace.set(cols.trace_root_err, cur_row, BE::ZERO);
            }

            // ok and other composition-related columns
            // remain at their default zero values.
        }

        row += m;
    }

    // Padding rows (if any):
    // keep accumulator constant and
    // disable seg_first, v_units_child
    // and trace_root_err.
    for cur_row in row..n_rows {
        trace.set(cols.seg_first, cur_row, BE::ZERO);
        trace.set(cols.v_units_child, cur_row, BE::ZERO);
        trace.set(cols.v_units_acc, cur_row, v_acc);
        trace.set(cols.trace_root_err, cur_row, BE::ZERO);
    }

    Ok(AggTrace::new(trace, cols))
}

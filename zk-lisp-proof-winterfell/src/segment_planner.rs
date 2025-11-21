// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Winterfell-specific execution segment planner.
//!
//! This module defines `WinterfellSegmentPlanner`, a backend-specific
//! implementation which partitions the base execution trace into
//! level-aligned segments. For small programs we keep a single
//! segment covering the full trace; for larger programs we split the
//! trace into multiple segments whose lengths are bounded by an
//! internal policy constant. Segment boundaries are always aligned to
//! full VM "levels" (multiples of `STEPS_PER_LEVEL_P2` rows).

use zk_lisp_proof::error;
use zk_lisp_proof::pi::PublicInputs as CorePublicInputs;
use zk_lisp_proof::segment::{Segment, SegmentPlanner};
use zk_lisp_proof::{ProverOptions, ZkBackend};

use crate::WinterfellBackend;
use crate::layout::STEPS_PER_LEVEL_P2;

/// Maximum number of base-trace rows per execution segment. Programs
/// whose full trace length does not exceed this value are kept as a
const MAX_SEGMENT_ROWS: usize = 1 << 16;

/// Segment planner for the Winterfell backend. For small programs this
/// returns a single segment covering the entire execution trace. For
pub struct WinterfellSegmentPlanner;

impl SegmentPlanner<WinterfellBackend> for WinterfellSegmentPlanner {
    fn plan_segments(
        program: &<WinterfellBackend as ZkBackend>::Program,
        _pub_inputs: &CorePublicInputs,
        _opts: &ProverOptions,
    ) -> error::Result<Vec<Segment>> {
        let levels = program.ops.len();
        let total_levels = levels.next_power_of_two().max(1);
        let steps = STEPS_PER_LEVEL_P2;
        let n_rows = total_levels
            .checked_mul(steps)
            .ok_or(error::Error::InvalidInput(
                "WinterfellSegmentPlanner trace length overflow",
            ))?;

        let max_rows = std::env::var("ZKL_MAX_SEGMENT_ROWS")
            .ok()
            .and_then(|s| s.parse::<usize>().ok())
            .unwrap_or(MAX_SEGMENT_ROWS);

        if n_rows <= max_rows {
            // Single well-formed segment covering the full base trace.
            let seg = Segment::new(0, n_rows)?;

            tracing::debug!(
                target = "planner",
                rows=%n_rows,
                segments=1,
                max_rows=%max_rows,
                "plan_segments single segment",
            );

            return Ok(vec![seg]);
        }

        let max_levels_per_segment = (max_rows / steps).max(1);

        let mut segments = Vec::new();
        let mut lvl_start = 0usize;
        let mut seg_count = 0usize;

        while lvl_start < total_levels {
            let lvl_end = core::cmp::min(total_levels, lvl_start + max_levels_per_segment);
            let r_start = lvl_start
                .checked_mul(steps)
                .ok_or(error::Error::InvalidInput(
                    "WinterfellSegmentPlanner segment start overflow",
                ))?;
            let r_end = lvl_end
                .checked_mul(steps)
                .ok_or(error::Error::InvalidInput(
                    "WinterfellSegmentPlanner segment end overflow",
                ))?;

            segments.push(Segment::new(r_start, r_end)?);
            seg_count += 1;
            lvl_start = lvl_end;
        }

        tracing::debug!(
            target = "planner",
            rows=%n_rows,
            segments=%seg_count,
            max_rows=%max_rows,
            "plan_segments multi segment",
        );

        Ok(segments)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zk_lisp_compiler::CompilerMetrics;
    use zk_lisp_compiler::builder::{self, Op};

    #[test]
    fn single_segment_covers_full_trace() {
        let metrics = CompilerMetrics::default();
        let mut b = builder::ProgramBuilder::new();

        b.push(Op::Const { dst: 0, imm: 1 });
        b.push(Op::Const { dst: 1, imm: 2 });
        b.push(Op::Add { dst: 2, a: 0, b: 1 });
        b.push(Op::End);

        let program = b.finalize(metrics).expect("finalize must succeed");
        let pi = CorePublicInputs::default();
        let opts = ProverOptions::default();

        let segments = WinterfellSegmentPlanner::plan_segments(&program, &pi, &opts)
            .expect("plan_segments must succeed");

        assert_eq!(segments.len(), 1);
        let seg = segments[0];

        let expected_levels = program.ops.len().next_power_of_two();
        let expected_rows = expected_levels * STEPS_PER_LEVEL_P2;

        assert_eq!(seg.r_start, 0);
        assert_eq!(seg.r_end, expected_rows);
        assert_eq!(seg.len(), expected_rows);
    }

    #[test]
    fn large_program_splits_into_multiple_segments() {
        let metrics = CompilerMetrics::default();
        let mut b = builder::ProgramBuilder::new();

        // Build a synthetic program with enough levels to exceed
        // MAX_SEGMENT_ROWS after padding to the next power of two.
        let steps = STEPS_PER_LEVEL_P2;
        let target_levels = (MAX_SEGMENT_ROWS / steps) + 1;

        for _ in 0..target_levels {
            b.push(Op::Const { dst: 0, imm: 1 });
        }

        b.push(Op::End);

        let program = b.finalize(metrics).expect("finalize must succeed");
        let pi = CorePublicInputs::default();
        let opts = ProverOptions::default();

        let segments = WinterfellSegmentPlanner::plan_segments(&program, &pi, &opts)
            .expect("plan_segments must succeed for large program");

        assert!(
            segments.len() > 1,
            "expected multiple segments for large program"
        );

        // Segments must be contiguous, non-overlapping and cover the
        // full [0, n_rows) range implied by the padded level count.
        let total_levels = program.ops.len().next_power_of_two().max(1);
        let expected_rows = total_levels * steps;

        let mut acc_start = 0usize;
        for seg in &segments {
            assert_eq!(seg.r_start, acc_start);
            assert!(seg.r_end > seg.r_start);
            assert_eq!(seg.r_start % steps, 0);
            assert_eq!(seg.r_end % steps, 0);
            acc_start = seg.r_end;
        }

        assert_eq!(acc_start, expected_rows);
    }
}

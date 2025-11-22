// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Winterfell-specific execution segment planner.

use zk_lisp_proof::error;
use zk_lisp_proof::pi::{
    FM_MERKLE, FM_POSEIDON, FM_RAM, FM_SPONGE, FM_VM, FM_VM_EXPECT, FeaturesMap,
    PublicInputs as CorePublicInputs,
};
use zk_lisp_proof::segment::{Segment, SegmentPlanner};
use zk_lisp_proof::{ProverOptions, ZkBackend};

use crate::WinterfellBackend;
use crate::vm::layout::STEPS_PER_LEVEL_P2;

/// Maximum number of base-trace rows per execution segment.
const MAX_SEGMENT_ROWS: usize = 1 << 10;

/// Per-segment feature summary over a contiguous
/// level range of the compiled program.
#[derive(Clone, Copy, Debug, Default)]
pub struct SegmentFeatures {
    /// Any VM activity (ALU, RAM, sponge, Merkle).
    pub vm: bool,
    /// Presence of RAM Load/Store ops.
    pub ram: bool,
    /// Presence of sponge ops (SAbsorbN/SSqueeze).
    pub sponge: bool,
    /// Presence of Merkle ops.
    pub merkle: bool,
}

impl SegmentFeatures {
    pub fn from_ops(ops: &[zk_lisp_compiler::builder::Op]) -> Self {
        use zk_lisp_compiler::builder::Op::*;

        let mut f = SegmentFeatures::default();

        for op in ops {
            match *op {
                // ALU ops imply VM activity.
                Const { .. }
                | Mov { .. }
                | Add { .. }
                | Sub { .. }
                | Mul { .. }
                | Neg { .. }
                | Eq { .. }
                | Select { .. }
                | Assert { .. }
                | AssertBit { .. }
                | AssertRange { .. }
                | AssertRangeLo { .. }
                | AssertRangeHi { .. }
                | DivMod { .. }
                | MulWide { .. }
                | DivMod128 { .. } => {
                    f.vm = true;
                }
                // RAM ops
                Load { .. } | Store { .. } => {
                    f.vm = true;
                    f.ram = true;
                }
                // Cryptographic sponge ops
                SAbsorbN { .. } | SSqueeze { .. } => {
                    f.vm = true;
                    f.sponge = true;
                }
                // Merkle ops
                MerkleStepFirst { .. } | MerkleStep { .. } | MerkleStepLast { .. } => {
                    f.merkle = true;
                }
                End => {}
            }
        }

        f
    }
}

/// Segment planner for the Winterfell backend.
pub struct WinterfellSegmentPlanner;

impl SegmentPlanner<WinterfellBackend> for WinterfellSegmentPlanner {
    fn plan_segments(
        program: &<WinterfellBackend as ZkBackend>::Program,
        _pub_inputs: &CorePublicInputs,
        opts: &ProverOptions,
    ) -> error::Result<Vec<Segment>> {
        let base_levels = program.ops.len();
        let total_levels = base_levels.next_power_of_two().max(1);
        let steps = STEPS_PER_LEVEL_P2;

        let n_rows_full = total_levels
            .checked_mul(steps)
            .ok_or(error::Error::InvalidInput(
                "WinterfellSegmentPlanner trace length overflow",
            ))?;

        let max_rows = opts.max_segment_rows.unwrap_or_else(|| {
            std::env::var("ZKL_MAX_SEGMENT_ROWS")
                .ok()
                .and_then(|s| s.parse::<usize>().ok())
                .unwrap_or(MAX_SEGMENT_ROWS)
        });

        // Small traces fit into a single segment.
        if n_rows_full <= max_rows {
            let seg = Segment::new(0, n_rows_full)?;

            tracing::debug!(
                target = "planner",
                rows = %n_rows_full,
                segments = 1,
                max_rows = %max_rows,
                blocks = %program.blocks.len(),
                "plan_segments single segment",
            );

            return Ok(vec![seg]);
        }

        let max_levels_per_segment = (max_rows / steps).max(1);

        // Build a level-partition [0, total_levels) expressed
        // as a sequence of disjoint ranges.
        let mut ranges: Vec<(usize, usize)> = Vec::new();

        if program.blocks.is_empty() {
            if base_levels > 0 {
                ranges.push((0, base_levels));
            }
        } else {
            // Collect block ranges and sort by level_start
            let mut block_ranges: Vec<(usize, usize)> = Vec::with_capacity(program.blocks.len());
            for b in &program.blocks {
                let start = b.level_start as usize;
                let len = b.level_len as usize;

                if len == 0 {
                    continue;
                }

                let end = start.checked_add(len).ok_or(error::Error::InvalidInput(
                    "WinterfellSegmentPlanner block level overflow",
                ))?;

                if end > base_levels {
                    return Err(error::Error::InvalidInput(
                        "WinterfellSegmentPlanner block out of bounds for program levels",
                    ));
                }

                block_ranges.push((start, end));
            }

            if block_ranges.is_empty() {
                if base_levels > 0 {
                    ranges.push((0, base_levels));
                }
            } else {
                block_ranges.sort_by_key(|(s, _)| *s);

                let mut cursor = 0usize;
                for (bs, be) in block_ranges {
                    // Gap before this block, if any
                    if cursor < bs {
                        ranges.push((cursor, bs));
                    }

                    // Merge with previous range when overlapping
                    // or adjacent; otherwise append a new range.
                    if let Some(last) = ranges.last_mut() {
                        if bs <= last.1 {
                            last.1 = last.1.max(be);
                        } else {
                            ranges.push((bs, be));
                        }
                    } else {
                        ranges.push((bs, be));
                    }

                    cursor = ranges.last().unwrap().1;
                }

                if cursor < base_levels {
                    ranges.push((cursor, base_levels));
                }
            }
        }

        // Append padded tail as a final range when
        // total_levels exceeds the number of code levels.
        if base_levels < total_levels {
            ranges.push((base_levels, total_levels));
        }

        // Walk the level ranges and emit level-aligned segments
        // whose length does not exceed max_levels_per_segment.
        let mut segments_levels: Vec<(usize, usize)> = Vec::new();
        let mut cur_start: Option<usize> = None;
        let mut cur_end: usize = 0;

        for (range_start, range_end) in ranges {
            let mut lvl = range_start;
            while lvl < range_end {
                if cur_start.is_none() {
                    cur_start = Some(lvl);
                    cur_end = lvl;
                }

                let taken_so_far = cur_end - cur_start.unwrap();
                let remaining_seg = max_levels_per_segment - taken_so_far;
                let remaining_range = range_end - lvl;
                let take = remaining_seg.min(remaining_range);

                cur_end += take;
                lvl += take;

                if (cur_end - cur_start.unwrap()) == max_levels_per_segment {
                    segments_levels.push((cur_start.unwrap(), cur_end));
                    cur_start = None;
                    cur_end = 0;
                }
            }
        }

        if let Some(start) = cur_start {
            if start < cur_end {
                segments_levels.push((start, cur_end));
            }
        }

        // Convert level segments into row segments
        let mut segments = Vec::with_capacity(segments_levels.len());
        for (lvl_start, lvl_end) in &segments_levels {
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
        }

        // Segments must cover [0, n_rows_full).
        if let Some(last) = segments.last() {
            if last.r_end != n_rows_full {
                return Err(error::Error::InvalidInput(
                    "WinterfellSegmentPlanner produced segments not covering full trace length",
                ));
            }
        }

        tracing::debug!(
            target = "planner",
            rows = %n_rows_full,
            segments = %segments.len(),
            max_rows = %max_rows,
            blocks = %program.blocks.len(),
            "plan_segments multi segment",
        );

        Ok(segments)
    }
}

/// Compute features for a level range `[lvl_start, lvl_end)`.
/// Out-of-bounds levels are clamped to the program ops len.
pub fn compute_segment_features_for_levels(
    program: &zk_lisp_compiler::Program,
    lvl_start: usize,
    lvl_end: usize,
) -> SegmentFeatures {
    let base_levels = program.ops.len();
    let start = lvl_start.min(base_levels);
    let end = lvl_end.min(base_levels);

    if start >= end {
        SegmentFeatures::default()
    } else {
        SegmentFeatures::from_ops(&program.ops[start..end])
    }
}

/// Derive a per-segment feature mask from the
/// global program features and a local summary
/// over the level range covered by the segment.
pub fn compute_segment_feature_mask(
    core_pi: &CorePublicInputs,
    seg_features: &SegmentFeatures,
) -> u64 {
    let base = FeaturesMap::from_mask(core_pi.feature_mask);
    let mut mask = 0u64;

    // VM is either globally enabled or not; we avoid
    // segment-local gating of the core VM block.
    if base.vm {
        mask |= FM_VM;
    }
    if base.vm_expect {
        mask |= FM_VM_EXPECT;
    }
    if base.ram && seg_features.ram {
        mask |= FM_RAM;
    }
    if base.merkle && seg_features.merkle {
        mask |= FM_MERKLE;
    }
    if base.sponge && seg_features.sponge {
        mask |= FM_SPONGE;
    }

    // Poseidon is required whenever either
    // sponge or Merkle is active.
    if base.poseidon && (seg_features.sponge || seg_features.merkle) {
        mask |= FM_POSEIDON;
    }

    mask
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

    #[test]
    fn segment_feature_mask_is_subset_of_global_mask() {
        let mut core_pi = CorePublicInputs::default();
        core_pi.feature_mask = FM_VM | FM_VM_EXPECT | FM_RAM | FM_MERKLE | FM_SPONGE | FM_POSEIDON;

        let seg_features = SegmentFeatures {
            vm: true,
            ram: false,
            sponge: true,
            merkle: false,
        };

        let seg_mask = compute_segment_feature_mask(&core_pi, &seg_features);
        assert_eq!(seg_mask & !core_pi.feature_mask, 0);

        assert_eq!(seg_mask & FM_RAM, 0);
        assert_eq!(seg_mask & FM_MERKLE, 0);

        assert_ne!(seg_mask & FM_VM, 0);
        assert_ne!(seg_mask & FM_VM_EXPECT, 0);

        assert_ne!(seg_mask & FM_SPONGE, 0);
        assert_ne!(seg_mask & FM_POSEIDON, 0);
    }

    #[test]
    fn segment_feature_mask_drops_optional_features_on_empty_segment() {
        let mut core_pi = CorePublicInputs::default();
        core_pi.feature_mask = FM_VM | FM_VM_EXPECT | FM_RAM | FM_MERKLE | FM_SPONGE | FM_POSEIDON;

        let seg_features = SegmentFeatures::default(); // vm=false, ram=false, sponge=false, merkle=false
        let seg_mask = compute_segment_feature_mask(&core_pi, &seg_features);

        assert_eq!(seg_mask & (FM_RAM | FM_MERKLE | FM_SPONGE | FM_POSEIDON), 0);

        assert_ne!(seg_mask & FM_VM, 0);
        assert_ne!(seg_mask & FM_VM_EXPECT, 0);
    }

    #[test]
    fn segment_feature_mask_keeps_core_vm_flags_only() {
        let mut core_pi = CorePublicInputs::default();
        core_pi.feature_mask = FM_VM | FM_VM_EXPECT;

        let seg_features = SegmentFeatures {
            vm: true,
            ram: true,
            sponge: true,
            merkle: true,
        };

        let seg_mask = compute_segment_feature_mask(&core_pi, &seg_features);
        assert_eq!(seg_mask, core_pi.feature_mask);
    }
}

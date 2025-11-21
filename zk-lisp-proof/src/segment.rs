// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Generic execution segmentation helpers.
//!
//! This module defines a small backend-agnostic
//! abstraction for planning execution segments in terms
//! of base-trace row intervals. Concrete backends are
//! expected to provide their own `SegmentPlanner`
//! implementations which can take backend-specific
//! layout details into account.

use crate::ZkBackend;
use crate::error;

/// Backend-agnostic trait for planning execution
/// segments. Implementors are expected to return a
pub trait SegmentPlanner<B: ZkBackend> {
    /// Select a sequence of execution segments for the
    /// given program, public inputs and prover options.
    fn plan_segments(
        program: &B::Program,
        pub_inputs: &B::PublicInputs,
        opts: &B::ProverOptions,
    ) -> error::Result<Vec<Segment>>;
}

/// A half-open row interval `[r_start, r_end)` in the
/// base execution trace. Segments are expressed in
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Segment {
    /// First row of the segment (inclusive).
    pub r_start: usize,
    /// One past the last row of the segment (exclusive).
    pub r_end: usize,
}

impl Segment {
    /// Construct a validated segment.
    pub fn new(r_start: usize, r_end: usize) -> error::Result<Self> {
        if r_start >= r_end {
            return Err(error::Error::InvalidInput(
                "segment r_start must be < r_end",
            ));
        }

        Ok(Self { r_start, r_end })
    }

    /// Return the number of rows in this segment.
    pub fn len(&self) -> usize {
        self.r_end - self.r_start
    }

    /// Return true if the segment is empty.
    pub fn is_empty(&self) -> bool {
        self.r_start >= self.r_end
    }
}

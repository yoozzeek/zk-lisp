// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Column layout for the IVC aggregator trace.
//!
//! The layout is intentionally minimal: it keeps just enough
//! state to express a simple additive chain from
//! `state_initial` to `state_final` and to fold step
//! digests into an execution root.

#[derive(Clone, Copy, Debug)]
pub struct IvColumns {
    /// Input state before processing
    /// the step digest on this row.
    pub state_in: usize,

    /// Output state after processing
    /// the step digest on this row.
    pub state_out: usize,

    /// Input execution-root accumulator.
    pub root_in: usize,

    /// Output execution-root accumulator.
    pub root_out: usize,

    /// Folded step digest for this row.
    pub digest: usize,

    /// Echo of the base trace length m_i for
    /// the step corresponding to this row.
    pub step_m: usize,

    /// Echo of the work units v_units_i for
    /// the step corresponding to this row.
    pub v_units: usize,

    /// Running accumulator over v_units_i.
    pub v_units_acc: usize,

    width: usize,
}

impl IvColumns {
    #[inline]
    pub const fn baseline() -> Self {
        Self {
            state_in: 0,
            state_out: 1,
            root_in: 2,
            root_out: 3,
            digest: 4,
            step_m: 5,
            v_units: 6,
            v_units_acc: 7,
            width: 8,
        }
    }

    #[inline]
    pub const fn width(&self) -> usize {
        self.width
    }
}

// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Lightweight metrics collected during compilation.
//!
//! [`CompilerMetrics`] tracks register pressure and simple
//! optimization counters so backends and tooling can inspect
//! compilation cost without depending on internal state.

#[derive(Clone, Debug, Default)]
pub struct CompilerMetrics {
    pub cur_live: u16,
    pub peak_live: u16,
    pub reuse_dst: u32,
    pub su_reorders: u32,
    pub balanced_chains: u32,
    pub mov_elided: u32,
}

impl CompilerMetrics {
    pub(super) fn inc_cur_live(&mut self) {
        self.cur_live += 1;
    }

    pub(super) fn dec_cur_live(&mut self) {
        self.cur_live -= 1;
    }

    pub(super) fn set_peak_live(&mut self, value: u16) {
        self.peak_live = value
    }

    pub(super) fn inc_mov_elided(&mut self) {
        self.mov_elided += 1
    }

    pub(super) fn inc_balanced_chains(&mut self) {
        self.balanced_chains += 1;
    }

    pub(super) fn inc_su_reorders(&mut self) {
        self.su_reorders += 1;
    }

    pub(super) fn inc_reuse_dst(&mut self) {
        self.reuse_dst += 1;
    }
}

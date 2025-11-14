// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

#![forbid(unsafe_code)]

mod air;
mod commit;
mod preflight;
mod schedule;
mod trace;
mod utils;

pub mod compiler;
pub mod error;
pub mod layout;
pub mod logging;
pub mod pi;
pub mod poseidon;
pub mod prove;

pub use preflight::{PreflightMode, run as run_preflight};
pub use schedule::{build_periodic_selectors, is_round_pos, pos_final, pos_map};
pub use trace::{TraceBuilderContext, build_trace};
pub use utils::{be_from_le8, vm_output_from_trace};

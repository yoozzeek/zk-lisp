// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Small error type shared by backend-agnostic helpers.
//!
//! Used by builders and helpers in this crate and backend
//! implementations to report user-facing input validation
//! issues without exposing backend internals.

pub type Result<T> = core::result::Result<T, Error>;

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("invalid input: {0}")]
    InvalidInput(&'static str),
}

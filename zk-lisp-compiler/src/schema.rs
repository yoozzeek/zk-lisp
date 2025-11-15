// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Simple type/schema definitions for functions and
//! variables in the zk-lisp DSL.
//!
//! These schemas are currently metadata only; they
//! are not enforced by the compiler yet but are
//! attached to [`Program`] so frontends and future
//! passes can inspect them.

use std::collections::BTreeMap;

/// Scalar types supported by the DSL schemas.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ScalarType {
    U64,
    U128,
    Bytes32,
    Str64,
}

/// Role of a function argument.
///
/// `Const` arguments are intended to be
/// compile-time parameters baked into the
/// program. `Let` arguments are intended
/// to be runtime public inputs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArgRole {
    Const,
    Let,
}

/// Type schema for a function.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnTypeSchema {
    pub name: String,
    pub args: Vec<(ArgRole, ScalarType)>,
    pub ret: ScalarType,
}

/// Type schema for a named
/// variable (e.g. top-level `let`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LetTypeSchema {
    pub name: String,
    pub ty: ScalarType,
}

/// Aggregate container for all
/// schemas attached to a program.
#[derive(Clone, Debug, Default)]
pub struct TypeSchemas {
    pub fns: BTreeMap<String, FnTypeSchema>,
    pub lets: BTreeMap<String, LetTypeSchema>,
}

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
//! These schemas are currently metadata for the
//! lowering pipeline. Function schemas are partially
//! enforced when finalizing [`Program`]: if a
//! `typed-fn` exists, there must be a matching
//! function definition with the same arity.
//! They are also attached to [`Program`] so
//! frontends and future passes can inspect them.

use std::collections::BTreeMap;

/// Scalar types supported by the DSL schemas.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ScalarType {
    U64,
    U128,
    Bytes32,
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

/// Type schema for a named variable.
///
/// `owner` identifies the function this
/// binding belongs to; `None` means
/// global scope.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LetTypeSchema {
    pub owner: Option<String>,
    pub name: String,
    pub ty: ScalarType,
}

/// Aggregate container for all
/// schemas attached to a program.
#[derive(Clone, Debug, Default)]
pub struct TypeSchemas {
    pub fns: BTreeMap<String, FnTypeSchema>,
    /// Map:
    /// owner -> (variable name -> schema)
    /// owner == "" represents global scope.
    pub lets: BTreeMap<String, BTreeMap<String, LetTypeSchema>>,
}

impl TypeSchemas {
    /// Lookup a `typed-let` schema by owner and name.
    ///
    /// `owner == None` queries the global scope.
    pub fn get_let_schema(&self, owner: Option<&str>, name: &str) -> Option<&LetTypeSchema> {
        let owner_key = owner.unwrap_or_default();
        self.lets.get(owner_key).and_then(|m| m.get(name))
    }
}

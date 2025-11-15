// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

use zk_lisp_compiler::{ArgRole, ScalarType, compile_str};

fn compile_with_schemas() -> zk_lisp_compiler::Program {
    let src = r#"
(typed-fn main (u64 (let u128) (const bytes32)) -> u64)
(typed-let total u128)

(def (main x y z)
  (let ((total 42))
    (+ x x)))
"#;

    compile_str(src).expect("compile")
}

#[test]
fn deftype_fn_records_arg_types_and_roles() {
    let p = compile_with_schemas();
    let main_schema = p.type_schemas.fns.get("main").expect("main schema");

    assert_eq!(main_schema.args.len(), 3);

    assert_eq!(main_schema.args[0], (ArgRole::Const, ScalarType::U64),);
    assert_eq!(main_schema.args[1], (ArgRole::Let, ScalarType::U128),);
    assert_eq!(main_schema.args[2], (ArgRole::Const, ScalarType::Bytes32),);
}

#[test]
fn deftype_fn_records_return_type() {
    let p = compile_with_schemas();
    let main_schema = p.type_schemas.fns.get("main").expect("main schema");

    assert_eq!(main_schema.ret, ScalarType::U64);
}

#[test]
fn deftype_let_records_binding_type() {
    let p = compile_with_schemas();
    let total_schema = p
        .type_schemas
        .get_let_schema(None, "total")
        .expect("total schema");

    assert!(matches!(total_schema.ty, ScalarType::U128));
}

#[test]
fn deftype_let_missing_binding_errors() {
    let src = r#"
(typed-let missing u64)

(def (main)
  0)
"#;

    let err = compile_str(src).expect_err("compile must fail");
    let msg = err.to_string();

    assert!(
        msg.contains("typed-let: no let binding found for 'missing'"),
        "msg={msg}",
    );
}

#[test]
fn deftype_let_conflicting_types_error() {
    let src = r#"
(typed-let total u64)

(def (main)
  (typed-let total u128)
  (let ((total 42))
    total))
"#;

    let err = compile_str(src).expect_err("compile must fail");
    let msg = err.to_string();

    assert!(
        msg.contains("typed-let: conflicting type for 'total'"),
        "msg={msg}",
    );
}

#[test]
fn deftype_fn_missing_def_errors() {
    let src = r#"
(typed-fn main (u64) -> u64)
"#;

    let err = compile_str(src).expect_err("compile must fail");
    let msg = err.to_string();

    assert!(
        msg.contains("typed-fn: no function definition found for 'main'"),
        "msg={msg}",
    );
}

#[test]
fn deftype_fn_arity_mismatch_errors() {
    let src = r#"
(typed-fn main (u64) -> u64)

(def (main x y)
  (+ x y))
"#;

    let err = compile_str(src).expect_err("compile must fail");
    let msg = err.to_string();

    assert!(
        msg.contains("typed-fn: function 'main' is defined with 2 args but schema declares 1"),
        "msg={msg}",
    );
}

#[test]
fn typed_let_same_name_different_types_across_functions_ok() {
    let src = r#"
(def (f1)
  (typed-let total u64)
  (let ((total 1))
    total))

(def (f2)
  (typed-let total u128)
  (let ((total 2))
    total))
"#;

    let p = compile_str(src).expect("compile must succeed");

    let total_f1 = p
        .type_schemas
        .get_let_schema(Some("f1"), "total")
        .expect("f1 total schema");
    assert!(matches!(total_f1.ty, ScalarType::U64));

    let total_f2 = p
        .type_schemas
        .get_let_schema(Some("f2"), "total")
        .expect("f2 total schema");
    assert!(matches!(total_f2.ty, ScalarType::U128));
}

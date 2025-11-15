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
(deftype-fn main (u64 (let u128) (const bytes32)) -> u64)
(deftype-let total u128)

(def (main x y z)
  (+ x x))
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
    let total_schema = p.type_schemas.lets.get("total").expect("total schema");

    assert!(matches!(total_schema.ty, ScalarType::U128));
}

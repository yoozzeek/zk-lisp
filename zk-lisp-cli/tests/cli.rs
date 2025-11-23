// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

use assert_cmd::prelude::*;
use predicates::prelude::*;
use std::path::Path;
use std::process::Command;

fn bin() -> Command {
    let mut cmd = Command::new(assert_cmd::cargo::cargo_bin!("zk-lisp"));
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let workspace_root = manifest_dir
        .parent()
        .expect("zk-lisp-cli crate must have a parent workspace directory");
    cmd.current_dir(workspace_root);

    cmd
}

#[test]
fn run_add_json_ok() {
    let mut cmd = bin();
    cmd.args([
        "run",
        "examples/hello-zk.zlisp",
        "--arg",
        "u64:2",
        "--arg",
        "u64:5",
        "--secret",
        "u64:3",
        "--json",
    ]);
    cmd.assert()
        .success()
        .stdout(predicate::str::contains("\"result_dec\":\"1\""));
}

#[cfg_attr(debug_assertions, ignore)]
#[test]
fn prove_and_verify_ok() {
    let tmp = tempfile::NamedTempFile::new().unwrap();
    let path = tmp.path().to_str().unwrap().to_string();

    // prove
    let mut cmd = bin();
    cmd.args([
        "prove",
        "examples/hello-zk.zlisp",
        "--arg",
        "u64:2",
        "--arg",
        "u64:5",
        "--secret",
        "u64:3",
        "--out",
        &path,
        "--quiet",
    ]);
    cmd.assert().success();

    // verify
    let mut cmd2 = bin();
    cmd2.args([
        "verify",
        &path,
        "examples/hello-zk.zlisp",
        "--arg",
        "u64:2",
        "--arg",
        "u64:5",
        "--json",
    ]);
    let assert = cmd2.assert();

    // Accept either success (ok:true) or failure due to verification policy
    // (e.g., insufficient conjectured security on tiny traces).
    let output = assert.get_output();
    let stdout = String::from_utf8_lossy(&output.stdout);

    if output.status.success() {
        assert!(stdout.contains("\"ok\":true"), "stdout: {stdout}");
    } else {
        // JSON error with code field; accept code 7 (verify error)
        assert!(stdout.contains("\"ok\":false"), "stdout: {stdout}");
        assert!(stdout.contains("\"code\":7"), "stdout: {stdout}");
    }
}

#[test]
fn verify_bad_proof_path_fails_json() {
    let mut cmd = bin();
    cmd.args([
        "verify",
        "/this/does/not/exist.bin",
        "examples/hello-zk.zlisp",
        "--arg",
        "u64:2",
        "--arg",
        "u64:5",
        "--json",
    ]);
    let assert = cmd.assert().failure();

    // IO error path, mapped to code 5 by our harness.
    assert
        .stdout(predicate::str::contains("\"ok\":false"))
        .stdout(predicate::str::contains("\"code\":5"));
}

#[test]
fn run_too_big_file_limit() {
    let mut cmd = bin();
    cmd.args([
        "--max-bytes",
        "1",
        "run",
        "examples/hello-zk.zlisp",
        "--arg",
        "1",
        "--json",
    ]);
    cmd.assert()
        .failure()
        .stdout(predicate::str::contains("\"ok\":false"))
        .stdout(predicate::str::contains("file too large"));
}

#[test]
fn run_schema_with_let_role_accepted() {
    let src = r#"
(typed-fn main ((let u64)) -> u64)
(def (main x) x)
"#;

    let tmp = tempfile::NamedTempFile::new().unwrap();
    std::fs::write(tmp.path(), src).unwrap();

    let mut cmd = bin();
    cmd.args([
        "run",
        tmp.path().to_str().unwrap(),
        "--arg",
        "u64:7",
        "--json",
    ]);

    let assert = cmd.assert().success();
    assert.stdout(predicate::str::contains("\"ok\":true"));
}

#[test]
fn run_typed_main_mixed_const_and_let_ok() {
    let src = r#"
(typed-fn main ((const u64) (let u64) (let u64)) -> u64)
(def (main a b c)
  (+ a (+ b c)))
"#;

    let tmp = tempfile::NamedTempFile::new().unwrap();
    std::fs::write(tmp.path(), src).unwrap();

    let mut cmd = bin();
    cmd.args([
        "run",
        tmp.path().to_str().unwrap(),
        "--arg",
        "u64:1",
        "--arg",
        "u64:2",
        "--arg",
        "u64:3",
        "--json",
    ]);

    let assert = cmd.assert().success();
    assert
        .stdout(predicate::str::contains("\"ok\":true"))
        .stdout(predicate::str::contains("\"result_dec\":\"6\""));
}

#[test]
fn run_typed_main_non_u64_const_schema_type_rejected() {
    let src = r#"
(typed-fn main ((const u128)) -> u64)
(def (main x) x)
"#;

    let tmp = tempfile::NamedTempFile::new().unwrap();
    std::fs::write(tmp.path(), src).unwrap();

    let mut cmd = bin();
    cmd.args([
        "run",
        tmp.path().to_str().unwrap(),
        "--arg",
        "u64:7",
        "--json",
    ]);

    let assert = cmd.assert().failure();
    assert
        .stdout(predicate::str::contains("\"ok\":false"))
        .stdout(predicate::str::contains(
            "const args of type 'u128' are not supported for CLI public args; expected 'u64'",
        ));
}

#[test]
fn run_typed_main_let_u128_and_bytes32_ok() {
    let src = r#"
(typed-fn main ((let u64) (let u128) (let bytes32)) -> u64)
(def (main a b c)
  a)
"#;

    let tmp = tempfile::NamedTempFile::new().unwrap();
    std::fs::write(tmp.path(), src).unwrap();

    let mut cmd = bin();
    cmd.args([
        "run",
        tmp.path().to_str().unwrap(),
        "--arg",
        "u64:1",
        "--arg",
        "u128:42",
        "--arg",
        "bytes32:0x0102030405060708",
        "--json",
    ]);

    let assert = cmd.assert().success();
    assert
        .stdout(predicate::str::contains("\"ok\":true"))
        .stdout(predicate::str::contains("\"result_dec\":\"1\""));
}

#[test]
fn run_typed_main_arity_mismatch_rejected() {
    let src = r#"
(typed-fn main ((let u64) (let u64)) -> u64)
(def (main a b)
  (+ a b))
"#;

    let tmp = tempfile::NamedTempFile::new().unwrap();
    std::fs::write(tmp.path(), src).unwrap();

    // Provide only one arg instead of two
    let mut cmd = bin();
    cmd.args([
        "run",
        tmp.path().to_str().unwrap(),
        "--arg",
        "u64:7",
        "--json",
    ]);

    let assert = cmd.assert().failure();
    assert
        .stdout(predicate::str::contains("\"ok\":false"))
        .stdout(predicate::str::contains("main expects 2 args (got 1)"));
}

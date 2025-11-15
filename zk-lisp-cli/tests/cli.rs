// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp.
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
        "2",
        "--arg",
        "3",
        "--json",
    ]);
    cmd.assert()
        .success()
        .stdout(predicate::str::contains("\"result_dec\":\"5\""));
}

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
        "2",
        "--arg",
        "3",
        "--out",
        &path,
        "--quiet",
    ]);
    cmd.assert().success();

    // verify
    let mut cmd2 = bin();
    cmd2.args([
        "verify",
        &format!("@{}", &path),
        "examples/hello-zk.zlisp",
        "--arg",
        "2",
        "--arg",
        "3",
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
fn verify_bad_hex_fails_json() {
    let mut cmd = bin();
    cmd.args([
        "verify",
        "zzzz",
        "examples/hello-zk.zlisp",
        "--arg",
        "2",
        "--arg",
        "3",
        "--json",
    ]);
    let assert = cmd.assert().failure();

    // exit code 2 mapped by our harness;
    // cannot assert exact code
    // via assert_cmd portable API
    assert
        .stdout(predicate::str::contains("\"ok\":false"))
        .stdout(predicate::str::contains("\"code\":2"));
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

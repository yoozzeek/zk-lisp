use assert_cmd::prelude::*;
use predicates::prelude::*;
use std::process::Command;

fn bin() -> Command {
    Command::new(assert_cmd::cargo::cargo_bin!("zk-lisp"))
}

#[test]
fn run_add_json_ok() {
    let mut cmd = bin();
    cmd.args([
        "run",
        "examples/zk_example.zlisp",
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
        "examples/zk_example.zlisp",
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
        "examples/zk_example.zlisp",
        "--arg",
        "2",
        "--arg",
        "3",
        "--json",
    ]);
    cmd2.assert()
        .success()
        .stdout(predicate::str::contains("\"ok\":true"));
}

#[test]
fn verify_bad_hex_fails_json() {
    let mut cmd = bin();
    cmd.args([
        "verify",
        "zzzz",
        "examples/zk_example.zlisp",
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
        "examples/zk_example.zlisp",
        "--arg",
        "1",
        "--json",
    ]);
    cmd.assert()
        .failure()
        .stdout(predicate::str::contains("\"ok\":false"))
        .stdout(predicate::str::contains("file too large"));
}

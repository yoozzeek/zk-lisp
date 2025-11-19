# zk-lisp
# Copyright (c) Andrei Kochergin. All rights reserved.

A small Lisp-like DSL and compiler for proving program
execution in zero-knowledge. Source code is compiled to
a register-based VM whose execution trace is proven using
the Winterfell STARK prover and verified with its verifier.

Experimental and unaudited; not production-ready.

Disclaimer:

  This program comes with ABSOLUTELY NO WARRANTY;
  This is free software, and you are welcome to
  redistribute it under certain conditions;

How it works:

  Parse source > AST > IR > VM ops

  The trace builder executes VM ops into a fixed-shape
  trace. AIR is predefined, you don't write constraints.
  Winterfell proves the trace satisfies AIR.

Example:

  (def (main x y)
    (let ((s (secret-arg 0)))
      (assert (= y (+ x s)))
      1))

Features:

  Backend-agnostic Lisp DSL compiler and virtual machine
  Abstract traits for plugging in multiple STARK backends
  Winterfell-based STARK implementation
  Strict STARK-in-STARK recursion (aggregated proofs)
  zk-lisp CLI with run | prove | verify | repl commands
  Interactive REPL with :prove and :verify built-ins

Roadmap:

  [planned] Website, documentation, and an online playground/REPL
  [planned] Program events and logs
  [planned] Cross-program invocations

Quickstart:

  Run:
    cargo run --bin zk-lisp -- \
      run examples/hello-zk.zlisp \
        --arg u64:2 --arg u64:5 --secret u64:3

  Prove:
    cargo run --bin zk-lisp -- \
      prove examples/hello-zk.zlisp \
        --out ./proof.bin \
        --arg u64:2 --arg u64:5 --secret u64:3

  Verify:
    cargo run --bin zk-lisp -- \
      verify ./proof.bin examples/hello-zk.zlisp \
        --arg u64:2 --arg u64:5

    If you pass another args verification will fail.

Testing:

  cargo run tests --release

License:

  This project is licensed under the GNU Affero
  General Public License v3.0 or any later version.

  See LICENSE for details.
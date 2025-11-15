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

Quickstart:

  Run:
    cargo run --bin zk-lisp -- \
      run examples/hello-zk.zlisp --arg 2 --arg 3

  Prove:
    cargo run --bin zk-lisp -- \
      prove examples/hello-zk.zlisp \
        --out ./proof.bin --quiet --arg 2 --arg 3

  Verify:
    cargo run --bin zk-lisp -- \
      verify @./proof.bin examples/hello-zk.zlisp \
        --arg 2 --arg 3

Testing:

  cargo run tests --release

License:

  This project is licensed under the GNU Affero
  General Public License v3.0 or any later version.

  See LICENSE for details.
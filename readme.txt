# zk-lisp

A Lisp-like dialect and compiler for writing zero-knowledge (ZK)
programs, executable on an experimental virtual machine built on
top of the Winterfell STARK prover and verifier.

Disclaimer:
  This is a pure experiment. It 100% contains bugs and security
  flaws. zk-lisp is not intended for production use, it doesn't
  even have RAM support yet.

How it works:

  Any program written in zk-lisp is compiled into:
    - IR (Intermediate Representation)
    - A stack of OP codes

This gives a higher-level abstraction over manually building
execution traces and AIR constraints, allowing developers to
focus on product logic and business use cases
instead of low-level STARK math.

Quickstart:

  Run a program:
    cargo run --bin zk-lisp -- run examples/zk_example.zlisp -- 2 3

  Prove and verify:
    cargo run --bin zk-lisp -- \
        prove examples/zk_example.zlisp --out ./proof.bin --quiet --arg 2 --arg 3

    cargo run --bin zk-lisp -- \
        verify @./proof.bin examples/zk_example.zlisp --arg 2 --arg 3

License:

  This project is licensed under the Apache 2.0 License. See LICENSE for details.

Zeek <zeek@tuta.com>
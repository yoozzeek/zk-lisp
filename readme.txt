# zk-lisp
# Copyright (c) Andrei Kochergin. All rights reserved.

A Lisp dialect and compiler for running zero-knowledge (ZK)
programs, executable on an experimental virtual machine built
on top of the Winterfell STARK prover and verifier.

Disclaimer:

  This program comes with ABSOLUTELY NO WARRANTY;
  This is free software, and you are welcome to
  redistribute it under certain conditions;

How it works:

  Any program written in zk-lisp is compiled into:
    - IR (Intermediate Representation)
    - A stack of OP codes

This gives a higher-level abstraction over manually building
execution traces and AIR constraints, allowing developers to
focus on product logic and business use cases
instead of low-level STARK math.

Program example:

  (def (main x y)
    (+ x y))

Quickstart:

  Run a program:
    cargo run --bin zk-lisp -- run examples/zk_example.zlisp --arg 2 --arg 3

  Prove and verify:
    cargo run --bin zk-lisp -- \
        prove examples/zk_example.zlisp --out ./proof.bin --quiet --arg 2 --arg 3

    cargo run --bin zk-lisp -- \
        verify @./proof.bin examples/zk_example.zlisp --arg 2 --arg 3

License:

  This project is licensed under the GPL v3 License. See LICENSE for details.
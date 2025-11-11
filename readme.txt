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

  Parse source /
              / -> lower to IR /
                              / -> emit sequence of VM ops.

  A trace builder executes these ops into a fixed-shape
  trace (VM/Poseidon/KV/Merkle blocks). AIR is predefined;
  you don't write constraints. Winterfell proves the
  trace satisfies the AIR.

  The VM includes arithmetic, Poseidon sponge, range/bit
  checks, and KV/Merkle gadgets.

  This gives a higher‑level programming model over manual
  trace/AIR authoring so you can focus on application logic,
  while the system handles STARK proving details.

  Program example:

    (def (main x y)
      (+ x y))

Quickstart:

  Check the examples:
    cargo run --example generate_root \
        -- verify 1 0:22,1:23
    cargo run --example merkle_verify \
        -- 1 0:22,1:23 0x7383de959c89890b122b26ea99cbf333

  Run a program from source file:
    cargo run --bin zk-lisp -- \
        run examples/zk_example.zlisp --arg 2 --arg 3

  Prove and verify:
    cargo run --bin zk-lisp -- \
        prove examples/zk_example.zlisp \
            --out ./proof.bin --quiet --arg 2 --arg 3

    cargo run --bin zk-lisp -- \
        verify @./proof.bin examples/zk_example.zlisp \
            --arg 2 --arg 3

Testing:

    cargo run tests --release

License:

  This project is licensed under the GPL v3 License.
  See LICENSE for details.
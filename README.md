# ZK Lisp

<img src="./zk-lisp-logo.jpg" alt="ZK Lisp logo" width="160"/>

*Copyright (c) Andrei Kochergin. All rights reserved.*

A small Lisp-like DSL and compiler for proving program
execution in zero-knowledge. Source code is compiled to
a register-based VM whose execution trace is proven using
the Winterfell STARK prover and verified with its verifier.

> [!WARNING]
> Experimental and unaudited; not production-ready.

> [!IMPORTANT]
> This program comes with ABSOLUTELY NO WARRANTY;
> This is free software, and you are welcome to
> redistribute it under certain conditions;

## How it works

Parse source > AST > IR > VM ops

The trace builder executes VM ops into a fixed-shape
trace. AIR is predefined, you don't write constraints.
Winterfell proves the trace satisfies AIR.

## Features

* Backend-agnostic Lisp DSL compiler and virtual machine
* Abstract traits for plugging in multiple STARK backends
* Winterfell-based STARK implementation
* Strict STARK-in-STARK recursion (aggregated proofs)
* Dynamic segment layout and feature mask
* zk-lisp CLI with run | prove | verify | repl commands
* Interactive REPL with :prove and :verify built-ins

## Roadmap

* Property and fuzz test coverage
* Complex types such as vectors and structs
* Examples, templates and better code-docs
* Website, documentation and online REPL
* Incrementally verifiable computation (IVC)
* Program events and logs
* Cross-program invocations

## Quickstart

Run:

```bash
cargo run --bin zk-lisp -- \
  run examples/hello-zk.zlisp \
    --arg u64:2 --arg u64:5 --secret u64:3
```

Prove:

```bash
cargo run --bin zk-lisp --release -- \
  prove examples/hello-zk.zlisp \
    --out ./proof.bin \
    --arg u64:2 --arg u64:5 --secret u64:3
```

Verify:

```bash
cargo run --bin zk-lisp --release -- \
  verify ./proof.bin examples/hello-zk.zlisp \
    --arg u64:2 --arg u64:5
```

*If you pass another args verification will fail.*

### Examples

#### Hello zkSTRAKs

```lisp
(def (main pub_x pub_y)
  (let ((s (secret-arg 0)))
    (assert (= pub_y (+ pub_x s)))
    1))
```

#### Simple state transition function (STF)

```lisp
(def N_ACCOUNTS       3)
(def N_TXS            10)
(def HASH_BALANCES_IV 12345)

(def (tx_base)
  N_ACCOUNTS)

(def (tx_from i)
  (load (+ (tx_base) (* i 4))))

(def (tx_to i)
  (load (+ (tx_base) (+ 1 (* i 4)))))

(def (tx_amount i)
  (load (+ (tx_base) (+ 2 (* i 4)))))

(def (tx_fee i)
  (load (+ (tx_base) (+ 3 (* i 4)))))

(def (apply_tx i)
  (let ((from (tx_from i))
        (to   (tx_to i)))
    (begin
      (store from
        (safe-sub (load from)
                  (safe-add (tx_amount i) (tx_fee i))))
      (store to
        (safe-add (load to) (tx_amount i)))
      (tx_fee i))))

(def (apply_batch)
  (loop :max N_TXS ((i 0) (fee_sum 0))
    fee_sum
    (recur (+ i 1) (safe-add fee_sum (apply_tx i)))))

(def (hash_balances)
  (loop :max N_ACCOUNTS ((i 0) (h HASH_BALANCES_IV))
    h
    (recur (+ i 1) (hash2 h (load i)))))

(def (main expected_fee_sum expected_root)
  (let ((fee_sum (apply_batch))
        (root    (hash_balances)))
    (begin
      (assert (= fee_sum expected_fee_sum))
      (assert (= root expected_root))
      root)))
```

## Testing

```bash
cargo run tests --release
```

## License

This project is licensed under the GNU Affero
General Public License v3.0 or any later version.

See LICENSE for details.
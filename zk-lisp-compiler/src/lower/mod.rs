// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Lexer, parser and lowering pipeline for zk-lisp.
//!
//! This module turns source text into s-expressions, resolves
//! bindings and functions, and lowers them into VM ops using
//! a small register allocator and compiler metrics tracking.

pub mod ctx;

mod alu;
mod assert;
mod bits;
mod hash;
mod hex;
mod iter;
mod merkle;
mod operators;
mod ram;
mod store;

use crate::builder::{Op, ProgramBuilder};
use crate::{ArgRole, Error, FnTypeSchema, LetTypeSchema, ScalarType};

use ctx::LowerCtx;
// Number of VM registers used by the compiler
const NR: usize = 8;

// stack memory base address
const STACK_BASE: u64 = 1_000_000;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ast {
    Atom(Atom),
    List(Vec<Ast>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Atom {
    Int(u64),
    Sym(String),
    Str(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Tok {
    LParen,
    RParen,
    Quote,
    Int(u64),
    Sym(String),
    Str(String),
    Eof,
}

enum BinOp {
    Add,
    Sub,
    Mul,
}

/// Return value ownership model
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum RVal {
    Owned(u8),
    Borrowed(u8),
    Imm(u64),
}

// register or immediate
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Binding {
    Reg(u8),
    Imm(u64),
}

struct LoopVarState {
    name: String,
    prior: Option<Binding>,
    reg: u8,
}

impl RVal {
    pub fn as_imm(self) -> Option<u64> {
        match self {
            RVal::Imm(v) => Some(v),
            _ => None,
        }
    }

    pub fn into_owned(self, cx: &mut LowerCtx) -> Result<RVal, Error> {
        match self {
            RVal::Owned(r) => Ok(RVal::Owned(r)),
            RVal::Borrowed(s) => {
                let dst = cx.alloc()?;
                cx.emit_mov(dst, s);

                Ok(RVal::Owned(dst))
            }
            RVal::Imm(v) => {
                let dst = cx.alloc()?;
                cx.builder.push(Op::Const { dst, imm: v });

                Ok(RVal::Owned(dst))
            }
        }
    }
}

pub fn lower_top(cx: &mut LowerCtx, ast: Ast) -> Result<(), Error> {
    match ast {
        Ast::List(ref items) if !items.is_empty() => {
            match &items[0] {
                Ast::Atom(Atom::Sym(s)) if s == "def" => lower_def(cx, &items[1..]),
                Ast::Atom(Atom::Sym(s)) if s == "deftype" => lower_deftype(cx, &items[1..]),
                Ast::Atom(Atom::Sym(s)) if s == "typed-fn" => lower_typed_fn(cx, &items[1..]),
                Ast::Atom(Atom::Sym(s)) if s == "typed-let" => lower_typed_let(cx, &items[1..]),
                _ => {
                    // treat as expression; compute and discard
                    let v = lower_expr(cx, ast)?;
                    free_if_owned(cx, v);

                    Ok(())
                }
            }
        }
        _ => {
            // expression or atom; compute and drop
            let v = lower_expr(cx, ast)?;
            free_if_owned(cx, v);

            Ok(())
        }
    }
}

pub fn lower_expr(cx: &mut LowerCtx, ast: Ast) -> Result<RVal, Error> {
    match ast {
        Ast::Atom(Atom::Int(v)) => {
            // Keep literal as immediate,
            // materialize only on demand.
            Ok(RVal::Imm(v))
        }
        Ast::Atom(Atom::Str(_)) => {
            // String literal must be used
            // under a dedicated macro.
            Err(Error::InvalidForm("string literal outside macro".into()))
        }
        Ast::Atom(Atom::Sym(s)) => {
            // Variable may be bound to
            // a register or an immediate.
            match cx.get_binding(&s)? {
                Binding::Reg(r) => Ok(RVal::Borrowed(r)),
                Binding::Imm(v) => Ok(RVal::Imm(v)),
            }
        }
        Ast::List(items) if !items.is_empty() => match items.as_slice() {
            [Ast::Atom(Atom::Sym(s)), rest @ ..] => {
                let tail = rest;
                match s.as_str() {
                    "+" => {
                        if tail.len() != 2 {
                            let balanced = balance_chain("+", tail);
                            cx.metrics.inc_balanced_chains();

                            return lower_expr(cx, balanced);
                        }

                        lower_bin(cx, tail, BinOp::Add)
                    }
                    "-" => lower_bin(cx, tail, BinOp::Sub),
                    "*" => {
                        if tail.len() != 2 {
                            let balanced = balance_chain("*", tail);
                            cx.metrics.inc_balanced_chains();

                            return lower_expr(cx, balanced);
                        }

                        lower_bin(cx, tail, BinOp::Mul)
                    }
                    "=" => operators::lower_eq(cx, tail),
                    "if" => operators::lower_if(cx, tail),
                    "when" => operators::lower_when(cx, tail),
                    "let" => lower_let(cx, tail),
                    "neg" => operators::lower_neg(cx, tail),
                    "hash2" => hash::lower_hash2(cx, tail),
                    "merkle-verify" => merkle::lower_merkle_verify(cx, tail),
                    "load-ca" => merkle::lower_load_ca(cx, tail),
                    "store-ca" => merkle::lower_store_ca(cx, tail),
                    "select" => operators::lower_select(cx, tail),
                    "assert" => assert::lower_assert(cx, tail),
                    "bit?" => bits::lower_bit_pred(cx, tail),
                    "assert-bit" => assert::lower_assert_bit(cx, tail),
                    "assert-range" => assert::lower_assert_range(cx, tail),
                    "safe-add" => alu::lower_safe_add(cx, tail),
                    "safe-sub" => alu::lower_safe_sub(cx, tail),
                    "safe-mul" => alu::lower_safe_mul(cx, tail),
                    "divmod-q" => alu::lower_divmod_q(cx, tail),
                    "divmod-r" => alu::lower_divmod_r(cx, tail),
                    "mulwide-hi" => alu::lower_mulwide_hi(cx, tail),
                    "mulwide-lo" => alu::lower_mulwide_lo(cx, tail),
                    "muldiv" => alu::lower_muldiv_floor(cx, tail),
                    "in-set" => operators::lower_in_set(cx, tail),
                    "load" => store::lower_load(cx, tail),
                    "store" => store::lower_store(cx, tail).map(|_| RVal::Imm(0)),
                    "push" => ram::lower_push(cx, tail),
                    "pop" => ram::lower_pop(cx, tail),
                    "push*" => ram::lower_push_star(cx, tail),
                    "pop*" => ram::lower_pop_star(cx, tail),
                    "hex-to-bytes32" => hex::lower_hex_to_bytes32(cx, tail),
                    "secret-arg" => lower_secret_arg(cx, tail),
                    "typed-let" => {
                        // typed-let inside expressions is a schema-only
                        // form; it is collected during the AST pass in
                        // lower_def. At runtime it behaves as a no-op.
                        Ok(RVal::Imm(0))
                    }
                    "begin" => lower_begin(cx, tail),
                    "block" => lower_block(cx, tail),
                    "loop" => iter::lower_loop(cx, tail),
                    "recur" => Err(Error::InvalidForm("recur outside loop".into())),
                    _ => lower_call(cx, s, tail),
                }
            }
            _ => Err(Error::InvalidForm("expr".into())),
        },
        Ast::List(_) => Err(Error::InvalidForm("expr".into())),
    }
}

fn lower_def(cx: &mut LowerCtx, rest: &[Ast]) -> Result<(), Error> {
    // forms:
    // (def (f x y) body...)
    // or (def name body...)
    if rest.is_empty() {
        return Err(Error::InvalidForm("def".into()));
    }

    let (name, params, body) = match &rest[0] {
        Ast::List(h) if !h.is_empty() => {
            let fname = match &h[0] {
                Ast::Atom(Atom::Sym(s)) => s.clone(),
                _ => return Err(Error::InvalidForm("def: name".into())),
            };

            let mut ps = Vec::new();
            for p in &h[1..] {
                match p {
                    Ast::Atom(Atom::Sym(s)) => ps.push(s.clone()),
                    _ => return Err(Error::InvalidForm("def: param".into())),
                }
            }

            if rest.len() < 2 {
                return Err(Error::InvalidForm("def: body".into()));
            }

            let body = implicit_begin(&rest[1..]);

            collect_let_names(&body, cx.builder);
            collect_typed_lets(&fname, &body, cx.builder)?;

            (fname, ps, body)
        }
        Ast::Atom(Atom::Sym(s)) => {
            if rest.len() < 2 {
                return Err(Error::InvalidForm("def: body".into()));
            }

            let body = implicit_begin(&rest[1..]);

            collect_let_names(&body, cx.builder);
            collect_typed_lets(s, &body, cx.builder)?;

            // Treat `(def NAME INT)` as a compile-time
            // integer constant and also make it available
            // as a global immutable binding.
            if let Ast::Atom(Atom::Int(v)) = &body {
                cx.const_ints.insert(s.clone(), *v);
                cx.map_var(s, Binding::Imm(*v));
            }

            (s.clone(), Vec::new(), body)
        }
        _ => return Err(Error::InvalidForm("def".into())),
    };

    cx.define_fun(&name, params, body);

    Ok(())
}

fn lower_let(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    // (let ((x expr) (y expr)) body...)
    if rest.is_empty() {
        return Err(Error::InvalidForm("let".into()));
    }

    let binds = match &rest[0] {
        Ast::List(pairs) => pairs,
        _ => return Err(Error::InvalidForm("let: binds".into())),
    };

    let mut saved: Vec<(String, Option<Binding>, Option<u8>, bool)> = Vec::new();

    for b in binds {
        match b {
            Ast::List(kv) if kv.len() == 2 => {
                let name = match &kv[0] {
                    Ast::Atom(Atom::Sym(s)) => s.clone(),
                    _ => return Err(Error::InvalidForm("let: name".into())),
                };

                // Record that this name has a concrete
                // `let` binding in the lowered program.
                cx.builder.add_let_name(name.clone());

                let v = lower_expr(cx, kv[1].clone())?;

                // Determine binding without
                // unnecessary materialization.
                match v {
                    RVal::Imm(k) => {
                        let prior = cx.env.vars.get(&name).cloned();
                        saved.push((name.clone(), prior, None, false));
                        cx.map_var(&name, Binding::Imm(k));
                    }
                    RVal::Borrowed(r) => {
                        let prior = cx.env.vars.get(&name).cloned();
                        saved.push((name.clone(), prior, Some(r), false));
                        cx.map_var(&name, Binding::Reg(r));
                    }
                    RVal::Owned(r) => {
                        let prior = cx.env.vars.get(&name).cloned();
                        saved.push((name.clone(), prior, Some(r), true));
                        cx.map_var(&name, Binding::Reg(r));
                    }
                }
            }
            _ => return Err(Error::InvalidForm("let: pair".into())),
        }
    }

    // body = one or more exprs;
    // implicit begin
    if rest.len() < 2 {
        return Err(Error::InvalidForm("let: body".into()));
    }

    let body_ast = implicit_begin(&rest[1..]);

    let res_v = lower_expr(cx, body_ast)?;
    let res_reg_opt: Option<u8> = match res_v {
        RVal::Owned(r) | RVal::Borrowed(r) => Some(r),
        RVal::Imm(_) => None,
    };

    // cleanup: free all let-bound regs
    // except result (if referenced by name).
    for (name, prior, reg_opt, owned) in saved.into_iter().rev() {
        let _ = cx.env.vars.remove(&name);
        if let Some(p) = prior {
            cx.env.vars.insert(name, p);
        } else if owned {
            if let Some(r) = reg_opt {
                if res_reg_opt != Some(r) {
                    cx.free_reg(r);
                }
            }
        }
    }

    Ok(res_v)
}

fn lower_bin(cx: &mut LowerCtx, rest: &[Ast], op: BinOp) -> Result<RVal, Error> {
    if rest.len() != 2 {
        return Err(Error::InvalidForm("bin".into()));
    }

    // Compute SU numbers to decide evaluation order
    let su_l = su_number(&rest[0]);
    let su_r = su_number(&rest[1]);
    let size_l = ast_size(&rest[0]);
    let size_r = ast_size(&rest[1]);

    // preserve left-to-right
    let both_pure = is_pure_arith(&rest[0]) && is_pure_arith(&rest[1]);

    // heavier-first policy
    let eval_left_first = if !both_pure {
        true
    } else if su_l != su_r {
        su_l > su_r
    } else {
        // tie-break on subtree size
        size_l >= size_r
    };

    if both_pure && !eval_left_first {
        cx.metrics.inc_su_reorders();
    }

    // Evaluate in chosen order
    // but preserve operand roles
    let (aval, bval) = if eval_left_first {
        (
            lower_expr(cx, rest[0].clone())?,
            lower_expr(cx, rest[1].clone())?,
        )
    } else {
        (
            lower_expr(cx, rest[1].clone())?,
            lower_expr(cx, rest[0].clone())?,
        )
    };

    // Constant folding for Imm+Imm
    // when representable as u64
    if let (Some(ai), Some(bi)) = (
        if eval_left_first {
            aval.as_imm()
        } else {
            bval.as_imm()
        },
        if eval_left_first {
            bval.as_imm()
        } else {
            aval.as_imm()
        },
    ) {
        let res = match op {
            BinOp::Add => {
                let sum = ai as u128 + bi as u128;
                if sum <= u64::MAX as u128 {
                    Some(sum as u64)
                } else {
                    None
                }
            }
            BinOp::Sub => {
                if ai >= bi {
                    Some(ai - bi)
                } else {
                    None
                }
            }
            BinOp::Mul => {
                let prod = (ai as u128) * (bi as u128);
                if prod <= u64::MAX as u128 {
                    Some(prod as u64)
                } else {
                    None
                }
            }
        };

        if let Some(v) = res {
            return Ok(RVal::Imm(v));
        }
    }

    // Materialize as needed
    let aval = aval.into_owned(cx)?;
    let bval = bval.into_owned(cx)?;

    // Remap to (a,b) respecting original semantics
    let (a_val, b_val) = if eval_left_first {
        (aval, bval)
    } else {
        // we evaluated right first => (a,b) are (bval, aval) in order
        (bval, aval)
    };

    // Choose destination register
    // For commutative ops prefer
    // reusing an Owned operand's register
    let (dst, reused): (u8, bool) = match op {
        BinOp::Add | BinOp::Mul => match a_val {
            RVal::Owned(r) => (r, true),
            _ => match b_val {
                RVal::Owned(r) => (r, true),
                _ => (cx.alloc()?, false),
            },
        },
        BinOp::Sub => match a_val {
            RVal::Owned(r) => (r, true),
            _ => (cx.alloc()?, false),
        },
    };

    // Resolve registers
    // for semantic (a,b)
    let a_r = cx.val_reg(&a_val)?;
    let b_r = cx.val_reg(&b_val)?;

    // Emit op using semantic (a,b)
    match op {
        BinOp::Add => cx.builder.push(Op::Add {
            dst,
            a: a_r,
            b: b_r,
        }),
        BinOp::Sub => cx.builder.push(Op::Sub {
            dst,
            a: a_r,
            b: b_r,
        }),
        BinOp::Mul => cx.builder.push(Op::Mul {
            dst,
            a: a_r,
            b: b_r,
        }),
    }

    // Free temps
    if reused {
        cx.metrics.inc_reuse_dst();

        // If dst == a, free b;
        // else free a (only when Owned)
        if dst == a_r {
            free_if_owned(cx, b_val);
        } else {
            free_if_owned(cx, a_val);
        }
    } else {
        // Both were temps; free both
        free_if_owned(cx, a_val);
        free_if_owned(cx, b_val);
    }

    Ok(RVal::Owned(dst))
}

fn lower_call(cx: &mut LowerCtx, name: &str, args: &[Ast]) -> Result<RVal, Error> {
    cx.with_ctx("call", |cx| {
        let (params, body) = cx
            .get_fun(name)
            .cloned()
            .ok_or_else(|| Error::UnknownSymbol(name.to_string()))?;

        // Recursion/DAG guard detects re-entry
        if cx.call_stack.iter().any(|s| s == name) {
            return Err(Error::Recursion(name.to_string()));
        }

        cx.call_stack.push(name.to_string());

        if params.len() != args.len() {
            return Err(Error::InvalidForm(format!(
                "call: {} expects {} args",
                name,
                params.len()
            )));
        }

        // evaluate args
        let mut argv: Vec<RVal> = Vec::with_capacity(args.len());
        for a in args {
            argv.push(lower_expr(cx, a.clone())?);
        }

        // Create new bindings for params
        // Track ownership of argument registers
        let mut saved: Vec<(String, Option<Binding>, Option<u8>, bool)> = Vec::new();

        for (p, v) in params.iter().cloned().zip(argv.into_iter()) {
            match v {
                RVal::Imm(k) => {
                    let prev = cx.env.vars.get(&p).cloned();
                    saved.push((p.clone(), prev, None, false));
                    cx.map_var(&p, Binding::Imm(k));
                }
                RVal::Borrowed(r) => {
                    let prev = cx.env.vars.get(&p).cloned();
                    saved.push((p.clone(), prev, Some(r), false));
                    cx.map_var(&p, Binding::Reg(r));
                }
                RVal::Owned(r) => {
                    let prev = cx.env.vars.get(&p).cloned();
                    saved.push((p.clone(), prev, Some(r), true));
                    cx.map_var(&p, Binding::Reg(r));
                }
            }
        }

        let res_v = lower_expr(cx, body.clone())?;
        let res_reg_opt: Option<u8> = match res_v {
            RVal::Owned(r) | RVal::Borrowed(r) => Some(r),
            RVal::Imm(_) => None,
        };

        // cleanup param bindings: do not free res reg;
        // free only Owned args without prior mapping
        for (p, prior, reg_opt, owned) in saved.into_iter().rev() {
            let _ = cx.env.vars.remove(&p);

            if let Some(pr) = prior {
                cx.env.vars.insert(p, pr);
            } else if owned {
                if let Some(reg) = reg_opt {
                    if res_reg_opt != Some(reg) {
                        cx.free_reg(reg);
                    }
                }
            }
        }

        cx.call_stack.pop();

        Ok(res_v)
    })
}

fn lower_deftype(cx: &mut LowerCtx, rest: &[Ast]) -> Result<(), Error> {
    // Supported forms:
    // (deftype T () '(member a b c))
    // (deftype T '(member a b c))
    if rest.is_empty() {
        return Err(Error::InvalidForm("deftype".into()));
    }

    let tname = match &rest[0] {
        Ast::Atom(Atom::Sym(s)) => s.clone(),
        _ => return Err(Error::InvalidForm("deftype: name".into())),
    };

    let mut member_form: Option<&Ast> = None;
    if let Some(f1) = rest.get(1) {
        member_form = extract_member_from_quote(f1);
    }

    if member_form.is_none() {
        if let Some(f2) = rest.get(2) {
            member_form = extract_member_from_quote(f2);
        }
    }

    let member_form =
        member_form.ok_or_else(|| Error::InvalidForm("deftype: member must be quoted".into()))?;

    let variants: Vec<String> = if let Ast::List(items) = member_form {
        if items.is_empty() {
            return Err(Error::InvalidForm("deftype: member empty".into()));
        }

        // items[0] == "member"
        let mut vs = Vec::new();

        for it in &items[1..] {
            match it {
                Ast::Atom(Atom::Sym(s)) => vs.push(s.clone()),
                _ => return Err(Error::InvalidForm("deftype: member item".into())),
            }
        }

        vs
    } else {
        return Err(Error::InvalidForm("deftype: member form".into()));
    };

    // Define constant functions for
    // each variant: (def variant 0), etc.
    for (i, v) in variants.iter().enumerate() {
        let cname = format!("{tname}:{v}");
        cx.define_fun(&cname, Vec::new(), Ast::Atom(Atom::Int(i as u64)));
    }

    // Define predicate function
    // via product-of-differences:
    // is = (= (* (- x a0) (- x a1) ...) 0)
    let pred_name = format!("{tname}:is");
    let x_sym = Ast::Atom(Atom::Sym("x".to_string()));

    // build terms: (- x ai)
    let mut terms: Vec<Ast> = Vec::with_capacity(variants.len());
    for (i, _) in variants.iter().enumerate() {
        let ai = Ast::Atom(Atom::Int(i as u64));
        let term = Ast::List(vec![
            Ast::Atom(Atom::Sym("-".to_string())),
            x_sym.clone(),
            ai,
        ]);

        terms.push(term);
    }

    // fold product: (* t1 (* t2 (* t3 ...)))
    let prod = if terms.is_empty() {
        Ast::Atom(Atom::Int(0)) // empty set ⇒ always false
    } else {
        let mut it = terms.into_iter();
        let mut acc = it.next().unwrap();

        for t in it {
            acc = Ast::List(vec![Ast::Atom(Atom::Sym("*".to_string())), acc, t]);
        }

        acc
    };

    let is_pred = Ast::List(vec![
        Ast::Atom(Atom::Sym("=".to_string())),
        prod.clone(),
        Ast::Atom(Atom::Int(0)),
    ]);

    cx.define_fun(&pred_name, vec!["x".to_string()], is_pred.clone());

    // Define assert helper:
    // (def (T:assert x) (assert (= prod 0)))
    let assert_name = format!("{tname}:assert");
    let assert_body = Ast::List(vec![Ast::Atom(Atom::Sym("assert".to_string())), is_pred]);

    cx.define_fun(&assert_name, vec!["x".to_string()], assert_body);

    Ok(())
}

fn lower_begin(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    // variadic:
    // (begin a b c ...) => evaluate in order,
    // return last
    if rest.is_empty() {
        return Err(Error::InvalidForm("begin".into()));
    }

    for it in &rest[..rest.len() - 1] {
        let v = lower_expr(cx, it.clone())?;
        free_if_owned(cx, v);
    }

    lower_expr(cx, rest.last().unwrap().clone())
}

fn lower_secret_arg(_cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    // (secret-arg idx) reads a secret VM argument
    // previously seeded into register idx.
    if rest.len() != 1 {
        return Err(Error::InvalidForm("secret-arg".into()));
    }

    let idx_ast = &rest[0];
    let idx_u64 = match idx_ast {
        Ast::Atom(Atom::Int(v)) => *v,
        _ => {
            return Err(Error::InvalidForm(
                "secret-arg: index must be integer literal".into(),
            ));
        }
    };

    let idx_u8 = u8::try_from(idx_u64).map_err(|_| {
        Error::InvalidForm("secret-arg: index out of range for register file".into())
    })?;

    if (idx_u8 as usize) >= NR {
        return Err(Error::InvalidForm(
            "secret-arg: index out of range for register file".into(),
        ));
    }

    Ok(RVal::Borrowed(idx_u8))
}

fn lower_typed_fn(cx: &mut LowerCtx, rest: &[Ast]) -> Result<(), Error> {
    // (typed-fn name (arg-type ...) -> ret-type)
    if rest.len() != 4 {
        return Err(Error::InvalidForm("typed-fn".into()));
    }

    let name = match &rest[0] {
        Ast::Atom(Atom::Sym(s)) => s.clone(),
        _ => return Err(Error::InvalidForm("typed-fn: name".into())),
    };

    let args_list = match &rest[1] {
        Ast::List(items) => items,
        _ => return Err(Error::InvalidForm("typed-fn: args".into())),
    };

    let mut args: Vec<(ArgRole, ScalarType)> = Vec::with_capacity(args_list.len());
    for a in args_list {
        args.push(parse_arg_spec(a)?);
    }

    match &rest[2] {
        Ast::Atom(Atom::Sym(s)) if s == "->" => {}
        _ => return Err(Error::InvalidForm("typed-fn: expected '->'".into())),
    }

    let ret_ty_sym = match &rest[3] {
        Ast::Atom(Atom::Sym(s)) => s.as_str(),
        _ => return Err(Error::InvalidForm("typed-fn: return type".into())),
    };
    let ret_ty = parse_scalar_type(ret_ty_sym)?;

    let schema = FnTypeSchema {
        name: name.clone(),
        args,
        ret: ret_ty,
    };

    cx.builder.add_fn_schema(schema);

    Ok(())
}

fn lower_typed_let(cx: &mut LowerCtx, rest: &[Ast]) -> Result<(), Error> {
    // Global typed-let (top-level).
    let schema = parse_typed_let(None, rest)?;
    cx.builder.add_let_schema(schema)?;

    Ok(())
}

fn lower_block(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    // (block expr1 expr2 ...) => like `begin`, but
    // also records the VM level range covered by the
    // lowered body as a logical block in the program.
    if rest.is_empty() {
        return Err(Error::InvalidForm("block".into()));
    }

    let lvl_start = cx.builder.current_level();
    let res = lower_begin(cx, rest)?;
    let lvl_end = cx.builder.current_level();

    if lvl_end > lvl_start {
        cx.builder.push_block(lvl_start, lvl_end)?;
    }

    Ok(res)
}

fn parse_typed_let(owner: Option<&str>, rest: &[Ast]) -> Result<LetTypeSchema, Error> {
    // (typed-let name type)
    if rest.len() != 2 {
        return Err(Error::InvalidForm("typed-let".into()));
    }

    let name = match &rest[0] {
        Ast::Atom(Atom::Sym(s)) => s.clone(),
        _ => return Err(Error::InvalidForm("typed-let: name".into())),
    };

    let ty_sym = match &rest[1] {
        Ast::Atom(Atom::Sym(s)) => s.as_str(),
        Ast::List(items) if items.len() == 2 => {
            // Allow (role type) but
            // ignore the role here.
            match &items[1] {
                Ast::Atom(Atom::Sym(s)) => s.as_str(),
                _ => {
                    return Err(Error::InvalidForm("typed-let: type must be symbol".into()));
                }
            }
        }
        _ => return Err(Error::InvalidForm("typed-let: type".into())),
    };

    let ty = parse_scalar_type(ty_sym)?;

    Ok(LetTypeSchema {
        owner: owner.map(|s| s.to_string()),
        name,
        ty,
    })
}

// Determine if subtree is pure arithmetic
fn is_pure_arith(ast: &Ast) -> bool {
    match ast {
        Ast::Atom(Atom::Int(_)) | Ast::Atom(Atom::Sym(_)) => true,
        Ast::Atom(Atom::Str(_)) => false,
        Ast::List(items) if !items.is_empty() => {
            let head = match &items[0] {
                Ast::Atom(Atom::Sym(s)) => s.as_str(),
                _ => return false,
            };
            match head {
                "+" | "-" | "*" | "neg" | "=" | "select" | "if" => {
                    items[1..].iter().all(is_pure_arith)
                }
                "let" => items[1..].iter().all(is_pure_arith),
                _ => false,
            }
        }
        Ast::List(_) => false,
    }
}

// Sethi–Ullman number for an AST node
// (binary arithmetic only). Returns
// minimal registers needed to evaluate
// the subtree without spilling.
fn su_number(ast: &Ast) -> u32 {
    match ast {
        Ast::Atom(_) => 1,
        Ast::List(items) if !items.is_empty() => {
            let op_sym = match &items[0] {
                Ast::Atom(Atom::Sym(s)) => s.as_str(),
                _ => return 1,
            };

            // only consider binary
            // ops with two args
            let (l, r) = match (items.get(1), items.get(2)) {
                (Some(a), Some(b)) => (a, b),
                _ => return 1,
            };

            let sl = su_number(l);
            let sr = su_number(r);

            match op_sym {
                "+" | "-" | "*" => {
                    if sl == sr {
                        sl + 1
                    } else {
                        sl.max(sr)
                    }
                }
                _ => 1,
            }
        }
        _ => 1,
    }
}

// Rough subtree size (node count)
// used for tie-breaking when su
// numbers are equal.
fn ast_size(ast: &Ast) -> u32 {
    match ast {
        Ast::Atom(_) => 1,
        Ast::List(items) => 1 + items.iter().map(ast_size).sum::<u32>(),
    }
}

// find the quoted (member ...)
// list at rest[1] or rest[2]
// Returns the quoted (member ...)
// form at rest[1] or rest[2]
fn extract_member_from_quote(ast: &Ast) -> Option<&Ast> {
    let Ast::List(items) = ast else { return None };
    if items.len() != 2 {
        return None;
    }

    let Ast::Atom(Atom::Sym(h)) = &items[0] else {
        return None;
    };
    if h != "quote" {
        return None;
    }

    let Ast::List(inner) = &items[1] else {
        return None;
    };
    let Some(Ast::Atom(Atom::Sym(m))) = inner.first() else {
        return None;
    };

    if m != "member" {
        return None;
    }

    Some(&items[1])
}

// Build a balanced binary
// tree for +/* chains.
fn balance_chain(op: &str, items: &[Ast]) -> Ast {
    fn flatten(op: &str, nodes: &[Ast], out: &mut Vec<Ast>) {
        for n in nodes {
            if let Ast::List(ls) = n {
                if !ls.is_empty() {
                    if let Ast::Atom(Atom::Sym(h)) = &ls[0] {
                        if h == op && ls.len() >= 3 {
                            flatten(op, &ls[1..], out);
                            continue;
                        }
                    }
                }
            }

            out.push(n.clone());
        }
    }

    fn build(op: &str, v: &[Ast]) -> Ast {
        if v.len() == 1 {
            return v[0].clone();
        }

        let mid = v.len() / 2;
        let left = build(op, &v[..mid]);
        let right = build(op, &v[mid..]);

        Ast::List(vec![Ast::Atom(Atom::Sym(op.to_string())), left, right])
    }

    let mut flat = Vec::new();
    flatten(op, items, &mut flat);

    build(op, &flat)
}

#[inline]
fn free_if_owned(cx: &mut LowerCtx, v: RVal) {
    if let RVal::Owned(r) = v {
        cx.free_reg(r);
    }
}

// Build implicit (begin ...)
// from one or more forms
fn implicit_begin(forms: &[Ast]) -> Ast {
    if forms.len() == 1 {
        return forms[0].clone();
    }

    let mut v = Vec::with_capacity(forms.len() + 1);
    v.push(Ast::Atom(Atom::Sym("begin".to_string())));
    v.extend_from_slice(forms);

    Ast::List(v)
}

fn parse_scalar_type(sym: &str) -> Result<ScalarType, Error> {
    match sym {
        "u64" => Ok(ScalarType::U64),
        "u128" => Ok(ScalarType::U128),
        "bytes32" => Ok(ScalarType::Bytes32),
        _ => Err(Error::InvalidForm(format!(
            "typed-fn: unknown type '{sym}'",
        ))),
    }
}

fn parse_arg_spec(ast: &Ast) -> Result<(ArgRole, ScalarType), Error> {
    match ast {
        // Shorthand: just the type symbol => Const
        Ast::Atom(Atom::Sym(t)) => {
            let ty = parse_scalar_type(t)?;
            Ok((ArgRole::Const, ty))
        }
        // (role type) with role in {const, let}
        Ast::List(items) if items.len() == 2 => {
            let role_sym = match &items[0] {
                Ast::Atom(Atom::Sym(s)) => s.as_str(),
                _ => {
                    return Err(Error::InvalidForm(
                        "typed-fn: arg role must be symbol".into(),
                    ));
                }
            };
            let ty_sym = match &items[1] {
                Ast::Atom(Atom::Sym(s)) => s.as_str(),
                _ => {
                    return Err(Error::InvalidForm(
                        "typed-fn: arg type must be symbol".into(),
                    ));
                }
            };

            let role = match role_sym {
                "const" => ArgRole::Const,
                "let" => ArgRole::Let,
                _ => {
                    return Err(Error::InvalidForm(format!(
                        "typed-fn: unknown arg role '{role_sym}'",
                    )));
                }
            };
            let ty = parse_scalar_type(ty_sym)?;

            Ok((role, ty))
        }
        _ => Err(Error::InvalidForm(
            "typed-fn: arg spec must be type or (role type)".into(),
        )),
    }
}

fn collect_let_names(ast: &Ast, builder: &mut ProgramBuilder) {
    match ast {
        Ast::List(items) if !items.is_empty() => {
            // Detect (let ((name expr) ...) body...)
            if let Ast::Atom(Atom::Sym(head)) = &items[0] {
                if head == "let" {
                    if let Some(Ast::List(pairs)) = items.get(1) {
                        for b in pairs {
                            if let Ast::List(kv) = b {
                                if kv.len() == 2 {
                                    if let Ast::Atom(Atom::Sym(name)) = &kv[0] {
                                        builder.add_let_name(name.clone());
                                    }
                                }
                            }
                        }
                    }
                }
            }

            // Recurse into children
            for sub in &items[1..] {
                collect_let_names(sub, builder);
            }
        }
        _ => {}
    }
}

fn collect_typed_lets(owner: &str, ast: &Ast, builder: &mut ProgramBuilder) -> Result<(), Error> {
    match ast {
        Ast::List(items) if !items.is_empty() => {
            if let Ast::Atom(Atom::Sym(head)) = &items[0] {
                if head == "typed-let" {
                    let schema = parse_typed_let(Some(owner), &items[1..])?;
                    builder.add_let_schema(schema)?;
                }
            }

            for sub in &items[1..] {
                collect_typed_lets(owner, sub, builder)?;
            }
        }
        _ => {}
    }

    Ok(())
}

fn contains_symbol(ast: &Ast, name: &str) -> bool {
    match ast {
        Ast::Atom(Atom::Sym(s)) => s == name,
        Ast::List(items) => items.iter().any(|a| contains_symbol(a, name)),
        _ => false,
    }
}

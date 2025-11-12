// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

use crate::compiler::ir::{Op, ProgramBuilder};
use crate::compiler::{Binding, Env, Error};
use crate::layout::NR;

use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::math::{FieldElement, StarkField};

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
                cx.b.push(Op::Const { dst, imm: v });

                Ok(RVal::Owned(dst))
            }
        }
    }
}

#[derive(Default, Debug, Clone)]
pub struct CompileStats {
    pub reuse_dst: u32,
    pub su_reorders: u32,
    pub balanced_chains: u32,
    pub mov_elided: u32,
}

#[derive(Debug)]
pub struct LowerCtx<'a> {
    pub b: ProgramBuilder,
    pub stats: CompileStats,
    env: Env,
    free: Vec<u8>,
    call_stack: Vec<String>,
    // Live-set tracking
    // for spillless metrics.
    cur_live: usize,
    peak_live: usize,
    _m: core::marker::PhantomData<&'a ()>,
}

impl<'a> LowerCtx<'a> {
    pub fn new() -> Self {
        let free: Vec<u8> = (0u8..NR as u8).collect();

        // simple stack: pop() to allocate from
        // the end gives high-numbered regs first.
        Self {
            b: ProgramBuilder::new(),
            free,
            env: Env::default(),
            call_stack: Vec::new(),
            cur_live: 0,
            peak_live: 0,
            stats: CompileStats::default(),
            _m: core::marker::PhantomData,
        }
    }

    pub fn peak_live(&self) -> usize {
        self.peak_live
    }

    fn alloc(&mut self) -> Result<u8, Error> {
        match self.free.pop() {
            Some(r) => {
                // track live-set size
                self.cur_live += 1;

                if self.cur_live > self.peak_live {
                    self.peak_live = self.cur_live;
                }

                Ok(r)
            }
            None => Err(Error::RegOverflow { need: 1, have: 0 }),
        }
    }

    fn free_reg(&mut self, r: u8) {
        // free and reduce current live-set
        self.free.push(r);

        if self.cur_live > 0 {
            self.cur_live -= 1;
        }
    }
    
    pub fn val_reg(&self, v: &RVal) -> Result<u8, Error> {
        match *v {
            RVal::Owned(r) | RVal::Borrowed(r) => Ok(r),
            RVal::Imm(_) => Err(Error::InvalidForm(
                "internal: immediate used where register required".into(),
            )),
        }
    }

    fn map_var(&mut self, name: &str, b: Binding) {
        self.env.vars.insert(name.to_string(), b);
    }

    fn get_binding(&self, name: &str) -> Result<Binding, Error> {
        self.env
            .vars
            .get(name)
            .cloned()
            .ok_or_else(|| Error::UnknownSymbol(name.to_string()))
    }

    fn define_fun(&mut self, name: &str, params: Vec<String>, body: Ast) {
        self.env.funs.insert(name.to_string(), (params, body));
    }

    fn get_fun(&self, name: &str) -> Option<&(Vec<String>, Ast)> {
        self.env.funs.get(name)
    }

    pub fn emit_mov(&mut self, dst: u8, src: u8) {
        if dst == src {
            self.stats.mov_elided += 1;
            return;
        }

        self.b.push(Op::Mov { dst, src });
    }
}

pub fn lower_top(cx: &mut LowerCtx, ast: Ast) -> Result<(), Error> {
    match ast {
        Ast::List(ref items) if !items.is_empty() => {
            match &items[0] {
                Ast::Atom(Atom::Sym(s)) if s == "def" => lower_def(cx, &items[1..]),
                Ast::Atom(Atom::Sym(s)) if s == "deftype" => lower_deftype(cx, &items[1..]),
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
            // under a macro (str64 "...")
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

                            cx.stats.balanced_chains += 1;

                            return lower_expr(cx, balanced);
                        }
                        lower_bin(cx, tail, BinOp::Add)
                    }
                    "-" => lower_bin(cx, tail, BinOp::Sub),
                    "*" => {
                        if tail.len() != 2 {
                            let balanced = balance_chain("*", tail);

                            cx.stats.balanced_chains += 1;

                            return lower_expr(cx, balanced);
                        }
                        lower_bin(cx, tail, BinOp::Mul)
                    }
                    "=" => lower_eq(cx, tail),
                    "if" => lower_if(cx, tail),
                    "let" => lower_let(cx, tail),
                    "neg" => lower_neg(cx, tail),
                    "str64" => lower_str64(cx, tail),
                    "hash2" => lower_hash2(cx, tail),
                    "merkle-verify" => lower_merkle_verify(cx, tail),
                    "load-ca" => lower_load_ca(cx, tail),
                    "store-ca" => lower_store_ca(cx, tail),
                    "select" => lower_select(cx, tail),
                    "assert" => lower_assert(cx, tail),
                    "bit?" => lower_bit_pred(cx, tail),
                    "assert-bit" => lower_assert_bit(cx, tail),
                    "assert-range" => lower_assert_range(cx, tail),
                    "safe-add" => lower_safe_add(cx, tail),
                    "safe-sub" => lower_safe_sub(cx, tail),
                    "safe-mul" => lower_safe_mul(cx, tail),
                    "divmod-q" => lower_divmod_q(cx, tail),
                    "divmod-r" => lower_divmod_r(cx, tail),
                    "mulwide-hi" => lower_mulwide_hi(cx, tail),
                    "mulwide-lo" => lower_mulwide_lo(cx, tail),
                    "muldiv" => lower_muldiv_floor(cx, tail),
                    "in-set" => lower_in_set(cx, tail),
                    "load" => lower_load(cx, tail),
                    "store" => lower_store(cx, tail).map(|_| RVal::Imm(0)),
                    "hex-to-bytes32" => lower_hex_to_bytes32(cx, tail),
                    "seq" => lower_seq(cx, tail),
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
    // (def (f x y) body)
    // or (def name body) -- no params
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

            let body = rest
                .get(1)
                .cloned()
                .ok_or_else(|| Error::InvalidForm("def: body".into()))?;

            (fname, ps, body)
        }
        Ast::Atom(Atom::Sym(s)) => {
            let body = rest
                .get(1)
                .cloned()
                .ok_or_else(|| Error::InvalidForm("def: body".into()))?;
            (s.clone(), Vec::new(), body)
        }
        _ => return Err(Error::InvalidForm("def".into())),
    };

    cx.define_fun(&name, params, body);

    Ok(())
}

fn lower_let(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    // (let ((x expr) (y expr)) body)
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

    // body = last expr or (body ...)
    let body_ast = rest
        .get(1)
        .cloned()
        .ok_or_else(|| Error::InvalidForm("let: body".into()))?;

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

fn lower_select(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 3 {
        return Err(Error::InvalidForm("select".into()));
    }

    let c = lower_expr(cx, rest[0].clone())?;
    let a = lower_expr(cx, rest[1].clone())?;
    let b = lower_expr(cx, rest[2].clone())?;

    // Constant fold when
    // condition is immediate 0/1
    if let Some(cv) = c.as_imm() {
        if cv == 0 {
            free_if_owned(cx, a);
            return Ok(b);
        } else if cv == 1 {
            free_if_owned(cx, b);
            return Ok(a);
        } else {
            return Err(Error::InvalidForm(
                "select: cond must be boolean (0/1)".into(),
            ));
        }
    }

    let c = c.into_owned(cx)?;
    let a = a.into_owned(cx)?;
    let b = b.into_owned(cx)?;

    let dst = cx.alloc()?;

    cx.b.push(Op::Select {
        dst,
        c: cx.val_reg(&c)?,
        a: cx.val_reg(&a)?,
        b: cx.val_reg(&b)?,
    });

    // free temps (keep dst)
    free_if_owned(cx, c);
    free_if_owned(cx, a);
    free_if_owned(cx, b);

    Ok(RVal::Owned(dst))
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
        cx.stats.su_reorders += 1;
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
        let ra = BE::from(ai);
        let rb = BE::from(bi);
        let r = match op {
            BinOp::Add => ra + rb,
            BinOp::Sub => ra - rb,
            BinOp::Mul => ra * rb,
        };
        let r128: u128 = r.as_int();
        if r128 <= u64::MAX as u128 {
            return Ok(RVal::Imm(r128 as u64));
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
        BinOp::Add => cx.b.push(Op::Add { dst, a: a_r, b: b_r }),
        BinOp::Sub => cx.b.push(Op::Sub { dst, a: a_r, b: b_r }),
        BinOp::Mul => cx.b.push(Op::Mul { dst, a: a_r, b: b_r }),
    }

    // Free temps
    if reused {
        cx.stats.reuse_dst += 1;

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

fn lower_neg(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 1 {
        return Err(Error::InvalidForm("neg".into()));
    }

    let a = lower_expr(cx, rest[0].clone())?;

    if let Some(ai) = a.as_imm() {
        let r = BE::ZERO - BE::from(ai);
        let r128: u128 = r.as_int();

        if r128 <= u64::MAX as u128 {
            return Ok(RVal::Imm(r128 as u64));
        }
    }

    let a = a.into_owned(cx)?;

    // Safe reuse
    let dst = match a {
        RVal::Owned(r) => r,
        _ => cx.alloc()?,
    };

    cx.b.push(Op::Neg { dst, a: cx.val_reg(&a)? });

    // reused 'a' remains
    // owned as result
    if let RVal::Owned(_) = a {
        // keep
    } else {
        free_if_owned(cx, a);
    }

    Ok(RVal::Owned(dst))
}

fn lower_assert(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 1 {
        return Err(Error::InvalidForm("assert".into()));
    }

    let c = lower_expr(cx, rest[0].clone())?;

    if let Some(cv) = c.as_imm() {
        if cv == 1 {
            return Ok(RVal::Imm(1));
        } else {
            return Err(Error::InvalidForm("assert: constant false".into()));
        }
    }

    let c = c.into_owned(cx)?;
    let dst = cx.alloc()?;

    cx.b.push(Op::Assert { dst, c: cx.val_reg(&c)? });
    free_if_owned(cx, c);

    Ok(RVal::Owned(dst))
}

fn lower_if(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 3 {
        return Err(Error::InvalidForm("if".into()));
    }

    let c = lower_expr(cx, rest[0].clone())?;
    let t = lower_expr(cx, rest[1].clone())?;
    let e = lower_expr(cx, rest[2].clone())?;

    if let Some(cv) = c.as_imm() {
        if cv == 0 {
            free_if_owned(cx, t);
            return Ok(e);
        } else if cv == 1 {
            free_if_owned(cx, e);
            return Ok(t);
        } else {
            return Err(Error::InvalidForm("if: cond must be boolean (0/1)".into()));
        }
    }

    let c = c.into_owned(cx)?;
    let t = t.into_owned(cx)?;
    let e = e.into_owned(cx)?;

    let dst = cx.alloc()?;

    cx.b.push(Op::Select {
        dst,
        c: cx.val_reg(&c)?,
        a: cx.val_reg(&t)?,
        b: cx.val_reg(&e)?,
    });

    free_if_owned(cx, c);
    free_if_owned(cx, t);
    free_if_owned(cx, e);

    Ok(RVal::Owned(dst))
}

fn lower_eq(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 2 {
        return Err(Error::InvalidForm("=".into()));
    }

    let a = lower_expr(cx, rest[0].clone())?;
    let b = lower_expr(cx, rest[1].clone())?;

    if let (Some(ai), Some(bi)) = (a.as_imm(), b.as_imm()) {
        return Ok(RVal::Imm(if ai == bi { 1 } else { 0 }));
    }

    let a = a.into_owned(cx)?;
    let b = b.into_owned(cx)?;

    let dst = cx.alloc()?;

    cx.b.push(Op::Eq {
        dst,
        a: cx.val_reg(&a)?,
        b: cx.val_reg(&b)?,
    });

    free_if_owned(cx, a);
    free_if_owned(cx, b);

    Ok(RVal::Owned(dst))
}

fn lower_hash2(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 2 {
        return Err(Error::InvalidForm("hash2".into()));
    }

    let a = lower_expr(cx, rest[0].clone())?;
    let b = lower_expr(cx, rest[1].clone())?;

    // Only materialize immediates;
    // borrowed regs can be used directly
    let a = if a.as_imm().is_some() {
        a.into_owned(cx)?
    } else {
        a
    };
    let b = if b.as_imm().is_some() {
        b.into_owned(cx)?
    } else {
        b
    };

    // Lower to SAbsorbN(2) + SSqueeze
    cx.b.push(Op::SAbsorbN {
        regs: vec![cx.val_reg(&a)?, cx.val_reg(&b)?],
    });

    let dst = cx.alloc()?;

    cx.b.push(Op::SSqueeze { dst });

    free_if_owned(cx, a);
    free_if_owned(cx, b);

    Ok(RVal::Owned(dst))
}

fn lower_call(cx: &mut LowerCtx, name: &str, args: &[Ast]) -> Result<RVal, Error> {
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

fn lower_str64(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    // (str64 "...") → digest
    if rest.len() != 1 {
        return Err(Error::InvalidForm("str64".into()));
    }

    let s = match &rest[0] {
        Ast::Atom(Atom::Str(st)) => st.clone(),
        _ => return Err(Error::InvalidForm("str64: expects string literal".into())),
    };

    let bytes_src = s.as_bytes();
    if bytes_src.len() > 64 {
        return Err(Error::InvalidForm("str64: length > 64".into()));
    }

    // Pad to 64
    let mut buf = [0u8; 64];
    buf[..bytes_src.len()].copy_from_slice(bytes_src);

    // Build chunk commitments from u64 pairs via Hash2 only
    // c0 = H(lo0, hi0), c1 = H(lo1, hi1), ...
    let c_hash = |cx: &mut LowerCtx, lo: u64, hi: u64| -> Result<u8, Error> {
        let r_lo = cx.alloc()?;
        cx.b.push(Op::Const { dst: r_lo, imm: lo });

        let r_hi = cx.alloc()?;
        cx.b.push(Op::Const { dst: r_hi, imm: hi });

        cx.b.push(Op::SAbsorbN {
            regs: vec![r_lo, r_hi],
        });

        let r_c = cx.alloc()?;

        cx.b.push(Op::SSqueeze { dst: r_c });

        cx.free_reg(r_lo);
        cx.free_reg(r_hi);

        Ok(r_c)
    };

    let (lo0, hi0) = u64_pair_from_le_16(&buf[0..16]);
    let r_c0 = c_hash(cx, lo0, hi0)?;
    let (lo1, hi1) = u64_pair_from_le_16(&buf[16..32]);
    let r_c1 = c_hash(cx, lo1, hi1)?;
    let r_p01 = {
        let dst = cx.alloc()?;
        cx.b.push(Op::SAbsorbN {
            regs: vec![r_c0, r_c1],
        });
        cx.b.push(Op::SSqueeze { dst });

        cx.free_reg(r_c0);
        cx.free_reg(r_c1);

        dst
    };

    let (lo2, hi2) = u64_pair_from_le_16(&buf[32..48]);
    let r_c2 = c_hash(cx, lo2, hi2)?;
    let (lo3, hi3) = u64_pair_from_le_16(&buf[48..64]);
    let r_c3 = c_hash(cx, lo3, hi3)?;
    let r_p23 = {
        let dst = cx.alloc()?;
        cx.b.push(Op::SAbsorbN {
            regs: vec![r_c2, r_c3],
        });
        cx.b.push(Op::SSqueeze { dst });

        cx.free_reg(r_c2);
        cx.free_reg(r_c3);

        dst
    };

    let r_payload = {
        let dst = cx.alloc()?;
        cx.b.push(Op::SAbsorbN {
            regs: vec![r_p01, r_p23],
        });
        cx.b.push(Op::SSqueeze { dst });

        cx.free_reg(r_p01);
        cx.free_reg(r_p23);

        dst
    };

    // t0 = H(TAG, L), TAG is 64-bit constant derived from blake3("zkl/str64")
    let tag8 = {
        let d = blake3::hash(b"zkl/str64");
        let mut t = [0u8; 8];
        t.copy_from_slice(&d.as_bytes()[0..8]);

        u64::from_le_bytes(t)
    };

    let r_tag = cx.alloc()?;
    cx.b.push(Op::Const {
        dst: r_tag,
        imm: tag8,
    });

    let r_len = cx.alloc()?;
    cx.b.push(Op::Const {
        dst: r_len,
        imm: bytes_src.len() as u64,
    });

    let r_t0 = {
        let dst = cx.alloc()?;
        cx.b.push(Op::SAbsorbN {
            regs: vec![r_tag, r_len],
        });
        cx.b.push(Op::SSqueeze { dst });

        cx.free_reg(r_tag);
        cx.free_reg(r_len);

        dst
    };

    // digest = H(t0, payload)
    let r_digest = cx.alloc()?;
    cx.b.push(Op::SAbsorbN {
        regs: vec![r_t0, r_payload],
    });
    cx.b.push(Op::SSqueeze { dst: r_digest });

    cx.free_reg(r_t0);
    cx.free_reg(r_payload);

    Ok(RVal::Owned(r_digest))
}

fn lower_hex_to_bytes32(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    // (hex-to-bytes32 "0x...")
    if rest.len() != 1 {
        return Err(Error::InvalidForm("hex-to-bytes32".into()));
    }

    let s = match &rest[0] {
        Ast::Atom(Atom::Str(st)) => st.clone(),
        _ => {
            return Err(Error::InvalidForm(
                "hex-to-bytes32: expects string literal".into(),
            ));
        }
    };

    let hex_str = s.strip_prefix("0x").unwrap_or(&s);
    let decoded = match hex::decode(hex_str) {
        Ok(b) => b,
        Err(_) => return Err(Error::InvalidForm("hex-to-bytes32: invalid hex".into())),
    };

    if decoded.len() > 32 {
        return Err(Error::InvalidForm("hex-to-bytes32: length > 32".into()));
    }

    // Pad to 32
    let mut buf = [0u8; 32];
    buf[..decoded.len()].copy_from_slice(&decoded);

    // Build chunk commitments
    // from u64 pairs via sponge ops.
    let c_hash = |cx: &mut LowerCtx, lo: u64, hi: u64| -> Result<u8, Error> {
        let r_lo = cx.alloc()?;
        cx.b.push(Op::Const { dst: r_lo, imm: lo });

        let r_hi = cx.alloc()?;
        cx.b.push(Op::Const { dst: r_hi, imm: hi });

        cx.b.push(Op::SAbsorbN {
            regs: vec![r_lo, r_hi],
        });

        let r_c = cx.alloc()?;

        cx.b.push(Op::SSqueeze { dst: r_c });

        cx.free_reg(r_lo);
        cx.free_reg(r_hi);

        Ok(r_c)
    };

    let (lo0, hi0) = u64_pair_from_le_16(&buf[0..16]);
    let r_c0 = c_hash(cx, lo0, hi0)?;
    let (lo1, hi1) = u64_pair_from_le_16(&buf[16..32]);
    let r_c1 = c_hash(cx, lo1, hi1)?;

    let r_payload = {
        let dst = cx.alloc()?;
        cx.b.push(Op::SAbsorbN {
            regs: vec![r_c0, r_c1],
        });
        cx.b.push(Op::SSqueeze { dst });

        cx.free_reg(r_c0);
        cx.free_reg(r_c1);

        dst
    };

    // t0 = H(TAG, L)
    let tag8 = {
        let d = blake3::hash(b"zkl/bytes32");
        let mut t = [0u8; 8];
        t.copy_from_slice(&d.as_bytes()[0..8]);

        u64::from_le_bytes(t)
    };

    let r_tag = cx.alloc()?;
    cx.b.push(Op::Const {
        dst: r_tag,
        imm: tag8,
    });

    let r_len = cx.alloc()?;
    cx.b.push(Op::Const {
        dst: r_len,
        imm: decoded.len() as u64,
    });

    let r_t0 = {
        let dst = cx.alloc()?;
        cx.b.push(Op::SAbsorbN {
            regs: vec![r_tag, r_len],
        });
        cx.b.push(Op::SSqueeze { dst });

        cx.free_reg(r_tag);
        cx.free_reg(r_len);

        dst
    };

    // digest = H(t0, payload)
    let r_digest = cx.alloc()?;
    cx.b.push(Op::SAbsorbN {
        regs: vec![r_t0, r_payload],
    });
    cx.b.push(Op::SSqueeze { dst: r_digest });

    cx.free_reg(r_t0);
    cx.free_reg(r_payload);

    Ok(RVal::Owned(r_digest))
}

fn lower_in_set(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    // (in-set x (s1 s2 ...)) -> assert(prod(x - si) == 0)
    if rest.len() != 2 {
        return Err(Error::InvalidForm("in-set".into()));
    }

    let x = lower_expr(cx, rest[0].clone())?;
    let x = x.into_owned(cx)?;

    let set_list = match &rest[1] {
        Ast::List(items) => items.clone(),
        _ => return Err(Error::InvalidForm("in-set: expects list".into())),
    };

    if set_list.is_empty() {
        return Err(Error::InvalidForm("in-set: empty set".into()));
    }

    // Build product
    let mut r_prod: Option<u8> = None;

    for it in set_list.into_iter() {
        let si = lower_expr(cx, it)?;
        let si = si.into_owned(cx)?;

        let r_diff = cx.alloc()?;

        cx.b.push(Op::Sub {
            dst: r_diff,
            a: cx.val_reg(&x)?,
            b: cx.val_reg(&si)?,
        });

        free_if_owned(cx, si);

        r_prod = Some(match r_prod.take() {
            None => r_diff,
            Some(prev) => {
                let r_mul = cx.alloc()?;

                cx.b.push(Op::Mul {
                    dst: r_mul,
                    a: prev,
                    b: r_diff,
                });

                cx.free_reg(prev);
                cx.free_reg(r_diff);

                r_mul
            }
        });
    }

    let r_zero = cx.alloc()?;

    cx.b.push(Op::Const {
        dst: r_zero,
        imm: 0,
    });

    let prev = r_prod.unwrap();
    let r_eq = cx.alloc()?;

    cx.b.push(Op::Eq {
        dst: r_eq,
        a: prev,
        b: r_zero,
    });

    cx.free_reg(r_zero);
    cx.free_reg(prev);

    let r_out = cx.alloc()?;

    cx.b.push(Op::Assert {
        dst: r_out,
        c: r_eq,
    });

    cx.free_reg(r_eq);

    // do not free x if
    // it was borrowed.
    if let RVal::Owned(rx) = x {
        cx.free_reg(rx);
    }

    Ok(RVal::Owned(r_out))
}

fn lower_merkle_verify(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 2 {
        return Err(Error::InvalidForm("merkle-verify".into()));
    }

    let leaf_v = lower_expr(cx, rest[0].clone())?;
    let leaf_v = if leaf_v.as_imm().is_some() {
        leaf_v.into_owned(cx)?
    } else {
        leaf_v
    };
    let leaf_r = cx.val_reg(&leaf_v)?;

    let pairs_ast = match &rest[1] {
        Ast::List(items) => items.clone(),
        _ => return Err(Error::InvalidForm("merkle-verify: path".into())),
    };
    if pairs_ast.is_empty() {
        return Err(Error::InvalidForm("merkle-verify: empty path".into()));
    }

    // First step
    let (dir0_v, sib0_v) = {
        let p = &pairs_ast[0];
        let (d_ast, s_ast) = match p {
            Ast::List(ps) if ps.len() == 2 => (&ps[0], &ps[1]),
            _ => return Err(Error::InvalidForm("merkle-verify: pair".into())),
        };

        let d = lower_expr(cx, d_ast.clone())?;
        let d = d.into_owned(cx)?;

        let s = lower_expr(cx, s_ast.clone())?;
        let s = s.into_owned(cx)?;

        (d, s)
    };

    cx.b.push(Op::MerkleStepFirst {
        leaf_reg: leaf_r,
        dir_reg: cx.val_reg(&dir0_v)?,
        sib_reg: cx.val_reg(&sib0_v)?,
    });

    // free temps
    free_if_owned(cx, leaf_v);
    free_if_owned(cx, dir0_v);
    free_if_owned(cx, sib0_v);

    // Middle steps
    for p in pairs_ast
        .iter()
        .skip(1)
        .take(pairs_ast.len().saturating_sub(2))
    {
        let (d_ast, s_ast) = match p {
            Ast::List(ps) if ps.len() == 2 => (&ps[0], &ps[1]),
            _ => return Err(Error::InvalidForm("merkle-verify: pair".into())),
        };

        let d = lower_expr(cx, d_ast.clone())?;
        let d = if d.as_imm().is_some() {
            d.into_owned(cx)?
        } else {
            d
        };

        let s = lower_expr(cx, s_ast.clone())?;
        let s = if s.as_imm().is_some() {
            s.into_owned(cx)?
        } else {
            s
        };

        cx.b.push(Op::MerkleStep {
            dir_reg: cx.val_reg(&d)?,
            sib_reg: cx.val_reg(&s)?,
        });

        free_if_owned(cx, d);
        free_if_owned(cx, s);
    }

    // Last step (if path len >= 2)
    if pairs_ast.len() >= 2 {
        let p_last = pairs_ast.last().unwrap();
        let (d_ast, s_ast) = match p_last {
            Ast::List(ps) if ps.len() == 2 => (&ps[0], &ps[1]),
            _ => return Err(Error::InvalidForm("merkle-verify: pair".into())),
        };

        let d = lower_expr(cx, d_ast.clone())?;
        let d = if d.as_imm().is_some() {
            d.into_owned(cx)?
        } else {
            d
        };

        let s = lower_expr(cx, s_ast.clone())?;
        let s = if s.as_imm().is_some() {
            s.into_owned(cx)?
        } else {
            s
        };

        cx.b.push(Op::MerkleStepLast {
            dir_reg: cx.val_reg(&d)?,
            sib_reg: cx.val_reg(&s)?,
        });

        free_if_owned(cx, d);
        free_if_owned(cx, s);
    }

    // Return 0 immediate;
    // verification is enforced by AIR.
    Ok(RVal::Imm(0))
}

// (bit? x) -> 1 if x in {0,1}, else 0
fn lower_bit_pred(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 1 {
        return Err(Error::InvalidForm("bit?".into()));
    }

    let x = lower_expr(cx, rest[0].clone())?;

    // If immediate, compute directly
    if let Some(xi) = x.as_imm() {
        return Ok(RVal::Imm(if xi == 0 || xi == 1 { 1 } else { 0 }));
    }

    // t = x * (x - 1)
    let x = x.into_owned(cx)?;
    let one = {
        let r = cx.alloc()?;
        cx.b.push(Op::Const { dst: r, imm: 1 });

        r
    };
    let xm1 = {
        let r = cx.alloc()?;
        cx.b.push(Op::Sub {
            dst: r,
            a: cx.val_reg(&x)?,
            b: one,
        });

        r
    };
    let t = {
        let r = cx.alloc()?;
        cx.b.push(Op::Mul {
            dst: r,
            a: cx.val_reg(&x)?,
            b: xm1,
        });

        r
    };

    // eq = (t == 0)
    let z = {
        let r = cx.alloc()?;
        cx.b.push(Op::Const { dst: r, imm: 0 });

        r
    };
    let eq = {
        let r = cx.alloc()?;
        cx.b.push(Op::Eq { dst: r, a: t, b: z });

        r
    };

    // free temps
    cx.free_reg(one);
    cx.free_reg(xm1);
    cx.free_reg(t);
    cx.free_reg(z);

    Ok(RVal::Owned(eq))
}

// (assert-bit x) -> assert(x in {0,1}) and return 1
fn lower_assert_bit(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 1 {
        return Err(Error::InvalidForm("assert-bit".into()));
    }

    let x = lower_expr(cx, rest[0].clone())?;
    if let Some(v) = x.as_imm() {
        if v == 0 || v == 1 {
            return Ok(RVal::Imm(1));
        } else {
            return Err(Error::InvalidForm("assert-bit: constant not a bit".into()));
        }
    }

    let x = x.into_owned(cx)?;
    let dst = cx.alloc()?;

    cx.b.push(Op::AssertBit { dst, r: cx.val_reg(&x)? });

    free_if_owned(cx, x);

    Ok(RVal::Owned(dst))
}

fn lower_assert_range(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 2 {
        return Err(Error::InvalidForm("assert-range".into()));
    }

    // parse bits
    let bits = match &rest[1] {
        Ast::Atom(Atom::Int(v)) => *v,
        _ => {
            return Err(Error::InvalidForm(
                "assert-range: bits must be integer".into(),
            ));
        }
    };

    let x = lower_expr(cx, rest[0].clone())?;

    if bits == 32 {
        if let Some(v) = x.as_imm() {
            let limit = 1u128 << 32;
            return if (v as u128) < limit {
                Ok(RVal::Imm(1))
            } else {
                Err(Error::InvalidForm(
                    "assert-range: constant out of range".into(),
                ))
            };
        }

        let x = x.into_owned(cx)?;
        let dst = cx.alloc()?;

        cx.b.push(Op::AssertRange {
            dst,
            r: cx.val_reg(&x)?,
            bits: 32,
        });

        free_if_owned(cx, x);

        Ok(RVal::Owned(dst))
    } else if bits == 64 {
        // Lo then Hi
        if let Some(_v) = x.as_imm() {
            // compile-time: 0 <= v < 2^64 for u64
            return Ok(RVal::Imm(1));
        }

        let x = x.into_owned(cx)?;
        let dst = cx.alloc()?;

        cx.b.push(Op::AssertRangeLo { dst, r: cx.val_reg(&x)? });
        cx.b.push(Op::AssertRangeHi { dst, r: cx.val_reg(&x)? });

        free_if_owned(cx, x);

        return Ok(RVal::Owned(dst));
    } else {
        return Err(Error::InvalidForm(
            "assert-range: bits must be 32 or 64".into(),
        ));
    }
}

fn lower_safe_add(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 2 {
        return Err(Error::InvalidForm("safe-add".into()));
    }

    let av = lower_expr(cx, rest[0].clone())?;
    let bv = lower_expr(cx, rest[1].clone())?;

    if let (Some(ai), Some(bi)) = (av.as_imm(), bv.as_imm()) {
        // constant fold in field, require u64
        let r = BE::from(ai) + BE::from(bi);
        let r128: u128 = r.as_int();

        if r128 <= u64::MAX as u128 {
            return Ok(RVal::Imm(r128 as u64));
        }
    }

    let a = av.into_owned(cx)?;
    let b = bv.into_owned(cx)?;

    // inputs in u64
    let a_r = cx.val_reg(&a)?;
    let b_r = cx.val_reg(&b)?;
    
    assert_range_bits_for_reg(cx, a_r, 64)?;
    assert_range_bits_for_reg(cx, b_r, 64)?;

    let dst = cx.alloc()?;
    cx.b.push(Op::Add {
        dst,
        a: a_r,
        b: b_r,
    });

    // result in u64
    assert_range_bits_for_reg(cx, dst, 64)?;

    free_if_owned(cx, a);
    free_if_owned(cx, b);

    Ok(RVal::Owned(dst))
}

fn lower_safe_sub(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 2 {
        return Err(Error::InvalidForm("safe-sub".into()));
    }

    let av = lower_expr(cx, rest[0].clone())?;
    let bv = lower_expr(cx, rest[1].clone())?;

    if let (Some(ai), Some(bi)) = (av.as_imm(), bv.as_imm()) {
        let r = BE::from(ai) - BE::from(bi);
        let r128: u128 = r.as_int();

        if r128 <= u64::MAX as u128 {
            return Ok(RVal::Imm(r128 as u64));
        }
    }

    let a = av.into_owned(cx)?;
    let b = bv.into_owned(cx)?;

    // inputs in u64
    let a_r = cx.val_reg(&a)?;
    let b_r = cx.val_reg(&b)?;
    
    assert_range_bits_for_reg(cx, a_r, 64)?;
    assert_range_bits_for_reg(cx, b_r, 64)?;

    let dst = cx.alloc()?;
    cx.b.push(Op::Sub {
        dst,
        a: a_r,
        b: b_r,
    });

    // no wrap-around:
    // enforce result in u64
    assert_range_bits_for_reg(cx, dst, 64)?;

    free_if_owned(cx, a);
    free_if_owned(cx, b);

    Ok(RVal::Owned(dst))
}

fn lower_safe_mul(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 2 {
        return Err(Error::InvalidForm("safe-mul".into()));
    }

    let av = lower_expr(cx, rest[0].clone())?;
    let bv = lower_expr(cx, rest[1].clone())?;

    if let (Some(ai), Some(bi)) = (av.as_imm(), bv.as_imm()) {
        // constant fold: 32x32->64 policy still holds
        let r = BE::from(ai) * BE::from(bi);
        let r128: u128 = r.as_int();

        if r128 <= u64::MAX as u128 {
            return Ok(RVal::Imm(r128 as u64));
        }
    }

    let a = av.into_owned(cx)?;
    let b = bv.into_owned(cx)?;

    // Use 32x32->64 safe policy
    let a_r = cx.val_reg(&a)?;
    let b_r = cx.val_reg(&b)?;
    
    assert_range_bits_for_reg(cx, a_r, 32)?;
    assert_range_bits_for_reg(cx, b_r, 32)?;

    let dst = cx.alloc()?;
    cx.b.push(Op::Mul {
        dst,
        a: a_r,
        b: b_r,
    });

    assert_range_bits_for_reg(cx, dst, 64)?;

    free_if_owned(cx, a);
    free_if_owned(cx, b);

    Ok(RVal::Owned(dst))
}

// (divmod-q a b) -> floor(a/b)
fn lower_divmod_q(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 2 {
        return Err(Error::InvalidForm("divmod-q".into()));
    }

    let av = lower_expr(cx, rest[0].clone())?;
    let bv = lower_expr(cx, rest[1].clone())?;

    let a = av.into_owned(cx)?;
    let b = bv.into_owned(cx)?;

    // Enforce inputs in u64
    let a_r = cx.val_reg(&a)?;
    let b_r = cx.val_reg(&b)?;

    assert_range_bits_for_reg(cx, a_r, 64)?;
    assert_range_bits_for_reg(cx, b_r, 64)?;

    // Enforce b != 0
    let zero_b = cx.alloc()?;
    cx.b.push(Op::Const {
        dst: zero_b,
        imm: 0,
    });

    let eq_b0 = cx.alloc()?;
    cx.b.push(Op::Eq {
        dst: eq_b0,
        a: b_r,
        b: zero_b,
    });

    cx.free_reg(zero_b);

    let one_b = cx.alloc()?;
    cx.b.push(Op::Const { dst: one_b, imm: 1 });

    let cond_b = cx.alloc()?;
    cx.b.push(Op::Sub {
        dst: cond_b,
        a: one_b,
        b: eq_b0,
    });

    cx.free_reg(one_b);

    let assert_b_nz = cx.alloc()?;
    cx.b.push(Op::Assert {
        dst: assert_b_nz,
        c: cond_b,
    });

    cx.free_reg(eq_b0);
    cx.free_reg(cond_b);
    cx.free_reg(assert_b_nz);

    // produce q,r in two regs
    let rq = cx.alloc()?;
    let rr = cx.alloc()?;
    cx.b.push(Op::DivMod {
        dst_q: rq,
        dst_r: rr,
        a: a_r,
        b: b_r,
    });

    // r = a - q*b
    let qmulb = cx.alloc()?;
    cx.b.push(Op::Mul {
        dst: qmulb,
        a: rq,
        b: b_r,
    });

    // Range constraints on remainder
    assert_range_bits_for_reg(cx, rr, 64)?;

    // Enforce a = b*q + r first,
    // while qmulb is alive.
    let sum1 = cx.alloc()?;
    cx.b.push(Op::Add {
        dst: sum1,
        a: qmulb,
        b: rr,
    });

    let eq = cx.alloc()?;
    cx.b.push(Op::Eq {
        dst: eq,
        a: sum1,
        b: a_r,
    });

    let assert_eq = cx.alloc()?;
    cx.b.push(Op::Assert {
        dst: assert_eq,
        c: eq,
    });

    // Free equality temps and qmulb
    cx.free_reg(sum1);
    cx.free_reg(eq);
    cx.free_reg(assert_eq);
    cx.free_reg(qmulb);

    // Enforce r < b via t = b - r;
    // t in u64 and t != 0
    let t = cx.alloc()?;
    cx.b.push(Op::Sub {
        dst: t,
        a: b_r,
        b: rr,
    });

    assert_range_bits_for_reg(cx, t, 64)?;

    // Assert t != 0 with minimal live regs
    let zero = cx.alloc()?;
    cx.b.push(Op::Const { dst: zero, imm: 0 });

    let eq_t0 = cx.alloc()?;
    cx.b.push(Op::Eq {
        dst: eq_t0,
        a: t,
        b: zero,
    });

    cx.free_reg(zero);

    let one = cx.alloc()?;
    cx.b.push(Op::Const { dst: one, imm: 1 });

    let cond = cx.alloc()?;
    cx.b.push(Op::Sub {
        dst: cond,
        a: one,
        b: eq_t0,
    });

    cx.free_reg(one);

    let assert_ok = cx.alloc()?;
    cx.b.push(Op::Assert {
        dst: assert_ok,
        c: cond,
    });

    // Free temps (keep rq; drop rr)
    cx.free_reg(eq_t0);
    cx.free_reg(cond);
    cx.free_reg(assert_ok);
    cx.free_reg(rr);
    cx.free_reg(t);

    // Free inputs if owned locally
    free_if_owned(cx, a);
    free_if_owned(cx, b);

    Ok(RVal::Owned(rq))
}

// (divmod-r a b) -> a % b
fn lower_divmod_r(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 2 {
        return Err(Error::InvalidForm("divmod-r".into()));
    }

    let av = lower_expr(cx, rest[0].clone())?;
    let bv = lower_expr(cx, rest[1].clone())?;

    let a = av.into_owned(cx)?;
    let b = bv.into_owned(cx)?;

    // Enforce inputs in u64
    let a_r = cx.val_reg(&a)?;
    let b_r = cx.val_reg(&b)?;

    assert_range_bits_for_reg(cx, a_r, 64)?;
    assert_range_bits_for_reg(cx, b_r, 64)?;

    // Enforce b != 0
    let zero_b = cx.alloc()?;
    cx.b.push(Op::Const {
        dst: zero_b,
        imm: 0,
    });

    let eq_b0 = cx.alloc()?;
    cx.b.push(Op::Eq {
        dst: eq_b0,
        a: b_r,
        b: zero_b,
    });

    cx.free_reg(zero_b);

    let one_b = cx.alloc()?;
    cx.b.push(Op::Const { dst: one_b, imm: 1 });

    let cond_b = cx.alloc()?;
    cx.b.push(Op::Sub {
        dst: cond_b,
        a: one_b,
        b: eq_b0,
    });

    cx.free_reg(one_b);

    let assert_b_nz = cx.alloc()?;
    cx.b.push(Op::Assert {
        dst: assert_b_nz,
        c: cond_b,
    });

    cx.free_reg(eq_b0);
    cx.free_reg(cond_b);
    cx.free_reg(assert_b_nz);

    // produce q,r in two regs
    let rq = cx.alloc()?;
    let rr = cx.alloc()?;
    cx.b.push(Op::DivMod {
        dst_q: rq,
        dst_r: rr,
        a: a_r,
        b: b_r,
    });

    let qmulb = cx.alloc()?;
    cx.b.push(Op::Mul {
        dst: qmulb,
        a: rq,
        b: b_r,
    });

    // Range constraints and r < b
    assert_range_bits_for_reg(cx, rr, 64)?;

    // Enforce a = b*q + r first (mulb is alive)
    let sum1 = cx.alloc()?;
    cx.b.push(Op::Add {
        dst: sum1,
        a: qmulb,
        b: rr,
    });

    let eq = cx.alloc()?;
    cx.b.push(Op::Eq {
        dst: eq,
        a: sum1,
        b: a_r,
    });

    let assert_eq = cx.alloc()?;
    cx.b.push(Op::Assert {
        dst: assert_eq,
        c: eq,
    });

    cx.free_reg(sum1);
    cx.free_reg(eq);
    cx.free_reg(assert_eq);
    cx.free_reg(qmulb);

    let t = cx.alloc()?;
    cx.b.push(Op::Sub {
        dst: t,
        a: b_r,
        b: rr,
    });

    assert_range_bits_for_reg(cx, t, 64)?;

    let zero = cx.alloc()?;
    cx.b.push(Op::Const { dst: zero, imm: 0 });

    let eq_t0 = cx.alloc()?;
    cx.b.push(Op::Eq {
        dst: eq_t0,
        a: t,
        b: zero,
    });

    cx.free_reg(zero);

    let one = cx.alloc()?;
    cx.b.push(Op::Const { dst: one, imm: 1 });

    let cond = cx.alloc()?;
    cx.b.push(Op::Sub {
        dst: cond,
        a: one,
        b: eq_t0,
    });

    cx.free_reg(one);

    let assert_ok = cx.alloc()?;
    cx.b.push(Op::Assert {
        dst: assert_ok,
        c: cond,
    });

    // Free temps (keep rr)
    cx.free_reg(eq_t0);
    cx.free_reg(cond);
    cx.free_reg(assert_ok);
    cx.free_reg(t);

    // Free inputs and q
    cx.free_reg(rq);

    free_if_owned(cx, a);
    free_if_owned(cx, b);

    Ok(RVal::Owned(rr))
}

// (mulwide-hi a b) -> upper 64 bits of a*b
fn lower_mulwide_hi(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 2 {
        return Err(Error::InvalidForm("mulwide-hi".into()));
    }

    let av = lower_expr(cx, rest[0].clone())?;
    let bv = lower_expr(cx, rest[1].clone())?;

    let a = av.into_owned(cx)?;
    let b = bv.into_owned(cx)?;

    // inputs in u64
    let a_r = cx.val_reg(&a)?;
    let b_r = cx.val_reg(&b)?;

    assert_range_bits_for_reg(cx, a_r, 64)?;
    assert_range_bits_for_reg(cx, b_r, 64)?;

    // produce hi/lo in two regs
    let rhi = cx.alloc()?;
    let rlo = cx.alloc()?;

    cx.b.push(Op::MulWide {
        dst_hi: rhi,
        dst_lo: rlo,
        a: a_r,
        b: b_r,
    });

    free_if_owned(cx, a);
    free_if_owned(cx, b);

    // outputs in u64
    assert_range_bits_for_reg(cx, rhi, 64)?;
    assert_range_bits_for_reg(cx, rlo, 64)?;

    cx.free_reg(rlo);

    Ok(RVal::Owned(rhi))
}

// (mulwide-lo a b) -> lower 64 bits of a*b
fn lower_mulwide_lo(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 2 {
        return Err(Error::InvalidForm("mulwide-lo".into()));
    }

    let av = lower_expr(cx, rest[0].clone())?;
    let bv = lower_expr(cx, rest[1].clone())?;

    let a = av.into_owned(cx)?;
    let b = bv.into_owned(cx)?;

    // inputs in u64
    let a_r = cx.val_reg(&a)?;
    let b_r = cx.val_reg(&b)?;

    assert_range_bits_for_reg(cx, a_r, 64)?;
    assert_range_bits_for_reg(cx, b_r, 64)?;

    // produce hi/lo in two regs
    let rhi = cx.alloc()?;
    let rlo = cx.alloc()?;

    cx.b.push(Op::MulWide {
        dst_hi: rhi,
        dst_lo: rlo,
        a: a_r,
        b: b_r,
    });

    free_if_owned(cx, a);
    free_if_owned(cx, b);

    // outputs in u64
    assert_range_bits_for_reg(cx, rhi, 64)?;
    assert_range_bits_for_reg(cx, rlo, 64)?;

    cx.free_reg(rhi);

    Ok(RVal::Owned(rlo))
}

// (muldiv a b c) -> floor((a*b)/c)
fn lower_muldiv_floor(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 3 {
        return Err(Error::InvalidForm("muldiv".into()));
    }

    let av = lower_expr(cx, rest[0].clone())?;
    let bv = lower_expr(cx, rest[1].clone())?;
    let cv = lower_expr(cx, rest[2].clone())?;

    let a = av.into_owned(cx)?;
    let b = bv.into_owned(cx)?;
    let c = cv.into_owned(cx)?;

    // Enforce inputs in u64
    let a_r = cx.val_reg(&a)?;
    let b_r = cx.val_reg(&b)?;
    let c_r = cx.val_reg(&c)?;

    assert_range_bits_for_reg(cx, a_r, 64)?;
    assert_range_bits_for_reg(cx, b_r, 64)?;
    assert_range_bits_for_reg(cx, c_r, 64)?;

    // Wide multiply
    let rhi = cx.alloc()?;
    let rlo = cx.alloc()?;
    cx.b.push(Op::MulWide {
        dst_hi: rhi,
        dst_lo: rlo,
        a: a_r,
        b: b_r,
    });

    free_if_owned(cx, a);
    free_if_owned(cx, b);

    // 128/64 division -> q,r
    let rq = cx.alloc()?;
    let rr = cx.alloc()?;
    cx.b.push(Op::DivMod128 {
        a_hi: rhi,
        a_lo: rlo,
        b: c_r,
        dst_q: rq,
        dst_r: rr,
    });

    // Outputs in u64
    assert_range_bits_for_reg(cx, rq, 64)?;
    assert_range_bits_for_reg(cx, rr, 64)?;

    free_if_owned(cx, c);

    cx.free_reg(rhi);
    cx.free_reg(rlo);
    cx.free_reg(rr);

    Ok(RVal::Owned(rq))
}

fn lower_seq(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 2 {
        return Err(Error::InvalidForm("seq".into()));
    }

    let a = lower_expr(cx, rest[0].clone())?;

    free_if_owned(cx, a);

    let b = lower_expr(cx, rest[1].clone())?;

    Ok(b)
}

fn lower_load(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 1 {
        return Err(Error::InvalidForm("load".into()));
    }

    let addr = lower_expr(cx, rest[0].clone())?;
    let addr = addr.into_owned(cx)?;
    let dst = cx.alloc()?;

    cx.b.push(Op::Load {
        dst,
        addr: cx.val_reg(&addr)?,
    });

    // free temp address
    free_if_owned(cx, addr);

    Ok(RVal::Owned(dst))
}

fn lower_store(cx: &mut LowerCtx, rest: &[Ast]) -> Result<(), Error> {
    if rest.len() != 2 {
        return Err(Error::InvalidForm("store".into()));
    }

    let addr = lower_expr(cx, rest[0].clone())?;
    let val = lower_expr(cx, rest[1].clone())?;

    let addr = addr.into_owned(cx)?;
    let val = val.into_owned(cx)?;

    cx.b.push(Op::Store {
        addr: cx.val_reg(&addr)?,
        src: cx.val_reg(&val)?,
    });

    free_if_owned(cx, addr);
    free_if_owned(cx, val);

    Ok(())
}

// Lower (load-ca leaf ((d0 s0) (d1 s1) ...)) -> leaf value;
// Verifies membership by binding
// last-level root to PI via MerkleStepLast.
fn lower_load_ca(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 2 {
        return Err(Error::InvalidForm("load-ca".into()));
    }

    let leaf = lower_expr(cx, rest[0].clone())?;
    let leaf = leaf.into_owned(cx)?;

    // list of (dir sib)
    let path_list = match &rest[1] {
        Ast::List(items) => items,
        _ => return Err(Error::InvalidForm("load-ca: path".into())),
    };

    if path_list.is_empty() {
        return Err(Error::InvalidForm("load-ca: empty path".into()));
    }

    // first step
    let (dir0_reg, sib0_reg) = parse_dir_sib_pair(cx, &path_list[0])?;
    cx.b.push(Op::MerkleStepFirst {
        leaf_reg: cx.val_reg(&leaf)?,
        dir_reg: dir0_reg,
        sib_reg: sib0_reg,
    });

    cx.free_reg(dir0_reg);
    cx.free_reg(sib0_reg);

    for pair in path_list
        .iter()
        .skip(1)
        .take(path_list.len().saturating_sub(2))
    {
        let (dir_r, sib_r) = parse_dir_sib_pair(cx, pair)?;
        cx.b.push(Op::MerkleStep {
            dir_reg: dir_r,
            sib_reg: sib_r,
        });

        cx.free_reg(dir_r);
        cx.free_reg(sib_r);
    }

    // last step binds
    // acc to PI root
    if path_list.len() > 1 {
        let (dir_l, sib_l) = parse_dir_sib_pair(cx, path_list.last().unwrap())?;
        cx.b.push(Op::MerkleStepLast {
            dir_reg: dir_l,
            sib_reg: sib_l,
        });

        cx.free_reg(dir_l);
        cx.free_reg(sib_l);
    }

    Ok(leaf)
}

// Lower (store-ca new_leaf ((d0 s0) (d1 s1) ...)) -> 0;
// acc holds new_root.
fn lower_store_ca(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    if rest.len() != 2 {
        return Err(Error::InvalidForm("store-ca".into()));
    }

    let leaf = lower_expr(cx, rest[0].clone())?;
    let leaf = leaf.into_owned(cx)?;

    let path_list = match &rest[1] {
        Ast::List(items) => items,
        _ => return Err(Error::InvalidForm("store-ca: path".into())),
    };

    if path_list.is_empty() {
        return Err(Error::InvalidForm("store-ca: empty path".into()));
    }

    let (dir0_reg, sib0_reg) = parse_dir_sib_pair(cx, &path_list[0])?;
    cx.b.push(Op::MerkleStepFirst {
        leaf_reg: cx.val_reg(&leaf)?,
        dir_reg: dir0_reg,
        sib_reg: sib0_reg,
    });

    cx.free_reg(dir0_reg);
    cx.free_reg(sib0_reg);

    // rest; no Last at the end
    // to avoid binding to PI root.
    for pair in path_list.iter().skip(1) {
        let (dir_r, sib_r) = parse_dir_sib_pair(cx, pair)?;
        cx.b.push(Op::MerkleStep {
            dir_reg: dir_r,
            sib_reg: sib_r,
        });

        cx.free_reg(dir_r);
        cx.free_reg(sib_r);
    }

    // free temp leaf
    cx.free_reg(cx.val_reg(&leaf)?);

    Ok(RVal::Imm(0))
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

fn u64_pair_from_le_16(b16: &[u8]) -> (u64, u64) {
    debug_assert!(b16.len() == 16);

    let mut lo8 = [0u8; 8];
    let mut hi8 = [0u8; 8];
    lo8.copy_from_slice(&b16[0..8]);
    hi8.copy_from_slice(&b16[8..16]);

    (u64::from_le_bytes(lo8), u64::from_le_bytes(hi8))
}

#[inline]
fn free_if_owned(cx: &mut LowerCtx, v: RVal) {
    if let RVal::Owned(r) = v {
        cx.free_reg(r);
    }
}

fn assert_range_bits_for_reg(cx: &mut LowerCtx, r: u8, bits: u8) -> Result<(), Error> {
    match bits {
        32 => {
            let dst = cx.alloc()?;
            cx.b.push(Op::AssertRange { dst, r, bits: 32 });

            cx.free_reg(dst);
        }
        64 => {
            let dst = cx.alloc()?;
            cx.b.push(Op::AssertRangeLo { dst, r });
            cx.b.push(Op::AssertRangeHi { dst, r });

            cx.free_reg(dst);
        }
        _ => {
            return Err(Error::InvalidForm(
                "assert-range: bits must be 32 or 64".into(),
            ));
        }
    }

    Ok(())
}

fn parse_dir_sib_pair(cx: &mut LowerCtx, pair: &Ast) -> Result<(u8, u8), Error> {
    let Ast::List(items) = pair else {
        return Err(Error::InvalidForm("path: pair".into()));
    };

    if items.len() != 2 {
        return Err(Error::InvalidForm("path: pair arity".into()));
    }

    let dir = lower_expr(cx, items[0].clone())?.into_owned(cx)?;
    let sib = lower_expr(cx, items[1].clone())?.into_owned(cx)?;

    Ok((cx.val_reg(&dir)?, cx.val_reg(&sib)?))
}

use std::collections::{BTreeMap, VecDeque};
use thiserror::Error;

use crate::ir::{Op, Program, ProgramBuilder};
use crate::layout::NR;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ast {
    Atom(Atom),
    List(Vec<Ast>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Atom {
    Int(u64),
    Sym(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Tok {
    LParen,
    RParen,
    Int(u64),
    Sym(String),
    Eof,
}

enum BinOp {
    Add,
    Sub,
    Mul,
}

#[derive(Debug, Error)]
pub enum Error {
    #[error("lex: invalid char '{0}' at {1}")]
    Lex(char, usize),
    #[error("parse: unexpected EOF")]
    Eof,
    #[error("parse: unexpected token")]
    Unexpected,
    #[error("parse: unmatched ')'")]
    Unmatched,
    #[error("lower: unknown symbol '{0}'")]
    UnknownSymbol(String),
    #[error("lower: regs exhausted (need {need}, have {have})")]
    RegOverflow { need: usize, have: usize },
    #[error("lower: invalid form '{0}'")]
    InvalidForm(String),
    #[error("lower: invalid kv-step dir '{0}' (expected 0 or 1)")]
    InvalidDir(u64),
}

#[derive(Default, Debug, Clone)]
struct Env {
    // variable -> register
    vars: BTreeMap<String, u8>,
    // function name -> (params, body)
    funs: BTreeMap<String, (Vec<String>, Ast)>,
}

impl Env {}

#[derive(Debug)]
struct LowerCtx<'a> {
    b: ProgramBuilder,
    free: Vec<u8>,
    env: Env,
    _m: core::marker::PhantomData<&'a ()>,
}

impl<'a> LowerCtx<'a> {
    fn new() -> Self {
        let free: Vec<u8> = (0u8..NR as u8).collect();

        // simple stack: pop() to allocate from
        // the end gives small regs first.
        Self {
            b: ProgramBuilder::new(),
            free,
            env: Env::default(),
            _m: core::marker::PhantomData,
        }
    }

    fn alloc(&mut self) -> Result<u8, Error> {
        self.free
            .pop()
            .ok_or(Error::RegOverflow { need: 1, have: 0 })
    }

    fn free_reg(&mut self, r: u8) {
        self.free.push(r);
    }

    fn map_var(&mut self, name: &str, r: u8) {
        self.env.vars.insert(name.to_string(), r);
    }

    fn get_var(&self, name: &str) -> Result<u8, Error> {
        self.env
            .vars
            .get(name)
            .copied()
            .ok_or_else(|| Error::UnknownSymbol(name.to_string()))
    }

    fn define_fun(&mut self, name: &str, params: Vec<String>, body: Ast) {
        self.env.funs.insert(name.to_string(), (params, body));
    }

    fn get_fun(&self, name: &str) -> Option<&(Vec<String>, Ast)> {
        self.env.funs.get(name)
    }
}

pub fn compile_str(src: &str) -> Result<Program, Error> {
    let toks = lex(src)?;
    let forms = parse(&toks)?;
    let mut cx = LowerCtx::new();

    for f in forms {
        lower_top(&mut cx, f)?;
    }

    cx.b.push(Op::End);

    Ok(cx.b.finalize())
}

// Lexer
fn lex(src: &str) -> Result<Vec<Tok>, Error> {
    let mut out = Vec::new();
    let mut it = src.chars().peekable();
    let mut i = 0usize;

    while let Some(&ch) = it.peek() {
        match ch {
            '(' => {
                out.push(Tok::LParen);
                it.next();

                i += 1;
            }
            ')' => {
                out.push(Tok::RParen);
                it.next();

                i += 1;
            }
            ' ' | '\n' | '\r' | '\t' => {
                it.next();
                i += 1;
            }
            '0'..='9' => {
                let mut s = String::new();
                while let Some(&c2) = it.peek() {
                    if c2.is_ascii_digit() {
                        s.push(c2);
                        it.next();

                        i += 1;
                    } else {
                        break;
                    }
                }

                let v = s.parse::<u64>().unwrap();
                out.push(Tok::Int(v));
            }
            _ => {
                if is_sym_start(ch) {
                    let mut s = String::new();
                    while let Some(&c2) = it.peek() {
                        if is_sym_continue(c2) {
                            s.push(c2);
                            it.next();

                            i += 1;
                        } else {
                            break;
                        }
                    }

                    out.push(Tok::Sym(s));
                } else {
                    return Err(Error::Lex(ch, i));
                }
            }
        }
    }

    out.push(Tok::Eof);

    Ok(out)
}

fn is_sym_start(c: char) -> bool {
    matches!(c, 'a'..='z' | 'A'..='Z' | '_' | '+' | '-' | '*' | '=' | '<' | '>' )
}

fn is_sym_continue(c: char) -> bool {
    is_sym_start(c) || matches!(c, '0'..='9' | '/' | ':')
}

// Parser: program := forms*
fn parse(tokens: &[Tok]) -> Result<Vec<Ast>, Error> {
    let mut q: VecDeque<Tok> = tokens.to_vec().into();
    let mut forms = Vec::new();

    while let Some(t) = q.front() {
        match t {
            Tok::Eof => break,
            _ => forms.push(parse_one(&mut q)?),
        }
    }

    Ok(forms)
}

fn parse_one(q: &mut VecDeque<Tok>) -> Result<Ast, Error> {
    let t = q.pop_front().ok_or(Error::Eof)?;
    match t {
        Tok::LParen => {
            let mut items = Vec::new();
            loop {
                match q.front() {
                    Some(Tok::RParen) => {
                        q.pop_front();
                        break;
                    }
                    Some(Tok::Eof) => return Err(Error::Eof),
                    _ => items.push(parse_one(q)?),
                }
            }

            Ok(Ast::List(items))
        }
        Tok::RParen => Err(Error::Unmatched),
        Tok::Int(v) => Ok(Ast::Atom(Atom::Int(v))),
        Tok::Sym(s) => Ok(Ast::Atom(Atom::Sym(s))),
        Tok::Eof => Err(Error::Eof),
    }
}

fn lower_top(cx: &mut LowerCtx, ast: Ast) -> Result<(), Error> {
    match ast {
        Ast::List(ref items) if !items.is_empty() => {
            match &items[0] {
                Ast::Atom(Atom::Sym(s)) if s == "def" => lower_def(cx, &items[1..]),
                _ => {
                    // treat as expression; compute and discard
                    let r = lower_expr(cx, ast)?;
                    cx.free_reg(r);

                    Ok(())
                }
            }
        }
        _ => {
            // expression or atom; compute and drop
            let r = lower_expr(cx, ast)?;
            cx.free_reg(r);

            Ok(())
        }
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

fn lower_expr(cx: &mut LowerCtx, ast: Ast) -> Result<u8, Error> {
    match ast {
        Ast::Atom(Atom::Int(v)) => {
            let r = cx.alloc()?;
            cx.b.push(Op::Const { dst: r, imm: v });

            Ok(r)
        }
        Ast::Atom(Atom::Sym(s)) => cx.get_var(&s),
        Ast::List(items) if !items.is_empty() => match &items[0] {
            Ast::Atom(Atom::Sym(s)) if s == "let" => lower_let(cx, &items[1..]),
            Ast::Atom(Atom::Sym(s)) if s == "select" => lower_select(cx, &items[1..]),
            Ast::Atom(Atom::Sym(s)) if s == "+" => lower_bin(cx, &items[1..], BinOp::Add),
            Ast::Atom(Atom::Sym(s)) if s == "-" => lower_bin(cx, &items[1..], BinOp::Sub),
            Ast::Atom(Atom::Sym(s)) if s == "*" => lower_bin(cx, &items[1..], BinOp::Mul),
            Ast::Atom(Atom::Sym(s)) if s == "neg" => lower_neg(cx, &items[1..]),
            Ast::Atom(Atom::Sym(s)) if s == "=" => lower_eq(cx, &items[1..]),
            Ast::Atom(Atom::Sym(s)) if s == "hash2" => lower_hash2(cx, &items[1..]),
            Ast::Atom(Atom::Sym(s)) if s == "kv-step" => {
                lower_kv_step(cx, &items[1..]).map(|_| cx.get_var("_kv_last").unwrap_or(0))
            }
            Ast::Atom(Atom::Sym(s)) if s == "kv-final" => {
                lower_kv_final(cx, &items[1..]).map(|_| cx.get_var("_kv_last").unwrap_or(0))
            }
            Ast::Atom(Atom::Sym(name)) => {
                // user function call: (f a b ...)
                lower_call(cx, name, &items[1..])
            }
            _ => Err(Error::InvalidForm("expr".into())),
        },
        _ => Err(Error::InvalidForm("atom".into())),
    }
}

fn lower_let(cx: &mut LowerCtx, rest: &[Ast]) -> Result<u8, Error> {
    // (let ((x expr) (y expr)) body)
    if rest.is_empty() {
        return Err(Error::InvalidForm("let".into()));
    }

    let binds = match &rest[0] {
        Ast::List(pairs) => pairs,
        _ => return Err(Error::InvalidForm("let: binds".into())),
    };

    let mut saved: Vec<(String, Option<u8>)> = Vec::new();
    for b in binds {
        match b {
            Ast::List(kv) if kv.len() == 2 => {
                let name = match &kv[0] {
                    Ast::Atom(Atom::Sym(s)) => s.clone(),
                    _ => return Err(Error::InvalidForm("let: name".into())),
                };
                let r = lower_expr(cx, kv[1].clone())?;

                saved.push((name.clone(), cx.env.vars.get(&name).copied()));
                cx.map_var(&name, r);
            }
            _ => return Err(Error::InvalidForm("let: pair".into())),
        }
    }

    // body = last expr or (body ...)
    let body_ast = rest
        .get(1)
        .cloned()
        .ok_or_else(|| Error::InvalidForm("let: body".into()))?;
    let res = lower_expr(cx, body_ast)?;

    // cleanup: free all let-bound regs
    // except result (if referenced by name).
    for (name, prior) in saved.into_iter().rev() {
        let r = cx.env.vars.remove(&name).unwrap();
        if let Some(p) = prior {
            cx.env.vars.insert(name, p);
        } else if r != res {
            cx.free_reg(r);
        }
    }

    Ok(res)
}

fn lower_select(cx: &mut LowerCtx, rest: &[Ast]) -> Result<u8, Error> {
    if rest.len() != 3 {
        return Err(Error::InvalidForm("select".into()));
    }

    let c = lower_expr(cx, rest[0].clone())?;
    let a = lower_expr(cx, rest[1].clone())?;
    let b = lower_expr(cx, rest[2].clone())?;

    let dst = cx.alloc()?;
    cx.b.push(Op::Select { dst, c, a, b });

    // free temps (keep dst)
    cx.free_reg(c);
    cx.free_reg(a);
    cx.free_reg(b);

    Ok(dst)
}

fn lower_bin(cx: &mut LowerCtx, rest: &[Ast], op: BinOp) -> Result<u8, Error> {
    if rest.len() != 2 {
        return Err(Error::InvalidForm("bin".into()));
    }

    let a = lower_expr(cx, rest[0].clone())?;
    let b = lower_expr(cx, rest[1].clone())?;

    let dst = cx.alloc()?;
    match op {
        BinOp::Add => cx.b.push(Op::Add { dst, a, b }),
        BinOp::Sub => cx.b.push(Op::Sub { dst, a, b }),
        BinOp::Mul => cx.b.push(Op::Mul { dst, a, b }),
    }

    cx.free_reg(a);
    cx.free_reg(b);

    Ok(dst)
}

fn lower_neg(cx: &mut LowerCtx, rest: &[Ast]) -> Result<u8, Error> {
    if rest.len() != 1 {
        return Err(Error::InvalidForm("neg".into()));
    }

    let a = lower_expr(cx, rest[0].clone())?;
    let dst = cx.alloc()?;

    cx.b.push(Op::Neg { dst, a });
    cx.free_reg(a);

    Ok(dst)
}

fn lower_eq(cx: &mut LowerCtx, rest: &[Ast]) -> Result<u8, Error> {
    if rest.len() != 2 {
        return Err(Error::InvalidForm("=".into()));
    }
    let a = lower_expr(cx, rest[0].clone())?;
    let b = lower_expr(cx, rest[1].clone())?;
    let dst = cx.alloc()?;

    cx.b.push(Op::Eq { dst, a, b });
    cx.free_reg(a);
    cx.free_reg(b);

    Ok(dst)
}

fn lower_hash2(cx: &mut LowerCtx, rest: &[Ast]) -> Result<u8, Error> {
    if rest.len() != 2 {
        return Err(Error::InvalidForm("hash2".into()));
    }
    let a = lower_expr(cx, rest[0].clone())?;
    let b = lower_expr(cx, rest[1].clone())?;
    let dst = cx.alloc()?;

    cx.b.push(Op::Hash2 { dst, a, b });
    cx.free_reg(a);
    cx.free_reg(b);

    Ok(dst)
}

fn lower_kv_step(cx: &mut LowerCtx, rest: &[Ast]) -> Result<u8, Error> {
    // (kv-step dir sib)
    if rest.len() != 2 {
        return Err(Error::InvalidForm("kv-step".into()));
    }

    let dir = match &rest[0] {
        Ast::Atom(Atom::Int(v)) => *v,
        _ => return Err(Error::InvalidForm("kv-step: dir".into())),
    };

    if dir > 1 {
        return Err(Error::InvalidDir(dir));
    }

    let sib_r = lower_expr(cx, rest[1].clone())?;
    cx.b.push(Op::KvMap {
        dir: dir as u32,
        sib_reg: sib_r,
    });

    // remember last sib reg
    // for potential chaining
    cx.map_var("_kv_last", sib_r);

    Ok(sib_r)
}

fn lower_kv_final(cx: &mut LowerCtx, rest: &[Ast]) -> Result<u8, Error> {
    if !rest.is_empty() {
        return Err(Error::InvalidForm("kv-final".into()));
    }

    cx.b.push(Op::KvFinal);

    // returns dummy reg 0 if not present;
    // the op itself writes KV columns
    Ok(*cx.env.vars.get("_kv_last").unwrap_or(&0))
}

fn lower_call(cx: &mut LowerCtx, name: &str, args: &[Ast]) -> Result<u8, Error> {
    let (params, body) = cx
        .get_fun(name)
        .cloned()
        .ok_or_else(|| Error::UnknownSymbol(name.to_string()))?;

    if params.len() != args.len() {
        return Err(Error::InvalidForm(format!(
            "call: {} expects {} args",
            name,
            params.len()
        )));
    }

    // evaluate args
    let mut arg_regs = Vec::with_capacity(args.len());
    for a in args {
        arg_regs.push(lower_expr(cx, a.clone())?);
    }

    // Create new bindings for params
    let mut saved: Vec<(String, Option<u8>)> = Vec::new();
    for (p, r) in params.iter().zip(arg_regs.iter().copied()) {
        saved.push((p.clone(), cx.env.vars.get(p).copied()));
        cx.map_var(p, r);
    }

    let res = lower_expr(cx, body.clone())?;

    // cleanup param bindings: do not free res reg here (caller decides)
    for (p, prior) in saved.into_iter().rev() {
        let r = cx.env.vars.remove(&p).unwrap();

        if let Some(pr) = prior {
            cx.env.vars.insert(p, pr);
        }

        if r != res {
            cx.free_reg(r);
        }
    }

    Ok(res)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_atoms_lists() {
        let s = "(add 1 2) (neg 3)";
        let toks = lex(s).unwrap();
        let ast = parse(&toks).unwrap();
        assert_eq!(ast.len(), 2);
    }

    #[test]
    fn lower_arith_and_select() {
        let src = "(def (add2 x y) (+ x y)) (let ((a 7) (b 9)) (select (= a b) (add2 a b) 0))";
        let p = compile_str(src).unwrap();
        assert!(!p.ops.is_empty());
    }

    #[test]
    fn lower_hash2_and_kv() {
        let src = "(let ((x 1) (y 2)) (hash2 x y)) (kv-step 0 7) (kv-final)";
        let p = compile_str(src).unwrap();
        assert!(p.ops.iter().any(|op| matches!(op, Op::Hash2 { .. })));
        assert!(p.ops.iter().any(|op| matches!(op, Op::KvMap { .. })));
        assert!(p.ops.iter().any(|op| matches!(op, Op::KvFinal)));
    }
}

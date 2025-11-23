// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Backend-agnostic compiler for the zk-lisp DSL.
//!
//! This crate lexes, parses and lowers zk-lisp source into a
//! compact VM instruction sequence with a Blake3 commitment.
//! It intentionally knows nothing about proof systems or trace
//! layout so it can be reused by multiple proving backends.

mod lower;
mod metrics;
mod schema;

pub mod builder;

pub use metrics::CompilerMetrics;
pub use schema::{ArgRole, FnTypeSchema, LetTypeSchema, ScalarType, TypeSchemas};

use crate::builder::{Op, ProgramBuilder};

use lower::{Ast, Atom, LowerCtx, Tok};
use std::collections::VecDeque;
use thiserror::Error;
use tracing::{debug, instrument};

const MAX_TOKENS: usize = 200_000;
const MAX_PARSE_DEPTH: usize = 1_024;

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
    #[error("lower: recursion detected in call '{0}'")]
    Recursion(String),
    #[error("limit: {0}")]
    Limit(&'static str),
}

#[derive(Clone, Debug)]
pub struct BlockMeta {
    pub level_start: u32,
    pub level_len: u32,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub commitment: [u8; 32],
    pub ops: Vec<Op>,
    pub reg_count: u8,
    pub out_reg: u8,
    pub out_row: u32,
    pub compiler_metrics: CompilerMetrics,
    pub type_schemas: TypeSchemas,
    pub blocks: Vec<BlockMeta>,
}

impl Program {
    pub fn new(
        commitment: [u8; 32],
        ops: Vec<Op>,
        reg_count: u8,
        compiler_metrics: CompilerMetrics,
        type_schemas: TypeSchemas,
        blocks: Vec<BlockMeta>,
    ) -> Self {
        Self {
            ops,
            reg_count,
            commitment,
            out_reg: 0,
            out_row: 0,
            compiler_metrics,
            type_schemas,
            blocks,
        }
    }
}

#[instrument(level = "info", skip(src))]
pub fn compile_str(src: &str) -> Result<Program, Error> {
    let toks = lex(src)?;
    debug!(toks_len = toks.len(), "lexed");

    let forms = parse(&toks)?;
    debug!(forms = forms.len(), "parsed");

    let mut metrics = CompilerMetrics::default();
    let mut builder = ProgramBuilder::new();

    {
        let mut cx = LowerCtx::new(&mut builder, &mut metrics);
        for f in forms {
            lower::lower_top(&mut cx, f)?;
        }
    }

    builder.push(Op::End);

    let program = builder.finalize(metrics)?;

    debug!(
        ops = program.ops.len(),
        reg_count = program.reg_count,
        peak_live = program.compiler_metrics.peak_live,
        "lowered"
    );

    Ok(program)
}

// Compile main
#[instrument(level = "info", skip(src, args))]
pub fn compile_entry(src: &str, args: &[u64]) -> Result<Program, Error> {
    let toks = lex(src)?;
    debug!(toks_len = toks.len(), "lexed");

    let forms = parse(&toks)?;
    debug!(forms = forms.len(), "parsed");

    // discover main signature
    let mut main_args: Option<usize> = None;
    for f in &forms {
        if let Ast::List(items) = f {
            if items.is_empty() {
                continue;
            }

            if let Ast::Atom(Atom::Sym(h)) = &items[0] {
                if h == "def" {
                    if let Some(Ast::List(hh)) = items.get(1) {
                        if let Some(Ast::Atom(Atom::Sym(name))) = hh.first() {
                            if name == "main" {
                                main_args = Some(hh.len().saturating_sub(1));
                            }
                        }
                    }
                }
            }
        }
    }

    let arity = main_args.ok_or_else(|| Error::InvalidForm("main: not found".into()))?;
    if arity != args.len() {
        return Err(Error::InvalidForm(format!(
            "main expects {} args (got {})",
            arity,
            args.len()
        )));
    }

    // Build (main ARG0 ... ARGN)
    let mut calls: Vec<Ast> = Vec::with_capacity(1 + args.len());
    calls.push(Ast::Atom(Atom::Sym("main".to_string())));

    for &v in args {
        calls.push(Ast::Atom(Atom::Int(v)));
    }

    let call_ast = Ast::List(calls);

    let mut metrics = CompilerMetrics::default();
    let mut builder = ProgramBuilder::new();

    // Lower: first all top-level forms (defs, etc.),
    // then tail-call main and capture its result reg.
    let mut cx = LowerCtx::new(&mut builder, &mut metrics);
    for f in forms {
        lower::lower_top(&mut cx, f)?;
    }

    // Lower (main ...) as expression
    let res_v = lower::lower_expr(&mut cx, call_ast)?;
    let res_v = res_v.into_owned(&mut cx)?;
    let res_reg = match res_v {
        lower::RVal::Owned(r) => r,
        lower::RVal::Borrowed(r) => r,
        lower::RVal::Imm(_) => {
            return Err(Error::InvalidForm(
                "internal: immediate result where register expected".into(),
            ));
        }
    };

    // Normalize main return into r0
    if res_reg != 0 {
        cx.emit_mov(0, res_reg);
    }

    // Drop lowering context
    drop(cx);

    builder.push(Op::End);

    // Finalize program
    let program = builder.finalize(metrics)?;

    debug!(
        ops = program.ops.len(),
        reg_count = program.reg_count,
        out_row = program.out_row,
        peak_live = program.compiler_metrics.peak_live,
        "entry lowered",
    );

    Ok(program)
}

// Lexer
pub fn lex(src: &str) -> Result<Vec<Tok>, Error> {
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
            '\'' => {
                out.push(Tok::Quote);
                it.next();
                i += 1;
            }
            ';' => {
                // Line comment; skip until end of line.
                it.next();
                i += 1;

                while let Some(&c2) = it.peek() {
                    if c2 == '\n' {
                        break;
                    }

                    it.next();
                    i += 1;
                }
            }
            '"' => {
                it.next(); // consume opening quote
                i += 1;

                let mut s = String::new();
                while let Some(&c2) = it.peek() {
                    match c2 {
                        '"' => {
                            it.next();
                            i += 1;

                            break;
                        }
                        '\\' => {
                            it.next();
                            i += 1;

                            let Some(&e) = it.peek() else {
                                return Err(Error::Eof);
                            };
                            match e {
                                '"' => {
                                    s.push('"');
                                    it.next();

                                    i += 1;
                                }
                                '\\' => {
                                    s.push('\\');
                                    it.next();

                                    i += 1;
                                }
                                'n' => {
                                    s.push('\n');
                                    it.next();
                                    i += 1;
                                }
                                'r' => {
                                    s.push('\r');
                                    it.next();
                                    i += 1;
                                }
                                't' => {
                                    s.push('\t');
                                    it.next();
                                    i += 1;
                                }
                                'x' => {
                                    it.next();
                                    i += 1;

                                    let h1 = it.peek().copied().ok_or(Error::Eof)?;
                                    let _ = it.next();
                                    i += 1;

                                    let h2 = it.peek().copied().ok_or(Error::Eof)?;
                                    let _ = it.next();
                                    i += 1;

                                    let parse_hex = |hc: char| -> Option<u8> {
                                        match hc {
                                            '0'..='9' => Some(hc as u8 - b'0'),
                                            'a'..='f' => Some(hc as u8 - b'a' + 10),
                                            'A'..='F' => Some(hc as u8 - b'A' + 10),
                                            _ => None,
                                        }
                                    };

                                    let hi = parse_hex(h1).ok_or(Error::Lex(h1, i))?;
                                    let lo = parse_hex(h2).ok_or(Error::Lex(h2, i))?;
                                    let val = (hi << 4) | lo;

                                    s.push(val as char);
                                }
                                other => return Err(Error::Lex(other, i)),
                            }
                        }
                        c => {
                            s.push(c);
                            it.next();
                            i += 1;
                        }
                    }
                }

                out.push(Tok::Str(s));
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

                let v = s.parse::<u64>().map_err(|_| Error::Lex(ch, i))?;
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

    if out.len() > MAX_TOKENS {
        return Err(Error::Limit("too many tokens"));
    }

    out.push(Tok::Eof);

    Ok(out)
}

pub fn is_sym_start(c: char) -> bool {
    matches!(c, 'a'..='z' | 'A'..='Z' | '_' | '+' | '-' | '*' | '=' | '<' | '>' | ':' )
}

pub fn is_sym_continue(c: char) -> bool {
    is_sym_start(c) || matches!(c, '0'..='9' | '/' | ':' | '?')
}

// Parser: program := forms*
fn parse(tokens: &[Tok]) -> Result<Vec<Ast>, Error> {
    let mut q: VecDeque<Tok> = tokens.to_vec().into();
    let mut forms = Vec::new();

    while let Some(t) = q.front() {
        match t {
            Tok::Eof => break,
            _ => forms.push(parse_one_limited(&mut q, 0)?),
        }
    }

    Ok(forms)
}

fn parse_one_limited(q: &mut VecDeque<Tok>, depth: usize) -> Result<Ast, Error> {
    if depth > MAX_PARSE_DEPTH {
        return Err(Error::Limit("parse depth exceeded"));
    }

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
                    _ => items.push(parse_one_limited(q, depth + 1)?),
                }
            }

            Ok(Ast::List(items))
        }
        Tok::Quote => {
            // 'X  => (quote X)
            let quoted = parse_one_limited(q, depth + 1)?;
            Ok(Ast::List(vec![
                Ast::Atom(Atom::Sym("quote".to_string())),
                quoted,
            ]))
        }
        Tok::RParen => Err(Error::Unmatched),
        Tok::Int(v) => Ok(Ast::Atom(Atom::Int(v))),
        Tok::Sym(s) => Ok(Ast::Atom(Atom::Sym(s))),
        Tok::Str(s) => Ok(Ast::Atom(Atom::Str(s))),
        Tok::Eof => Err(Error::Eof),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lex_ignores_line_comments() {
        let s = "(def (x) 1)\n;; comment here\n(def (y) 2)";
        let s_no = "(def (x) 1)(def (y) 2)";

        let toks = lex(s).unwrap();
        let toks_no = lex(s_no).unwrap();

        assert_eq!(toks, toks_no);
    }

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
    fn lower_hash2_produces_sponge_ops() {
        let src = "(let ((x 1) (y 2)) (hash2 x y))";
        let p = compile_str(src).unwrap();
        // hash represented via sponge ops SAbsorbN/SSqueeze
        assert!(
            p.ops
                .iter()
                .any(|op| matches!(op, Op::SAbsorbN { .. } | Op::SSqueeze { .. }))
        );
    }

    #[test]
    fn lower_deftype_member() {
        let src = "
            (deftype fruit () '(member apple orange banana))
            (def (main x)
              (if (fruit:is x) x 0))
            (main (fruit:apple))
        ";
        let p = compile_str(src).unwrap();
        // Ensure some ops were generated (ALU + function structure)
        assert!(!p.ops.is_empty());
    }

    #[test]
    fn program_blocks_default_single_block() {
        let src = "(def (main) 0) (main)";
        let p = compile_str(src).unwrap();

        assert_eq!(p.blocks.len(), 1);

        let b = &p.blocks[0];
        assert_eq!(b.level_start, 0);
        assert_eq!(b.level_len, p.ops.len() as u32);
    }

    #[test]
    fn program_blocks_from_block_form() {
        let src = "
            (def (main)
              (block (let ((a 1)) a))
              (block (let ((b 2)) b)))
            (main)
        ";

        let p = compile_str(src).unwrap();
        assert!(!p.ops.is_empty());
        assert!(!p.blocks.is_empty());

        // Blocks must be non-empty
        // and ordered by level_start.
        let mut last_start = 0u32;
        for (i, b) in p.blocks.iter().enumerate() {
            assert!(b.level_len > 0, "block {i} must be non-empty");

            if i == 0 {
                last_start = b.level_start;
            } else {
                assert!(b.level_start >= last_start);
                last_start = b.level_start;
            }

            let end = b.level_start + b.level_len;
            assert!(end <= p.ops.len() as u32);
        }
    }

    #[test]
    fn loop_without_recur_compiles() {
        let src = "
            (def (main)
              (loop :max 3 ((x 1)) x))
            (main)
        ";

        let p = compile_str(src).unwrap();
        assert!(!p.ops.is_empty());
        assert!(!p.blocks.is_empty());
    }

    #[test]
    fn loop_with_recur_compiles() {
        let src = "
            (def (main)
              (loop :max 3 ((x 1))
                x
                (recur (+ x 1))))
            (main)
        ";

        let p = compile_str(src).unwrap();
        assert!(!p.ops.is_empty());
        assert!(!p.blocks.is_empty());
    }
}

mod lower;

use crate::ir::{Op, Program};

use lower::{Ast, Atom, LowerCtx, Tok};
use std::collections::{BTreeMap, VecDeque};
use thiserror::Error;

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

pub fn compile_str(src: &str) -> Result<Program, Error> {
    let toks = lex(src)?;
    let forms = parse(&toks)?;
    let mut cx = LowerCtx::new();

    for f in forms {
        lower::lower_top(&mut cx, f)?;
    }

    cx.b.push(Op::End);

    Ok(cx.b.finalize())
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

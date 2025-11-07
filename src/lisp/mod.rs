mod lexer;
mod lower;

use crate::ir::{Op, Program};
use lower::LowerCtx;
use std::collections::{BTreeMap, VecDeque};
use thiserror::Error;
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

pub fn compile_str(src: &str) -> Result<Program, Error> {
    let toks = lexer::lex(src)?;
    let forms = parse(&toks)?;
    let mut cx = LowerCtx::new();

    for f in forms {
        lower::lower_top(&mut cx, f)?;
    }

    cx.b.push(Op::End);

    Ok(cx.b.finalize())
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
    use crate::lisp::lexer::lex;

    #[test]
    fn parse_atoms_lists() {
        let s = "(add 1 2) (neg 3)";
        let toks = lex(s).unwrap();
        let ast = parse(&toks).unwrap();
        assert_eq!(ast.len(), 2);
    }
}

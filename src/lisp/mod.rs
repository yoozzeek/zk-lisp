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
    #[error("lower: recursion detected in call '{0}'")]
    Recursion(String),
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

// Compile main
pub fn compile_entry(src: &str, args: &[u64]) -> Result<Program, Error> {
    let toks = lex(src)?;
    let forms = parse(&toks)?;

    // discover main signature
    let mut main_params: Option<usize> = None;

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
                                main_params = Some(hh.len().saturating_sub(1));
                            }
                        }
                    }
                }
            }
        }
    }

    let arity = main_params.ok_or_else(|| Error::InvalidForm("main: not found".into()))?;
    if arity != args.len() {
        return Err(Error::InvalidForm(format!(
            "main expects {} args (got {})",
            arity,
            args.len()
        )));
    }

    // Build (main ARG0 ... ARGN)
    let mut call_items: Vec<Ast> = Vec::with_capacity(1 + args.len());
    call_items.push(Ast::Atom(Atom::Sym("main".to_string())));
    for &v in args {
        call_items.push(Ast::Atom(Atom::Int(v)));
    }

    let call_ast = Ast::List(call_items);

    // Lower: first all top-level forms (defs, etc.),
    // then tail-call main and capture its result reg.
    let mut cx = LowerCtx::new();
    for f in forms {
        // lower all top-level forms except
        // we don't append the (main ...) here
        lower::lower_top(&mut cx, f)?;
    }

    // Lower (main ...) as expression
    // to capture its result register.
    let res_reg = lower::lower_expr(&mut cx, call_ast)?;

    // Finalize program
    cx.b.push(Op::End);

    let mut program = cx.b.finalize();

    // Compute ProgramMeta from the captured
    // result register: last level writing to res_reg.
    let mut last_lvl = 0usize;
    for (i, op) in program.ops.iter().enumerate() {
        match *op {
            Op::Const { dst, .. }
            | Op::Mov { dst, .. }
            | Op::Add { dst, .. }
            | Op::Sub { dst, .. }
            | Op::Mul { dst, .. }
            | Op::Neg { dst, .. }
            | Op::Eq { dst, .. }
            | Op::Select { dst, .. }
            | Op::Hash2 { dst, .. }
            | Op::Assert { dst, .. } => {
                if dst == res_reg {
                    last_lvl = i;
                }
            }
            _ => {}
        }
    }

    let steps = crate::layout::STEPS_PER_LEVEL_P2;
    let pos_fin = crate::schedule::pos_final();

    program.meta.out_reg = res_reg;
    program.meta.out_row = (last_lvl * steps + pos_fin + 1) as u32;

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
        Tok::Quote => {
            // 'X  => (quote X)
            let quoted = parse_one(q)?;
            Ok(Ast::List(vec![
                Ast::Atom(Atom::Sym("quote".to_string())),
                quoted,
            ]))
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
}

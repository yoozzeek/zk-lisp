use crate::ir::{Op, ProgramBuilder};
use crate::layout::NR;
use crate::lisp::{Env, Error};

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
pub enum Tok {
    LParen,
    RParen,
    Quote,
    Int(u64),
    Sym(String),
    Eof,
}

enum BinOp {
    Add,
    Sub,
    Mul,
}

#[derive(Debug)]
pub struct LowerCtx<'a> {
    pub b: ProgramBuilder,

    env: Env,
    free: Vec<u8>,
    call_stack: Vec<String>,
    _m: core::marker::PhantomData<&'a ()>,
}

impl<'a> LowerCtx<'a> {
    pub fn new() -> Self {
        let free: Vec<u8> = (0u8..NR as u8).collect();

        // simple stack: pop() to allocate from
        // the end gives small regs first.
        Self {
            b: ProgramBuilder::new(),
            free,
            env: Env::default(),
            call_stack: Vec::new(),
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

pub fn lower_top(cx: &mut LowerCtx, ast: Ast) -> Result<(), Error> {
    match ast {
        Ast::List(ref items) if !items.is_empty() => {
            match &items[0] {
                Ast::Atom(Atom::Sym(s)) if s == "def" => lower_def(cx, &items[1..]),
                Ast::Atom(Atom::Sym(s)) if s == "deftype" => lower_deftype(cx, &items[1..]),
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

pub fn lower_expr(cx: &mut LowerCtx, ast: Ast) -> Result<u8, Error> {
    match ast {
        Ast::Atom(Atom::Int(v)) => {
            let r = cx.alloc()?;
            cx.b.push(Op::Const { dst: r, imm: v });

            Ok(r)
        }
        Ast::Atom(Atom::Sym(s)) => {
            let src = cx.get_var(&s)?;
            let dst = cx.alloc()?;

            cx.b.push(Op::Mov { dst, src });

            Ok(dst)
        }
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
            Ast::Atom(Atom::Sym(s)) if s == "assert" => lower_assert(cx, &items[1..]),
            Ast::Atom(Atom::Sym(s)) if s == "if" => lower_if(cx, &items[1..]),
            Ast::Atom(Atom::Sym(name)) => {
                // user function call: (f a b ...)
                lower_call(cx, name, &items[1..])
            }
            _ => Err(Error::InvalidForm("expr".into())),
        },
        _ => Err(Error::InvalidForm("atom".into())),
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

fn lower_assert(cx: &mut LowerCtx, rest: &[Ast]) -> Result<u8, Error> {
    if rest.len() != 1 {
        return Err(Error::InvalidForm("assert".into()));
    }

    let c = lower_expr(cx, rest[0].clone())?;
    let dst = cx.alloc()?;

    cx.b.push(Op::Assert { dst, c });
    cx.free_reg(c);

    Ok(dst)
}

fn lower_if(cx: &mut LowerCtx, rest: &[Ast]) -> Result<u8, Error> {
    if rest.len() != 3 {
        return Err(Error::InvalidForm("if".into()));
    }

    let c = lower_expr(cx, rest[0].clone())?;
    let t = lower_expr(cx, rest[1].clone())?;
    let e = lower_expr(cx, rest[2].clone())?;

    let dst = cx.alloc()?;

    cx.b.push(Op::Select { dst, c, a: t, b: e });

    cx.free_reg(c);
    cx.free_reg(t);
    cx.free_reg(e);

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

    cx.call_stack.pop();

    Ok(res)
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

// find the quoted (member ...)
// list at rest[1] or rest[2]
fn extract_member_from_quote(ast: &Ast) -> Option<&Ast> {
    if let Ast::List(items) = ast {
        if items.len() == 2 {
            if let Ast::Atom(Atom::Sym(h)) = &items[0] {
                if h == "quote" {
                    if let Ast::List(inner) = &items[1] {
                        if !inner.is_empty() {
                            if let Ast::Atom(Atom::Sym(m)) = &inner[0] {
                                if m == "member" {
                                    return Some(&items[1]);
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    None
}

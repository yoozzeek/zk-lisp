// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

use crate::lower::ctx::LowerCtx;
use crate::lower::{Ast, Atom, Binding, LoopVarState, RVal};
use crate::{Error, lower};

pub fn lower_loop(cx: &mut LowerCtx, rest: &[Ast]) -> Result<RVal, Error> {
    cx.with_ctx("loop", |cx| {
        // (loop :max N ((v1 init1) ... (vk initk)) body... (recur ...))
        if rest.len() < 3 {
            return Err(Error::InvalidForm("loop".into()));
        }

        // Expect :max keyword
        let max_kw = match &rest[0] {
            Ast::Atom(Atom::Sym(s)) => s,
            _ => return Err(Error::InvalidForm("loop: expected :max".into())),
        };

        if max_kw != ":max" {
            return Err(Error::InvalidForm("loop: expected :max keyword".into()));
        }

        // Static bound N
        let max_n = match &rest[1] {
            Ast::Atom(Atom::Int(n)) => *n as usize,
            Ast::Atom(Atom::Sym(name)) => {
                // Prefer local bindings first
                if let Ok(Binding::Imm(k)) = cx.get_binding(name) {
                    k as usize
                } else if let Some(k) = cx.const_ints.get(name) {
                    (*k) as usize
                } else {
                    return Err(Error::InvalidForm(
                        "loop: :max must be integer literal or constant".into(),
                    ));
                }
            }
            _ => {
                return Err(Error::InvalidForm(
                    "loop: :max must be integer literal or constant".into(),
                ));
            }
        };

        if max_n == 0 {
            return Err(Error::InvalidForm("loop: :max must be >= 1".into()));
        }

        let binds_ast = match &rest[2] {
            Ast::List(items) => items,
            _ => return Err(Error::InvalidForm("loop: expected binding list".into())),
        };

        if binds_ast.is_empty() {
            return Err(Error::InvalidForm("loop: empty binding list".into()));
        }

        let mut bind_names: Vec<String> = Vec::with_capacity(binds_ast.len());
        let mut bind_inits: Vec<Ast> = Vec::with_capacity(binds_ast.len());

        for b in binds_ast {
            match b {
                Ast::List(kv) if kv.len() == 2 => {
                    let name = match &kv[0] {
                        Ast::Atom(Atom::Sym(s)) => s.clone(),
                        _ => return Err(Error::InvalidForm("loop: binding name".into())),
                    };

                    bind_names.push(name);
                    bind_inits.push(kv[1].clone());
                }
                _ => return Err(Error::InvalidForm("loop: binding pair".into())),
            }
        }

        if rest.len() < 4 {
            return Err(Error::InvalidForm("loop: missing body".into()));
        }

        let body_forms: &[Ast] = &rest[3..];

        // Check for tail recur
        let (has_recur, recur_args) = match body_forms.last() {
            Some(Ast::List(items)) if !items.is_empty() => match &items[0] {
                Ast::Atom(Atom::Sym(h)) if h == "recur" => {
                    let args = &items[1..];
                    if args.len() != bind_names.len() {
                        return Err(Error::InvalidForm(
                            "recur: arity must match loop bindings".into(),
                        ));
                    }

                    // Forbid recur anywhere else in the body
                    for prefix_form in &body_forms[..body_forms.len() - 1] {
                        if lower::contains_symbol(prefix_form, "recur") {
                            return Err(Error::InvalidForm(
                                "recur: only allowed in tail position of loop body".into(),
                            ));
                        }
                    }

                    (true, Some(args.to_vec()))
                }
                _ => (false, None),
            },
            _ => (false, None),
        };

        if !has_recur {
            let mut bind_pairs: Vec<Ast> = Vec::with_capacity(bind_names.len());
            for (name, init) in bind_names.into_iter().zip(bind_inits.into_iter()) {
                bind_pairs.push(Ast::List(vec![Ast::Atom(Atom::Sym(name)), init]));
            }

            let binds_ast = Ast::List(bind_pairs);
            let body_ast = lower::implicit_begin(body_forms);

            let expanded = Ast::List(vec![
                Ast::Atom(Atom::Sym("block".to_string())),
                Ast::List(vec![
                    Ast::Atom(Atom::Sym("let".to_string())),
                    binds_ast,
                    body_ast,
                ]),
            ]);

            return lower::lower_expr(cx, expanded);
        }

        // With recur
        let recur_args = recur_args.unwrap();
        let prefix: &[Ast] = &body_forms[..body_forms.len() - 1];

        // Record start of loop block for segmentation.
        let lvl_start = cx.builder.current_level();

        let mut states: Vec<LoopVarState> = Vec::with_capacity(bind_names.len());

        // Initialize loop variables
        for (name, init_ast) in bind_names.iter().zip(bind_inits.iter()) {
            let v = lower::lower_expr(cx, init_ast.clone())?;
            let owned = v.into_owned(cx)?;
            let r = match owned {
                RVal::Owned(r) => r,
                _ => unreachable!("into_owned must return Owned"),
            };

            let prior = cx.env.vars.get(name).cloned();
            cx.map_var(name, Binding::Reg(r));

            states.push(LoopVarState {
                name: name.clone(),
                prior,
                reg: r,
            });
        }

        let mut loop_result: Option<RVal> = None;

        // Unroll up to max_n iterations in a flat manner
        for iter in 0..max_n {
            let mut last_val: Option<RVal> = None;
            if !prefix.is_empty() {
                for (idx, form) in prefix.iter().enumerate() {
                    let v = lower::lower_expr(cx, form.clone())?;
                    if idx + 1 < prefix.len() {
                        lower::free_if_owned(cx, v);
                    } else {
                        last_val = Some(v);
                    }
                }
            }

            let last_val = last_val.unwrap_or(RVal::Imm(0));
            let is_last_iter = iter + 1 == max_n;

            if is_last_iter {
                // Last iteration:
                // the last prefix value becomes the loop result.
                loop_result = Some(last_val);
                break;
            } else {
                // Intermediate iterations:
                // prefix result is not returned from loop.
                lower::free_if_owned(cx, last_val);
            }

            // Compute next state values sequentially from
            // the current state using recur args.
            for (idx, expr) in recur_args.iter().enumerate() {
                let v = lower::lower_expr(cx, expr.clone())?;
                let owned = v.into_owned(cx)?;
                let new_r = match owned {
                    RVal::Owned(r) => r,
                    _ => unreachable!("into_owned must return Owned"),
                };

                let st = &mut states[idx];
                let old_r = st.reg;

                // Rebind variable name to the new register
                cx.map_var(&st.name, Binding::Reg(new_r));
                st.reg = new_r;

                if old_r != new_r {
                    cx.free_reg(old_r);
                }
            }
        }

        let res = loop_result.unwrap_or(RVal::Imm(0));
        let res_reg_opt = match res {
            RVal::Owned(r) | RVal::Borrowed(r) => Some(r),
            RVal::Imm(_) => None,
        };

        // Restore outer environment and free loop state registers
        for st in states.into_iter().rev() {
            cx.env.vars.remove(&st.name);

            if let Some(pr) = st.prior {
                cx.env.vars.insert(st.name, pr);
            } else if Some(st.reg) != res_reg_opt {
                cx.free_reg(st.reg);
            }
        }

        // Close the loop block
        let lvl_end = cx.builder.current_level();
        if lvl_end > lvl_start {
            cx.builder.push_block(lvl_start, lvl_end)?;
        }

        Ok(res)
    })
}

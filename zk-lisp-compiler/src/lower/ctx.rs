// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

use crate::builder::{Op, ProgramBuilder};
use crate::lower::{Ast, Binding, NR, RVal};
use crate::{CompilerMetrics, Error};
use std::collections::BTreeMap;

#[derive(Default, Debug, Clone)]
pub struct Env {
    // variable -> binding
    pub vars: BTreeMap<String, Binding>,
    // function name -> (params, body)
    pub funs: BTreeMap<String, (Vec<String>, Ast)>,
}

#[derive(Debug)]
pub struct LowerCtx<'a> {
    pub builder: &'a mut ProgramBuilder,
    pub metrics: &'a mut CompilerMetrics,

    pub env: Env,
    pub call_stack: Vec<String>,
    pub sp_reg: Option<u8>,
    pub const_ints: BTreeMap<String, u64>,

    free: Vec<u8>,
    ctx_stack: Vec<&'static str>,
}

impl<'a> LowerCtx<'a> {
    pub fn new(builder: &'a mut ProgramBuilder, metrics: &'a mut CompilerMetrics) -> Self {
        let free: Vec<u8> = (0u8..NR as u8).collect();

        // simple stack: pop() to allocate from
        // the end gives high-numbered regs first.
        Self {
            builder,
            metrics,
            free,
            env: Env::default(),
            call_stack: Vec::new(),
            sp_reg: None,
            const_ints: BTreeMap::new(),
            ctx_stack: Vec::new(),
        }
    }

    pub fn emit_mov(&mut self, dst: u8, src: u8) {
        if dst == src {
            self.metrics.inc_mov_elided();
            return;
        }

        self.builder.push(Op::Mov { dst, src });
    }

    pub fn val_reg(&self, v: &RVal) -> Result<u8, Error> {
        match *v {
            RVal::Owned(r) | RVal::Borrowed(r) => Ok(r),
            RVal::Imm(_) => Err(Error::InvalidForm(
                "internal: immediate used where register required".into(),
            )),
        }
    }

    pub fn alloc(&mut self) -> Result<u8, Error> {
        match self.free.pop() {
            Some(r) => {
                // track live-set size
                self.metrics.inc_cur_live();

                if self.metrics.cur_live > self.metrics.peak_live {
                    self.metrics.set_peak_live(self.metrics.cur_live);
                }

                Ok(r)
            }
            None => Err(Error::RegOverflow {
                need: 1,
                have: 0,
                context: self.format_ctx(),
            }),
        }
    }

    pub fn free_reg(&mut self, r: u8) {
        // free and reduce current live-set
        self.free.push(r);

        if self.metrics.cur_live > 0 {
            self.metrics.dec_cur_live();
        }
    }

    pub fn map_var(&mut self, name: &str, b: Binding) {
        self.env.vars.insert(name.to_string(), b);
    }

    pub fn with_ctx<F, T>(&mut self, label: &'static str, f: F) -> T
    where
        F: FnOnce(&mut LowerCtx<'a>) -> T,
    {
        self.ctx_stack.push(label);

        let res = f(self);
        self.ctx_stack.pop();

        res
    }

    pub fn format_ctx(&self) -> String {
        if self.ctx_stack.is_empty() {
            "(root)".to_string()
        } else {
            self.ctx_stack.join(" -> ")
        }
    }

    pub fn get_binding(&self, name: &str) -> Result<Binding, Error> {
        self.env
            .vars
            .get(name)
            .cloned()
            .ok_or_else(|| Error::UnknownSymbol(name.to_string()))
    }

    pub fn define_fun(&mut self, name: &str, params: Vec<String>, body: Ast) {
        // Record function declaration on the builder
        // so that type schemas can be cross-checked
        // during finalize.
        self.builder.add_fn_decl(name.to_string(), params.len());
        self.env.funs.insert(name.to_string(), (params, body));
    }

    pub fn get_fun(&self, name: &str) -> Option<&(Vec<String>, Ast)> {
        self.env.funs.get(name)
    }
}

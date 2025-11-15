// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp attribution in copies
//   of this file or substantial portions of it.See the NOTICE file for details.

//! VM instruction set and program builder for zk-lisp.
//!
//! This module defines the low-level [`Op`] enum and
//! [`ProgramBuilder`] used by lowering to construct the
//! final instruction stream and track register usage.

use crate::metrics::CompilerMetrics;
use crate::{Error, FnTypeSchema, LetTypeSchema, Program, TypeSchemas};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Op {
    // ALU
    Const {
        dst: u8,
        imm: u64,
    },
    Mov {
        dst: u8,
        src: u8,
    },
    Add {
        dst: u8,
        a: u8,
        b: u8,
    },
    Sub {
        dst: u8,
        a: u8,
        b: u8,
    },
    Mul {
        dst: u8,
        a: u8,
        b: u8,
    },
    Neg {
        dst: u8,
        a: u8,
    },
    // 0/1 result
    Eq {
        dst: u8,
        a: u8,
        b: u8,
    },
    // dst = c?a:b, c ∈ {0,1}
    Select {
        dst: u8,
        c: u8,
        a: u8,
        b: u8,
    },
    // enforces c==1 and writes 1 to dst
    Assert {
        dst: u8,
        c: u8,
    },
    // 32-bit: enforce r in [0,2^32];
    // writes 1 to dst
    AssertBit {
        dst: u8,
        r: u8,
    },
    AssertRange {
        dst: u8,
        r: u8,
        bits: u8,
    },
    // stage 0 for 64-bit:
    // write sum_lo to dst
    AssertRangeLo {
        dst: u8,
        r: u8,
    },
    // stage 1 for 64-bit:
    // enforce r == dst(prev) + 2^32*sum_hi
    // writes 1 to dst
    AssertRangeHi {
        dst: u8,
        r: u8,
    },
    // writes q and r
    DivMod {
        dst_q: u8,
        dst_r: u8,
        a: u8,
        b: u8,
    },
    // divides (a_hi<<64)+a_lo by b -> q, r
    DivMod128 {
        a_hi: u8,
        a_lo: u8,
        b: u8,
        dst_q: u8,
        dst_r: u8,
    },
    // writes hi and lo of 64x64->128
    MulWide {
        dst_hi: u8,
        dst_lo: u8,
        a: u8,
        b: u8,
    },

    // RAM
    // Load: dst <- Mem[addr]
    Load {
        dst: u8,
        addr: u8,
    },
    // Store: Mem[addr] <- src
    Store {
        addr: u8,
        src: u8,
    },

    // CRYPTO
    // Sponge: absorb up to 10 elements (rate=10)
    SAbsorbN {
        regs: Vec<u8>,
    },
    // Sponge: squeeze lane 0 into dst
    SSqueeze {
        dst: u8,
    },

    // MERKLE
    MerkleStepFirst {
        leaf_reg: u8,
        dir_reg: u8,
        sib_reg: u8,
    },
    MerkleStep {
        dir_reg: u8,
        sib_reg: u8,
    },
    MerkleStepLast {
        dir_reg: u8,
        sib_reg: u8,
    },

    // CTRL
    End,
}

#[derive(Debug)]
pub struct ProgramBuilder {
    ops: Vec<Op>,
    reg_max: u8,
    type_schemas: TypeSchemas,

    // Collected function declarations
    // from `def`/generated defs.
    // Maps function name to its
    // arity (number of parameters).
    fn_decls: BTreeMap<String, usize>,

    // Names that were bound via `let`
    // inside function bodies or
    // top-level expressions.
    let_names: BTreeSet<String>,
}

impl Default for ProgramBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl ProgramBuilder {
    pub fn new() -> Self {
        Self {
            ops: Vec::new(),
            reg_max: 0,
            type_schemas: TypeSchemas::default(),
            fn_decls: BTreeMap::new(),
            let_names: BTreeSet::new(),
        }
    }

    pub fn push(&mut self, op: Op) {
        use Op::*;
        match op {
            Const { dst, .. } => self.touch_reg(dst),
            Mov { dst, src } => {
                if dst == src {
                    // Avoid redundant move
                    return;
                }

                self.touch_reg(dst);
                self.touch_reg(src);
            }
            Add { dst, a, b } => {
                self.touch_reg(dst);
                self.touch_reg(a);
                self.touch_reg(b);
            }
            Sub { dst, a, b } => {
                self.touch_reg(dst);
                self.touch_reg(a);
                self.touch_reg(b);
            }
            Mul { dst, a, b } => {
                self.touch_reg(dst);
                self.touch_reg(a);
                self.touch_reg(b);
            }
            Neg { dst, a } => {
                self.touch_reg(dst);
                self.touch_reg(a);
            }
            Eq { dst, a, b } => {
                self.touch_reg(dst);
                self.touch_reg(a);
                self.touch_reg(b);
            }
            Select { dst, c, a, b } => {
                self.touch_reg(dst);
                self.touch_reg(c);
                self.touch_reg(a);
                self.touch_reg(b);
            }
            Assert { dst, c } => {
                self.touch_reg(dst);
                self.touch_reg(c);
            }
            AssertBit { dst, r } => {
                self.touch_reg(dst);
                self.touch_reg(r);
            }
            AssertRange { dst, r, .. } => {
                self.touch_reg(dst);
                self.touch_reg(r);
            }
            AssertRangeLo { dst, r } | AssertRangeHi { dst, r } => {
                self.touch_reg(dst);
                self.touch_reg(r);
            }
            Load { dst, addr } => {
                self.touch_reg(dst);
                self.touch_reg(addr);
            }
            Store { addr, src } => {
                self.touch_reg(addr);
                self.touch_reg(src);
            }
            SAbsorbN { ref regs } => {
                for &r in regs {
                    self.touch_reg(r);
                }
            }
            DivMod { dst_q, dst_r, a, b } => {
                self.touch_reg(dst_q);
                self.touch_reg(dst_r);
                self.touch_reg(a);
                self.touch_reg(b);
            }
            DivMod128 {
                a_hi,
                a_lo,
                b,
                dst_q,
                dst_r,
            } => {
                self.touch_reg(a_hi);
                self.touch_reg(a_lo);
                self.touch_reg(b);
                self.touch_reg(dst_q);
                self.touch_reg(dst_r);
            }
            MulWide {
                dst_hi,
                dst_lo,
                a,
                b,
            } => {
                self.touch_reg(dst_hi);
                self.touch_reg(dst_lo);
                self.touch_reg(a);
                self.touch_reg(b);
            }
            SSqueeze { dst } => {
                self.touch_reg(dst);
            }
            MerkleStepFirst {
                leaf_reg,
                dir_reg,
                sib_reg,
            } => {
                self.touch_reg(leaf_reg);
                self.touch_reg(dir_reg);
                self.touch_reg(sib_reg);
            }
            MerkleStep { dir_reg, sib_reg } | MerkleStepLast { dir_reg, sib_reg } => {
                self.touch_reg(dir_reg);
                self.touch_reg(sib_reg);
            }
            End => {}
        }

        self.ops.push(op);
    }

    pub fn add_fn_schema(&mut self, schema: FnTypeSchema) {
        self.type_schemas.fns.insert(schema.name.clone(), schema);
    }

    pub fn add_let_schema(&mut self, schema: LetTypeSchema) -> Result<(), Error> {
        let owner_key = schema.owner.clone().unwrap_or_default();

        // Check for conflicts within
        // the same owner scope.
        if let Some(scope) = self.type_schemas.lets.get(&owner_key) {
            if let Some(existing) = scope.get(&schema.name) {
                if existing.ty != schema.ty {
                    return Err(Error::InvalidForm(format!(
                        "typed-let: conflicting type for '{}'",
                        schema.name,
                    )));
                }

                // Same name and type
                return Ok(());
            }
        }

        // Check for conflicts between
        // global and function scopes.
        match &schema.owner {
            // Function-local schema:
            // ensure it does not conflict
            // with a global schema of
            // the same name.
            Some(_) => {
                if let Some(global_scope) = self.type_schemas.lets.get("") {
                    if let Some(global_schema) = global_scope.get(&schema.name) {
                        if global_schema.ty != schema.ty {
                            return Err(Error::InvalidForm(format!(
                                "typed-let: conflicting type for '{}'",
                                schema.name,
                            )));
                        }
                    }
                }
            }
            // Global schema:
            // ensure it does not conflict
            // with any existing function-local
            // schemas of the same name.
            None => {
                for (owner, scope) in &self.type_schemas.lets {
                    if owner.is_empty() {
                        continue;
                    }

                    if let Some(existing) = scope.get(&schema.name) {
                        if existing.ty != schema.ty {
                            return Err(Error::InvalidForm(format!(
                                "typed-let: conflicting type for '{}'",
                                schema.name,
                            )));
                        }
                    }
                }
            }
        }

        // No conflicts;
        // insert into owner scope
        let scope = self.type_schemas.lets.entry(owner_key).or_default();
        scope.insert(schema.name.clone(), schema);

        Ok(())
    }

    /// Record a function declaration with its arity.
    ///
    /// This is later cross-checked against any `typed-fn`
    /// schemas during [`ProgramBuilder::finalize`].
    pub fn add_fn_decl(&mut self, name: String, arity: usize) {
        self.fn_decls.insert(name, arity);
    }

    /// Record a variable name that was introduced by
    /// a `let` binding somewhere in the program.
    pub fn add_let_name(&mut self, name: String) {
        self.let_names.insert(name);
    }

    pub fn finalize(self, metrics: CompilerMetrics) -> Result<Program, Error> {
        // Enforce that all function type
        // schemas have a matching function
        // definition with the same arity.
        for (name, schema) in &self.type_schemas.fns {
            let Some(arity) = self.fn_decls.get(name) else {
                return Err(Error::InvalidForm(format!(
                    "typed-fn: no function definition found for '{name}'",
                )));
            };

            let schema_arity = schema.args.len();
            if *arity != schema_arity {
                return Err(Error::InvalidForm(format!(
                    "typed-fn: function '{name}' is defined with {arity} args but schema declares {schema_arity}",
                )));
            }
        }

        // Enforce that every `typed-let` has
        // at least one matching `let` binding
        // somewhere in the program.
        for scope in self.type_schemas.lets.values() {
            for name in scope.keys() {
                if !self.let_names.contains(name) {
                    return Err(Error::InvalidForm(format!(
                        "typed-let: no let binding found for '{name}'",
                    )));
                }
            }
        }

        let reg_count = self.reg_max;
        let bytes = encode_ops(&self.ops);
        let commitment = program_commitment(&bytes);

        Ok(Program::new(
            commitment,
            self.ops,
            reg_count,
            metrics,
            self.type_schemas,
        ))
    }

    #[inline]
    fn touch_reg(&mut self, r: u8) {
        self.reg_max = self.reg_max.max(r.saturating_add(1));
    }
}

pub fn encode_ops(ops: &[Op]) -> Vec<u8> {
    let mut out = Vec::with_capacity(ops.len() * 8);
    for op in ops {
        use Op::*;
        match *op {
            Const { dst, imm } => {
                out.push(0x01);
                out.push(dst);
                out.extend_from_slice(&imm.to_le_bytes());
            }
            Mov { dst, src } => {
                out.push(0x02);
                out.push(dst);
                out.push(src);
            }
            Add { dst, a, b } => {
                out.push(0x03);
                out.push(dst);
                out.push(a);
                out.push(b);
            }
            Sub { dst, a, b } => {
                out.push(0x04);
                out.push(dst);
                out.push(a);
                out.push(b);
            }
            Mul { dst, a, b } => {
                out.push(0x05);
                out.push(dst);
                out.push(a);
                out.push(b);
            }
            Neg { dst, a } => {
                out.push(0x06);
                out.push(dst);
                out.push(a);
            }
            Eq { dst, a, b } => {
                out.push(0x07);
                out.push(dst);
                out.push(a);
                out.push(b);
            }
            Select { dst, c, a, b } => {
                out.push(0x08);
                out.push(dst);
                out.push(c);
                out.push(a);
                out.push(b);
            }
            End => {
                out.push(0x0C);
            }
            Assert { dst, c } => {
                out.push(0x0D);
                out.push(dst);
                out.push(c);
            }
            SSqueeze { dst } => {
                out.push(0x0F);
                out.push(dst);
            }
            SAbsorbN { ref regs } => {
                out.push(0x10);
                out.push(regs.len() as u8);

                for &r in regs {
                    out.push(r);
                }
            }
            MerkleStepFirst {
                leaf_reg,
                dir_reg,
                sib_reg,
            } => {
                out.push(0x11);
                out.push(leaf_reg);
                out.push(dir_reg);
                out.push(sib_reg);
            }
            MerkleStep { dir_reg, sib_reg } => {
                out.push(0x12);
                out.push(dir_reg);
                out.push(sib_reg);
            }
            MerkleStepLast { dir_reg, sib_reg } => {
                out.push(0x13);
                out.push(dir_reg);
                out.push(sib_reg);
            }
            AssertBit { dst, r } => {
                out.push(0x14);
                out.push(dst);
                out.push(r);
            }
            AssertRange { dst, r, bits } => {
                out.push(0x15);
                out.push(dst);
                out.push(r);
                out.push(bits);
            }
            AssertRangeLo { dst, r } => {
                out.push(0x16);
                out.push(dst);
                out.push(r);
            }
            AssertRangeHi { dst, r } => {
                out.push(0x17);
                out.push(dst);
                out.push(r);
            }
            DivMod { dst_q, dst_r, a, b } => {
                out.push(0x18);
                out.push(dst_q);
                out.push(dst_r);
                out.push(a);
                out.push(b);
            }
            DivMod128 {
                a_hi,
                a_lo,
                b,
                dst_q,
                dst_r,
            } => {
                out.push(0x1A);
                out.push(a_hi);
                out.push(a_lo);
                out.push(b);
                out.push(dst_q);
                out.push(dst_r);
            }
            MulWide {
                dst_hi,
                dst_lo,
                a,
                b,
            } => {
                out.push(0x19);
                out.push(dst_hi);
                out.push(dst_lo);
                out.push(a);
                out.push(b);
            }
            Load { dst, addr } => {
                out.push(0x1B);
                out.push(dst);
                out.push(addr);
            }
            Store { addr, src } => {
                out.push(0x1C);
                out.push(addr);
                out.push(src);
            }
        }
    }

    out
}

fn program_commitment(bytes: &[u8]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(bytes);

    let mut out = [0u8; 32];
    out.copy_from_slice(hasher.finalize().as_bytes());

    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn build_and_commit() {
        let metrics = CompilerMetrics::default();
        let mut b = ProgramBuilder::new();

        b.push(Op::Const { dst: 0, imm: 7 });
        b.push(Op::Const { dst: 1, imm: 9 });
        b.push(Op::Add { dst: 2, a: 0, b: 1 });
        b.push(Op::End);

        let p = b.finalize(metrics).expect("finalize must succeed");
        assert_eq!(p.reg_count, 3);
        assert_eq!(p.ops.len(), 4);
        assert_eq!(p.commitment.len(), 32);

        // basic encoding sanity
        let enc = encode_ops(&p.ops);
        assert!(enc.len() >= 1 + 1 + 8);
    }
}

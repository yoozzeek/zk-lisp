// SPDX-License-Identifier: GPL-3.0-or-later
// This file is part of zk-lisp.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>

//! IR for zk-lisp

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Op {
    // ALU
    Const { dst: u8, imm: u64 },
    Mov { dst: u8, src: u8 },
    Add { dst: u8, a: u8, b: u8 },
    Sub { dst: u8, a: u8, b: u8 },
    Mul { dst: u8, a: u8, b: u8 },
    Neg { dst: u8, a: u8 },
    Eq { dst: u8, a: u8, b: u8 },            // 0/1 result
    Select { dst: u8, c: u8, a: u8, b: u8 }, // dst = c?a:b, c ∈ {0,1}
    Assert { dst: u8, c: u8 },               // enforces c==1 and writes 1 to dst

    // CRYPTO
    Hash2 { dst: u8, a: u8, b: u8 }, // Poseidon2 map/final within one level

    // KV
    KvMap { dir: u32, sib_reg: u8 }, // one level of path
    KvFinal,

    // CTRL
    End,
}

#[derive(Clone, Debug, Default)]
pub struct ProgramMeta {
    pub out_reg: u8,
    pub out_row: u32,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub ops: Vec<Op>,
    pub reg_count: u8,
    pub commitment: [u8; 32],
    pub meta: ProgramMeta,
}

impl Program {
    pub fn new(ops: Vec<Op>, reg_count: u8, commitment: [u8; 32], meta: ProgramMeta) -> Self {
        Self {
            ops,
            reg_count,
            commitment,
            meta,
        }
    }
}

#[derive(Default, Debug)]
pub struct ProgramBuilder {
    ops: Vec<Op>,
    reg_max: u8,
}

impl ProgramBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn push(&mut self, op: Op) {
        use Op::*;
        match op {
            Const { dst, .. } => self.touch_reg(dst),
            Mov { dst, src } => {
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
            Hash2 { dst, a, b } => {
                self.touch_reg(dst);
                self.touch_reg(a);
                self.touch_reg(b);
            }
            KvMap { dir: _, sib_reg } => {
                self.touch_reg(sib_reg);
            }
            KvFinal => {}
            End => {}
        }

        self.ops.push(op);
    }

    pub fn finalize(self) -> Program {
        let reg_count = self.reg_max;
        let bytes = encode_ops(&self.ops);
        let commitment = crate::commit::program_commitment(&bytes);

        // ProgramMeta is computed at compile_entry time
        // for programs generated from source; for ad-hoc
        // ProgramBuilder usage we leave it as default (0,0).
        let meta = ProgramMeta {
            out_reg: 0,
            out_row: 0,
        };

        Program::new(self.ops, reg_count, commitment, meta)
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
            Hash2 { dst, a, b } => {
                out.push(0x09);
                out.push(dst);
                out.push(a);
                out.push(b);
            }
            KvMap { dir, sib_reg } => {
                out.push(0x0A);
                out.extend_from_slice(&dir.to_le_bytes());
                out.push(sib_reg);
            }
            KvFinal => {
                out.push(0x0B);
            }
            End => {
                out.push(0x0C);
            }
            Assert { dst, c } => {
                out.push(0x0D);
                out.push(dst);
                out.push(c);
            }
        }
    }

    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn build_and_commit() {
        let mut b = ProgramBuilder::new();
        b.push(Op::Const { dst: 0, imm: 7 });
        b.push(Op::Const { dst: 1, imm: 9 });
        b.push(Op::Add { dst: 2, a: 0, b: 1 });
        b.push(Op::End);

        let p = b.finalize();
        assert_eq!(p.reg_count, 3);
        assert_eq!(p.ops.len(), 4);
        assert_eq!(p.commitment.len(), 32);

        // basic encoding sanity
        let enc = encode_ops(&p.ops);
        assert!(enc.len() >= 1 + 1 + 8);
    }
}

// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Step-level metadata and digest for zk-lisp STARK proofs.
//!
//! This module defines a minimal echo of per-proof
//! parameters (`StepMeta`) and a Poseidon-based
//! digest function (`step_digest`) used by the
//! STARK-in-STARK recursion layer, along with a
//! concrete step proof wrapper (`ZlStepProof`).

use crate::AirPublicInputs;
use crate::zl1;

use winterfell::Proof as WProof;
use winterfell::ProofOptions;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::math::{FieldElement, ToElements};
use zk_lisp_proof::error;
use zk_lisp_proof::pi::{PublicInputs as CorePublicInputs, VmArg};

/// Minimal per-proof echo used for digest computation.
///
/// These fields are chosen to capture the essential
/// shape of the proof (trace length, blowup, queries)
/// and a coarse "work" estimate without pulling the
/// entire public input vector into the digest.
#[derive(Clone, Copy, Debug, Default)]
pub struct StepMeta {
    /// Base trace length m (number of rows before blowup).
    pub m: u32,

    /// Blowup factor rho used for this proof.
    pub rho: u16,

    /// Number of FRI queries q.
    pub q: u16,

    /// Number of committed oracles (trace + composition).
    pub o: u16,

    /// Target security level in bits.
    pub lambda: u16,

    /// Length of encoded public inputs vector
    /// (in field elements) as seen by the AIR.
    pub pi_len: u32,

    /// Coarse estimate of verifier work units.
    pub v_units: u64,
}

/// Concrete step-proof wrapper used as the
/// backend-specific `StepProof` type for
/// the recursion layer.
///
/// This structure carries the zl1 step proof container
/// which in turn encapsulates profile metadata, public
/// inputs echo, commitment echo and the underlying
/// Winterfell proof.
#[derive(Clone, Debug)]
pub struct ZlStepProof {
    pub proof: zl1::format::Proof,
    /// Backend-agnostic public inputs used when building
    /// this step trace.
    pub pi_core: zk_lisp_proof::pi::PublicInputs,
    /// Final ROM accumulator lanes for this step.
    pub rom_acc: [BE; 3],
}

impl ZlStepProof {
    /// Compute the step digest for this proof using
    /// the zl1 format and digest construction.
    pub fn digest(&self) -> [u8; 32] {
        zl1::digest::step_digest(&self.proof)
    }

    /// Return the VM state hash at the beginning
    /// of this segment as recorded in the zl1
    /// step public inputs.
    pub fn state_in_hash(&self) -> [u8; 32] {
        self.proof.pi.state_in_hash
    }

    /// Return the VM state hash at the end of
    /// this segment as recorded in the zl1
    /// step public inputs.
    pub fn state_out_hash(&self) -> [u8; 32] {
        self.proof.pi.state_out_hash
    }

    /// Encode this step proof into a compact binary format
    /// suitable for CLI storage. The encoding focuses on
    /// data required to reconstruct an equivalent
    /// `ZlStepProof` for recursion and FS replay and does
    /// not aim to be a general-purpose archive of all
    /// backend internals.
    pub fn to_bytes(&self) -> error::Result<Vec<u8>> {
        let mut out = Vec::new();

        // Magic tag for basic sanity checking
        out.extend_from_slice(b"ZKLSTP1");

        let lambda_bits = self.proof.meta.lambda as u32;
        out.extend_from_slice(&lambda_bits.to_le_bytes());

        out.extend_from_slice(&self.proof.header.suite_id);
        out.extend_from_slice(&self.pi_core.program_id);
        out.extend_from_slice(&self.pi_core.program_commitment);
        out.extend_from_slice(&self.pi_core.merkle_root);
        out.extend_from_slice(&self.pi_core.feature_mask.to_le_bytes());

        // Encode main_args needed for AirPublicInputs
        let main_len = self.pi_core.main_args.len() as u32;
        out.extend_from_slice(&main_len.to_le_bytes());

        for arg in &self.pi_core.main_args {
            match arg {
                VmArg::U64(v) => {
                    out.push(0u8);
                    out.extend_from_slice(&v.to_le_bytes());
                }
                VmArg::U128(v) => {
                    out.push(1u8);
                    out.extend_from_slice(&v.to_le_bytes());
                }
                VmArg::Bytes32(b) => {
                    out.push(2u8);
                    out.extend_from_slice(b);
                }
            }
        }

        // Segment indexing and pc_init
        out.extend_from_slice(&self.proof.pi.segment_index.to_le_bytes());
        out.extend_from_slice(&self.proof.pi.segments_total.to_le_bytes());
        out.extend_from_slice(&self.proof.pi.pc_init);

        // State hashes and per-segment RAM / ROM boundary
        // state used by the recursion layer.
        let pi = &self.proof.pi;
        out.extend_from_slice(&pi.state_in_hash);
        out.extend_from_slice(&pi.state_out_hash);
        out.extend_from_slice(&pi.ram_gp_unsorted_in);
        out.extend_from_slice(&pi.ram_gp_unsorted_out);
        out.extend_from_slice(&pi.ram_gp_sorted_in);
        out.extend_from_slice(&pi.ram_gp_sorted_out);
        out.extend_from_slice(&pi.rom_s_in_0);
        out.extend_from_slice(&pi.rom_s_in_1);
        out.extend_from_slice(&pi.rom_s_in_2);
        out.extend_from_slice(&pi.rom_s_out_0);
        out.extend_from_slice(&pi.rom_s_out_1);
        out.extend_from_slice(&pi.rom_s_out_2);

        // Inner Winterfell proof bytes (length-prefixed)
        let inner_bytes = self.proof.inner.to_bytes();
        let inner_len = inner_bytes.len() as u32;
        out.extend_from_slice(&inner_len.to_le_bytes());
        out.extend_from_slice(&inner_bytes);

        Ok(out)
    }

    /// Decode a `ZlStepProof` from bytes produced by
    /// [`ZlStepProof::to_bytes`]. This reconstructs an
    /// equivalent zl1 step container and public inputs
    /// sufficient for recursion and FS replay.
    pub fn from_bytes(bytes: &[u8]) -> error::Result<Self> {
        const MAGIC: &[u8; 7] = b"ZKLSTP1";

        if bytes.len() < MAGIC.len() {
            return Err(error::Error::InvalidInput(
                "step proof too short to contain magic header",
            ));
        }
        if &bytes[..MAGIC.len()] != MAGIC {
            return Err(error::Error::InvalidInput("invalid step proof magic tag"));
        }

        let mut cursor = MAGIC.len();

        // lambda_bits
        if bytes.len() < cursor + 4 {
            return Err(error::Error::InvalidInput(
                "step proof truncated before lambda_bits",
            ));
        }

        let mut buf4 = [0u8; 4];
        buf4.copy_from_slice(&bytes[cursor..cursor + 4]);

        let lambda_bits = u32::from_le_bytes(buf4);
        cursor += 4;

        // Helper to read fixed-size 32-byte fields with
        // descriptive error messages.
        fn take_32(bytes: &[u8], cursor: &mut usize, what: &str) -> error::Result<[u8; 32]> {
            if bytes.len() < *cursor + 32 {
                let msg = match what {
                    "suite_id" => "step proof truncated before suite_id bytes",
                    "program_id" => "step proof truncated before program_id bytes",
                    "program_commitment" => "step proof truncated before program_commitment bytes",
                    "merkle_root" => "step proof truncated before merkle_root bytes",
                    "state_in_hash" => "step proof truncated before state_in_hash bytes",
                    "state_out_hash" => "step proof truncated before state_out_hash bytes",
                    "ram_gp_unsorted_in" => "step proof truncated before ram_gp_unsorted_in bytes",
                    "ram_gp_unsorted_out" => {
                        "step proof truncated before ram_gp_unsorted_out bytes"
                    }
                    "ram_gp_sorted_in" => "step proof truncated before ram_gp_sorted_in bytes",
                    "ram_gp_sorted_out" => "step proof truncated before ram_gp_sorted_out bytes",
                    "rom_s_in_0" => "step proof truncated before rom_s_in_0 bytes",
                    "rom_s_in_1" => "step proof truncated before rom_s_in_1 bytes",
                    "rom_s_in_2" => "step proof truncated before rom_s_in_2 bytes",
                    "rom_s_out_0" => "step proof truncated before rom_s_out_0 bytes",
                    "rom_s_out_1" => "step proof truncated before rom_s_out_1 bytes",
                    "rom_s_out_2" => "step proof truncated before rom_s_out_2 bytes",
                    _ => "step proof truncated before 32-byte field",
                };

                return Err(error::Error::InvalidInput(msg));
            }

            let mut out = [0u8; 32];
            out.copy_from_slice(&bytes[*cursor..*cursor + 32]);

            *cursor += 32;

            Ok(out)
        }

        let suite_id = take_32(bytes, &mut cursor, "suite_id")?;
        let program_id = take_32(bytes, &mut cursor, "program_id")?;
        let program_commitment = take_32(bytes, &mut cursor, "program_commitment")?;
        let merkle_root = take_32(bytes, &mut cursor, "merkle_root")?;

        // feature_mask
        if bytes.len() < cursor + 8 {
            return Err(error::Error::InvalidInput(
                "step proof truncated before feature_mask",
            ));
        }

        let mut buf8 = [0u8; 8];
        buf8.copy_from_slice(&bytes[cursor..cursor + 8]);

        let feature_mask = u64::from_le_bytes(buf8);

        cursor += 8;

        // main_args length
        if bytes.len() < cursor + 4 {
            return Err(error::Error::InvalidInput(
                "step proof truncated before main_args length",
            ));
        }

        let mut len_buf = [0u8; 4];
        len_buf.copy_from_slice(&bytes[cursor..cursor + 4]);

        let main_len = u32::from_le_bytes(len_buf) as usize;

        cursor += 4;

        let mut main_args = Vec::with_capacity(main_len);
        for _ in 0..main_len {
            if bytes.len() < cursor + 1 {
                return Err(error::Error::InvalidInput(
                    "step proof truncated in VmArg tag",
                ));
            }

            let tag = bytes[cursor];
            cursor += 1;

            match tag {
                0 => {
                    if bytes.len() < cursor + 8 {
                        return Err(error::Error::InvalidInput(
                            "step proof truncated in VmArg::U64",
                        ));
                    }

                    let mut vbuf = [0u8; 8];
                    vbuf.copy_from_slice(&bytes[cursor..cursor + 8]);

                    cursor += 8;

                    main_args.push(VmArg::U64(u64::from_le_bytes(vbuf)));
                }
                1 => {
                    if bytes.len() < cursor + 16 {
                        return Err(error::Error::InvalidInput(
                            "step proof truncated in VmArg::U128",
                        ));
                    }

                    let mut vbuf = [0u8; 16];
                    vbuf.copy_from_slice(&bytes[cursor..cursor + 16]);

                    cursor += 16;

                    main_args.push(VmArg::U128(u128::from_le_bytes(vbuf)));
                }
                2 => {
                    if bytes.len() < cursor + 32 {
                        return Err(error::Error::InvalidInput(
                            "step proof truncated in VmArg::Bytes32",
                        ));
                    }

                    let mut barr = [0u8; 32];
                    barr.copy_from_slice(&bytes[cursor..cursor + 32]);

                    cursor += 32;

                    main_args.push(VmArg::Bytes32(barr));
                }
                _ => {
                    return Err(error::Error::InvalidInput(
                        "invalid VmArg tag in step proof encoding",
                    ));
                }
            }
        }

        // segment_index / segments_total / pc_init
        if bytes.len() < cursor + 4 {
            return Err(error::Error::InvalidInput(
                "step proof truncated before segment_index",
            ));
        }
        let mut u32buf = [0u8; 4];
        u32buf.copy_from_slice(&bytes[cursor..cursor + 4]);
        let segment_index = u32::from_le_bytes(u32buf);
        cursor += 4;

        if bytes.len() < cursor + 4 {
            return Err(error::Error::InvalidInput(
                "step proof truncated before segments_total",
            ));
        }
        let mut u32buf2 = [0u8; 4];
        u32buf2.copy_from_slice(&bytes[cursor..cursor + 4]);
        let segments_total = u32::from_le_bytes(u32buf2);
        cursor += 4;

        let pc_init = take_32(bytes, &mut cursor, "pc_init")?;

        // state_in_hash, state_out_hash and per-segment
        // RAM / ROM boundary state.
        let state_in_hash = take_32(bytes, &mut cursor, "state_in_hash")?;
        let state_out_hash = take_32(bytes, &mut cursor, "state_out_hash")?;
        let ram_gp_unsorted_in = take_32(bytes, &mut cursor, "ram_gp_unsorted_in")?;
        let ram_gp_unsorted_out = take_32(bytes, &mut cursor, "ram_gp_unsorted_out")?;
        let ram_gp_sorted_in = take_32(bytes, &mut cursor, "ram_gp_sorted_in")?;
        let ram_gp_sorted_out = take_32(bytes, &mut cursor, "ram_gp_sorted_out")?;
        let rom_s_in_0 = take_32(bytes, &mut cursor, "rom_s_in_0")?;
        let rom_s_in_1 = take_32(bytes, &mut cursor, "rom_s_in_1")?;
        let rom_s_in_2 = take_32(bytes, &mut cursor, "rom_s_in_2")?;
        let rom_s_out_0 = take_32(bytes, &mut cursor, "rom_s_out_0")?;
        let rom_s_out_1 = take_32(bytes, &mut cursor, "rom_s_out_1")?;
        let rom_s_out_2 = take_32(bytes, &mut cursor, "rom_s_out_2")?;

        // inner proof length and bytes
        if bytes.len() < cursor + 4 {
            return Err(error::Error::InvalidInput(
                "step proof truncated before inner proof length",
            ));
        }

        let mut len_inner_buf = [0u8; 4];
        len_inner_buf.copy_from_slice(&bytes[cursor..cursor + 4]);

        let inner_len = u32::from_le_bytes(len_inner_buf) as usize;
        cursor += 4;

        if bytes.len() < cursor + inner_len {
            return Err(error::Error::InvalidInput(
                "step proof truncated before inner proof bytes",
            ));
        }

        let inner_bytes = &bytes[cursor..cursor + inner_len];
        let inner_proof = WProof::from_bytes(inner_bytes).map_err(|_| {
            error::Error::InvalidInput("failed to decode inner Winterfell proof in step proof")
        })?;

        // Rebuild minimal core public inputs used by the AIR.
        let core_pi = CorePublicInputs {
            program_id,
            program_commitment,
            merkle_root,
            feature_mask,
            main_args,
            ..CorePublicInputs::default()
        };

        // Compute pi_len via AirPublicInputs::to_elements.
        let air_pi = AirPublicInputs {
            core: core_pi.clone(),
            rom_acc: [BE::ZERO; 3],
            pc_init: BE::ZERO,
            ram_gp_unsorted_in: BE::ZERO,
            ram_gp_unsorted_out: BE::ZERO,
            ram_gp_sorted_in: BE::ZERO,
            ram_gp_sorted_out: BE::ZERO,
            rom_s_in: [BE::ZERO; 3],
            rom_s_out: [BE::ZERO; 3],
        };
        let pi_len = air_pi.to_elements().len() as u32;

        let trace_len = inner_proof.trace_info().length();
        let wf_opts = inner_proof.options().clone();
        let meta = StepMeta::from_env(trace_len, &wf_opts, lambda_bits, pi_len);

        let zl1_proof = if segments_total <= 1 {
            zl1::format::Proof::new_single_segment(
                suite_id,
                meta,
                &core_pi,
                pc_init,
                state_in_hash,
                state_out_hash,
                ram_gp_unsorted_in,
                ram_gp_unsorted_out,
                ram_gp_sorted_in,
                ram_gp_sorted_out,
                rom_s_in_0,
                rom_s_in_1,
                rom_s_in_2,
                rom_s_out_0,
                rom_s_out_1,
                rom_s_out_2,
                inner_proof,
            )?
        } else {
            zl1::format::Proof::new_multi_segment(
                suite_id,
                meta,
                &core_pi,
                segment_index,
                segments_total,
                pc_init,
                state_in_hash,
                state_out_hash,
                ram_gp_unsorted_in,
                ram_gp_unsorted_out,
                ram_gp_sorted_in,
                ram_gp_sorted_out,
                rom_s_in_0,
                rom_s_in_1,
                rom_s_in_2,
                rom_s_out_0,
                rom_s_out_1,
                rom_s_out_2,
                inner_proof,
            )?
        };

        Ok(ZlStepProof {
            proof: zl1_proof,
            pi_core: core_pi,
            rom_acc: [BE::ZERO; 3],
        })
    }
}

impl StepMeta {
    /// Construct a `StepMeta` from basic profile numbers.
    pub fn new(m: u32, rho: u16, q: u16, o: u16, lambda: u16, pi_len: u32) -> Self {
        let v_units = (m as u64).saturating_mul(q as u64);

        Self {
            m,
            rho,
            q,
            o,
            lambda,
            pi_len,
            v_units,
        }
    }

    /// Convenience constructor for building
    /// step metadata from runtime proof
    /// options and trace shape.
    pub fn from_env(
        trace_len: usize,
        wf_opts: &ProofOptions,
        lambda_bits: u32,
        pi_len: u32,
    ) -> Self {
        let m = trace_len as u32;
        let rho = wf_opts.blowup_factor() as u16;
        let q = wf_opts.num_queries() as u16;

        // current backend commits the
        // main trace and a single
        // composition column;
        let o: u16 = 2;

        let lambda = lambda_bits.min(u16::MAX as u32) as u16;

        StepMeta::new(m, rho, q, o, lambda, pi_len)
    }
}

// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Winterfell-based STARK backend for zk-lisp.
//!
//! This crate implements [`ZkBackend`] and frontend extension
//! traits for the Winterfell prover, wiring zk-lisp programs,
//! backend-agnostic public inputs and Winterfell's AIR/trace
//! into a concrete proof system.

pub mod agg;
pub mod commit;
pub mod poseidon;
pub mod preflight;
pub mod proof;
pub mod prove;
pub mod romacc;
pub mod segment_planner;
pub mod utils;
pub mod vm;

use vm::trace::build_trace;

use agg::air::AggAirPublicInputs;
use agg::child::{
    ZlChildCompact, ZlChildTranscript, children_root_from_compact, verify_child_transcript,
};
use proof::step;
use vm::layout;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::math::{FieldElement, StarkField, ToElements};
use winterfell::{BatchingMethod, FieldExtension, Proof, ProofOptions, Trace};
use zk_lisp_compiler::Program;
use zk_lisp_proof::frontend::{PreflightBackend, PreflightMode, VmBackend, VmRunResult};
use zk_lisp_proof::pi::PublicInputs as CorePublicInputs;
use zk_lisp_proof::recursion::{
    RecursionArtifactCodec, RecursionBackend, RecursionDigest, RecursionPublicBuilder,
    RecursionStepProver,
};
use zk_lisp_proof::{ProverOptions, ZkBackend, ZkField};

#[derive(Clone, Debug)]
pub struct WinterfellField(pub BE);

impl ZkField for WinterfellField {
    fn zero() -> Self {
        WinterfellField(BE::ZERO)
    }

    fn one() -> Self {
        WinterfellField(BE::ONE)
    }

    fn from_u64(x: u64) -> Self {
        WinterfellField(BE::from(x))
    }

    fn to_u128(&self) -> u128 {
        self.0.as_int()
    }
}

#[derive(Clone, Debug)]
pub struct AirPublicInputs {
    pub core: CorePublicInputs,
    pub segment_feature_mask: u64,
    pub rom_acc: [BE; 3],
    pub pc_init: BE,
    pub ram_gp_unsorted_in: BE,
    pub ram_gp_unsorted_out: BE,
    pub ram_gp_sorted_in: BE,
    pub ram_gp_sorted_out: BE,
    pub rom_s_in: [BE; 3],
    pub rom_s_out: [BE; 3],
}

impl Default for AirPublicInputs {
    fn default() -> Self {
        Self {
            core: CorePublicInputs::default(),
            segment_feature_mask: 0,
            rom_acc: [BE::ZERO; 3],
            pc_init: BE::ZERO,
            ram_gp_unsorted_in: BE::ZERO,
            ram_gp_unsorted_out: BE::ZERO,
            ram_gp_sorted_in: BE::ZERO,
            ram_gp_sorted_out: BE::ZERO,
            rom_s_in: [BE::ZERO; 3],
            rom_s_out: [BE::ZERO; 3],
        }
    }
}

impl ToElements<BE> for AirPublicInputs {
    fn to_elements(&self) -> Vec<BE> {
        let mut out = Vec::with_capacity(16);

        // Keep the global feature mask as the public
        // contract; segment_feature_mask is used only
        // internally by the backend AIR.
        out.push(BE::from(self.core.feature_mask));
        out.push(utils::be_from_le8(&self.core.program_commitment));
        out.push(utils::be_from_le8(&self.core.merkle_root));

        if self.core.program_commitment.iter().any(|b| *b != 0) {
            let fc = commit::program_field_commitment(&self.core.program_commitment);
            out.push(fc[0]);
            out.push(fc[1]);
        } else {
            out.push(BE::ZERO);
            out.push(BE::ZERO);
        }

        // Encode main_args as a flattened sequence of
        // base-field elements using the same layout as
        let main_slots = utils::encode_main_args_to_slots(&self.core.main_args);
        out.reserve(main_slots.len() + 16);
        out.extend_from_slice(&main_slots);

        // Include segment-local boundary state into the
        // public-element vector so that Fiat–Shamir
        out.push(self.pc_init);
        out.push(self.ram_gp_unsorted_in);
        out.push(self.ram_gp_unsorted_out);
        out.push(self.ram_gp_sorted_in);
        out.push(self.ram_gp_sorted_out);

        for lane in &self.rom_s_in {
            out.push(*lane);
        }
        for lane in &self.rom_s_out {
            out.push(*lane);
        }

        out
    }
}

pub struct WinterfellBackend;

impl ZkBackend for WinterfellBackend {
    type Field = WinterfellField;
    type Program = Program;
    type PublicInputs = CorePublicInputs;
    type Error = crate::prove::Error;
    type ProverOptions = ProverOptions;
}

impl VmBackend for WinterfellBackend {
    fn eval_vm(
        program: &Self::Program,
        pub_inputs: &Self::PublicInputs,
    ) -> Result<VmRunResult<Self::Field>, Self::Error> {
        let trace = build_trace(program, pub_inputs)?;
        let (out_reg, out_row) = utils::vm_output_from_trace(&trace);
        let cols = layout::Columns::baseline();
        let val = trace.get(cols.r_index(out_reg as usize), out_row as usize);

        Ok(VmRunResult {
            out_reg,
            out_row,
            value: WinterfellField(val),
            trace_len: trace.length(),
        })
    }
}

impl PreflightBackend for WinterfellBackend {
    fn run_preflight(
        mode: PreflightMode,
        opts: &Self::ProverOptions,
        program: &Self::Program,
        pub_inputs: &Self::PublicInputs,
    ) -> Result<(), Self::Error> {
        let base_opts = ProofOptions::new(
            opts.queries as usize,
            opts.blowup as usize,
            opts.grind,
            FieldExtension::None,
            2,
            1,
            BatchingMethod::Linear,
            BatchingMethod::Linear,
        );

        let trace = build_trace(program, pub_inputs)?;

        let (num_partitions, hash_rate) =
            utils::select_partitions_for_trace(trace.width(), trace.length());
        let wf_opts = base_opts.with_partitions(num_partitions, hash_rate);

        preflight::run(mode, &wf_opts, pub_inputs, &trace)
    }
}

impl RecursionBackend for WinterfellBackend {
    type StepProof = step::StepProof;
    type RecursionProof = Proof;
    type RecursionPublic = AggAirPublicInputs;

    fn prove(
        steps: &[Self::StepProof],
        rc_pi: &Self::RecursionPublic,
        opts: &Self::ProverOptions,
    ) -> Result<(Self::RecursionProof, RecursionDigest), Self::Error> {
        if steps.is_empty() {
            return Err(prove::Error::RecursionInvalid(
                "RecursionBackend::recursion_prove requires at least one step proof",
            ));
        }

        let expected_children = steps.len() as u32;
        if rc_pi.children_count != 0 && rc_pi.children_count != expected_children {
            return Err(prove::Error::RecursionInvalid(
                "RecursionBackend::recursion_prove requires AggAirPublicInputs.children_count to be 0 or match number of step proofs",
            ));
        }

        if !rc_pi.children_ms.is_empty() && rc_pi.children_ms.len() != steps.len() {
            return Err(prove::Error::RecursionInvalid(
                "RecursionBackend::recursion_prove requires AggAirPublicInputs.children_ms length to be 0 or match number of step proofs",
            ));
        }

        let mut transcripts = Vec::with_capacity(steps.len());
        for step in steps {
            let tx = ZlChildTranscript::from_step(step)?;
            verify_child_transcript(&tx)?;
            transcripts.push(tx);
        }

        let mut agg_pi = rc_pi.clone();

        let suite_id = steps[0].proof.header.suite_id;
        for step in steps.iter().skip(1) {
            if step.proof.header.suite_id != suite_id {
                return Err(prove::Error::RecursionInvalid(
                    "RecursionBackend::recursion_prove requires all steps to share the same suite_id",
                ));
            }
        }

        agg_pi.suite_id = suite_id;
        agg_pi.children_count = steps.len() as u32;
        agg_pi.children_ms = steps.iter().map(|s| s.proof.meta.m).collect();

        let proof = prove::prove_agg_proof(&agg_pi, &transcripts, opts)?;
        let digest = prove::recursion_digest_from_agg_pi(&agg_pi);

        Ok((proof, digest))
    }

    fn verify(
        proof: Self::RecursionProof,
        rc_pi: &Self::RecursionPublic,
        opts: &Self::ProverOptions,
    ) -> Result<(), Self::Error> {
        let min_bits = opts.min_security_bits;
        let agg_queries = core::cmp::max(opts.queries as usize, 16usize);

        let field_extension = if min_bits >= 128 {
            FieldExtension::Quadratic
        } else {
            FieldExtension::None
        };

        let wf_opts = ProofOptions::new(
            agg_queries,
            opts.blowup as usize,
            opts.grind,
            field_extension,
            2,
            1,
            BatchingMethod::Linear,
            BatchingMethod::Linear,
        );

        prove::verify_agg_proof(proof, rc_pi, &wf_opts, min_bits)
    }
}

impl RecursionStepProver for WinterfellBackend {
    fn prove_all_steps(
        program: &Self::Program,
        pub_inputs: &Self::PublicInputs,
        opts: &Self::ProverOptions,
    ) -> Result<Vec<Self::StepProof>, Self::Error> {
        prove::prove_program(program, pub_inputs, opts)
    }
}

impl RecursionPublicBuilder for WinterfellBackend {
    fn build_public(
        _program: &Self::Program,
        pub_inputs: &Self::PublicInputs,
        steps: &[Self::StepProof],
        _opts: &Self::ProverOptions,
    ) -> Result<Self::RecursionPublic, Self::Error> {
        if steps.is_empty() {
            return Err(prove::Error::RecursionInvalid(
                "build_recursion_public requires at least one step",
            ));
        }

        for step in steps {
            let pi = &step.pi_core;
            if pi.program_id != pub_inputs.program_id
                || pi.program_commitment != pub_inputs.program_commitment
                || pi.main_args != pub_inputs.main_args
            {
                return Err(prove::Error::RecursionInvalid(
                    "build_recursion_public requires all steps to share the same program_id, program_commitment and main_args as recursion public inputs",
                ));
            }
        }

        let mut children = Vec::with_capacity(steps.len());
        let mut v_units_total: u64 = 0;

        for step in steps {
            let c = ZlChildCompact::from_step(step)?;
            v_units_total = v_units_total.saturating_add(c.meta.v_units);
            children.push(c);
        }

        let first = &children[0];
        let children_root = children_root_from_compact(&first.suite_id, &children);
        let suite_id = first.suite_id;
        let children_ms = children.iter().map(|c| c.meta.m).collect::<Vec<_>>();

        let profile_meta = agg::air::AggProfileMeta {
            m: first.meta.m,
            rho: first.meta.rho,
            q: first.meta.q,
            o: first.meta.o,
            lambda: first.meta.lambda,
            pi_len: first.meta.pi_len,
            v_units: first.meta.v_units,
        };
        let profile_fri = agg::air::AggFriProfile {
            lde_blowup: first.meta.rho as u32,
            folding_factor: 2,
            redundancy: 1,
            num_layers: 1,
        };
        let profile_queries = agg::air::AggQueryProfile {
            num_queries: first.meta.q,
            grinding_factor: 0,
        };

        let vm_state_initial = steps.first().unwrap().state_in_hash();
        let vm_state_final = steps.last().unwrap().state_out_hash();

        let program_id = pub_inputs.program_id;
        let program_commitment = pub_inputs.program_commitment;
        let pi_digest = pub_inputs.digest();

        let a0 = AggAirPublicInputs::from_step_proof(&steps[0])?;
        let al = AggAirPublicInputs::from_step_proof(steps.last().unwrap())?;

        Ok(AggAirPublicInputs {
            program_id,
            program_commitment,
            pi_digest,
            children_root,
            v_units_total,
            children_count: steps.len() as u32,
            batch_id: [0u8; 32],
            profile_meta,
            profile_fri,
            profile_queries,
            suite_id,
            children_ms,
            vm_state_initial,
            vm_state_final,
            ram_gp_unsorted_initial: a0.ram_gp_unsorted_initial,
            ram_gp_unsorted_final: al.ram_gp_unsorted_final,
            ram_gp_sorted_initial: a0.ram_gp_sorted_initial,
            ram_gp_sorted_final: al.ram_gp_sorted_final,
            rom_s_initial: a0.rom_s_initial,
            rom_s_final: al.rom_s_final,
        })
    }
}

impl RecursionArtifactCodec for WinterfellBackend {
    type CodecError = crate::prove::Error;

    fn encode(
        proof: &Self::RecursionProof,
        rc_pi: &Self::RecursionPublic,
    ) -> Result<Vec<u8>, Self::CodecError> {
        let mut out = Vec::new();
        out.extend_from_slice(b"ZKLRC1");

        let pi = rc_pi;

        out.extend_from_slice(&pi.program_id);
        out.extend_from_slice(&pi.program_commitment);
        out.extend_from_slice(&pi.pi_digest);

        out.extend_from_slice(&pi.children_root);
        out.extend_from_slice(&pi.batch_id);
        out.extend_from_slice(&pi.v_units_total.to_le_bytes());
        out.extend_from_slice(&pi.children_count.to_le_bytes());

        out.extend_from_slice(&pi.profile_meta.m.to_le_bytes());
        out.extend_from_slice(&pi.profile_meta.rho.to_le_bytes());
        out.extend_from_slice(&pi.profile_meta.q.to_le_bytes());
        out.extend_from_slice(&pi.profile_meta.o.to_le_bytes());
        out.extend_from_slice(&pi.profile_meta.lambda.to_le_bytes());
        out.extend_from_slice(&pi.profile_meta.pi_len.to_le_bytes());
        out.extend_from_slice(&pi.profile_meta.v_units.to_le_bytes());

        out.extend_from_slice(&pi.profile_fri.lde_blowup.to_le_bytes());
        out.extend_from_slice(&pi.profile_fri.folding_factor.to_le_bytes());
        out.extend_from_slice(&pi.profile_fri.redundancy.to_le_bytes());
        out.extend_from_slice(&pi.profile_fri.num_layers.to_le_bytes());

        out.extend_from_slice(&pi.profile_queries.num_queries.to_le_bytes());
        out.extend_from_slice(&pi.profile_queries.grinding_factor.to_le_bytes());

        out.extend_from_slice(&pi.suite_id);

        let n_ms = pi.children_ms.len() as u32;
        out.extend_from_slice(&n_ms.to_le_bytes());

        for m in &pi.children_ms {
            out.extend_from_slice(&m.to_le_bytes());
        }

        out.extend_from_slice(&pi.vm_state_initial);
        out.extend_from_slice(&pi.vm_state_final);
        out.extend_from_slice(&pi.ram_gp_unsorted_initial);
        out.extend_from_slice(&pi.ram_gp_unsorted_final);
        out.extend_from_slice(&pi.ram_gp_sorted_initial);
        out.extend_from_slice(&pi.ram_gp_sorted_final);

        for lane in &pi.rom_s_initial {
            out.extend_from_slice(lane);
        }

        for lane in &pi.rom_s_final {
            out.extend_from_slice(lane);
        }

        let p_bytes = proof.to_bytes();
        out.extend_from_slice(&(p_bytes.len() as u32).to_le_bytes());
        out.extend_from_slice(&p_bytes);

        Ok(out)
    }

    fn decode(
        bytes: &[u8],
    ) -> Result<(Self::RecursionProof, Self::RecursionPublic), Self::CodecError> {
        let mut i = 0usize;
        let magic = b"ZKLRC1";

        if bytes.len() < magic.len() || &bytes[..magic.len()] != magic {
            return Err(prove::Error::PublicInputs(
                zk_lisp_proof::error::Error::InvalidInput("invalid recursion artifact magic"),
            ));
        }

        i += magic.len();

        let take32 = |idx: &mut usize, name: &'static str| -> Result<[u8; 32], Self::CodecError> {
            if bytes.len() < *idx + 32 {
                return Err(prove::Error::PublicInputs(
                    zk_lisp_proof::error::Error::InvalidInput(name),
                ));
            }

            let mut out = [0u8; 32];
            out.copy_from_slice(&bytes[*idx..*idx + 32]);

            *idx += 32;

            Ok(out)
        };

        // Program binding fields
        let program_id = take32(&mut i, "program_id truncated")?;
        let program_commitment = take32(&mut i, "program_commitment truncated")?;
        let pi_digest = take32(&mut i, "pi_digest truncated")?;

        let children_root = take32(&mut i, "children_root truncated")?;
        let batch_id = take32(&mut i, "batch_id truncated")?;

        // u64 v_units_total
        if bytes.len() < i + 8 {
            return Err(prove::Error::PublicInputs(
                zk_lisp_proof::error::Error::InvalidInput("v_units_total truncated"),
            ));
        }

        let mut u8b = [0u8; 8];
        u8b.copy_from_slice(&bytes[i..i + 8]);

        let v_units_total = u64::from_le_bytes(u8b);
        i += 8;

        // children_count u32
        if bytes.len() < i + 4 {
            return Err(prove::Error::PublicInputs(
                zk_lisp_proof::error::Error::InvalidInput("children_count truncated"),
            ));
        }

        let mut u4 = [0u8; 4];
        u4.copy_from_slice(&bytes[i..i + 4]);

        let children_count = u32::from_le_bytes(u4);
        i += 4;

        // profile_meta
        let read_u32 = |bytes: &[u8], i: &mut usize| -> Result<u32, Self::CodecError> {
            if bytes.len() < *i + 4 {
                return Err(prove::Error::PublicInputs(
                    zk_lisp_proof::error::Error::InvalidInput("u32 truncated"),
                ));
            }

            let mut b = [0u8; 4];
            b.copy_from_slice(&bytes[*i..*i + 4]);
            *i += 4;

            Ok(u32::from_le_bytes(b))
        };

        let read_u16 = |bytes: &[u8], i: &mut usize| -> Result<u16, Self::CodecError> {
            if bytes.len() < *i + 2 {
                return Err(prove::Error::PublicInputs(
                    zk_lisp_proof::error::Error::InvalidInput("u16 truncated"),
                ));
            }

            let mut b = [0u8; 2];
            b.copy_from_slice(&bytes[*i..*i + 2]);
            *i += 2;

            Ok(u16::from_le_bytes(b))
        };

        let read_u8 = |bytes: &[u8], i: &mut usize| -> Result<u8, Self::CodecError> {
            if bytes.len() < *i + 1 {
                return Err(prove::Error::PublicInputs(
                    zk_lisp_proof::error::Error::InvalidInput("u8 truncated"),
                ));
            }

            let b = bytes[*i];
            *i += 1;

            Ok(b)
        };

        let m = read_u32(bytes, &mut i)?;
        let rho = read_u16(bytes, &mut i)?;
        let q = read_u16(bytes, &mut i)?;
        let o = read_u16(bytes, &mut i)?;
        let lambda = read_u16(bytes, &mut i)?;
        let pi_len = read_u32(bytes, &mut i)?;

        let mut u8b2 = [0u8; 8];

        if bytes.len() < i + 8 {
            return Err(prove::Error::PublicInputs(
                zk_lisp_proof::error::Error::InvalidInput("v_units(meta) truncated"),
            ));
        }

        u8b2.copy_from_slice(&bytes[i..i + 8]);
        i += 8;

        let v_units_meta = u64::from_le_bytes(u8b2);
        let profile_meta = agg::air::AggProfileMeta {
            m,
            rho,
            q,
            o,
            lambda,
            pi_len,
            v_units: v_units_meta,
        };
        let lde_blowup = read_u32(bytes, &mut i)?;
        let folding_factor = read_u8(bytes, &mut i)?;
        let redundancy = read_u8(bytes, &mut i)?;
        let num_layers = read_u8(bytes, &mut i)?;
        let profile_fri = agg::air::AggFriProfile {
            lde_blowup,
            folding_factor,
            redundancy,
            num_layers,
        };
        let num_queries = read_u16(bytes, &mut i)?;
        let grinding_factor = read_u32(bytes, &mut i)?;
        let profile_queries = agg::air::AggQueryProfile {
            num_queries,
            grinding_factor,
        };
        let suite_id = take32(&mut i, "suite_id truncated")?;
        let n_ms = read_u32(bytes, &mut i)? as usize;

        let mut children_ms = Vec::with_capacity(n_ms);
        for _ in 0..n_ms {
            children_ms.push(read_u32(bytes, &mut i)?);
        }

        let vm_state_initial = take32(&mut i, "vm_state_initial truncated")?;
        let vm_state_final = take32(&mut i, "vm_state_final truncated")?;
        let ram_gp_unsorted_initial = take32(&mut i, "ram_gp_unsorted_initial truncated")?;
        let ram_gp_unsorted_final = take32(&mut i, "ram_gp_unsorted_final truncated")?;
        let ram_gp_sorted_initial = take32(&mut i, "ram_gp_sorted_initial truncated")?;
        let ram_gp_sorted_final = take32(&mut i, "ram_gp_sorted_final truncated")?;

        let mut rom_s_initial = [[0u8; 32]; 3];
        for lane in &mut rom_s_initial {
            *lane = take32(&mut i, "rom_s_initial lane truncated")?;
        }

        let mut rom_s_final = [[0u8; 32]; 3];
        for lane in &mut rom_s_final {
            *lane = take32(&mut i, "rom_s_final lane truncated")?;
        }

        // proof bytes
        if bytes.len() < i + 4 {
            return Err(prove::Error::PublicInputs(
                zk_lisp_proof::error::Error::InvalidInput("proof length truncated"),
            ));
        }

        let mut pb = [0u8; 4];
        pb.copy_from_slice(&bytes[i..i + 4]);
        i += 4;

        let plen = u32::from_le_bytes(pb) as usize;

        if bytes.len() < i + plen {
            return Err(prove::Error::PublicInputs(
                zk_lisp_proof::error::Error::InvalidInput("proof bytes truncated"),
            ));
        }

        let proof = Proof::from_bytes(&bytes[i..i + plen])
            .map_err(|e| prove::Error::BackendSource(Box::new(e)))?;

        let rc_pi = AggAirPublicInputs {
            program_id,
            program_commitment,
            pi_digest,
            children_root,
            v_units_total,
            children_count,
            batch_id,
            profile_meta,
            profile_fri,
            profile_queries,
            suite_id,
            children_ms,
            vm_state_initial,
            vm_state_final,
            ram_gp_unsorted_initial,
            ram_gp_unsorted_final,
            ram_gp_sorted_initial,
            ram_gp_sorted_final,
            rom_s_initial,
            rom_s_final,
        };

        Ok((proof, rc_pi))
    }
}

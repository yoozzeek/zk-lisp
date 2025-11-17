// SPDX-License-Identifier: AGPL-3.0-or-later
// This file is part of zk-lisp project.
// Copyright (C) 2025  Andrei Kochergin <zeek@tuta.com>
//
// Additional terms under GNU AGPL v3 section 7:
//   You must preserve this notice and the zk-lisp
//   attribution in copies of this file or substantial
//   portions of it. See the NOTICE file for details.

//! Thin wrapper around Winterfell's prover and verifier.
//!
//! [`ZkProver`] validates public inputs, optionally runs
//! preflight checks and delegates to the underlying
//! Winterfell prover, mapping errors into a small enum.

use std::error::Error as StdError;
use thiserror::Error;
use winterfell::{
    Air, CompositionPoly, CompositionPolyTrace, DefaultConstraintCommitment,
    DefaultConstraintEvaluator, DefaultTraceLde, PartitionOptions, Proof, ProofOptions,
    Prover as WProver, StarkDomain, Trace, TraceInfo, TracePolyTable, TraceTable,
    crypto::{DefaultRandomCoin, MerkleTree},
    math::FieldElement,
    math::ToElements,
    math::fields::f128::BaseElement as BE,
    matrix::ColMatrix,
};
use zk_lisp_compiler::Program;
use zk_lisp_proof::error;
use zk_lisp_proof::frontend::PreflightMode;
use zk_lisp_proof::ivc::IvPublic;
use zk_lisp_proof::pi as core_pi;
use zk_lisp_proof::pi::PublicInputs;

use crate::air::ZkLispAir;
use crate::ivc_air::{IvAirPublicInputs, ZlIvAir};
use crate::poseidon_hasher::PoseidonHasher;
use crate::zl_step::{StepMeta, ZlStepProof};
use crate::{ivc_trace, preflight::run as run_preflight, schedule, utils};

#[derive(Debug, Error)]
pub enum Error {
    #[error("backend error: {0}")]
    Backend(String),
    #[error("backend error: {0}")]
    BackendSource(#[source] Box<dyn StdError + Send + Sync + 'static>),
    #[error("ivc invalid input: {0}")]
    IvInvalid(&'static str),
    #[error(transparent)]
    PublicInputs(#[from] error::Error),
}

#[derive(Debug)]
pub struct ZkProver {
    options: ProofOptions,
    pub_inputs: PublicInputs,
    rom_acc: [BE; 3],
    preflight: PreflightMode,
}

impl ZkProver {
    pub fn new(options: ProofOptions, pub_inputs: PublicInputs, rom_acc: [BE; 3]) -> Self {
        let mut pf = if cfg!(debug_assertions) {
            PreflightMode::Console
        } else {
            PreflightMode::Off
        };

        if let Ok(s) = std::env::var("ZKL_PREFLIGHT") {
            pf = match s.to_ascii_lowercase().as_str() {
                "off" => PreflightMode::Off,
                "console" => PreflightMode::Console,
                "json" => PreflightMode::Json,
                _ => pf,
            };
        }

        Self {
            options,
            pub_inputs,
            rom_acc,
            preflight: pf,
        }
    }

    pub fn with_preflight_mode(mut self, mode: PreflightMode) -> Self {
        self.preflight = mode;
        self
    }

    #[tracing::instrument(
        level = "info",
        skip(self, trace),
        fields(
            q = %self.options.num_queries(),
            blowup = %self.options.blowup_factor(),
            grind = %self.options.grinding_factor(),
        )
    )]
    pub fn prove(&self, trace: TraceTable<BE>) -> Result<Proof, Error> {
        self.pub_inputs.validate_flags()?;

        tracing::info!(
            target = "proof.prove",
            q = %self.options.num_queries(),
            blowup = %self.options.blowup_factor(),
            grind = %self.options.grinding_factor(),
            width = %trace.width(),
            length = %trace.length(),
            "prove start",
        );

        if !matches!(self.preflight, PreflightMode::Off) {
            run_preflight(self.preflight, &self.options, &self.pub_inputs, &trace)?;
        }

        let prover = ZkWinterfellProver {
            options: self.options.clone(),
            pub_inputs: self.pub_inputs.clone(),
            rom_acc: self.rom_acc,
        };

        let t0 = std::time::Instant::now();
        let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| prover.prove(trace)))
            .map_err(|_| Error::Backend("winterfell panic during proving".into()))
            .and_then(|r| r.map_err(|e| Error::BackendSource(Box::new(e))));

        match res {
            Ok(proof) => {
                let dt = t0.elapsed();
                tracing::info!(
                    target = "proof.prove",
                    elapsed_ms = %dt.as_millis(),
                    "prove created",
                );

                Ok(proof)
            }
            Err(e) => Err(e),
        }
    }
}

struct ZkWinterfellProver {
    options: ProofOptions,
    pub_inputs: PublicInputs,
    rom_acc: [BE; 3],
}

impl WProver for ZkWinterfellProver {
    type BaseField = BE;
    type Air = ZkLispAir;
    type Trace = TraceTable<Self::BaseField>;
    type HashFn = PoseidonHasher<Self::BaseField>;
    type VC = MerkleTree<Self::HashFn>;
    type RandomCoin = DefaultRandomCoin<Self::HashFn>;
    type TraceLde<E: FieldElement<BaseField = Self::BaseField>> =
        DefaultTraceLde<E, Self::HashFn, Self::VC>;
    type ConstraintEvaluator<'a, E: FieldElement<BaseField = Self::BaseField>> =
        DefaultConstraintEvaluator<'a, Self::Air, E>;
    type ConstraintCommitment<E: FieldElement<BaseField = Self::BaseField>> =
        DefaultConstraintCommitment<E, Self::HashFn, Self::VC>;

    fn get_pub_inputs(&self, trace: &Self::Trace) -> <Self::Air as Air>::PublicInputs {
        let mut pi = self.pub_inputs.clone();

        // Compute VM output location (last op level)
        if (pi.feature_mask & core_pi::FM_VM) != 0 {
            // If caller provided explicit VM_EXPECT location via
            // vm_out_reg/vm_out_row, respect it. Otherwise, detect
            // the output cell from the trace even when FM_VM_EXPECT
            // is set (builder-provided expected value only).
            let has_explicit_loc = pi.vm_out_row != 0 || pi.vm_out_reg != 0;
            if !has_explicit_loc {
                let (r, row) = utils::vm_output_from_trace(trace);
                pi.vm_out_reg = r;
                pi.vm_out_row = row;
            }
        }

        crate::AirPublicInputs {
            core: pi,
            rom_acc: self.rom_acc,
        }
    }

    fn options(&self) -> &ProofOptions {
        &self.options
    }

    fn new_trace_lde<E: FieldElement<BaseField = Self::BaseField>>(
        &self,
        trace_info: &TraceInfo,
        main_trace: &ColMatrix<Self::BaseField>,
        domain: &StarkDomain<Self::BaseField>,
        partition_option: PartitionOptions,
    ) -> (Self::TraceLde<E>, TracePolyTable<E>) {
        DefaultTraceLde::new(trace_info, main_trace, domain, partition_option)
    }

    fn new_evaluator<'a, E: FieldElement<BaseField = Self::BaseField>>(
        &self,
        air: &'a Self::Air,
        aux_rand_elements: Option<winterfell::AuxRandElements<E>>,
        composition_coefficients: winterfell::ConstraintCompositionCoefficients<E>,
    ) -> Self::ConstraintEvaluator<'a, E> {
        DefaultConstraintEvaluator::new(air, aux_rand_elements, composition_coefficients)
    }

    fn build_constraint_commitment<E: FieldElement<BaseField = Self::BaseField>>(
        &self,
        composition_poly_trace: CompositionPolyTrace<E>,
        num_constraint_composition_columns: usize,
        domain: &StarkDomain<Self::BaseField>,
        partition_options: PartitionOptions,
    ) -> (Self::ConstraintCommitment<E>, CompositionPoly<E>) {
        DefaultConstraintCommitment::new(
            composition_poly_trace,
            num_constraint_composition_columns,
            domain,
            partition_options,
        )
    }
}

// -----------------------------------------
// IVC AIR PROVER
// -----------------------------------------

struct ZlIvWinterfellProver {
    options: ProofOptions,
    pub_inputs: IvAirPublicInputs,
}

impl WProver for ZlIvWinterfellProver {
    type BaseField = BE;
    type Air = ZlIvAir;
    type Trace = TraceTable<Self::BaseField>;
    type HashFn = PoseidonHasher<Self::BaseField>;
    type VC = MerkleTree<Self::HashFn>;
    type RandomCoin = DefaultRandomCoin<Self::HashFn>;
    type TraceLde<E: FieldElement<BaseField = Self::BaseField>> =
        DefaultTraceLde<E, Self::HashFn, Self::VC>;
    type ConstraintEvaluator<'a, E: FieldElement<BaseField = Self::BaseField>> =
        DefaultConstraintEvaluator<'a, Self::Air, E>;
    type ConstraintCommitment<E: FieldElement<BaseField = Self::BaseField>> =
        DefaultConstraintCommitment<E, Self::HashFn, Self::VC>;

    fn get_pub_inputs(&self, _trace: &Self::Trace) -> <Self::Air as Air>::PublicInputs {
        self.pub_inputs.clone()
    }

    fn options(&self) -> &ProofOptions {
        &self.options
    }

    fn new_trace_lde<E: FieldElement<BaseField = Self::BaseField>>(
        &self,
        trace_info: &TraceInfo,
        main_trace: &ColMatrix<Self::BaseField>,
        domain: &StarkDomain<Self::BaseField>,
        partition_option: PartitionOptions,
    ) -> (Self::TraceLde<E>, TracePolyTable<E>) {
        DefaultTraceLde::new(trace_info, main_trace, domain, partition_option)
    }

    fn new_evaluator<'a, E: FieldElement<BaseField = Self::BaseField>>(
        &self,
        air: &'a Self::Air,
        aux_rand_elements: Option<winterfell::AuxRandElements<E>>,
        composition_coefficients: winterfell::ConstraintCompositionCoefficients<E>,
    ) -> Self::ConstraintEvaluator<'a, E> {
        DefaultConstraintEvaluator::new(air, aux_rand_elements, composition_coefficients)
    }

    fn build_constraint_commitment<E: FieldElement<BaseField = Self::BaseField>>(
        &self,
        composition_poly_trace: CompositionPolyTrace<E>,
        num_constraint_composition_columns: usize,
        domain: &StarkDomain<Self::BaseField>,
        partition_options: PartitionOptions,
    ) -> (Self::ConstraintCommitment<E>, CompositionPoly<E>) {
        DefaultConstraintCommitment::new(
            composition_poly_trace,
            num_constraint_composition_columns,
            domain,
            partition_options,
        )
    }
}

#[tracing::instrument(
    level = "info",
    skip(proof, program, pi, opts),
    fields(
        q = %opts.num_queries(),
        blowup = %opts.blowup_factor(),
        grind = %opts.grinding_factor(),
    )
)]
pub fn verify_proof(
    proof: Proof,
    program: &Program,
    pi: PublicInputs,
    opts: &ProofOptions,
    min_bits: u32,
) -> Result<(), Error> {
    pi.validate_flags()?;

    // Enforce a minimum conjectured security
    let acceptable = winterfell::AcceptableOptions::MinConjecturedSecurity(min_bits);

    // Recompute offline ROM accumulator
    // from the program when a non-zero
    // program commitment is present.
    let rom_acc = if pi.program_commitment.iter().any(|b| *b != 0) {
        crate::romacc::rom_acc_from_program(program)
    } else {
        [BE::ZERO; 3]
    };

    tracing::info!(
        target = "proof.verify",
        q = %opts.num_queries(),
        blowup = %opts.blowup_factor(),
        grind = %opts.grinding_factor(),
        "verify proof",
    );

    let t0 = std::time::Instant::now();
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        winterfell::verify::<
            ZkLispAir,
            PoseidonHasher<BE>,
            DefaultRandomCoin<PoseidonHasher<BE>>,
            MerkleTree<PoseidonHasher<BE>>,
        >(
            proof,
            crate::AirPublicInputs { core: pi, rom_acc },
            &acceptable,
        )
    }));

    match res {
        Ok(Ok(())) => {
            let dt = t0.elapsed();
            tracing::info!(
                target = "proof.verify",
                elapsed_ms = %dt.as_millis(),
                "proof verified",
            );

            Ok(())
        }
        Ok(Err(e)) => {
            tracing::error!(
                target = "proof.verify",
                error = %e,
                debug_error = ?e,
                min_bits,
                "verify backend error",
            );

            Err(Error::BackendSource(Box::new(e)))
        }
        Err(_) => {
            tracing::error!(target = "proof.verify", "winterfell panic during verify");

            Err(Error::Backend("winterfell panic during verify".into()))
        }
    }
}

/// Produce a step-level proof wrapper for a single
/// zk-lisp execution segment. This helper mirrors
/// the configuration used by `WinterfellBackend` and
/// returns a `ZlStepProof` ready to be used by IVC.
#[tracing::instrument(
    level = "info",
    skip(program, pub_inputs, opts),
    fields(
        q = %opts.queries,
        blowup = %opts.blowup,
        grind = %opts.grind,
    )
)]
pub fn prove_step(
    program: &Program,
    pub_inputs: &PublicInputs,
    opts: &zk_lisp_proof::ProverOptions,
) -> Result<ZlStepProof, Error> {
    let min_bits = opts.min_security_bits;
    let blowup = if min_bits >= 128 && opts.blowup < 16 {
        16
    } else {
        opts.blowup
    };
    let grind = if min_bits >= 128 && opts.grind < 16 {
        16
    } else {
        opts.grind
    };

    let base_opts = ProofOptions::new(
        opts.queries as usize,
        blowup as usize,
        grind,
        winterfell::FieldExtension::None,
        2,
        1,
        winterfell::BatchingMethod::Linear,
        winterfell::BatchingMethod::Linear,
    );

    let trace = crate::trace::build_trace(program, pub_inputs)?;
    let trace_len = trace.length();

    let (num_partitions, hash_rate) =
        crate::trace::select_partitions_for_trace(trace.width(), trace_len);
    let wf_opts = base_opts.with_partitions(num_partitions, hash_rate);

    // Derive VM state hashes at the beginning
    // and end of the segment. For single-segment
    // proofs we bind the initial state to the map
    // row of level 0 and the final state to the
    // row where the VM output is observed.
    let row0_map = schedule::pos_map();
    let state_in_hash = utils::vm_state_hash_row(&trace, row0_map);

    let (_out_reg, out_row) = utils::vm_output_from_trace(&trace);
    let out_row_usize = (out_row as usize).min(trace_len.saturating_sub(1));
    let state_out_hash = utils::vm_state_hash_row(&trace, out_row_usize);

    // Offline ROM accumulator from program
    let rom_acc = if pub_inputs.program_commitment.iter().any(|b| *b != 0) {
        crate::romacc::rom_acc_from_program(program)
    } else {
        [BE::ZERO; 3]
    };

    // Compute AIR public-input length for metadata
    let air_pi = crate::AirPublicInputs {
        core: pub_inputs.clone(),
        rom_acc,
    };
    let pi_len = air_pi.to_elements().len() as u32;
    let meta = StepMeta::from_env(trace_len, &wf_opts, min_bits, pi_len);
    let suite_id = pub_inputs.program_commitment;

    let prover = ZkProver::new(wf_opts, pub_inputs.clone(), rom_acc);
    let proof = prover.prove(trace)?;

    let zl1_proof = crate::zl1::format::Proof::new_single_segment(
        suite_id,
        meta,
        pub_inputs,
        state_in_hash,
        state_out_hash,
        proof,
    )?;

    Ok(ZlStepProof {
        proof: zl1_proof,
        pi_core: pub_inputs.clone(),
        rom_acc,
    })
}

/// Prove a single IVC aggregation step
/// over ZlIvAir using the provided public
/// inputs and step proofs.
#[tracing::instrument(
    level = "info",
    skip(iv_pi, steps, opts),
    fields(
        q = %opts.queries,
        blowup = %opts.blowup,
        grind = %opts.grind,
    )
)]
pub fn prove_ivc_air(
    iv_pi: &IvPublic,
    steps: &[ZlStepProof],
    opts: &zk_lisp_proof::ProverOptions,
) -> Result<Proof, Error> {
    let min_bits = opts.min_security_bits;
    let blowup = if min_bits >= 128 && opts.blowup < 16 {
        16
    } else {
        opts.blowup
    };
    let grind = if min_bits >= 128 && opts.grind < 16 {
        16
    } else {
        opts.grind
    };

    // Build IVC trace first
    // to size partition options.
    let iv_trace = ivc_trace::build_iv_trace(iv_pi, steps)?;
    let trace = iv_trace.trace;
    let trace_width = trace.width();
    let trace_length = trace.length();

    let (num_partitions, hash_rate) =
        crate::trace::select_partitions_for_trace(trace_width, trace_length);

    let wf_opts = ProofOptions::new(
        opts.queries as usize,
        blowup as usize,
        grind,
        winterfell::FieldExtension::None,
        2,
        1,
        winterfell::BatchingMethod::Linear,
        winterfell::BatchingMethod::Linear,
    )
    .with_partitions(num_partitions, hash_rate);

    let prover = ZlIvWinterfellProver {
        options: wf_opts,
        pub_inputs: IvAirPublicInputs::from(iv_pi),
    };

    tracing::info!(
        target = "proof.ivc.prove",
        q = %prover.options.num_queries(),
        blowup = %prover.options.blowup_factor(),
        grind = %prover.options.grinding_factor(),
        width = %trace_width,
        length = %trace.length(),
        num_partitions = num_partitions,
        hash_rate = hash_rate,
        "ivc prove start",
    );

    let t0 = std::time::Instant::now();
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| prover.prove(trace)))
        .map_err(|_| Error::Backend("winterfell panic during ivc proving".into()))
        .and_then(|r| r.map_err(|e| Error::BackendSource(Box::new(e))));

    match res {
        Ok(proof) => {
            let dt = t0.elapsed();
            tracing::info!(
                target = "proof.ivc.prove",
                elapsed_ms = %dt.as_millis(),
                "ivc proof created",
            );

            Ok(proof)
        }
        Err(e) => Err(e),
    }
}

/// Verify an IVC aggregation proof under ZlIvAir.
#[tracing::instrument(
    level = "info",
    skip(proof, iv_pi, opts),
    fields(
        q = %opts.num_queries(),
        blowup = %opts.blowup_factor(),
        grind = %opts.grinding_factor(),
    )
)]
pub fn verify_ivc_air(
    proof: Proof,
    iv_pi: &IvPublic,
    opts: &ProofOptions,
    min_bits: u32,
) -> Result<(), Error> {
    let acceptable = winterfell::AcceptableOptions::MinConjecturedSecurity(min_bits);
    let pi = IvAirPublicInputs::from(iv_pi);

    tracing::info!(
        target = "proof.ivc.verify",
        q = %opts.num_queries(),
        blowup = %opts.blowup_factor(),
        grind = %opts.grinding_factor(),
        "verify ivc proof",
    );

    let t0 = std::time::Instant::now();
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        winterfell::verify::<
            ZlIvAir,
            PoseidonHasher<BE>,
            DefaultRandomCoin<PoseidonHasher<BE>>,
            MerkleTree<PoseidonHasher<BE>>,
        >(proof, pi, &acceptable)
    }));

    match res {
        Ok(Ok(())) => {
            let dt = t0.elapsed();
            tracing::info!(
                target = "proof.ivc.verify",
                elapsed_ms = %dt.as_millis(),
                "ivc proof verified",
            );

            Ok(())
        }
        Ok(Err(e)) => {
            tracing::error!(
                target = "proof.ivc.verify",
                error = %e,
                debug_error = ?e,
                min_bits,
                "verify ivc backend error",
            );

            Err(Error::BackendSource(Box::new(e)))
        }
        Err(_) => {
            tracing::error!(
                target = "proof.ivc.verify",
                "winterfell panic during ivc verify"
            );

            Err(Error::Backend("winterfell panic during ivc verify".into()))
        }
    }
}

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

use blake3::Hasher;
use rayon::{ThreadPoolBuilder, prelude::*};
use std::error::Error as StdError;
use thiserror::Error;
use winterfell::math::fields::f128::BaseElement;
use winterfell::{
    Air, CompositionPoly, CompositionPolyTrace, DefaultConstraintCommitment,
    DefaultConstraintEvaluator, DefaultTraceLde, PartitionOptions, Proof, ProofOptions,
    Prover as WProver, StarkDomain, Trace, TraceInfo, TracePolyTable, TraceTable,
    crypto::{DefaultRandomCoin, Hasher as WfHasher, MerkleTree},
    math::fields::f128::BaseElement as BE,
    math::{FieldElement, StarkField, ToElements},
    matrix::ColMatrix,
};
use zk_lisp_compiler::Program;
use zk_lisp_proof::error;
use zk_lisp_proof::frontend::PreflightMode;
use zk_lisp_proof::pi as core_pi;
use zk_lisp_proof::pi::PublicInputs;
use zk_lisp_proof::segment::SegmentPlanner;

use crate::agg::air::{AggAirPublicInputs, ZlAggAir};
use crate::agg::child::ZlChildTranscript;
use crate::agg::trace::build_agg_trace_from_transcripts;
use crate::poseidon::hasher::PoseidonHasher;
use crate::proof::step::{StepMeta, StepProof};
use crate::segment_planner::{
    WinterfellSegmentPlanner, compute_segment_feature_mask, compute_segment_features_for_levels,
};
use crate::vm::air::ZkLispAir;
use crate::vm::layout::{Columns, LayoutConfig, STEPS_PER_LEVEL_P2};
use crate::vm::{schedule, trace};
use crate::{preflight::run as run_preflight, utils};

#[derive(Debug, Error)]
pub enum Error {
    #[error("backend error: {0}")]
    Backend(String),
    #[error("backend error: {0}")]
    BackendSource(#[source] Box<dyn StdError + Send + Sync + 'static>),
    #[error("recursion invalid input: {0}")]
    RecursionInvalid(&'static str),
    #[error(transparent)]
    PublicInputs(#[from] error::Error),
}

#[derive(Clone, Debug)]
pub struct VerifyBoundaries {
    pub pc_init: [u8; 32],
    pub ram_gp_unsorted_in: [u8; 32],
    pub ram_gp_unsorted_out: [u8; 32],
    pub ram_gp_sorted_in: [u8; 32],
    pub ram_gp_sorted_out: [u8; 32],
    pub rom_s_in: [[u8; 32]; 3],
    pub rom_s_out: [[u8; 32]; 3],
}

impl VerifyBoundaries {
    pub fn from_step(step: &StepProof) -> Self {
        let pi = &step.proof.pi;
        VerifyBoundaries {
            pc_init: pi.pc_init,
            ram_gp_unsorted_in: pi.ram_gp_unsorted_in,
            ram_gp_unsorted_out: pi.ram_gp_unsorted_out,
            ram_gp_sorted_in: pi.ram_gp_sorted_in,
            ram_gp_sorted_out: pi.ram_gp_sorted_out,
            rom_s_in: [pi.rom_s_in_0, pi.rom_s_in_1, pi.rom_s_in_2],
            rom_s_out: [pi.rom_s_out_0, pi.rom_s_out_1, pi.rom_s_out_2],
        }
    }
}

/// Field-level boundary state for a single
/// execution segment, mirroring
/// [`SegmentBoundaryBytes`] but using
/// `BaseElement` values.
#[derive(Clone, Debug)]
pub(crate) struct SegmentBoundariesFe {
    pc_init: BE,
    ram_gp_unsorted_in: BE,
    ram_gp_unsorted_out: BE,
    ram_gp_sorted_in: BE,
    ram_gp_sorted_out: BE,
    rom_s_in: [BE; 3],
    rom_s_out: [BE; 3],
}

#[derive(Debug)]
pub struct ZkProver {
    options: ProofOptions,
    pub_inputs: PublicInputs,
    rom_acc: [BE; 3],
    preflight: PreflightMode,
    /// Optional segment-local feature mask used
    /// when proving a single execution segment.
    /// Zero means "use core.feature_mask".
    segment_feature_mask: u64,
    /// Optional layout for the concrete trace.
    segment_cols: Option<Columns>,
    /// Optional precomputed boundary state.
    segment_boundaries: Option<SegmentBoundariesFe>,
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
            segment_feature_mask: 0,
            segment_cols: None,
            segment_boundaries: None,
        }
    }

    fn with_segment_layout(
        mut self,
        segment_feature_mask: u64,
        cols: Columns,
        boundaries: SegmentBoundariesFe,
    ) -> Self {
        self.segment_feature_mask = segment_feature_mask;
        self.segment_cols = Some(cols);
        self.segment_boundaries = Some(boundaries);
        self
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
            "creating proof...",
        );

        // Preflight timing
        if !matches!(self.preflight, PreflightMode::Off) {
            let t_pf = std::time::Instant::now();
            run_preflight(self.preflight, &self.options, &self.pub_inputs, &trace)?;

            tracing::debug!(
                target = "proof.prove",
                elapsed_ms = %t_pf.elapsed().as_millis(),
                "preflight done",
            );
        }

        let prover = ZkWinterfellProver {
            options: self.options.clone(),
            pub_inputs: self.pub_inputs.clone(),
            rom_acc: self.rom_acc,
            segment_feature_mask: self.segment_feature_mask,
            segment_cols: self.segment_cols.clone(),
            segment_boundaries: self.segment_boundaries.clone(),
        };

        // Winterfell orchestration timing
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
    segment_feature_mask: u64,
    segment_cols: Option<Columns>,
    segment_boundaries: Option<SegmentBoundariesFe>,
}

/// Byte-encoded boundary state for a single execution
/// segment. These values are derived from the concrete
struct SegmentBoundaryBytes {
    pc_init: [u8; 32],
    ram_gp_unsorted_in: [u8; 32],
    ram_gp_unsorted_out: [u8; 32],
    ram_gp_sorted_in: [u8; 32],
    ram_gp_sorted_out: [u8; 32],
    rom_s_in_0: [u8; 32],
    rom_s_in_1: [u8; 32],
    rom_s_in_2: [u8; 32],
    rom_s_out_0: [u8; 32],
    rom_s_out_1: [u8; 32],
    rom_s_out_2: [u8; 32],
}

impl From<&SegmentBoundaryBytes> for SegmentBoundariesFe {
    fn from(b: &SegmentBoundaryBytes) -> Self {
        SegmentBoundariesFe {
            pc_init: utils::fe_from_bytes_fold(&b.pc_init),
            ram_gp_unsorted_in: utils::fe_from_bytes_fold(&b.ram_gp_unsorted_in),
            ram_gp_unsorted_out: utils::fe_from_bytes_fold(&b.ram_gp_unsorted_out),
            ram_gp_sorted_in: utils::fe_from_bytes_fold(&b.ram_gp_sorted_in),
            ram_gp_sorted_out: utils::fe_from_bytes_fold(&b.ram_gp_sorted_out),
            rom_s_in: [
                utils::fe_from_bytes_fold(&b.rom_s_in_0),
                utils::fe_from_bytes_fold(&b.rom_s_in_1),
                utils::fe_from_bytes_fold(&b.rom_s_in_2),
            ],
            rom_s_out: [
                utils::fe_from_bytes_fold(&b.rom_s_out_0),
                utils::fe_from_bytes_fold(&b.rom_s_out_1),
                utils::fe_from_bytes_fold(&b.rom_s_out_2),
            ],
        }
    }
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

        // Compute VM output location (last op level).
        // For segment proofs rely on the segment-local
        // layout when provided.
        if (pi.feature_mask & core_pi::FM_VM) != 0 {
            let has_explicit_loc = pi.vm_out_row != 0 || pi.vm_out_reg != 0;
            if !has_explicit_loc {
                if let Some(cols) = &self.segment_cols {
                    let (r, row) = utils::vm_output_from_trace_with_layout(trace, cols);
                    pi.vm_out_reg = r;
                    pi.vm_out_row = row;
                } else {
                    let (r, row) = utils::vm_output_from_trace(trace);
                    pi.vm_out_reg = r;
                    pi.vm_out_row = row;
                }
            }
        }

        let steps = STEPS_PER_LEVEL_P2;
        let n_rows = trace.length();

        let boundaries = if let Some(b) = &self.segment_boundaries {
            b.clone()
        } else {
            let cols = if let Some(cols) = &self.segment_cols {
                cols.clone()
            } else {
                Columns::baseline()
            };

            debug_assert_eq!(trace.width(), cols.width(0));

            let pc_init = if n_rows > 0 {
                trace.get(cols.pc, schedule::pos_map())
            } else {
                BE::ZERO
            };

            let last = n_rows.saturating_sub(1);

            let (ram_gp_unsorted_in, ram_gp_unsorted_out, ram_gp_sorted_in, ram_gp_sorted_out) =
                if n_rows > 0 {
                    (
                        trace.get(cols.ram_gp_unsorted, 0),
                        trace.get(cols.ram_gp_unsorted, last),
                        trace.get(cols.ram_gp_sorted, 0),
                        trace.get(cols.ram_gp_sorted, last),
                    )
                } else {
                    (BE::ZERO, BE::ZERO, BE::ZERO, BE::ZERO)
                };

            // ROM boundaries at the first map row and the final row of
            // the last level present in this trace segment.
            let (rom_s_in, rom_s_out) = if n_rows > 0 && steps > 0 {
                let lvl_first = 0usize;
                let lvl_last = last / steps;

                let row_map_first = lvl_first * steps + schedule::pos_map();
                let row_final_last = lvl_last * steps + schedule::pos_final();

                if row_map_first < n_rows && row_final_last < n_rows {
                    let s_in = [
                        trace.get(cols.rom_s_index(0), row_map_first),
                        trace.get(cols.rom_s_index(1), row_map_first),
                        trace.get(cols.rom_s_index(2), row_map_first),
                    ];
                    let s_out = [
                        trace.get(cols.rom_s_index(0), row_final_last),
                        trace.get(cols.rom_s_index(1), row_final_last),
                        trace.get(cols.rom_s_index(2), row_final_last),
                    ];

                    (s_in, s_out)
                } else {
                    ([BE::ZERO; 3], [BE::ZERO; 3])
                }
            } else {
                ([BE::ZERO; 3], [BE::ZERO; 3])
            };

            SegmentBoundariesFe {
                pc_init,
                ram_gp_unsorted_in,
                ram_gp_unsorted_out,
                ram_gp_sorted_in,
                ram_gp_sorted_out,
                rom_s_in,
                rom_s_out,
            }
        };

        crate::AirPublicInputs {
            core: pi,
            segment_feature_mask: self.segment_feature_mask,
            rom_acc: self.rom_acc,
            pc_init: boundaries.pc_init,
            ram_gp_unsorted_in: boundaries.ram_gp_unsorted_in,
            ram_gp_unsorted_out: boundaries.ram_gp_unsorted_out,
            ram_gp_sorted_in: boundaries.ram_gp_sorted_in,
            ram_gp_sorted_out: boundaries.ram_gp_sorted_out,
            rom_s_in: boundaries.rom_s_in,
            rom_s_out: boundaries.rom_s_out,
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
        let t = std::time::Instant::now();
        let (lde, polys) = DefaultTraceLde::new(trace_info, main_trace, domain, partition_option);

        tracing::debug!(
            target = "proof.prove",
            rows = %main_trace.num_rows(),
            cols = %main_trace.num_cols(),
            blowup = %domain.trace_to_lde_blowup(),
            elapsed_ms = %t.elapsed().as_millis(),
            "new_trace_lde done",
        );

        (lde, polys)
    }

    fn new_evaluator<'a, E: FieldElement<BaseField = Self::BaseField>>(
        &self,
        air: &'a Self::Air,
        aux_rand_elements: Option<winterfell::AuxRandElements<E>>,
        composition_coefficients: winterfell::ConstraintCompositionCoefficients<E>,
    ) -> Self::ConstraintEvaluator<'a, E> {
        let t = std::time::Instant::now();
        let ev = DefaultConstraintEvaluator::new(air, aux_rand_elements, composition_coefficients);

        tracing::debug!(
            target = "proof.prove",
            elapsed_ms=%t.elapsed().as_millis(),
            "new_evaluator done",
        );

        ev
    }

    fn build_constraint_commitment<E: FieldElement<BaseField = Self::BaseField>>(
        &self,
        composition_poly_trace: CompositionPolyTrace<E>,
        num_constraint_composition_columns: usize,
        domain: &StarkDomain<Self::BaseField>,
        partition_options: PartitionOptions,
    ) -> (Self::ConstraintCommitment<E>, CompositionPoly<E>) {
        let t = std::time::Instant::now();
        let out = DefaultConstraintCommitment::new(
            composition_poly_trace,
            num_constraint_composition_columns,
            domain,
            partition_options,
        );

        tracing::debug!(
            target = "proof.prove",
            elapsed_ms=%t.elapsed().as_millis(),
            "build_constraint_commitment done",
        );

        out
    }
}

/// Winterfell prover wrapper for the aggregation AIR
/// `ZlAggAir`. This mirrors `ZlIvWinterfellProver` but
struct ZlAggWinterfellProver {
    options: ProofOptions,
    pub_inputs: AggAirPublicInputs,
}

impl WProver for ZlAggWinterfellProver {
    type BaseField = BE;
    type Air = ZlAggAir;
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

/// Compute a 32-byte recursion digest from aggregation
/// public inputs. This binds the aggregation proof to
pub(crate) fn recursion_digest_from_agg_pi(agg_pi: &AggAirPublicInputs) -> [u8; 32] {
    let mut h = Hasher::new();
    h.update(b"zkl/recursion/agg");
    h.update(&agg_pi.suite_id);
    h.update(&agg_pi.batch_id);
    h.update(&agg_pi.children_root);

    h.update(&agg_pi.children_count.to_le_bytes());
    h.update(&agg_pi.v_units_total.to_le_bytes());

    h.update(&agg_pi.profile_meta.m.to_le_bytes());
    h.update(&agg_pi.profile_meta.rho.to_le_bytes());
    h.update(&agg_pi.profile_meta.q.to_le_bytes());
    h.update(&agg_pi.profile_meta.o.to_le_bytes());
    h.update(&agg_pi.profile_meta.lambda.to_le_bytes());
    h.update(&agg_pi.profile_meta.pi_len.to_le_bytes());
    h.update(&agg_pi.profile_meta.v_units.to_le_bytes());

    h.update(&agg_pi.profile_fri.lde_blowup.to_le_bytes());
    h.update(&agg_pi.profile_fri.folding_factor.to_le_bytes());
    h.update(&agg_pi.profile_fri.redundancy.to_le_bytes());
    h.update(&agg_pi.profile_fri.num_layers.to_le_bytes());

    h.update(&agg_pi.profile_queries.num_queries.to_le_bytes());
    h.update(&agg_pi.profile_queries.grinding_factor.to_le_bytes());

    let digest = h.finalize();
    let mut out = [0u8; 32];
    out.copy_from_slice(digest.as_bytes());

    out
}

/// Prove a single aggregation step over `ZlAggAir` using
/// fully decoded child transcripts and aggregation public
#[tracing::instrument(
    level = "info",
    skip(agg_pi, transcripts, opts),
    fields(
        q = %opts.queries,
        blowup = %opts.blowup,
        grind = %opts.grind,
    )
)]
pub fn prove_agg_proof(
    agg_pi: &AggAirPublicInputs,
    transcripts: &[ZlChildTranscript],
    opts: &zk_lisp_proof::ProverOptions,
) -> Result<Proof, Error> {
    let min_bits = opts.min_security_bits;
    let blowup = opts.blowup;
    let grind = opts.grind;

    let agg_trace = build_agg_trace_from_transcripts(agg_pi, transcripts)?;
    let trace = agg_trace.trace;
    let trace_width = trace.width();
    let trace_length = trace.length();

    let (num_partitions, hash_rate) = utils::select_partitions_for_trace(trace_width, trace_length);

    let agg_queries = opts.queries.max(16) as usize;

    let field_extension = if min_bits >= 128 {
        winterfell::FieldExtension::Quadratic
    } else {
        winterfell::FieldExtension::None
    };

    let base_opts = ProofOptions::new(
        agg_queries,
        blowup as usize,
        grind,
        field_extension,
        2,
        1,
        winterfell::BatchingMethod::Linear,
        winterfell::BatchingMethod::Linear,
    );

    if min_bits >= 64 {
        let bits = estimate_conjectured_security_bits(&base_opts);
        if bits < min_bits {
            tracing::error!(
                target = "proof.agg.prove",
                estimated_bits = bits,
                min_bits,
                queries = agg_queries,
                blowup,
                grind,
                "aggregation prover options do not meet requested security",
            );

            return Err(Error::PublicInputs(error::Error::InvalidInput(
                "aggregation prover options do not achieve requested min_security_bits; increase --queries/--blowup/--grind or lower --security-bits",
            )));
        }
    }

    let wf_opts = base_opts.with_partitions(num_partitions, hash_rate);
    let prover = ZlAggWinterfellProver {
        options: wf_opts,
        pub_inputs: agg_pi.clone(),
    };

    tracing::info!(
        target = "proof.agg.prove",
        q = %prover.options.num_queries(),
        blowup = %prover.options.blowup_factor(),
        grind = %prover.options.grinding_factor(),
        width = %trace_width,
        length = %trace.length(),
        num_partitions = num_partitions,
        hash_rate = hash_rate,
        "creating agg proof...",
    );

    let t0 = std::time::Instant::now();
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| prover.prove(trace)))
        .map_err(|_| Error::Backend("winterfell panic during agg proving".into()))
        .and_then(|r| r.map_err(|e| Error::BackendSource(Box::new(e))));

    match res {
        Ok(proof) => {
            let dt = t0.elapsed();
            tracing::info!(
                target = "proof.agg.prove",
                elapsed_ms = %dt.as_millis(),
                "agg proof created",
            );

            Ok(proof)
        }
        Err(e) => Err(e),
    }
}

/// Verify an aggregation proof under `ZlAggAir`.
#[tracing::instrument(
    level = "info",
    skip(proof, agg_pi, opts),
    fields(
        min_bits = %min_bits,
        q = %opts.num_queries(),
        blowup = %opts.blowup_factor(),
        grind = %opts.grinding_factor(),
    )
)]
pub fn verify_agg_proof(
    proof: Proof,
    agg_pi: &AggAirPublicInputs,
    opts: &ProofOptions,
    min_bits: u32,
) -> Result<(), Error> {
    let acceptable = winterfell::AcceptableOptions::MinConjecturedSecurity(min_bits);

    tracing::info!(
        target = "proof.agg.verify",
        min_bits = %min_bits,
        q = %opts.num_queries(),
        blowup = %opts.blowup_factor(),
        grind = %opts.grinding_factor(),
        "verify agg proof",
    );

    let t0 = std::time::Instant::now();
    let pi = agg_pi.clone();
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        winterfell::verify::<
            ZlAggAir,
            PoseidonHasher<BE>,
            DefaultRandomCoin<PoseidonHasher<BE>>,
            MerkleTree<PoseidonHasher<BE>>,
        >(proof, pi, &acceptable)
    }));

    match res {
        Ok(Ok(())) => {
            let dt = t0.elapsed();
            tracing::info!(
                target = "proof.agg.verify",
                elapsed_ms = %dt.as_millis(),
                "agg proof verified",
            );

            Ok(())
        }
        Ok(Err(e)) => {
            tracing::error!(
                target = "proof.agg.verify",
                error = %e,
                debug_error = ?e,
                min_bits,
                "verify agg backend error",
            );

            Err(Error::BackendSource(Box::new(e)))
        }
        Err(_) => {
            tracing::error!(
                target = "proof.agg.verify",
                "winterfell panic during agg verify"
            );

            Err(Error::Backend("winterfell panic during agg verify".into()))
        }
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
    // Slow path retained for compatibility;
    // prefer verify_proof_fast when caller
    pi.validate_flags()?;

    // Enforce a minimum conjectured security
    let acceptable = winterfell::AcceptableOptions::MinConjecturedSecurity(min_bits);

    // Recompute offline ROM accumulator
    // from the program when a non-zero
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

    // Rebuild a minimal execution trace to derive the same
    // boundary public inputs used by the prover so that the
    let trace = trace::build_trace(program, &pi)?;
    let cols = Columns::baseline();
    let steps = STEPS_PER_LEVEL_P2;
    let n_rows = trace.length();
    let last = n_rows.saturating_sub(1);

    let pc_init = if n_rows > 0 {
        trace.get(cols.pc, schedule::pos_map())
    } else {
        BE::ZERO
    };

    let (ram_gp_unsorted_in, ram_gp_unsorted_out, ram_gp_sorted_in, ram_gp_sorted_out) =
        if n_rows > 0 {
            (
                trace.get(cols.ram_gp_unsorted, 0),
                trace.get(cols.ram_gp_unsorted, last),
                trace.get(cols.ram_gp_sorted, 0),
                trace.get(cols.ram_gp_sorted, last),
            )
        } else {
            (BE::ZERO, BE::ZERO, BE::ZERO, BE::ZERO)
        };

    let (rom_s_in, rom_s_out) = if n_rows > 0 && steps > 0 {
        let lvl_first = 0usize;
        let lvl_last = last / steps;
        let row_map_first = lvl_first * steps + schedule::pos_map();
        let row_final_last = lvl_last * steps + schedule::pos_final();

        if row_map_first < n_rows && row_final_last < n_rows {
            let s_in = [
                trace.get(cols.rom_s_index(0), row_map_first),
                trace.get(cols.rom_s_index(1), row_map_first),
                trace.get(cols.rom_s_index(2), row_map_first),
            ];
            let s_out = [
                trace.get(cols.rom_s_index(0), row_final_last),
                trace.get(cols.rom_s_index(1), row_final_last),
                trace.get(cols.rom_s_index(2), row_final_last),
            ];
            (s_in, s_out)
        } else {
            ([BE::ZERO; 3], [BE::ZERO; 3])
        }
    } else {
        ([BE::ZERO; 3], [BE::ZERO; 3])
    };

    let t0 = std::time::Instant::now();
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        winterfell::verify::<
            ZkLispAir,
            PoseidonHasher<BE>,
            DefaultRandomCoin<PoseidonHasher<BE>>,
            MerkleTree<PoseidonHasher<BE>>,
        >(
            proof,
            crate::AirPublicInputs {
                core: pi,
                segment_feature_mask: 0,
                rom_acc,
                pc_init,
                ram_gp_unsorted_in,
                ram_gp_unsorted_out,
                ram_gp_sorted_in,
                ram_gp_sorted_out,
                rom_s_in,
                rom_s_out,
            },
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

/// Prove a sequence of execution segments for a single
/// zk-lisp program, returning one `ZlStepProof` per
#[tracing::instrument(
    level = "info",
    skip(program, pub_inputs, opts),
    fields(
        q = %opts.queries,
        blowup = %opts.blowup,
        grind = %opts.grind,
    )
)]
pub fn prove_program(
    program: &Program,
    pub_inputs: &PublicInputs,
    opts: &zk_lisp_proof::ProverOptions,
) -> Result<Vec<StepProof>, Error> {
    let min_bits = opts.min_security_bits;
    let blowup = opts.blowup;
    let grind = opts.grind;

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

    let segments = WinterfellSegmentPlanner::plan_segments(program, pub_inputs, opts)?;
    if segments.is_empty() {
        return Err(Error::PublicInputs(error::Error::InvalidInput(
            "WinterfellSegmentPlanner returned no segments",
        )));
    }

    // Build the full trace once and reuse both boundary
    // state and segment-local traces per segment.
    let full_trace = trace::build_trace(program, pub_inputs)?;
    let segments_len = segments.len();
    let suite_id = pub_inputs.program_id;
    let rom_acc = if pub_inputs.program_id.iter().any(|b| *b != 0) {
        crate::romacc::rom_acc_from_program(program)
    } else {
        [BE::ZERO; 3]
    };

    let max_parallel = opts.max_concurrent_segments.unwrap_or(1);
    let max_parallel = max_parallel.max(1);

    let mut steps = Vec::with_capacity(segments.len());
    let mut prev_state: Option<trace::PrevState> = None;

    if max_parallel == 1 || segments_len == 1 {
        for (i, seg) in segments.iter().enumerate() {
            let (step, state_out_hash) = prove_segment(
                suite_id,
                rom_acc,
                i,
                segments_len,
                seg,
                &full_trace,
                program,
                pub_inputs,
                &base_opts,
                min_bits,
                prev_state.as_ref(),
            )?;

            steps.push(step);
            prev_state = Some(trace::PrevState { state_out_hash });
        }
    } else {
        // Build a local rayon thread pool to bound the
        // number of worker threads used for child proofs.
        let pool = ThreadPoolBuilder::new()
            .num_threads(max_parallel)
            .build()
            .map_err(|e| Error::Backend(format!("failed to build rayon thread pool: {e}")))?;

        // Run all segments in parallel
        let results: Result<Vec<StepProof>, Error> = pool.install(|| {
            segments
                .par_iter()
                .enumerate()
                .map(|(i, seg)| {
                    let (step, _state_out_hash) = prove_segment(
                        suite_id,
                        rom_acc,
                        i,
                        segments_len,
                        seg,
                        &full_trace,
                        program,
                        pub_inputs,
                        &base_opts,
                        min_bits,
                        None, // disable prev_state chain check in parallel mode
                    )?;

                    Ok(step)
                })
                .collect()
        });

        steps = results?;
    }

    Ok(steps)
}

#[allow(clippy::too_many_arguments)]
fn prove_segment(
    suite_id: [u8; 32],
    rom_acc: [BaseElement; 3],
    segment_index: usize,
    segments_total: usize,
    seg: &zk_lisp_proof::segment::Segment,
    full_trace: &TraceTable<BE>,
    program: &Program,
    pub_inputs: &PublicInputs,
    base_opts: &ProofOptions,
    min_bits: u32,
    prev_state: Option<&trace::PrevState>,
) -> Result<(StepProof, [u8; 32]), Error> {
    let lvl_start = seg.r_start / STEPS_PER_LEVEL_P2;
    let lvl_end = seg.r_end / STEPS_PER_LEVEL_P2;
    let seg_features = compute_segment_features_for_levels(program, lvl_start, lvl_end);

    tracing::debug!(
        target = "proof.steps",
        segment_index = segment_index,
        lvl_start = lvl_start,
        lvl_end = lvl_end,
        features = ?seg_features,
    );

    let base_mask = pub_inputs.feature_mask;
    let seg_mask = compute_segment_feature_mask(pub_inputs, &seg_features);
    let use_seg_mask = seg_mask != 0 && seg_mask != base_mask;
    let eff_mask = if use_seg_mask { seg_mask } else { base_mask };
    let features_map = zk_lisp_proof::pi::FeaturesMap::from_mask(eff_mask);
    let rom_enabled = pub_inputs.program_id.iter().any(|b| *b != 0);

    let layout_cfg = if use_seg_mask {
        LayoutConfig {
            vm: true,
            ram: features_map.ram,
            sponge: features_map.sponge,
            merkle: features_map.merkle,
            rom: rom_enabled,
        }
    } else {
        LayoutConfig {
            vm: true,
            ram: true,
            sponge: true,
            merkle: true,
            rom: rom_enabled,
        }
    };

    let full_cols = Columns::baseline();
    let seg_layout = trace::SegmentLayout::from_full_columns(&full_cols, &layout_cfg);

    let (trace, state_in_hash, state_out_hash) =
        trace::build_segment_trace_with_state_without_full(
            &full_trace,
            &seg,
            &seg_layout,
            prev_state,
        )?;
    let trace_len = trace.length();

    let boundary_bytes = compute_segment_boundary_bytes(&full_trace, &seg)?;
    let boundaries_fe = SegmentBoundariesFe::from(&boundary_bytes);
    let segment_feature_mask_for_air = if use_seg_mask { eff_mask } else { 0 };

    let (num_partitions, hash_rate) = utils::select_partitions_for_trace(trace.width(), trace_len);
    let wf_opts = base_opts.clone().with_partitions(num_partitions, hash_rate);

    let air_pi = crate::AirPublicInputs {
        core: pub_inputs.clone(),
        segment_feature_mask: segment_feature_mask_for_air,
        rom_acc,
        pc_init: boundaries_fe.pc_init,
        ram_gp_unsorted_in: boundaries_fe.ram_gp_unsorted_in,
        ram_gp_unsorted_out: boundaries_fe.ram_gp_unsorted_out,
        ram_gp_sorted_in: boundaries_fe.ram_gp_sorted_in,
        ram_gp_sorted_out: boundaries_fe.ram_gp_sorted_out,
        rom_s_in: boundaries_fe.rom_s_in,
        rom_s_out: boundaries_fe.rom_s_out,
    };
    let pi_len = air_pi.to_elements().len() as u32;
    let meta = StepMeta::from_env(trace_len, &wf_opts, min_bits, pi_len);

    let prover = ZkProver::new(wf_opts, pub_inputs.clone(), rom_acc).with_segment_layout(
        segment_feature_mask_for_air,
        seg_layout.cols.clone(),
        boundaries_fe,
    );
    let proof = prover.prove(trace)?;

    let zl1_proof = crate::proof::format::Proof::new_multi_segment(
        suite_id,
        meta,
        pub_inputs,
        segment_index as u32,
        segments_total as u32,
        boundary_bytes.pc_init,
        state_in_hash,
        state_out_hash,
        boundary_bytes.ram_gp_unsorted_in,
        boundary_bytes.ram_gp_unsorted_out,
        boundary_bytes.ram_gp_sorted_in,
        boundary_bytes.ram_gp_sorted_out,
        boundary_bytes.rom_s_in_0,
        boundary_bytes.rom_s_in_1,
        boundary_bytes.rom_s_in_2,
        boundary_bytes.rom_s_out_0,
        boundary_bytes.rom_s_out_1,
        boundary_bytes.rom_s_out_2,
        proof,
    )?;

    let step_proof = StepProof {
        proof: zl1_proof,
        pi_core: pub_inputs.clone(),
        rom_acc,
    };

    Ok((step_proof, state_out_hash))
}

fn estimate_conjectured_security_bits(opts: &ProofOptions) -> u32 {
    let base_field_bits = BE::MODULUS_BITS;
    let field_security = base_field_bits * opts.field_extension().degree();

    let blowup = opts.blowup_factor() as u32;
    let security_per_query = blowup.ilog2();
    let mut query_security = security_per_query * opts.num_queries() as u32;

    if query_security >= 80 {
        query_security += opts.grinding_factor();
    }

    let collision_resistance = <PoseidonHasher<BE> as WfHasher>::COLLISION_RESISTANCE;

    core::cmp::min(
        core::cmp::min(field_security, query_security) - 1,
        collision_resistance,
    )
}

fn compute_segment_boundary_bytes(
    trace: &TraceTable<BE>,
    segment: &zk_lisp_proof::segment::Segment,
) -> error::Result<SegmentBoundaryBytes> {
    let t = std::time::Instant::now();

    if segment.r_start >= segment.r_end {
        return Err(error::Error::InvalidInput(
            "segment r_start must be < r_end when computing boundary state",
        ));
    }

    let n_rows = trace.length();
    if segment.r_end > n_rows {
        return Err(error::Error::InvalidInput(
            "segment end row out of bounds for trace in boundary computation",
        ));
    }

    let cols = Columns::baseline();
    let steps = STEPS_PER_LEVEL_P2;
    let r_start = segment.r_start;
    let r_end = segment.r_end;

    // pc at the first map row of the segment
    let row_map_first = (r_start / steps) * steps + schedule::pos_map();
    let pc_init_fe = trace.get(cols.pc, row_map_first);

    // RAM grand-product accumulators are carried row-wise; we
    // take the values at the first and last rows of the segment.
    let ram_gp_unsorted_in_fe = trace.get(cols.ram_gp_unsorted, r_start);
    let ram_gp_unsorted_out_fe = trace.get(cols.ram_gp_unsorted, r_end - 1);
    let ram_gp_sorted_in_fe = trace.get(cols.ram_gp_sorted, r_start);
    let ram_gp_sorted_out_fe = trace.get(cols.ram_gp_sorted, r_end - 1);

    // ROM t=3 accumulator state is defined in terms of VM levels.
    // We select the map row of the first level touched by the
    let lvl_first = r_start / steps;
    let lvl_last = (r_end - 1) / steps;

    let row_map_first = lvl_first
        .checked_mul(steps)
        .and_then(|base| base.checked_add(schedule::pos_map()))
        .ok_or(error::Error::InvalidInput(
            "overflow while computing ROM map row for segment boundary state",
        ))?;

    let row_final_last = lvl_last
        .checked_mul(steps)
        .and_then(|base| base.checked_add(schedule::pos_final()))
        .ok_or(error::Error::InvalidInput(
            "overflow while computing ROM final row for segment boundary state",
        ))?;

    if row_map_first >= n_rows || row_final_last >= n_rows {
        return Err(error::Error::InvalidInput(
            "ROM boundary rows out of bounds for trace in boundary computation",
        ));
    }

    let rom_s_in_0_fe = trace.get(cols.rom_s_index(0), row_map_first);
    let rom_s_in_1_fe = trace.get(cols.rom_s_index(1), row_map_first);
    let rom_s_in_2_fe = trace.get(cols.rom_s_index(2), row_map_first);

    let rom_s_out_0_fe = trace.get(cols.rom_s_index(0), row_final_last);
    let rom_s_out_1_fe = trace.get(cols.rom_s_index(1), row_final_last);
    let rom_s_out_2_fe = trace.get(cols.rom_s_index(2), row_final_last);

    let out = SegmentBoundaryBytes {
        pc_init: utils::fe_to_bytes_fold(pc_init_fe),
        ram_gp_unsorted_in: utils::fe_to_bytes_fold(ram_gp_unsorted_in_fe),
        ram_gp_unsorted_out: utils::fe_to_bytes_fold(ram_gp_unsorted_out_fe),
        ram_gp_sorted_in: utils::fe_to_bytes_fold(ram_gp_sorted_in_fe),
        ram_gp_sorted_out: utils::fe_to_bytes_fold(ram_gp_sorted_out_fe),
        rom_s_in_0: utils::fe_to_bytes_fold(rom_s_in_0_fe),
        rom_s_in_1: utils::fe_to_bytes_fold(rom_s_in_1_fe),
        rom_s_in_2: utils::fe_to_bytes_fold(rom_s_in_2_fe),
        rom_s_out_0: utils::fe_to_bytes_fold(rom_s_out_0_fe),
        rom_s_out_1: utils::fe_to_bytes_fold(rom_s_out_1_fe),
        rom_s_out_2: utils::fe_to_bytes_fold(rom_s_out_2_fe),
    };

    tracing::debug!(
        target = "proof.segment",
        seg_rows = %segment.len(),
        elapsed_ms = %t.elapsed().as_millis(),
        "segment boundary bytes computed",
    );

    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::segment_planner::{SegmentFeatures, compute_segment_feature_mask};
    use zk_lisp_proof::pi::{FM_POSEIDON, FM_RAM, FM_SPONGE, FM_VM, FM_VM_EXPECT};

    fn derive_seg_mask_for_air(base_mask: u64, seg_features: &SegmentFeatures) -> (u64, u64) {
        let pi = PublicInputs {
            feature_mask: base_mask,
            ..Default::default()
        };

        let seg_mask = compute_segment_feature_mask(&pi, seg_features);
        let use_seg_mask = seg_mask != 0 && seg_mask != base_mask;
        let eff_mask = if use_seg_mask { seg_mask } else { base_mask };
        let seg_air = if use_seg_mask { eff_mask } else { 0 };

        (seg_mask, seg_air)
    }

    #[test]
    fn seg_air_mask_zero_when_equal_to_global() {
        let base = FM_VM | FM_VM_EXPECT | FM_RAM;
        let seg = SegmentFeatures {
            vm: true,
            ram: true,
            sponge: false,
            merkle: false,
        };

        let (seg_mask, seg_air) = derive_seg_mask_for_air(base, &seg);
        assert_eq!(seg_mask, base);
        assert_eq!(seg_air, 0);
    }

    #[test]
    fn seg_air_mask_nonzero_when_optional_feature_dropped() {
        let base = FM_VM | FM_VM_EXPECT | FM_RAM | FM_SPONGE | FM_POSEIDON;
        let seg = SegmentFeatures {
            vm: true,
            ram: false,
            sponge: false,
            merkle: false,
        };
        let (seg_mask, seg_air) = derive_seg_mask_for_air(base, &seg);

        assert_ne!(seg_mask, 0);
        assert_ne!(seg_mask, base);
        assert_eq!(seg_air, seg_mask);
        assert_eq!(seg_air & !base, 0);
        assert_eq!(seg_air & (FM_RAM | FM_SPONGE | FM_POSEIDON), 0);
        assert_ne!(seg_air & (FM_VM | FM_VM_EXPECT), 0);
    }
}

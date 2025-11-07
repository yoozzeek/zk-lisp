use thiserror::Error;
use winterfell::{
    Air, CompositionPoly, CompositionPolyTrace, DefaultConstraintCommitment,
    DefaultConstraintEvaluator, DefaultTraceLde, EvaluationFrame, PartitionOptions, Proof,
    ProofOptions, Prover as WProver, StarkDomain, Trace, TraceInfo, TracePolyTable, TraceTable,
    crypto::{DefaultRandomCoin, MerkleTree, hashers::Blake3_256},
    math::FieldElement,
    math::fields::f128::BaseElement as BE,
    matrix::ColMatrix,
};

use crate::air::ZkLispAir;
use crate::pi::PublicInputs;
use crate::trace::TraceBuilder;

#[derive(Debug, Error)]
pub enum Error {
    #[error("prove: backend error {0}")]
    Backend(String),
}

pub struct ZkProver {
    options: ProofOptions,
    pub_inputs: PublicInputs,
}

impl ZkProver {
    pub fn new(options: ProofOptions, pub_inputs: PublicInputs) -> Self {
        Self {
            options,
            pub_inputs,
        }
    }

    pub fn prove(&self, trace: TraceTable<BE>) -> Result<Proof, Error> {
        // Optional preflight in debug
        if cfg!(debug_assertions) {
            preflight(&self.options, &self.pub_inputs, &trace)?;
        }

        let prover = ZkWinterfellProver {
            options: self.options.clone(),
            pub_inputs: self.pub_inputs.clone(),
        };
        prover
            .prove(trace)
            .map_err(|e| Error::Backend(e.to_string()))
    }
}

struct ZkWinterfellProver {
    options: ProofOptions,
    pub_inputs: PublicInputs,
}

impl WProver for ZkWinterfellProver {
    type BaseField = BE;
    type Air = ZkLispAir;
    type Trace = TraceTable<Self::BaseField>;
    type HashFn = Blake3_256<Self::BaseField>;
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

pub fn verify_proof(proof: Proof, pi: PublicInputs, opts: &ProofOptions) -> Result<(), Error> {
    let acceptable = winterfell::AcceptableOptions::OptionSet(vec![opts.clone()]);
    winterfell::verify::<
        ZkLispAir,
        Blake3_256<BE>,
        DefaultRandomCoin<Blake3_256<BE>>,
        MerkleTree<Blake3_256<BE>>,
    >(proof, pi, &acceptable)
    .map_err(|e| Error::Backend(e.to_string()))
}

pub fn build_trace(program: &crate::ir::Program) -> TraceTable<BE> {
    TraceBuilder::build_from_program(program).expect("trace")
}

fn preflight(
    options: &ProofOptions,
    pub_inputs: &PublicInputs,
    trace: &TraceTable<BE>,
) -> Result<(), Error> {
    let ti = TraceInfo::new(trace.width(), trace.length());
    let air = ZkLispAir::new(ti, pub_inputs.clone(), options.clone());
    let res_len = air.context().num_main_transition_constraints();
    let pc = air.get_periodic_column_values();

    let mut frame = EvaluationFrame::<BE>::new(trace.width());
    for r in 0..trace.length() {
        for c in 0..trace.width() {
            frame.current_mut()[c] = trace.get(c, r);

            let nxt = if r + 1 < trace.length() { r + 1 } else { r };
            frame.next_mut()[c] = trace.get(c, nxt);
        }

        let mut res = vec![BE::ZERO; res_len];
        let pv: Vec<BE> = pc.iter().map(|col| col[r]).collect();

        air.evaluate_transition(&frame, &pv, &mut res);

        if let Some((i, v)) = res.iter().enumerate().find(|&(_, &x)| x != BE::ZERO) {
            let cols = crate::layout::Columns::baseline();
            let pos = r % crate::layout::STEPS_PER_LEVEL_P2;
            let g_map = frame.current()[cols.g_map];
            let g_final = frame.current()[cols.g_final];
            
            let mut g_rounds = Vec::new();

            for j in 0..crate::layout::POSEIDON_ROUNDS {
                g_rounds.push(frame.current()[cols.g_r_index(j)]);
            }
            
            println!(
                "[preflight] row={} pos={} gates: map={} final={} rounds={:?} first_bad={{idx:{}, val:{:?}}}",
                r, pos, g_map, g_final, g_rounds, i, v
            );
            
            // If in Poseidon block, dump lane values and expected next
            let pose_constraints = 4 * crate::layout::POSEIDON_ROUNDS;
            if i < pose_constraints {
                let j = i / 4; // which round
                let mm = crate::poseidon::mds_matrix();
                let rc = crate::poseidon::round_constants();
                let sl = frame.current()[cols.lane_l];
                let sr = frame.current()[cols.lane_r];
                let sc0 = frame.current()[cols.lane_c0];
                let sc1 = frame.current()[cols.lane_c1];
                let sl3 = sl * sl * sl;
                let sr3 = sr * sr * sr;
                let sc03 = sc0 * sc0 * sc0;
                let sc13 = sc1 * sc1 * sc1;
                
                let yl = BE::from(mm[0][0]) * sl3
                    + BE::from(mm[0][1]) * sr3
                    + BE::from(mm[0][2]) * sc03
                    + BE::from(mm[0][3]) * sc13
                    + BE::from(rc[j][0]);
                let yr = BE::from(mm[1][0]) * sl3
                    + BE::from(mm[1][1]) * sr3
                    + BE::from(mm[1][2]) * sc03
                    + BE::from(mm[1][3]) * sc13
                    + BE::from(rc[j][1]);
                let yc0 = BE::from(mm[2][0]) * sl3
                    + BE::from(mm[2][1]) * sr3
                    + BE::from(mm[2][2]) * sc03
                    + BE::from(mm[2][3]) * sc13
                    + BE::from(rc[j][2]);
                let yc1 = BE::from(mm[3][0]) * sl3
                    + BE::from(mm[3][1]) * sr3
                    + BE::from(mm[3][2]) * sc03
                    + BE::from(mm[3][3]) * sc13
                    + BE::from(rc[j][3]);
                let nl = frame.next()[cols.lane_l];
                let nr = frame.next()[cols.lane_r];
                let nc0 = frame.next()[cols.lane_c0];
                let nc1 = frame.next()[cols.lane_c1];
                
                println!(
                    "[poseidon] j={} cur=(l:{:?} r:{:?} c0:{:?} c1:{:?}) next=(l:{:?} r:{:?} c0:{:?} c1:{:?}) exp_next=(l:{:?} r:{:?} c0:{:?} c1:{:?})",
                    j, sl, sr, sc0, sc1, nl, nr, nc0, nc1, yl, yr, yc0, yc1
                );
            }
            
            // also dump next row trace
            let cols2 = crate::layout::Columns::baseline();
            println!(
                "[next row {}] lanes: l={:?} r={:?} c0={:?} c1={:?}",
                r + 1,
                frame.next()[cols2.lane_l],
                frame.next()[cols2.lane_r],
                frame.next()[cols2.lane_c0],
                frame.next()[cols2.lane_c1]
            );
            
            return Err(Error::Backend(format!(
                "preflight: constraint {i} non-zero at row {r}: {v:?}"
            )));
        }
    }

    Ok(())
}

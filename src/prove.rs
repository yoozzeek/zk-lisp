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
use crate::pi::{PublicInputs, be_from_le8};
use crate::trace::TraceBuilder;
use crate::{layout, logging, poseidon, schedule};

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
        logging::init();

        self.pub_inputs
            .validate_flags()
            .map_err(|e| Error::Backend(e.to_string()))?;

        tracing::info!(
            target = "proof.prove",
            q = %self.options.num_queries(),
            blowup = %self.options.blowup_factor(),
            grind = %self.options.grinding_factor(),
            "prove start",
        );

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

    fn get_pub_inputs(&self, trace: &Self::Trace) -> <Self::Air as Air>::PublicInputs {
        let mut pi = self.pub_inputs.clone();
        if (pi.feature_mask & crate::pi::FM_KV) != 0 {
            let cols = layout::Columns::baseline();
            let steps = layout::STEPS_PER_LEVEL_P2;
            let lvls = trace.length() / steps;

            let mut mask: u128 = 0;

            for lvl in 0..lvls {
                let base = lvl * steps;
                let row_map = base + schedule::pos_map();

                if trace.get(cols.kv_g_map, row_map) == BE::ONE {
                    mask |= 1u128 << lvl;
                }
            }

            pi.kv_levels_mask = mask;
        }

        pi
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

    // Validate PI
    {
        pi.validate_flags()
            .map_err(|e| Error::Backend(e.to_string()))?;
    }

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
    use winterfell::math::{fields::f128::BaseElement, polynom};

    let ti = TraceInfo::new(trace.width(), trace.length());
    let air = ZkLispAir::new(ti, pub_inputs.clone(), options.clone());
    let res_len = air.context().num_main_transition_constraints();
    let pc = air.get_periodic_column_values();

    // Extra: replicate Winterfell's periodic
    // poly eval at step 0 for debugging.
    if cfg!(debug_assertions) {
        let periodic_polys = air.get_periodic_column_polys();

        let mut periodic_poly_vals = vec![BaseElement::ZERO; periodic_polys.len()];
        let x = BaseElement::ONE; // step 0

        for (p, v) in periodic_polys.iter().zip(periodic_poly_vals.iter_mut()) {
            let num_cycles = air.trace_length() / p.len();
            let x_eval = x.exp((num_cycles as u32).into());
            *v = polynom::eval(p, x_eval);
        }

        // evaluate transition at step 0 using poly-evaluated periodic values
        let mut frame0 = EvaluationFrame::<BE>::new(trace.width());

        for c in 0..trace.width() {
            frame0.current_mut()[c] = trace.get(c, 0);
            frame0.next_mut()[c] = trace.get(c, 1.min(trace.length() - 1));
        }

        let mut res0 = vec![BE::ZERO; res_len];
        air.evaluate_transition(&frame0, &periodic_poly_vals, &mut res0);

        let cols_dbg = crate::layout::Columns::baseline();
        let sd0 = frame0.current()[cols_dbg.sel_dst_index(0)];
        let p_map0 = periodic_poly_vals[0];
        let p_fin0 = periodic_poly_vals[1 + crate::layout::POSEIDON_ROUNDS];
        let p_pad0 = periodic_poly_vals[1 + crate::layout::POSEIDON_ROUNDS + 1];
        let p_last0 = periodic_poly_vals[1 + crate::layout::POSEIDON_ROUNDS + 3];

        println!(
            "[preflight poly step0] first 8: {:?}",
            &res0[0..res0.len().min(8)]
        );
        println!(
            "[preflight poly step0] gates: p_map={p_map0:?} p_final={p_fin0:?} p_pad={p_pad0:?} p_last={p_last0:?} sd0={sd0:?}"
        );
    }

    let mut frame = EvaluationFrame::<BE>::new(trace.width());
    let last_row = trace.length().saturating_sub(1);

    for r in 0..trace.length() {
        for c in 0..trace.width() {
            frame.current_mut()[c] = trace.get(c, r);

            let nxt = if r + 1 < trace.length() { r + 1 } else { r };
            frame.next_mut()[c] = trace.get(c, nxt);
        }

        // Skip transition exemption row (last row)
        if r == last_row {
            continue;
        }

        let mut res = vec![BE::ZERO; res_len];
        let pv: Vec<BE> = pc.iter().map(|col| col[r]).collect();

        air.evaluate_transition(&frame, &pv, &mut res);

        if let Some((i, v)) = res.iter().enumerate().find(|&(_, &x)| x != BE::ZERO) {
            let cols = layout::Columns::baseline();
            let pos = r % layout::STEPS_PER_LEVEL_P2;
            let g_map = frame.current()[cols.g_map];
            let g_final = frame.current()[cols.g_final];

            let mut g_rounds = Vec::new();

            for j in 0..layout::POSEIDON_ROUNDS {
                g_rounds.push(frame.current()[cols.g_r_index(j)]);
            }

            println!(
                "[preflight] row={r} pos={pos} gates: map={g_map} final={g_final} rounds={g_rounds:?} first_bad={{idx:{i}, val:{v:?}}}"
            );

            // extra KV debug
            let p_map = pc[0][r];
            let p_final = pc[1 + layout::POSEIDON_ROUNDS][r];
            let kv_ver = frame.current()[cols.kv_version];
            let kv_ver_next = frame.next()[cols.kv_version];
            let kv_acc_cur = frame.current()[cols.kv_acc];
            let kv_acc_next = frame.next()[cols.kv_acc];
            let exp_map = be_from_le8(&pub_inputs.kv_map_acc_bytes);
            let exp_fin = be_from_le8(&pub_inputs.kv_fin_acc_bytes);
            let exp_en = if (pub_inputs.feature_mask & crate::pi::FM_KV_EXPECT) != 0 {
                1
            } else {
                0
            };

            println!(
                "  kv: p_map={p_map:?} p_final={p_final:?} ver_cur={kv_ver:?} ver_next={kv_ver_next:?} acc_cur={kv_acc_cur:?} acc_next={kv_acc_next:?} exp_en={exp_en} exp_map={exp_map:?} exp_fin={exp_fin:?}"
            );

            // If in Poseidon block, dump lane values and expected next
            let pose_constraints = 4 * crate::layout::POSEIDON_ROUNDS;
            if i < pose_constraints {
                let j = i / 4; // which round
                let mm = poseidon::derive_poseidon_mds_cauchy_4x4(&pub_inputs.program_commitment);
                let rc = poseidon::derive_poseidon_round_constants(&pub_inputs.program_commitment);
                let sl = frame.current()[cols.lane_l];
                let sr = frame.current()[cols.lane_r];
                let sc0 = frame.current()[cols.lane_c0];
                let sc1 = frame.current()[cols.lane_c1];
                let sl3 = sl * sl * sl;
                let sr3 = sr * sr * sr;
                let sc03 = sc0 * sc0 * sc0;
                let sc13 = sc1 * sc1 * sc1;

                let yl =
                    mm[0][0] * sl3 + mm[0][1] * sr3 + mm[0][2] * sc03 + mm[0][3] * sc13 + rc[j][0];
                let yr =
                    mm[1][0] * sl3 + mm[1][1] * sr3 + mm[1][2] * sc03 + mm[1][3] * sc13 + rc[j][1];
                let yc0 =
                    mm[2][0] * sl3 + mm[2][1] * sr3 + mm[2][2] * sc03 + mm[2][3] * sc13 + rc[j][2];
                let yc1 =
                    mm[3][0] * sl3 + mm[3][1] * sr3 + mm[3][2] * sc03 + mm[3][3] * sc13 + rc[j][3];
                let nl = frame.next()[cols.lane_l];
                let nr = frame.next()[cols.lane_r];
                let nc0 = frame.next()[cols.lane_c0];
                let nc1 = frame.next()[cols.lane_c1];

                println!(
                    "[poseidon] j={j} cur=(l:{sl:?} r:{sr:?} c0:{sc0:?} c1:{sc1:?}) next=(l:{nl:?} r:{nr:?} c0:{nc0:?} c1:{nc1:?}) exp_next=(l:{yl:?} r:{yr:?} c0:{yc0:?} c1:{yc1:?})"
                );
            }

            // Also dump write-constraint context when in VM-only mode
            // VM: ctrl=37, carry=8 (idx 37..44), writes=8 (idx 45..52), eq=2 (53..54)
            if (45..=52).contains(&i) {
                let wi = i - 45; // register index
                let dst = frame.current()[cols.sel_dst_index(wi)];
                let a_val_dbg = {
                    let mut a = BE::ZERO;
                    for k in 0..layout::NR {
                        a +=
                            frame.current()[cols.sel_a_index(k)] * frame.current()[cols.r_index(k)];
                    }
                    a
                };
                let b_val_dbg = {
                    let mut b = BE::ZERO;
                    for k in 0..layout::NR {
                        b +=
                            frame.current()[cols.sel_b_index(k)] * frame.current()[cols.r_index(k)];
                    }
                    b
                };
                let c_val_dbg = {
                    let mut c = BE::ZERO;
                    for k in 0..layout::NR {
                        c +=
                            frame.current()[cols.sel_c_index(k)] * frame.current()[cols.r_index(k)];
                    }
                    c
                };
                let b_const = frame.current()[cols.op_const];
                let b_mov = frame.current()[cols.op_mov];
                let b_add = frame.current()[cols.op_add];
                let b_sub = frame.current()[cols.op_sub];
                let b_mul = frame.current()[cols.op_mul];
                let b_neg = frame.current()[cols.op_neg];
                let b_eqb = frame.current()[cols.op_eq];
                let b_sel = frame.current()[cols.op_select];
                let b_hash = frame.current()[cols.op_hash2];
                let imm = frame.current()[cols.imm];
                let res_dbg = b_const * imm
                    + b_mov * a_val_dbg
                    + b_add * (a_val_dbg + b_val_dbg)
                    + b_sub * (a_val_dbg - b_val_dbg)
                    + b_mul * (a_val_dbg * b_val_dbg)
                    + b_neg * (BE::ZERO - a_val_dbg)
                    + b_sel * (c_val_dbg * a_val_dbg + (BE::ONE - c_val_dbg) * b_val_dbg)
                    + b_hash * frame.current()[cols.lane_l];
                let lhs = frame.next()[cols.r_index(wi)]
                    - ((BE::ONE - dst) * frame.current()[cols.r_index(wi)] + dst * res_dbg);

                println!(
                    "  write[idx={wi}] dst={dst:?} res={res_dbg:?} cur={:?} next={:?} lhs={lhs:?}",
                    frame.current()[cols.r_index(wi)],
                    frame.next()[cols.r_index(wi)]
                );

                let mut sel_dst_idxs = Vec::new();
                let mut sel_a_idxs = Vec::new();
                let mut sel_b_idxs = Vec::new();
                let mut sel_c_idxs = Vec::new();
                for k in 0..layout::NR {
                    if frame.current()[cols.sel_dst_index(k)] == BE::ONE {
                        sel_dst_idxs.push(k);
                    }
                    if frame.current()[cols.sel_a_index(k)] == BE::ONE {
                        sel_a_idxs.push(k);
                    }
                    if frame.current()[cols.sel_b_index(k)] == BE::ONE {
                        sel_b_idxs.push(k);
                    }
                    if frame.current()[cols.sel_c_index(k)] == BE::ONE {
                        sel_c_idxs.push(k);
                    }
                }

                println!(
                    "  sel_dst={sel_dst_idxs:?} sel_a={sel_a_idxs:?} sel_b={sel_b_idxs:?} sel_c={sel_c_idxs:?}"
                );
                println!(
                    "  ops(const, mov, add, sub, mul, neg, eq, sel, hash)=({b_const:?},{b_mov:?},{b_add:?},{b_sub:?},{b_mul:?},{b_neg:?},{b_eqb:?},{b_sel:?},{b_hash:?}) a={a_val_dbg:?} b={b_val_dbg:?} c={c_val_dbg:?}"
                );
            }

            // also dump next row trace
            let cols2 = layout::Columns::baseline();
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

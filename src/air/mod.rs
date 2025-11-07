mod kv;
mod poseidon;
mod schedule;
mod vm_alu;
mod vm_ctrl;

use crate::air::{
    kv::KvBlock, poseidon::PoseidonBlock, schedule::ScheduleBlock, vm_alu::VmAluBlock,
    vm_ctrl::VmCtrlBlock,
};
use crate::layout::{Columns, POSEIDON_ROUNDS, STEPS_PER_LEVEL_P2};
use crate::pi::{FeaturesMap, PublicInputs};
use crate::poseidon as poseidon_core;
use crate::schedule as schedule_core;

use core::marker::PhantomData;
use winterfell::math::FieldElement;
use winterfell::math::fft;
use winterfell::math::fields::f128::{BaseElement as BE, BaseElement};
use winterfell::{
    Air, AirContext, Assertion, EvaluationFrame, ProofOptions, TraceInfo,
    TransitionConstraintDegree,
};

pub struct BlockCtx<'a, E: FieldElement> {
    pub cols: &'a Columns,
    pub pub_inputs: &'a PublicInputs,
    pub poseidon_rc: &'a [[BE; 4]; POSEIDON_ROUNDS],
    pub poseidon_mds: &'a [[BE; 4]; 4],
    pub poseidon_dom: &'a [BE; 2],
    _pd: PhantomData<E>,
}

impl<'a, E: FieldElement> BlockCtx<'a, E> {
    pub fn new(
        cols: &'a Columns,
        pub_inputs: &'a PublicInputs,
        poseidon_rc: &'a [[BE; 4]; POSEIDON_ROUNDS],
        poseidon_mds: &'a [[BE; 4]; 4],
        poseidon_dom: &'a [BE; 2],
    ) -> Self {
        Self {
            cols,
            pub_inputs,
            poseidon_rc,
            poseidon_mds,
            poseidon_dom,
            _pd: PhantomData,
        }
    }
}

pub trait AirBlock<E: FieldElement> {
    fn push_degrees(out: &mut Vec<TransitionConstraintDegree>);

    fn eval_block(
        ctx: &BlockCtx<E>,
        frame: &EvaluationFrame<E>,
        periodic: &[E],
        result: &mut [E],
        ix: &mut usize,
    );

    fn append_assertions(ctx: &BlockCtx<E>, out: &mut Vec<Assertion<E::BaseField>>, last: usize) {
        let _ = (ctx, out, last);
    }
}

#[derive(Clone)]
#[allow(dead_code)]
pub struct ZkLispAir {
    ctx: AirContext<BaseElement>,
    pub_inputs: PublicInputs,
    cols: Columns,
    features: FeaturesMap,

    poseidon_rc: [[BaseElement; 4]; POSEIDON_ROUNDS],
    poseidon_mds: [[BaseElement; 4]; 4],
    poseidon_dom: [BaseElement; 2],
}

impl Air for ZkLispAir {
    type BaseField = BaseElement;
    type PublicInputs = PublicInputs;

    fn new(info: TraceInfo, pub_inputs: Self::PublicInputs, options: ProofOptions) -> Self {
        let mut degrees = Vec::new();

        let features = pub_inputs.get_features();
        if features.poseidon {
            PoseidonBlock::push_degrees(&mut degrees);
        }
        if features.vm {
            VmCtrlBlock::push_degrees(&mut degrees);
            VmAluBlock::push_degrees(&mut degrees);
        }
        if features.kv {
            KvBlock::push_degrees(&mut degrees);
        }

        // Boundary assertions count per level:
        let levels = (info.length() / STEPS_PER_LEVEL_P2).max(1);

        // schedule/domain
        // (4 + POSEIDON_ROUNDS)
        // per level
        let mut num_assertions = (4 + POSEIDON_ROUNDS) * levels;

        // Program commitment
        // bound once (level 0 map)
        if features.vm {
            num_assertions += 1;
        }
        if num_assertions == 0 {
            num_assertions = 1;
        }

        // Debug: print expected evals and context
        Self::print_evals_debug(&pub_inputs, &info, &features, &degrees);

        let ctx = AirContext::new(info, degrees, num_assertions, options);
        let cols = Columns::baseline();

        Self::print_degrees_debug(&ctx, &pub_inputs, &features);

        let suite = &pub_inputs.program_commitment;
        let rc = poseidon_core::derive_poseidon_round_constants(suite);
        let mds = poseidon_core::derive_poseidon_mds_cauchy_4x4(suite);
        let dom = poseidon_core::derive_poseidon_domain_tags(suite);

        Self {
            ctx,
            pub_inputs,
            cols,
            features,
            poseidon_rc: rc,
            poseidon_mds: mds,
            poseidon_dom: dom,
        }
    }

    fn context(&self) -> &AirContext<Self::BaseField> {
        &self.ctx
    }

    fn evaluate_transition<E: FieldElement<BaseField = Self::BaseField>>(
        &self,
        frame: &EvaluationFrame<E>,
        periodic_values: &[E],
        result: &mut [E],
    ) {
        let bctx = BlockCtx::<E>::new(
            &self.cols,
            &self.pub_inputs,
            &self.poseidon_rc,
            &self.poseidon_mds,
            &self.poseidon_dom,
        );

        let mut ix = 0usize;

        if self.features.poseidon {
            PoseidonBlock::eval_block(&bctx, frame, periodic_values, result, &mut ix);
        }
        if self.features.vm {
            vm_ctrl::VmCtrlBlock::eval_block(&bctx, frame, periodic_values, result, &mut ix);
            vm_alu::VmAluBlock::eval_block(&bctx, frame, periodic_values, result, &mut ix);
        }
        if self.features.kv {
            kv::KvBlock::eval_block(&bctx, frame, periodic_values, result, &mut ix);
        }

        debug_assert_eq!(ix, result.len());
    }

    fn get_assertions(&self) -> Vec<Assertion<Self::BaseField>> {
        let last = self.ctx.trace_len().saturating_sub(1);
        let mut out = Vec::new();

        // Schedule/domain-tag assertions (per-level)
        let bctx_sched = BlockCtx::<BaseElement>::new(
            &self.cols,
            &self.pub_inputs,
            &self.poseidon_rc,
            &self.poseidon_mds,
            &self.poseidon_dom,
        );
        ScheduleBlock::append_assertions(&bctx_sched, &mut out, last);

        // Kv per-level boundary assertions
        if self.features.kv {
            let bctx = BlockCtx::<BaseElement>::new(
                &self.cols,
                &self.pub_inputs,
                &self.poseidon_rc,
                &self.poseidon_mds,
                &self.poseidon_dom,
            );
            KvBlock::append_assertions(&bctx, &mut out, last);
        }

        if out.is_empty() {
            out.push(Assertion::single(self.cols.mask, last, BE::from(0u32)));
        }

        // Debug: validate assertion columns
        let width = self.cols.width(self.pub_inputs.feature_mask);
        let mut bad = 0usize;
        let mut max_col = 0usize;

        for a in &out {
            let c = a.column();
            if c > max_col {
                max_col = c;
            }
            if c >= width {
                bad += 1;
            }
        }

        tracing::info!(
            target="proof.air",
            assertions_len=%out.len(),
            width=%width,
            last=%last,
            bad_cols=%bad,
            max_col=%max_col,
        );

        out
    }

    fn get_periodic_column_values(&self) -> Vec<Vec<Self::BaseField>> {
        let n = self.ctx.trace_len();
        let sels_u8 = schedule_core::build_periodic_selectors(n);

        sels_u8
            .into_iter()
            .map(|col| {
                col.into_iter()
                    .map(|b| if b == 1 { BE::ONE } else { BE::ZERO })
                    .collect()
            })
            .collect()
    }

    fn get_periodic_column_polys(&self) -> Vec<Vec<Self::BaseField>> {
        let n = self.ctx.trace_len();
        let cycle = STEPS_PER_LEVEL_P2;
        let cols_len = 1 + POSEIDON_ROUNDS + 1 + 1 + 1;

        let mut values: Vec<Vec<BE>> = (0..cols_len).map(|_| Vec::new()).collect();

        for pos in 0..cycle {
            // p_map
            values[0].push(if pos == schedule_core::pos_map() {
                BE::ONE
            } else {
                BE::ZERO
            });

            // rounds
            for j in 0..POSEIDON_ROUNDS {
                values[1 + j].push(if pos == 1 + j { BE::ONE } else { BE::ZERO });
            }

            // p_final
            values[1 + POSEIDON_ROUNDS].push(if pos == schedule_core::pos_final() {
                BE::ONE
            } else {
                BE::ZERO
            });

            // p_pad
            let is_pad = pos != schedule_core::pos_map()
                && pos != schedule_core::pos_final()
                && !schedule_core::is_round_pos(pos);
            values[1 + POSEIDON_ROUNDS + 1].push(if is_pad { BE::ONE } else { BE::ZERO });
        }

        // p_last over full n as a true
        // polynomial over the full trace domain.
        let mut p_last = vec![BE::ZERO; n];
        if n > 0 {
            p_last[n - 1] = BE::ONE;
        }

        // interpolate to polynomial
        // coefficients over size-n domain.
        if n > 0 {
            let inv_twiddles_n = fft::get_inv_twiddles::<BE>(n);
            fft::interpolate_poly(&mut p_last, &inv_twiddles_n);
        }

        values[1 + POSEIDON_ROUNDS + 2] = p_last;

        // interpolate first (1 + R + 1 + 1)
        // columns to polys over cycle
        for col in values.iter_mut().take(1 + POSEIDON_ROUNDS + 1 + 1) {
            let inv_twiddles = fft::get_inv_twiddles::<BE>(col.len());
            fft::interpolate_poly(col, &inv_twiddles);
        }

        values
    }
}

impl ZkLispAir {
    #[inline]
    fn print_evals_debug(
        _pub_inputs: &PublicInputs,
        info: &TraceInfo,
        features: &FeaturesMap,
        degrees: &[TransitionConstraintDegree],
    ) {
        let trace_len = info.length();
        let evals: Vec<usize> = degrees
            .iter()
            .map(|d| d.get_evaluation_degree(trace_len) - (trace_len - 1))
            .collect();

        tracing::info!(
            target = "proof.air",
            "expected_eval_degrees_len={} evals={:?}",
            evals.len(),
            evals
        );

        // print per-block slices for easier debugging
        let mut ofs = 0usize;
        let mut dbg: Vec<(&str, Vec<usize>)> = Vec::new();

        if features.poseidon {
            let len = 4 * POSEIDON_ROUNDS;
            dbg.push(("poseidon", evals[ofs..ofs + len].to_vec()));
            ofs += len;
        }
        if features.vm {
            // vm_ctrl (37)
            let len = 37;
            dbg.push(("vm_ctrl", evals[ofs..ofs + len].to_vec()));
            ofs += len;

            // vm_alu (18)
            let len = 18;
            dbg.push(("vm_alu", evals[ofs..ofs + len].to_vec()));
            ofs += len;
        }
        if features.kv {
            let len = 8;
            dbg.push(("kv", evals[ofs..ofs + len].to_vec()));
        }

        tracing::info!(target = "proof.air", "per_block_evals: {:?}", dbg);
    }

    #[inline]
    fn print_degrees_debug(
        ctx: &AirContext<BE>,
        _pub_inputs: &PublicInputs,
        features: &FeaturesMap,
    ) {
        let tl = ctx.trace_len();
        let ce = ctx.ce_domain_size();
        let lde = ctx.lde_domain_size();
        let blow_ce = ce / tl;

        tracing::info!(
            target = "proof.air",
            "ctx: trace_len={} ce_domain_size={} lde_domain_size={} ce_blowup={} exemptions={}",
            tl,
            ce,
            lde,
            blow_ce,
            ctx.num_transition_exemptions()
        );

        let mut ofs = 0usize;
        let mut ranges = Vec::new();

        if features.poseidon {
            let len = 4 * POSEIDON_ROUNDS;
            ranges.push(("poseidon", ofs, ofs + len));
            ofs += len;
        }
        if features.vm {
            let len = 37;
            ranges.push(("vm_ctrl", ofs, ofs + len));
            ofs += len;

            let len2 = 18;
            ranges.push(("vm_alu", ofs, ofs + len2));
            ofs += len2;
        }
        if features.kv {
            let len = 8;
            ranges.push(("kv", ofs, ofs + len));
            ofs += len;
        }

        tracing::info!(target = "proof.air", "deg_ranges: {:?}", ranges);
        tracing::info!(target = "proof.air", "deg_len={} (computed)", ofs);
    }
}

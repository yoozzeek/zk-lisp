use core::marker::PhantomData;
use winterfell::math::FieldElement;
use winterfell::math::fft;
use winterfell::math::fields::f128::{BaseElement as BE, BaseElement};
use winterfell::{
    Air, AirContext, Assertion, EvaluationFrame, ProofOptions, TraceInfo,
    TransitionConstraintDegree,
};

use crate::layout::{Columns, POSEIDON_ROUNDS, STEPS_PER_LEVEL_P2};
use crate::pi::{FeaturesMap, PublicInputs};
use crate::poseidon::{domain_tags, mds_matrix, round_constants};
use crate::schedule;

pub mod kv;
pub mod poseidon_blk;
pub mod schedule_blk;
pub mod vm_alu;
pub mod vm_ctrl;

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
            poseidon_blk::PoseidonBlock::push_degrees(&mut degrees);
        }
        if features.vm {
            vm_ctrl::VmCtrlBlock::push_degrees(&mut degrees);
            vm_alu::VmAluBlock::push_degrees(&mut degrees);
        }
        if features.kv {
            kv::KvBlock::push_degrees(&mut degrees);
        }

        // Boundary assertions count per level:
        let levels = (info.length() / STEPS_PER_LEVEL_P2).max(1);

        // schedule/domain
        // (4 + POSEIDON_ROUNDS)
        // per level
        let mut num_assertions = (4 + POSEIDON_ROUNDS) * levels;

        // KV gate one-hot
        // per level (4 per level)
        if features.kv {
            num_assertions += 4 * levels;
        }

        // Program commitment
        // bound once (level 0 map)
        if features.vm {
            num_assertions += 1;
        }

        if num_assertions == 0 {
            num_assertions = 1;
        }

        let ctx = AirContext::new(info, degrees, num_assertions, options);
        let cols = Columns::baseline();

        let rc = round_constants();
        let mds = mds_matrix();
        let dom = domain_tags();

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
            poseidon_blk::PoseidonBlock::eval_block(&bctx, frame, periodic_values, result, &mut ix);
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
        schedule_blk::ScheduleBlock::append_assertions(&bctx_sched, &mut out, last);

        // Kv per-level boundary assertions
        if self.features.kv {
            let bctx = BlockCtx::<BaseElement>::new(
                &self.cols,
                &self.pub_inputs,
                &self.poseidon_rc,
                &self.poseidon_mds,
                &self.poseidon_dom,
            );
            kv::KvBlock::append_assertions(&bctx, &mut out, last);
        }

        if out.is_empty() {
            out.push(Assertion::single(self.cols.mask, last, BE::from(0u32)));
        }

        out
    }

    fn get_periodic_column_values(&self) -> Vec<Vec<Self::BaseField>> {
        let n = self.ctx.trace_len();
        let sels_u8 = schedule::build_periodic_selectors(n);

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
        // Build per-cycle polynomials for periodic 
        // columns via FFT interpolation
        // p_map, p_r[0..R-1], p_final, p_pad, p_last
        let n = self.ctx.trace_len();
        let cycle = STEPS_PER_LEVEL_P2;
        let cols_len = 1 + POSEIDON_ROUNDS + 1 + 1 + 1;
        
        let mut values: Vec<Vec<BE>> = (0..cols_len).map(|_| Vec::new()).collect();

        for pos in 0..cycle {
            // p_map
            values[0].push(if pos == schedule::pos_map() { BE::ONE } else { BE::ZERO });
            
            // rounds
            for j in 0..POSEIDON_ROUNDS {
                values[1 + j].push(if pos == 1 + j { BE::ONE } else { BE::ZERO });
            }
            
            // p_final
            values[1 + POSEIDON_ROUNDS].push(if pos == schedule::pos_final() { BE::ONE } else { BE::ZERO });
            
            // p_pad
            let is_pad = pos != schedule::pos_map() && pos != schedule::pos_final() && !schedule::is_round_pos(pos);
            values[1 + POSEIDON_ROUNDS + 1].push(if is_pad { BE::ONE } else { BE::ZERO });
        }

        // p_last over full n
        let mut p_last = vec![BE::ZERO; n];
        if n > 0 { p_last[n - 1] = BE::ONE; }
        
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

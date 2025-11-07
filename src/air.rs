use core::marker::PhantomData;

use winterfell::math::FieldElement;
use winterfell::math::fields::f128::{BaseElement as BE, BaseElement};
use winterfell::{
    Air, AirContext, Assertion, EvaluationFrame, ProofOptions, TraceInfo,
    TransitionConstraintDegree,
};

use crate::layout::{self, Columns, POSEIDON_ROUNDS, STEPS_PER_LEVEL_P2};
use crate::pi::{FeaturesMap, PublicInputs};
use crate::poseidon;
use crate::schedule;

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

        // Poseidon round transition degrees:
        // 4 constraints per round, gated by level-cycle.
        for _ in 0..POSEIDON_ROUNDS {
            for _ in 0..4 {
                degrees.push(TransitionConstraintDegree::with_cycles(
                    3,
                    vec![STEPS_PER_LEVEL_P2],
                ));
            }
        }

        // Boundary assertions count per level:
        // schedule ties + domain tags (2 per level)
        let levels = (info.length() / STEPS_PER_LEVEL_P2).max(1);

        let mut num_assertions = (2 + POSEIDON_ROUNDS + 2) * levels;

        if num_assertions == 0 {
            num_assertions = 1;
        }

        let ctx = AirContext::new(info, degrees, num_assertions, options);
        let cols = Columns::baseline();

        let rc = poseidon::round_constants();
        let mds = poseidon::mds_matrix();
        let dom = poseidon::domain_tags();

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
        let cur = frame.current();
        let next = frame.next();
        let mm = self.poseidon_mds;

        let mut ix = 0usize;

        for j in 0..POSEIDON_ROUNDS {
            let gr = periodic_values[1 + j];

            let sl = cur[self.cols.lane_l];
            let sr = cur[self.cols.lane_r];
            let sc0 = cur[self.cols.lane_c0];
            let sc1 = cur[self.cols.lane_c1];

            let sl3 = sl * sl * sl;
            let sr3 = sr * sr * sr;
            let sc03 = sc0 * sc0 * sc0;
            let sc13 = sc1 * sc1 * sc1;

            let rc = &self.poseidon_rc[j];
            let yl = E::from(mm[0][0]) * sl3
                + E::from(mm[0][1]) * sr3
                + E::from(mm[0][2]) * sc03
                + E::from(mm[0][3]) * sc13
                + E::from(rc[0]);
            let yr = E::from(mm[1][0]) * sl3
                + E::from(mm[1][1]) * sr3
                + E::from(mm[1][2]) * sc03
                + E::from(mm[1][3]) * sc13
                + E::from(rc[1]);
            let yc0 = E::from(mm[2][0]) * sl3
                + E::from(mm[2][1]) * sr3
                + E::from(mm[2][2]) * sc03
                + E::from(mm[2][3]) * sc13
                + E::from(rc[2]);
            let yc1 = E::from(mm[3][0]) * sl3
                + E::from(mm[3][1]) * sr3
                + E::from(mm[3][2]) * sc03
                + E::from(mm[3][3]) * sc13
                + E::from(rc[3]);

            result[ix] = gr * (next[self.cols.lane_l] - yl);
            ix += 1;
            result[ix] = gr * (next[self.cols.lane_r] - yr);
            ix += 1;
            result[ix] = gr * (next[self.cols.lane_c0] - yc0);
            ix += 1;
            result[ix] = gr * (next[self.cols.lane_c1] - yc1);
            ix += 1;
        }

        debug_assert_eq!(ix, result.len());
    }

    fn get_assertions(&self) -> Vec<Assertion<Self::BaseField>> {
        let last = self.ctx.trace_len().saturating_sub(1);
        let mut out = Vec::new();

        // Schedule gate ties: set
        // g_map/g_final/g_r[j] = 1
        // at their level positions.
        let steps = layout::STEPS_PER_LEVEL_P2;
        let lvls = if steps == 0 {
            0
        } else {
            self.ctx.trace_len() / steps
        };

        for lvl in 0..lvls {
            let base = lvl * steps;
            let row_map = base + schedule::pos_map();
            let row_final = base + schedule::pos_final();

            // Domain tags at map row
            out.push(Assertion::single(
                self.cols.lane_c0,
                row_map,
                self.poseidon_dom[0],
            ));
            out.push(Assertion::single(
                self.cols.lane_c1,
                row_map,
                self.poseidon_dom[1],
            ));

            // Schedule gate ties
            out.push(Assertion::single(self.cols.g_map, row_map, BE::from(1u32)));
            out.push(Assertion::single(
                self.cols.g_final,
                row_final,
                BE::from(1u32),
            ));

            for j in 0..POSEIDON_ROUNDS {
                let rj = base + 1 + j;
                out.push(Assertion::single(
                    self.cols.g_r_index(j),
                    rj,
                    BE::from(1u32),
                ));
            }
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
        // just reuse values
        self.get_periodic_column_values()
    }
}

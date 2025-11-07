use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::{Assertion, EvaluationFrame, TransitionConstraintDegree};

use crate::layout::{POSEIDON_ROUNDS, STEPS_PER_LEVEL_P2};
use crate::pi;
use crate::schedule;

use super::{AirBlock, BlockCtx};

pub struct ScheduleBlock;

impl<E> AirBlock<E> for ScheduleBlock
where
    E: FieldElement<BaseField = BE> + From<BE>,
{
    fn push_degrees(_out: &mut Vec<TransitionConstraintDegree>) {}

    fn eval_block(
        _ctx: &BlockCtx<E>,
        _frame: &EvaluationFrame<E>,
        _periodic: &[E],
        _result: &mut [E],
        _ix: &mut usize,
    ) {
    }

    fn append_assertions(
        ctx: &BlockCtx<E>,
        out: &mut Vec<Assertion<<E as FieldElement>::BaseField>>,
        last: usize,
    ) {
        // Per-level assertions:
        // - domain tags at map row (lane_c0/lane_c1)
        // - schedule gate ties for g_map, g_final, g_r[j]
        let steps = STEPS_PER_LEVEL_P2;
        let lvls = if steps == 0 { 0 } else { (last + 1) / steps };

        for lvl in 0..lvls {
            let base = lvl * steps;
            let row_map = base + schedule::pos_map();
            let row_final = base + schedule::pos_final();

            // Domain tags at map row
            out.push(Assertion::single(
                ctx.cols.lane_c0,
                row_map,
                ctx.poseidon_dom[0],
            ));
            out.push(Assertion::single(
                ctx.cols.lane_c1,
                row_map,
                ctx.poseidon_dom[1],
            ));

            // Schedule gate ties
            out.push(Assertion::single(ctx.cols.g_map, row_map, BE::from(1u32)));
            out.push(Assertion::single(
                ctx.cols.g_final,
                row_final,
                BE::from(1u32),
            ));

            // Program commitment bound at the very first map row (level 0)
            if lvl == 0 {
                let vm_enabled = ctx.pub_inputs.get_features().vm;
                if vm_enabled {
                    let pc = pi::be_from_le8(&ctx.pub_inputs.program_commitment);
                    out.push(Assertion::single(ctx.cols.pi_prog, row_map, pc));
                }
            }

            for j in 0..POSEIDON_ROUNDS {
                let rj = base + 1 + j;
                out.push(Assertion::single(ctx.cols.g_r_index(j), rj, BE::from(1u32)));
            }
        }
    }
}

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
        // - schedule ties: 1s at positions g_map(map), g_final(final), g_r[j] (round rows)
        // - zeros at non-positions:
        //   map row: g_final=0 and all g_r[*]=0
        //   final row: g_map=0 and all g_r[*]=0
        //   round rows: g_map=0 and g_final=0
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

            // Ones at positions
            out.push(Assertion::single(ctx.cols.g_map, row_map, BE::from(1u32)));
            out.push(Assertion::single(
                ctx.cols.g_final,
                row_final,
                BE::from(1u32),
            ));

            for j in 0..POSEIDON_ROUNDS {
                let rj = base + 1 + j;
                out.push(Assertion::single(ctx.cols.g_r_index(j), rj, BE::from(1u32)));
            }

            // Zeros at non-positions
            // Map row: g_final=0 and all g_r[*]=0
            out.push(Assertion::single(ctx.cols.g_final, row_map, BE::from(0u32)));

            for j in 0..POSEIDON_ROUNDS {
                out.push(Assertion::single(
                    ctx.cols.g_r_index(j),
                    row_map,
                    BE::from(0u32),
                ));
            }

            // Final row: g_map=0 and all g_r[*]=0
            out.push(Assertion::single(ctx.cols.g_map, row_final, BE::from(0u32)));

            for j in 0..POSEIDON_ROUNDS {
                out.push(Assertion::single(
                    ctx.cols.g_r_index(j),
                    row_final,
                    BE::from(0u32),
                ));
            }

            // Round rows: g_map=0 and g_final=0
            for j in 0..POSEIDON_ROUNDS {
                let rj = base + 1 + j;
                out.push(Assertion::single(ctx.cols.g_map, rj, BE::from(0u32)));
                out.push(Assertion::single(ctx.cols.g_final, rj, BE::from(0u32)));
            }

            // Program commitment bound at the very first map row (level 0)
            if lvl == 0 {
                let vm_enabled = ctx.pub_inputs.get_features().vm;
                if vm_enabled {
                    let pc = pi::be_from_le8(&ctx.pub_inputs.program_commitment);
                    out.push(Assertion::single(ctx.cols.pi_prog, row_map, pc));
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{air, layout};
    use winterfell::math::StarkField;
    use winterfell::{Air, ProofOptions, TraceInfo};

    #[test]
    fn schedule_strict_boundary() {
        let cols = layout::Columns::baseline();
        let width = cols.width(0);
        let steps = STEPS_PER_LEVEL_P2; // one level
        let info = TraceInfo::new(width, steps);
        let opts = ProofOptions::new(
            1,
            8,
            0,
            winterfell::FieldExtension::None,
            2,
            1,
            winterfell::BatchingMethod::Linear,
            winterfell::BatchingMethod::Linear,
        );

        let air = air::ZkLispAir::new(info, Default::default(), opts);
        let asserts = air.get_assertions();

        let row_map = 0usize;
        let row_fin = 1 + POSEIDON_ROUNDS;

        // Must include: g_final=0 at map
        assert!(asserts.iter().any(|a| a.column() == cols.g_final
            && a.first_step() == row_map
            && a.values()[0].as_int() == 0));

        // Must include: g_map=0 at final
        assert!(asserts.iter().any(|a| a.column() == cols.g_map
            && a.first_step() == row_fin
            && a.values()[0].as_int() == 0));

        // Round row 1: g_map=0 and g_final=0
        let r1 = 1usize;
        assert!(asserts.iter().any(|a| a.column() == cols.g_map
            && a.first_step() == r1
            && a.values()[0].as_int() == 0));
        assert!(asserts.iter().any(|a| a.column() == cols.g_final
            && a.first_step() == r1
            && a.values()[0].as_int() == 0));
    }
}

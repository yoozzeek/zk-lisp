use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::{Assertion, EvaluationFrame, TransitionConstraintDegree};

use crate::layout::{POSEIDON_ROUNDS, STEPS_PER_LEVEL_P2};
use crate::pi;

use super::{AirBlock, BlockCtx};

pub struct KvBlock;

impl KvBlock {
    pub fn push_degrees(out: &mut Vec<TransitionConstraintDegree>) {
        // dir boolean at map
        out.push(TransitionConstraintDegree::with_cycles(
            2,
            vec![STEPS_PER_LEVEL_P2],
        ));
        // lane selections at map (2 constraints)
        out.push(TransitionConstraintDegree::with_cycles(
            3,
            vec![STEPS_PER_LEVEL_P2],
        ));
        out.push(TransitionConstraintDegree::with_cycles(
            3,
            vec![STEPS_PER_LEVEL_P2],
        ));
        // version transition (map hold, final bump)
        out.push(TransitionConstraintDegree::with_cycles(
            2,
            vec![STEPS_PER_LEVEL_P2],
        ));
        // final tie acc==lane_l (gated by fin & map)
        out.push(TransitionConstraintDegree::with_cycles(
            2,
            vec![STEPS_PER_LEVEL_P2],
        ));
        // Expected acc checks when enabled
        out.push(TransitionConstraintDegree::with_cycles(
            1,
            vec![STEPS_PER_LEVEL_P2],
        ));
        out.push(TransitionConstraintDegree::with_cycles(
            1,
            vec![STEPS_PER_LEVEL_P2],
        ));
        // carry acc on non-final rows
        out.push(TransitionConstraintDegree::with_cycles(
            1,
            vec![STEPS_PER_LEVEL_P2],
        ));
    }
}

impl<E> AirBlock<E> for KvBlock
where
    E: FieldElement<BaseField = BE> + From<BE>,
{
    fn push_degrees(_out: &mut Vec<TransitionConstraintDegree>) {}

    fn eval_block(
        ctx: &BlockCtx<E>,
        frame: &EvaluationFrame<E>,
        periodic: &[E],
        result: &mut [E],
        ix: &mut usize,
    ) {
        let cur = frame.current();
        let next = frame.next();

        let p_map = periodic[0];
        let p_final = periodic[1 + POSEIDON_ROUNDS];
        let not_final = E::ONE - p_final;

        // mixers: s1 ~ deg1, s2 ~ deg2,
        // s3 ~ deg3 (after dividing by z).
        let p_last = periodic[1 + POSEIDON_ROUNDS + 2];
        let s1 = p_last * p_map;
        let pi = cur[ctx.cols.pi_prog];
        let s2 = s1 * pi;
        let s3 = s2 * pi;

        let kv_map = cur[ctx.cols.kv_g_map];
        let kv_fin = cur[ctx.cols.kv_g_final];
        let dir = cur[ctx.cols.kv_dir];
        let sib = cur[ctx.cols.kv_sib];
        let acc = cur[ctx.cols.kv_acc];

        // dir boolean at map
        result[*ix] = p_map * kv_map * dir * (dir - E::ONE) + s2;
        *ix += 1;

        // lane selection at map
        let left_sel = (E::ONE - dir) * acc + dir * sib;
        let right_sel = (E::ONE - dir) * sib + dir * acc;
        result[*ix] = p_map * kv_map * (cur[ctx.cols.lane_l] - left_sel) + s3;
        *ix += 1;
        result[*ix] = p_map * kv_map * (cur[ctx.cols.lane_r] - right_sel) + s3;
        *ix += 1;

        // version transition: hold on map
        // (kv_map), bump on final (kv_fin)
        let ver = cur[ctx.cols.kv_version];
        let ver_next = next[ctx.cols.kv_version];
        result[*ix] = (p_map * kv_map) * (ver_next - ver)
            + (p_final * kv_fin) * (ver_next - (ver + E::ONE))
            + s2;
        *ix += 1;

        // final tie acc == lane_l only
        // for KV map-final levels.
        result[*ix] =
            p_final * kv_fin * kv_map * (cur[ctx.cols.kv_acc] - cur[ctx.cols.lane_l]) + s2;
        *ix += 1;

        // Expected acc checks gated by feature mask
        let expect_enabled = if (ctx.pub_inputs.feature_mask & pi::FM_KV_EXPECT) != 0 {
            E::ONE
        } else {
            E::ZERO
        };

        // decode first 8 bytes (little-endian)
        // into field for expected map/final
        let map_exp = be_from_le8::<E>(ctx.pub_inputs.kv_map_acc_bytes);
        let fin_exp = be_from_le8::<E>(ctx.pub_inputs.kv_fin_acc_bytes);
        result[*ix] = expect_enabled * p_map * kv_map * (cur[ctx.cols.kv_acc] - map_exp) + s1;
        *ix += 1;
        result[*ix] = expect_enabled * p_final * kv_fin * (cur[ctx.cols.kv_acc] - fin_exp) + s1;
        *ix += 1;

        // carry acc across non-final rows
        result[*ix] = not_final * (next[ctx.cols.kv_acc] - cur[ctx.cols.kv_acc]) + s1;
        *ix += 1;
    }

    fn append_assertions(
        _ctx: &BlockCtx<E>,
        _out: &mut Vec<Assertion<<E as FieldElement>::BaseField>>,
        _last: usize,
    ) {
        // No KV gate boundary assertions by default.
    }
}

fn be_from_le8<E: FieldElement<BaseField = BE>>(bytes32: [u8; 32]) -> E {
    let mut le = [0u8; 8];
    le.copy_from_slice(&bytes32[0..8]);
    E::from(BE::from(u64::from_le_bytes(le)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::layout::Columns;
    use winterfell::EvaluationFrame;

    #[test]
    fn dir_non_boolean_fails_at_map() {
        let cols = Columns::baseline();
        let mut frame = EvaluationFrame::<BE>::new(cols.width(0));
        let mut periodic = vec![BE::ZERO; 1 + POSEIDON_ROUNDS + 1 + 1 + 1];

        let pi = pi::PublicInputs::default();
        let rc_box = Box::new([[BE::ZERO; 4]; POSEIDON_ROUNDS]);
        let mds_box = Box::new({
            let mut m = [[BE::ZERO; 4]; 4];
            m[0][0] = BE::ONE;
            m[1][1] = BE::ONE;
            m[2][2] = BE::ONE;
            m[3][3] = BE::ONE;
            m
        });
        let dom_box = Box::new([BE::ONE, BE::from(2u64)]);
        let ctx = BlockCtx::<BE>::new(&cols, &pi, &rc_box, &mds_box, &dom_box);

        // map row: p_map=1
        periodic[0] = BE::ONE;
        periodic[1 + POSEIDON_ROUNDS] = BE::ZERO;

        // set gates
        frame.current_mut()[cols.kv_g_map] = BE::ONE;
        frame.current_mut()[cols.kv_g_final] = BE::ZERO;

        // dir=2 (non-boolean),
        // set other values harmless
        frame.current_mut()[cols.kv_dir] = BE::from(2u64);
        frame.current_mut()[cols.kv_acc] = BE::from(5u64);
        frame.current_mut()[cols.kv_sib] = BE::from(7u64);

        // carry acc across non-final rows
        frame.next_mut()[cols.kv_acc] = frame.current()[cols.kv_acc];

        let mut res = vec![BE::ZERO; 8];
        let mut ix = 0usize;
        KvBlock::eval_block(&ctx, &frame, &periodic, &mut res, &mut ix);

        // first constraint is dir*(dir-1)
        assert_ne!(res[0], BE::ZERO);
    }

    #[test]
    fn expected_map_mismatch_fails_only_expected_constraint() {
        let cols = Columns::baseline();
        let mut frame = EvaluationFrame::<BE>::new(cols.width(0));
        let mut periodic = vec![BE::ZERO; 1 + POSEIDON_ROUNDS + 1 + 1 + 1];

        // enable KV_EXPECT
        let mut pi = pi::PublicInputs::default();
        pi.feature_mask |= pi::FM_KV_EXPECT;

        // set expected map acc != 5
        let bad = 6u64;
        let mut map_bytes = [0u8; 32];
        map_bytes[0..8].copy_from_slice(&bad.to_le_bytes());

        pi.kv_map_acc_bytes = map_bytes;
        pi.kv_fin_acc_bytes = [0u8; 32];

        let rc_box = Box::new([[BE::ZERO; 4]; POSEIDON_ROUNDS]);
        let mds_box = Box::new({
            let mut m = [[BE::ZERO; 4]; 4];
            m[0][0] = BE::ONE;
            m[1][1] = BE::ONE;
            m[2][2] = BE::ONE;
            m[3][3] = BE::ONE;

            m
        });
        let dom_box = Box::new([BE::ONE, BE::from(2u64)]);
        let ctx = BlockCtx::<BE>::new(&cols, &pi, &rc_box, &mds_box, &dom_box);

        // map row
        periodic[0] = BE::ONE;
        periodic[1 + POSEIDON_ROUNDS] = BE::ZERO;

        frame.current_mut()[cols.kv_g_map] = BE::ONE;
        frame.current_mut()[cols.kv_g_final] = BE::ZERO;

        // dir boolean 0, lanes match selection
        frame.current_mut()[cols.kv_dir] = BE::ZERO;
        frame.current_mut()[cols.kv_acc] = BE::from(5u64);
        frame.current_mut()[cols.kv_sib] = BE::from(7u64);
        frame.current_mut()[cols.lane_l] = BE::from(5u64);
        frame.current_mut()[cols.lane_r] = BE::from(7u64);

        // version hold
        frame.current_mut()[cols.kv_version] = BE::from(3u64);
        frame.next_mut()[cols.kv_version] = BE::from(3u64);
        // carry acc
        frame.next_mut()[cols.kv_acc] = frame.current()[cols.kv_acc];

        let mut res = vec![BE::ZERO; 8];
        let mut ix = 0usize;
        KvBlock::eval_block(&ctx, &frame, &periodic, &mut res, &mut ix);

        // expected map constraint index = 5
        // (0 dir, 1-2 lanes, 3 version, 4 final_tie, 5 expected_map)
        assert_ne!(res[5], BE::ZERO);

        // other constraints zero
        for (i, v) in res.iter().enumerate() {
            if i != 5 {
                assert_eq!(*v, BE::ZERO, "idx {i}");
            }
        }
    }

    #[test]
    fn version_wrong_at_final_fails() {
        let cols = Columns::baseline();
        let mut frame = EvaluationFrame::<BE>::new(cols.width(0));
        let mut periodic = vec![BE::ZERO; 1 + POSEIDON_ROUNDS + 1 + 1 + 1];

        let pi = pi::PublicInputs::default();
        let rc_box = Box::new([[BE::ZERO; 4]; POSEIDON_ROUNDS]);
        let mds_box = Box::new({
            let mut m = [[BE::ZERO; 4]; 4];
            m[0][0] = BE::ONE;
            m[1][1] = BE::ONE;
            m[2][2] = BE::ONE;
            m[3][3] = BE::ONE;
            m
        });
        let dom_box = Box::new([BE::ONE, BE::from(2u64)]);
        let ctx = BlockCtx::<BE>::new(&cols, &pi, &rc_box, &mds_box, &dom_box);

        // final row
        periodic[0] = BE::ZERO;
        periodic[1 + POSEIDON_ROUNDS] = BE::ONE;

        frame.current_mut()[cols.kv_g_map] = BE::ONE; // kv_map can be 1 same level
        frame.current_mut()[cols.kv_g_final] = BE::ONE;

        // wrong version bump (should +1)
        frame.current_mut()[cols.kv_version] = BE::from(10u64);
        frame.next_mut()[cols.kv_version] = BE::from(10u64);

        let mut res = vec![BE::ZERO; 8];
        let mut ix = 0usize;
        KvBlock::eval_block(&ctx, &frame, &periodic, &mut res, &mut ix);

        // version index = 3
        assert_ne!(res[3], BE::ZERO);
    }

    #[test]
    fn final_tie_acc_vs_lane_mismatch_fails() {
        let cols = Columns::baseline();
        let mut frame = EvaluationFrame::<BE>::new(cols.width(0));
        let mut periodic = vec![BE::ZERO; 1 + POSEIDON_ROUNDS + 1 + 1 + 1];

        let pi = pi::PublicInputs::default();
        let rc_box = Box::new([[BE::ZERO; 4]; POSEIDON_ROUNDS]);
        let mds_box = Box::new({
            let mut m = [[BE::ZERO; 4]; 4];
            m[0][0] = BE::ONE;
            m[1][1] = BE::ONE;
            m[2][2] = BE::ONE;
            m[3][3] = BE::ONE;
            m
        });
        let dom_box = Box::new([BE::ONE, BE::from(2u64)]);
        let ctx = BlockCtx::<BE>::new(&cols, &pi, &rc_box, &mds_box, &dom_box);

        // final row
        periodic[0] = BE::ONE; // kv_map may also be 1
        periodic[1 + POSEIDON_ROUNDS] = BE::ONE;

        frame.current_mut()[cols.kv_g_map] = BE::ONE;
        frame.current_mut()[cols.kv_g_final] = BE::ONE;

        // mismatch acc vs lane_l
        frame.current_mut()[cols.kv_acc] = BE::from(9u64);
        frame.current_mut()[cols.lane_l] = BE::from(1u64);

        let mut res = vec![BE::ZERO; 8];
        let mut ix = 0usize;
        KvBlock::eval_block(&ctx, &frame, &periodic, &mut res, &mut ix);

        // final tie index = 4
        assert_ne!(res[4], BE::ZERO);
    }
}

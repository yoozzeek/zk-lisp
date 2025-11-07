use winterfell::TraceTable;
use winterfell::math::fields::f128::BaseElement as BE;

use crate::layout::{self, Columns, POSEIDON_ROUNDS};
use crate::{poseidon, schedule};

// map row: sets lane_l=left, lane_r=right, lane_c0/c1=domain tags;
// then applies R rounds: next = MDS * cubic(cur) + RC[j].
pub fn apply_level(trace: &mut TraceTable<BE>, level: usize, left: BE, right: BE) {
    let cols = Columns::baseline();
    let steps = layout::STEPS_PER_LEVEL_P2;
    let base = level * steps;
    let row_map = base + schedule::pos_map();

    let dom = poseidon::domain_tags();
    let mds = poseidon::mds_matrix();
    let rc = poseidon::round_constants();

    // map row
    trace.set(cols.lane_l, row_map, left);
    trace.set(cols.lane_r, row_map, right);
    trace.set(cols.lane_c0, row_map, dom[0]);
    trace.set(cols.lane_c1, row_map, dom[1]);

    // iterate rounds
    let mut sl = left;
    let mut sr = right;
    let mut sc0 = dom[0];
    let mut sc1 = dom[1];

    for (j, rcj) in rc.iter().enumerate().take(POSEIDON_ROUNDS) {
        let r = base + 1 + j; // round row
        
        // set current state on round row (s_j)
        trace.set(cols.lane_l, r, sl);
        trace.set(cols.lane_r, r, sr);
        trace.set(cols.lane_c0, r, sc0);
        trace.set(cols.lane_c1, r, sc1);

        // compute next state s_{j+1}
        let sl3 = sl * sl * sl;
        let sr3 = sr * sr * sr;
        let sc03 = sc0 * sc0 * sc0;
        let sc13 = sc1 * sc1 * sc1;

        let yl = mds[0][0] * sl3 + mds[0][1] * sr3 + mds[0][2] * sc03 + mds[0][3] * sc13 + rcj[0];
        let yr = mds[1][0] * sl3 + mds[1][1] * sr3 + mds[1][2] * sc03 + mds[1][3] * sc13 + rcj[1];
        let yc0 = mds[2][0] * sl3 + mds[2][1] * sr3 + mds[2][2] * sc03 + mds[2][3] * sc13 + rcj[2];
        let yc1 = mds[3][0] * sl3 + mds[3][1] * sr3 + mds[3][2] * sc03 + mds[3][3] * sc13 + rcj[3];

        // advance state to s_{j+1}
        sl = yl;
        sr = yr;
        sc0 = yc0;
        sc1 = yc1;
    }

    // set final row to last state for convenience
    let row_fin = base + schedule::pos_final();
    trace.set(cols.lane_l, row_fin, sl);
    trace.set(cols.lane_r, row_fin, sr);
    trace.set(cols.lane_c0, row_fin, sc0);
    trace.set(cols.lane_c1, row_fin, sc1);
    
    #[cfg(debug_assertions)]
    {
        println!(
            "[poseidon.apply_level] level={} map_row={} fin_row={} final=(l:{:?} r:{:?} c0:{:?} c1:{:?})",
            level, row_map, row_fin, sl, sr, sc0, sc1
        );
    }
}

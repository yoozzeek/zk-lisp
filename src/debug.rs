use winterfell::math::FieldElement;
use winterfell::math::fields::f128::BaseElement as BE;
use winterfell::{Air, EvaluationFrame, Trace, TraceTable};

use crate::air::ZkLispAir;
use crate::layout::{Columns, POSEIDON_ROUNDS, STEPS_PER_LEVEL_P2};
use crate::schedule;

pub fn print_trace_row(_air: &ZkLispAir, trace: &TraceTable<BE>, row: usize) {
    let cols = Columns::baseline();
    let n = trace.length();

    if row >= n {
        tracing::error!("row {row} out of range (n={n})");
        return;
    }

    let lvl = row / STEPS_PER_LEVEL_P2;
    let pos = row % STEPS_PER_LEVEL_P2;

    let g_map = trace.get(cols.g_map, row);
    let g_final = trace.get(cols.g_final, row);

    let mut g_rounds = Vec::new();
    for j in 0..POSEIDON_ROUNDS {
        g_rounds.push(trace.get(cols.g_r_index(j), row));
    }

    tracing::debug!(
        "[row={row} lvl={lvl} pos={pos} ({})] gates: map={g_map} final={g_final} rounds={g_rounds:?}",
        pos_label(pos)
    );

    // dump a few VM columns on map rows
    if pos == schedule::pos_map() {
        let mut ops = Vec::new();
        for (name, c) in [
            ("const", cols.op_const),
            ("mov", cols.op_mov),
            ("add", cols.op_add),
            ("sub", cols.op_sub),
            ("mul", cols.op_mul),
            ("neg", cols.op_neg),
            ("eq", cols.op_eq),
            ("select", cols.op_select),
            ("hash2", cols.op_hash2),
        ] {
            ops.push((name, trace.get(c, row)));
        }

        tracing::debug!("  vm.ops: {ops:?}");
    }
}

pub fn print_first_bad_row(air: &ZkLispAir, trace: &TraceTable<BE>) {
    let width = trace.width();
    let n = trace.length();
    let pc = air.get_periodic_column_polys();

    let mut frame = EvaluationFrame::<BE>::new(width);
    let mut res = vec![BE::ZERO; Air::context(air).num_main_transition_constraints()];

    for r in 0..n {
        for c in 0..width {
            frame.current_mut()[c] = trace.get(c, r);

            let nxt = if r + 1 < n { r + 1 } else { r };
            frame.next_mut()[c] = trace.get(c, nxt);
        }

        let pv: Vec<BE> = pc.iter().map(|col| col[r]).collect();
        Air::evaluate_transition(air, &frame, &pv, &mut res);

        if let Some((i, v)) = res.iter().enumerate().find(|(_, x)| **x != BE::ZERO) {
            tracing::debug!("first bad row={r} constraint={i} value={v:?}");
            print_trace_row(air, trace, r);

            break;
        }
    }
}

#[inline]
fn pos_label(pos: usize) -> &'static str {
    if pos == schedule::pos_map() {
        "map"
    } else if pos == schedule::pos_final() {
        "final"
    } else if schedule::is_round_pos(pos) {
        "round"
    } else {
        "pad"
    }
}

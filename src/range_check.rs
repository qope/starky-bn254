use core::ops::Range;

use itertools::Itertools;
use plonky2::{
    field::{extension::Extendable, packed::PackedField, types::Field},
    hash::hash_types::RichField,
    plonk::circuit_builder::CircuitBuilder,
};

use crate::constants::LIMB_BITS;
use crate::lookup::{eval_lookups, eval_lookups_circuit, permuted_cols};

use starky::{
    constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer},
    permutation::PermutationPair,
    vars::{StarkEvaluationTargets, StarkEvaluationVars},
};

/// 1 + 2*target_cols.len()
pub fn generate_u16_range_check<F: RichField>(
    target_cols: Range<usize>,
    trace_cols: &mut Vec<Vec<F>>,
) {
    let range_max: u64 = 1 << LIMB_BITS;

    assert!(trace_cols.iter().all(|col| col.len() == range_max as usize));

    let mut table = vec![];

    for i in 0..range_max {
        table.push(F::from_canonical_u64(i));
    }

    trace_cols.push(table.clone());

    for i in target_cols {
        let col = trace_cols[i].clone();
        assert!(col.iter().all(|&x| x.to_canonical_u64() < range_max));

        let (col_perm, table_perm) = permuted_cols(&col, &table);
        trace_cols.push(col_perm);
        trace_cols.push(table_perm);
    }
}

pub fn eval_u16_range_check<
    F: Field,
    P: PackedField<Scalar = F>,
    const COLS: usize,
    const PUBLIC_INPUTS: usize,
>(
    vars: StarkEvaluationVars<F, P, COLS, PUBLIC_INPUTS>,
    yield_constr: &mut ConstraintConsumer<P>,
    main_col: usize,
    target_cols: Range<usize>,
) {
    // lookup
    for i in (main_col + 1..main_col + 1 + 2 * target_cols.len()).step_by(2) {
        eval_lookups(vars, yield_constr, i, i + 1); //col_perm_lo and table_perm_lo
    }

    // table format
    let cur_table = vars.local_values[main_col];
    let next_table = vars.next_values[main_col];
    yield_constr.constraint_first_row(cur_table);
    let incr = next_table - cur_table;
    yield_constr.constraint_transition(incr * incr - incr);
    let range_max = P::Scalar::from_canonical_u64(((1 << LIMB_BITS) - 1) as u64);
    yield_constr.constraint_last_row(cur_table - range_max);
}

pub fn eval_u16_range_check_circuit<
    F: RichField + Extendable<D>,
    const D: usize,
    const COLS: usize,
    const PUBLIC_INPUTS: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    vars: StarkEvaluationTargets<D, COLS, PUBLIC_INPUTS>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    main_col: usize,
    target_cols: Range<usize>,
) {
    // lookup
    for i in (main_col + 1..main_col + 1 + 2 * target_cols.len()).step_by(2) {
        eval_lookups_circuit(builder, vars, yield_constr, i, i + 1);
    }

    // table format
    let cur_table = vars.local_values[main_col];
    let next_table = vars.next_values[main_col];
    yield_constr.constraint_first_row(builder, cur_table);
    let incr = builder.sub_extension(next_table, cur_table);
    let t = builder.mul_sub_extension(incr, incr, incr);
    yield_constr.constraint_transition(builder, t);

    let range_max =
        builder.constant_extension(F::Extension::from_canonical_usize((1 << LIMB_BITS) - 1));
    let t = builder.sub_extension(cur_table, range_max);
    yield_constr.constraint_last_row(builder, t);
}

pub fn u16_range_check_pairs(main_col: usize, target_cols: Range<usize>) -> Vec<PermutationPair> {
    let mut pairs = vec![];

    for (i, pos) in target_cols.enumerate() {
        // table
        pairs.push(PermutationPair::singletons(
            main_col,
            main_col + 1 + 2 * i + 1,
        ));

        // cols
        pairs.push(PermutationPair::singletons(pos, main_col + 1 + 2 * i));
    }
    pairs
}

/// 1 + 6*target_cols.len()
pub fn generate_split_u16_range_check<F: RichField>(
    target_cols: Range<usize>,
    trace_cols: &mut Vec<Vec<F>>,
) {
    let range_max: u64 = 1 << 8;
    let num_rows = trace_cols[0].len() as u64;
    assert!(trace_cols.iter().all(|col| col.len() == num_rows as usize));
    assert!(num_rows.is_power_of_two() && range_max <= num_rows);

    let mut table = vec![];

    for i in 0..range_max {
        table.push(F::from_canonical_u64(i));
    }
    for _ in range_max..num_rows {
        table.push(F::from_canonical_u64(range_max - 1));
    }

    trace_cols.push(table.clone());

    for i in target_cols {
        let col = trace_cols[i].clone();
        assert!(col.iter().all(|&x| x.to_canonical_u64() < (1 << 16)));

        // split to lo and hi
        let col_lo = col
            .iter()
            .map(|&x| F::from_canonical_u8(x.to_canonical_u64() as u8))
            .collect_vec();
        let col_hi = col
            .iter()
            .map(|&x| F::from_canonical_u8((x.to_canonical_u64() >> 8) as u8))
            .collect_vec();

        let (col_perm_lo, table_perm_lo) = permuted_cols(&col_lo, &table);
        let (col_perm_hi, table_perm_hi) = permuted_cols(&col_hi, &table);

        trace_cols.push(col_lo);
        trace_cols.push(col_perm_lo);
        trace_cols.push(table_perm_lo);
        trace_cols.push(col_hi);
        trace_cols.push(col_perm_hi);
        trace_cols.push(table_perm_hi);
    }
}

pub fn eval_split_u16_range_check<
    F: Field,
    P: PackedField<Scalar = F>,
    const COLS: usize,
    const PUBLIC_INPUTS: usize,
>(
    vars: StarkEvaluationVars<F, P, COLS, PUBLIC_INPUTS>,
    yield_constr: &mut ConstraintConsumer<P>,
    main_col: usize,
    target_cols: Range<usize>,
) {
    // split
    for (i, col) in target_cols.clone().enumerate() {
        let original = vars.local_values[col];
        let lo = vars.local_values[main_col + 1 + 6 * i];
        let hi = vars.local_values[main_col + 4 + 6 * i];

        let recoverd = lo + hi * P::Scalar::from_canonical_u64(1 << 8);
        yield_constr.constraint(original - recoverd);
    }

    // lookup
    for i in (main_col + 1..main_col + 1 + 6 * target_cols.len()).step_by(6) {
        eval_lookups(vars, yield_constr, i + 1, i + 2); //col_perm_lo and table_perm_lo
        eval_lookups(vars, yield_constr, i + 4, i + 5); //col_perm_hi and table_perm_hi
    }

    // table format
    let cur_table = vars.local_values[main_col];
    let next_table = vars.next_values[main_col];
    yield_constr.constraint_first_row(cur_table);
    let incr = next_table - cur_table;
    yield_constr.constraint_transition(incr * incr - incr);
    let range_max = P::Scalar::from_canonical_u64(((1 << 8) - 1) as u64);
    yield_constr.constraint_last_row(cur_table - range_max);
}

pub fn eval_split_u16_range_check_circuit<
    F: RichField + Extendable<D>,
    const D: usize,
    const COLS: usize,
    const PUBLIC_INPUTS: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    vars: StarkEvaluationTargets<D, COLS, PUBLIC_INPUTS>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    main_col: usize,
    target_cols: Range<usize>,
) {
    let base = builder.constant_extension(F::Extension::from_canonical_u64(1u64 << 8));
    for (i, col) in target_cols.clone().enumerate() {
        let original = vars.local_values[col];
        let lo = vars.local_values[main_col + 1 + 6 * i];
        let hi = vars.local_values[main_col + 4 + 6 * i];
        let recovered = builder.mul_add_extension(base, hi, lo);
        let diff = builder.sub_extension(original, recovered);
        yield_constr.constraint(builder, diff);
    }

    // lookup
    for i in (main_col + 1..main_col + 1 + 6 * target_cols.len()).step_by(6) {
        eval_lookups_circuit(builder, vars, yield_constr, i + 1, i + 2); //col_perm_lo and table_perm_lo
        eval_lookups_circuit(builder, vars, yield_constr, i + 4, i + 5); //col_perm_hi and table_perm_hi
    }

    // table format
    let cur_table = vars.local_values[main_col];
    let next_table = vars.next_values[main_col];
    yield_constr.constraint_first_row(builder, cur_table);
    let incr = builder.sub_extension(next_table, cur_table);
    let t = builder.mul_sub_extension(incr, incr, incr);
    yield_constr.constraint_transition(builder, t);

    let range_max = builder.constant_extension(F::Extension::from_canonical_usize((1 << 8) - 1));
    let t = builder.sub_extension(cur_table, range_max);
    yield_constr.constraint_last_row(builder, t);
}

pub fn split_u16_range_check_pairs(
    main_col: usize,
    target_cols: Range<usize>,
) -> Vec<PermutationPair> {
    let mut pairs = vec![];

    for i in (main_col + 1..main_col + 1 + 6 * target_cols.len()).step_by(6) {
        // table
        pairs.push(PermutationPair::singletons(main_col, i + 2));
        pairs.push(PermutationPair::singletons(main_col, i + 5));

        // cols
        pairs.push(PermutationPair::singletons(i, i + 1));
        pairs.push(PermutationPair::singletons(i + 3, i + 4));
    }
    pairs
}

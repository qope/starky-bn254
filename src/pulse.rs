use itertools::Itertools;
use plonky2::{
    field::{extension::Extendable, packed::PackedField, types::Field},
    hash::hash_types::RichField,
    iop::ext_target::ExtensionTarget,
    plonk::circuit_builder::CircuitBuilder,
};
use starky::constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer};

pub fn get_pulse_col(start_pulse_col: usize, i: usize) -> usize {
    start_pulse_col + 1 + 2 * i + 1
}

pub fn get_witness_col(start_pulse_col: usize, i: usize) -> usize {
    start_pulse_col + 1 + 2 * i
}

/// Adds a pulse column of the given positions to trace_cols.
/// 1 + 2*pulse_positions.len() columns are added to trace_cols.
pub fn generate_pulse<F: RichField>(trace_cols: &mut Vec<Vec<F>>, pulse_positions: Vec<usize>) {
    let rows = trace_cols[0].len();
    assert!(trace_cols.iter().all(|col| col.len() == rows));
    assert!(pulse_positions.iter().all(|&pos| pos < rows));
    let counter = (0..rows).map(|x| F::from_canonical_usize(x)).collect_vec();
    trace_cols.push(counter.clone());
    for pos in pulse_positions {
        let witness = counter
            .iter()
            .map(|&x| {
                if x == F::from_canonical_usize(pos) {
                    F::ZERO
                } else {
                    let diff = x - F::from_canonical_usize(pos);
                    diff.inverse()
                }
            })
            .collect_vec();
        let mut pulse = vec![F::ZERO; rows];
        pulse[pos] = F::ONE;
        trace_cols.push(witness);
        trace_cols.push(pulse);
    }
}

pub fn eval_pulse<P: PackedField>(
    yield_constr: &mut ConstraintConsumer<P>,
    lv: &[P],
    nv: &[P],
    start_pulse_col: usize,
    pulse_positions: Vec<usize>,
) {
    let counter = lv[start_pulse_col];
    yield_constr.constraint_first_row(counter);
    let next_counter: P = nv[start_pulse_col];
    yield_constr.constraint_transition(next_counter - counter - P::ONES);
    for (i, &pos) in pulse_positions.iter().enumerate() {
        let counter_minus_pos = counter - P::Scalar::from_canonical_usize(pos);
        let witness = lv[get_witness_col(start_pulse_col, i)];
        let pulse = lv[get_pulse_col(start_pulse_col, i)];
        yield_constr.constraint(counter_minus_pos * witness + pulse - P::ONES); // pulse = 1 - (counter - pos) * witness
        yield_constr.constraint(counter_minus_pos * pulse);
    }
}

pub fn eval_pulse_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    lv: &[ExtensionTarget<D>],
    nv: &[ExtensionTarget<D>],
    start_pulse_col: usize,
    pulse_positions: Vec<usize>,
) {
    let one = builder.one_extension();
    let counter = lv[start_pulse_col];
    yield_constr.constraint_first_row(builder, counter);
    let next_counter = nv[start_pulse_col];
    {
        let diff = builder.sub_extension(next_counter, counter);
        let diff = builder.sub_extension(diff, one);
        yield_constr.constraint_transition(builder, diff);
    }
    for (i, &pos) in pulse_positions.iter().enumerate() {
        let pos = builder.constant_extension(F::Extension::from_canonical_usize(pos));
        let counter_minus_pos = builder.sub_extension(counter, pos);
        let witness = lv[get_witness_col(start_pulse_col, i)];
        let pulse = lv[get_pulse_col(start_pulse_col, i)];
        {
            let pulse_minus_one = builder.sub_extension(pulse, one);
            let t = builder.mul_add_extension(counter_minus_pos, witness, pulse_minus_one);
            yield_constr.constraint(builder, t);
        }
        {
            let t = builder.mul_extension(counter_minus_pos, pulse);
            yield_constr.constraint(builder, t);
        }
    }
}

/// add 2 cols
pub fn generate_periodic_pulse_witness<F: RichField>(
    trace_cols: &mut Vec<Vec<F>>,
    pulse_col: usize,
    period: usize,
    first_pulse: usize,
) {
    let pulse = trace_cols[pulse_col].clone();
    let rows = pulse.len();
    assert!(trace_cols.iter().all(|col| col.len() == rows));
    assert!(first_pulse < period);

    let initial_counter = period - first_pulse - 1;
    let mut counter = vec![initial_counter];
    for i in 1..rows {
        counter.push((counter[i - 1] + 1) % period);
    }
    let counter = counter
        .into_iter()
        .map(F::from_canonical_usize)
        .collect_vec();
    counter
        .iter()
        .zip(pulse.iter())
        .for_each(|(&counter, &pulse)| {
            if counter == F::from_canonical_usize(period - 1) {
                assert!(pulse == F::ONE);
            } else {
                assert!(pulse == F::ZERO);
            }
        });

    trace_cols.push(counter.clone());
    let witness = counter
        .iter()
        .map(|&x| {
            if x == F::from_canonical_usize(period - 1) {
                F::ZERO
            } else {
                let diff = x - F::from_canonical_usize(period - 1);
                diff.inverse()
            }
        })
        .collect_vec();
    trace_cols.push(witness);
}

pub fn eval_periodic_pulse<P: PackedField>(
    yield_constr: &mut ConstraintConsumer<P>,
    lv: &[P],
    nv: &[P],
    pulse_col: usize,
    start_pulse_col: usize,
    period: usize,
    first_pulse: usize,
) {
    let counter = lv[start_pulse_col];
    let witness = lv[start_pulse_col + 1];
    let is_reset = lv[pulse_col];
    let next_counter = nv[start_pulse_col];

    let initial_counter = period - first_pulse - 1;
    yield_constr.constraint_first_row(counter - P::Scalar::from_canonical_usize(initial_counter));

    let is_not_reset = P::ONES - is_reset;
    yield_constr.constraint_transition(is_not_reset * (next_counter - counter - P::ONES));
    yield_constr.constraint_transition(is_reset * next_counter);

    let delta = counter - P::Scalar::from_canonical_usize(period - 1);
    yield_constr.constraint(delta * witness + is_reset - P::ONES); // is_reset = 1 - delta * witness
    yield_constr.constraint(delta * is_reset);
}

pub fn eval_periodic_pulse_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    lv: &[ExtensionTarget<D>],
    nv: &[ExtensionTarget<D>],
    pulse_col: usize,
    start_pulse_col: usize,
    period: usize,
    first_pulse: usize,
) {
    let one = builder.one_extension();
    let counter = lv[start_pulse_col];
    let witness = lv[start_pulse_col + 1];
    let is_reset = lv[pulse_col];
    let next_counter = nv[start_pulse_col];

    let initial_counter =
        builder.constant_extension(F::Extension::from_canonical_usize(period - first_pulse - 1));
    let diff = builder.sub_extension(counter, initial_counter);
    yield_constr.constraint_first_row(builder, diff);

    let is_not_reset = builder.sub_extension(one, is_reset);
    let diff = builder.sub_extension(next_counter, counter);
    let diff = builder.sub_extension(diff, one);
    let t = builder.mul_extension(is_not_reset, diff);
    yield_constr.constraint_transition(builder, t);
    let t = builder.mul_extension(is_reset, next_counter);
    yield_constr.constraint_transition(builder, t);

    let period_minus_one =
        builder.constant_extension(F::Extension::from_canonical_usize(period - 1));
    let delta = builder.sub_extension(counter, period_minus_one);
    let is_reset_minus_one = builder.sub_extension(is_reset, one);
    let t = builder.mul_add_extension(delta, witness, is_reset_minus_one);
    yield_constr.constraint(builder, t);
    let t = builder.mul_extension(delta, is_reset);
    yield_constr.constraint(builder, t);
}

#[cfg(test)]
mod tests {
    use itertools::Itertools;
    use plonky2::field::{
        goldilocks_field::GoldilocksField,
        types::{Field, PrimeField64},
    };

    use super::generate_periodic_pulse_witness;

    type F = GoldilocksField;

    #[test]
    fn test_periodic_pulse_simple() {
        let period = 4usize;
        let dummy_col = (0..16).map(F::from_canonical_usize).collect_vec();
        let pulse_col = dummy_col
            .iter()
            .map(|&x| {
                if x.to_canonical_u64() as usize % period == period - 2 {
                    F::ONE
                } else {
                    F::ZERO
                }
            })
            .collect_vec();
        let mut trace_cols = vec![dummy_col, pulse_col];
        generate_periodic_pulse_witness(&mut trace_cols, 1, period, period - 2);
        dbg!(trace_cols);
    }
}

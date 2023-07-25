use plonky2::{
    field::{extension::Extendable, packed::PackedField},
    hash::hash_types::RichField,
    iop::ext_target::ExtensionTarget,
    plonk::circuit_builder::CircuitBuilder,
};

use starky::constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer};

use super::constants::N_LIMBS;

pub fn eval_bool<P: PackedField>(yield_constr: &mut ConstraintConsumer<P>, val: P) {
    yield_constr.constraint(val * val - val);
}

pub fn eval_bool_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    val: ExtensionTarget<D>,
) {
    let t = builder.mul_sub_extension(val, val, val);
    yield_constr.constraint(builder, t);
}

pub fn vec_equal<P: PackedField>(
    yield_constr: &mut ConstraintConsumer<P>,
    filter: P,
    x: &[P],
    y: &[P],
) {
    assert!(x.len() == y.len());
    x.iter()
        .zip(y.iter())
        .for_each(|(&x_i, &y_i)| yield_constr.constraint(filter * (x_i - y_i)));
}

pub fn vec_equal_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    filter: ExtensionTarget<D>,
    x: &[ExtensionTarget<D>],
    y: &[ExtensionTarget<D>],
) {
    assert!(x.len() == y.len());
    x.iter().zip(y.iter()).for_each(|(&x_i, &y_i)| {
        let diff = builder.sub_extension(x_i, y_i);
        let t = builder.mul_extension(filter, diff);
        yield_constr.constraint(builder, t);
    });
}

pub fn fq_equal_transition<P: PackedField>(
    yield_constr: &mut ConstraintConsumer<P>,
    filter: P,
    x: &[P; N_LIMBS],
    y: &[P; N_LIMBS],
) {
    x.iter()
        .zip(y.iter())
        .for_each(|(&x_i, &y_i)| yield_constr.constraint_transition(filter * (x_i - y_i)));
}

pub fn fq_equal_transition_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    filter: ExtensionTarget<D>,
    x: &[ExtensionTarget<D>; N_LIMBS],
    y: &[ExtensionTarget<D>; N_LIMBS],
) {
    x.iter().zip(y.iter()).for_each(|(&x_i, &y_i)| {
        let diff = builder.sub_extension(x_i, y_i);
        let t = builder.mul_extension(filter, diff);
        yield_constr.constraint_transition(builder, t);
    });
}

pub fn fq_equal_first<P: PackedField>(
    yield_constr: &mut ConstraintConsumer<P>,
    x: [P; N_LIMBS],
    y: [P; N_LIMBS],
) {
    x.iter()
        .zip(y.iter())
        .for_each(|(&x_i, &y_i)| yield_constr.constraint_first_row(x_i - y_i));
}

pub fn fq_equal_first_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    x: [ExtensionTarget<D>; N_LIMBS],
    y: [ExtensionTarget<D>; N_LIMBS],
) {
    x.iter().zip(y.iter()).for_each(|(&x_i, &y_i)| {
        let diff = builder.sub_extension(x_i, y_i);
        yield_constr.constraint_first_row(builder, diff);
    });
}

pub fn fq_equal_last<P: PackedField>(
    yield_constr: &mut ConstraintConsumer<P>,
    x: [P; N_LIMBS],
    y: [P; N_LIMBS],
) {
    x.iter()
        .zip(y.iter())
        .for_each(|(&x_i, &y_i)| yield_constr.constraint_last_row(x_i - y_i));
}

pub fn fq_equal_last_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    x: [ExtensionTarget<D>; N_LIMBS],
    y: [ExtensionTarget<D>; N_LIMBS],
) {
    x.iter().zip(y.iter()).for_each(|(&x_i, &y_i)| {
        let diff = builder.sub_extension(x_i, y_i);
        yield_constr.constraint_last_row(builder, diff);
    });
}

pub fn fq2_equal_transition<P: PackedField>(
    yield_constr: &mut ConstraintConsumer<P>,
    filter: P,
    x: [[P; N_LIMBS]; 2],
    y: [[P; N_LIMBS]; 2],
) {
    x.iter()
        .zip(y.iter())
        .for_each(|(&x_i, &y_i)| fq_equal_transition(yield_constr, filter, &x_i, &y_i));
}

pub fn fq2_equal_transition_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    filter: ExtensionTarget<D>,
    x: [[ExtensionTarget<D>; N_LIMBS]; 2],
    y: [[ExtensionTarget<D>; N_LIMBS]; 2],
) {
    x.iter().zip(y.iter()).for_each(|(&x_i, &y_i)| {
        fq_equal_transition_circuit(builder, yield_constr, filter, &x_i, &y_i)
    });
}

pub fn fq2_equal_first<P: PackedField>(
    yield_constr: &mut ConstraintConsumer<P>,
    x: [[P; N_LIMBS]; 2],
    y: [[P; N_LIMBS]; 2],
) {
    x.iter()
        .zip(y.iter())
        .for_each(|(&x_i, &y_i)| fq_equal_first(yield_constr, x_i, y_i));
}

pub fn fq2_equal_first_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    x: [[ExtensionTarget<D>; N_LIMBS]; 2],
    y: [[ExtensionTarget<D>; N_LIMBS]; 2],
) {
    x.iter()
        .zip(y.iter())
        .for_each(|(&x_i, &y_i)| fq_equal_first_circuit(builder, yield_constr, x_i, y_i));
}

pub fn fq2_equal_last<P: PackedField>(
    yield_constr: &mut ConstraintConsumer<P>,
    x: [[P; N_LIMBS]; 2],
    y: [[P; N_LIMBS]; 2],
) {
    x.iter()
        .zip(y.iter())
        .for_each(|(&x_i, &y_i)| fq_equal_last(yield_constr, x_i, y_i));
}

pub fn fq2_equal_last_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    x: [[ExtensionTarget<D>; N_LIMBS]; 2],
    y: [[ExtensionTarget<D>; N_LIMBS]; 2],
) {
    x.iter()
        .zip(y.iter())
        .for_each(|(&x_i, &y_i)| fq_equal_last_circuit(builder, yield_constr, x_i, y_i));
}

pub fn fq12_equal_first<P: PackedField>(
    yield_constr: &mut ConstraintConsumer<P>,
    x: &Vec<[P; N_LIMBS]>,
    y: &Vec<[P; N_LIMBS]>,
) {
    assert!(x.len() == 12);
    assert!(y.len() == 12);
    x.iter()
        .zip(y.iter())
        .for_each(|(&x_i, &y_i)| fq_equal_first(yield_constr, x_i, y_i));
}

pub fn fq12_equal_first_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    x: &Vec<[ExtensionTarget<D>; N_LIMBS]>,
    y: &Vec<[ExtensionTarget<D>; N_LIMBS]>,
) {
    x.iter()
        .zip(y.iter())
        .for_each(|(&x_i, &y_i)| fq_equal_first_circuit(builder, yield_constr, x_i, y_i));
}

pub fn fq12_equal_last<P: PackedField>(
    yield_constr: &mut ConstraintConsumer<P>,
    x: &Vec<[P; N_LIMBS]>,
    y: &Vec<[P; N_LIMBS]>,
) {
    assert!(x.len() == 12);
    assert!(y.len() == 12);
    x.iter()
        .zip(y.iter())
        .for_each(|(&x_i, &y_i)| fq_equal_last(yield_constr, x_i, y_i));
}

pub fn fq12_equal_last_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    x: &Vec<[ExtensionTarget<D>; N_LIMBS]>,
    y: &Vec<[ExtensionTarget<D>; N_LIMBS]>,
) {
    x.iter()
        .zip(y.iter())
        .for_each(|(&x_i, &y_i)| fq_equal_last_circuit(builder, yield_constr, x_i, y_i));
}

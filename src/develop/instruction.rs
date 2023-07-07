use core::fmt;

use plonky2::{
    field::{extension::Extendable, packed::PackedField, types::PrimeField64},
    hash::hash_types::RichField,
    iop::ext_target::ExtensionTarget,
    plonk::circuit_builder::CircuitBuilder,
};

use crate::constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer};

use super::constants::{BITS_LEN, N_LIMBS};

pub fn write_instruction<F: Copy, const N: usize, const INSTRUCTION_LEN: usize>(
    lv: &mut [F; N],
    instruction: &[F; INSTRUCTION_LEN],
    cur_col: &mut usize,
) {
    lv[*cur_col..*cur_col + INSTRUCTION_LEN].copy_from_slice(instruction);
    *cur_col += INSTRUCTION_LEN;
}

pub fn read_instruction<F: Clone + fmt::Debug, const N: usize, const INSTRUCTION_LEN: usize>(
    lv: &[F; N],
    cur_col: &mut usize,
) -> [F; INSTRUCTION_LEN] {
    let output = lv[*cur_col..*cur_col + INSTRUCTION_LEN].to_vec();
    *cur_col += INSTRUCTION_LEN;
    output.try_into().unwrap()
}

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

pub fn generate_initial_pow_instruction<F: PrimeField64, const N: usize>(
    lv: &mut [F; N],
    is_sq_col: usize,
    is_mul_col: usize,
    is_noop_col: usize,
    exp_bits: [F; BITS_LEN],
) {
    lv[is_sq_col] = F::ZERO;
    let mut cur_col = is_mul_col;
    write_instruction::<_, N, BITS_LEN>(lv, &exp_bits, &mut cur_col);
    lv[is_noop_col] = F::ONE - lv[is_mul_col];
}

pub fn generate_next_pow_instruction<F: PrimeField64, const N: usize>(
    lv: &[F; N],
    nv: &mut [F; N],
    is_sq_col: usize,
    is_mul_col: usize,
    is_noop_col: usize,
) {
    nv[is_sq_col] = F::ONE - lv[is_sq_col];
    let mut cur_col = is_mul_col;
    if lv[is_sq_col] == F::ONE {
        // rotate instruction
        let mut rotated_instruction = lv[is_mul_col + 1..is_mul_col + BITS_LEN].to_vec();
        rotated_instruction.push(F::ZERO);
        write_instruction::<_, N, BITS_LEN>(
            nv,
            &rotated_instruction.try_into().unwrap(),
            &mut cur_col,
        );
    } else {
        let instruction: [F; BITS_LEN] = lv[is_mul_col..is_mul_col + BITS_LEN]
            .to_vec()
            .try_into()
            .unwrap();
        write_instruction::<_, N, BITS_LEN>(nv, &instruction, &mut cur_col);
        // set nv[IS_MUL_COL] to 0 to ensure is_mul + is_sq + is_noop = 1
        // this cell is never used.
        nv[is_mul_col] = F::ZERO;
    }
    nv[is_noop_col] = (F::ONE - nv[is_mul_col]) * (F::ONE - nv[is_sq_col]);
}

pub fn eval_pow_instruction<P: PackedField, const N: usize>(
    yield_constr: &mut ConstraintConsumer<P>,
    lv: &[P; N],
    nv: &[P; N],
    is_sq_col: usize,
    is_mul_col: usize,
    is_noop_col: usize,
) {
    // validation of first row
    yield_constr.constraint_first_row(lv[is_sq_col]);

    // validation of instruction
    eval_bool(yield_constr, lv[is_noop_col]);
    yield_constr.constraint(lv[is_sq_col] + lv[is_mul_col] + lv[is_noop_col] - P::ONES);

    // transition rule for instruction
    let mut cur_col = is_mul_col;
    let instruction: [_; BITS_LEN] = read_instruction(&lv, &mut cur_col);
    cur_col = is_mul_col;
    let next_instruction: [_; BITS_LEN] = read_instruction(&nv, &mut cur_col);
    yield_constr.constraint_transition(nv[is_sq_col] + lv[is_sq_col] - P::ONES);

    // if is_sq == 1, then rotate instruction
    for i in 1..BITS_LEN {
        yield_constr
            .constraint_transition(lv[is_sq_col] * (next_instruction[i - 1] - instruction[i]));
    }
    yield_constr.constraint_transition(lv[is_sq_col] * next_instruction[BITS_LEN - 1]);

    // if is_sq == 0, then copy instruction, except for the first which is set to 0 (this does not have to be verified)
    let not_is_sq = P::ONES - lv[is_sq_col];
    for i in 1..BITS_LEN {
        yield_constr.constraint_transition(not_is_sq * (next_instruction[i] - instruction[i]));
    }
}

pub fn eval_pow_instruction_cirucuit<
    F: RichField + Extendable<D>,
    const D: usize,
    const N: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    lv: &[ExtensionTarget<D>; N],
    nv: &[ExtensionTarget<D>; N],
    is_sq_col: usize,
    is_mul_col: usize,
    is_noop_col: usize,
) {
    let one = builder.one_extension();
    // validation of first row
    yield_constr.constraint_first_row(builder, lv[is_sq_col]);

    // validation of instruction
    eval_bool_circuit(builder, yield_constr, lv[is_noop_col]);
    let sum = builder.add_many_extension([lv[is_sq_col], lv[is_mul_col], lv[is_noop_col]]);
    let diff = builder.sub_extension(sum, one);
    yield_constr.constraint(builder, diff);

    // transition rule for instruction
    let mut cur_col = is_mul_col;
    let instruction: [_; BITS_LEN] = read_instruction(&lv, &mut cur_col);
    cur_col = is_mul_col;
    let next_instruction: [_; BITS_LEN] = read_instruction(&nv, &mut cur_col);

    let sum = builder.add_extension(nv[is_sq_col], lv[is_sq_col]);
    let diff = builder.sub_extension(sum, one);
    yield_constr.constraint_transition(builder, diff);

    // if is_sq == 1, then rotate instruction
    for i in 1..BITS_LEN {
        let diff = builder.sub_extension(next_instruction[i - 1], instruction[i]);
        let t = builder.mul_extension(lv[is_sq_col], diff);
        yield_constr.constraint_transition(builder, t);
    }
    let t = builder.mul_extension(lv[is_sq_col], next_instruction[BITS_LEN - 1]);
    yield_constr.constraint_transition(builder, t);

    // if is_sq == 0, then copy instruction, except for the first which is set to 0 (this does not have to be verified)
    let not_is_sq = builder.sub_extension(one, lv[is_sq_col]);
    for i in 1..BITS_LEN {
        let diff = builder.sub_extension(next_instruction[i], instruction[i]);
        let t = builder.mul_extension(not_is_sq, diff);
        yield_constr.constraint_transition(builder, t);
    }
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

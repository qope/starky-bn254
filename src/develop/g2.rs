use core::fmt::Debug;
use core::marker::PhantomData;

use ark_bn254::{Fq2, G2Affine};
use ark_std::UniformRand;
use itertools::Itertools;
use plonky2::field::extension::{Extendable, FieldExtension};
use plonky2::field::packed::PackedField;
use plonky2::field::polynomial::PolynomialValues;
use plonky2::field::types::Field;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::ext_target::ExtensionTarget;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::util::transpose;

use crate::constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer};
use crate::develop::constants::N_LIMBS;
use crate::develop::fq2::{read_fq2, write_fq2};
use crate::develop::modular::{read_modulus_aux, ModulusAux};
use crate::develop::modular_zero::{read_modulus_aux_zero, write_modulus_aux_zero, ModulusAuxZero};
use crate::permutation::PermutationPair;
use crate::stark::Stark;
use crate::vars::{StarkEvaluationTargets, StarkEvaluationVars};

use super::constants::BITS_LEN;
use super::fq2::{
    pol_add_fq2, pol_add_fq2_circuit, pol_mul_fq2, pol_mul_fq2_circuit, pol_mul_scalar_fq2,
    pol_mul_scalar_fq2_circuit, pol_sub_fq2, pol_sub_fq2_circuit, to_wide_fq2, to_wide_fq2_circuit,
};
use super::modular::{
    bn254_base_modulus_bigint, bn254_base_modulus_packfield, eval_modular_op,
    eval_modular_op_circuit, generate_modular_op, write_modulus_aux,
};
use super::modular_zero::{eval_modular_zero, eval_modular_zero_circuit, generate_modular_zero};
use super::range_check::{
    eval_split_u16_range_check, eval_split_u16_range_check_circuit, generate_split_u16_range_check,
    split_u16_range_check_pairs,
};
use super::utils::{
    columns_to_fq2, fq2_to_columns, i64_to_column_positive, positive_column_to_i64,
};

pub struct G2Output<F> {
    pub lambda: [[F; N_LIMBS]; 2],
    pub new_x: [[F; N_LIMBS]; 2],
    pub new_y: [[F; N_LIMBS]; 2],
    pub aux_zeros: [ModulusAuxZero<F>; 2],
    pub auxs: [ModulusAux<F>; 4],
    pub quot_sign_zeros: [F; 2],
    pub quot_signs: [F; 4],
}

impl<F: RichField + Default> Default for G2Output<F> {
    fn default() -> Self {
        Self {
            lambda: [[F::ZERO; N_LIMBS]; 2],
            new_x: [[F::ZERO; N_LIMBS]; 2],
            new_y: [[F::ZERO; N_LIMBS]; 2],
            aux_zeros: [ModulusAuxZero::default(); 2],
            auxs: [ModulusAux::default(); 4],
            quot_sign_zeros: [F::ONE; 2],
            quot_signs: [F::ONE; 4],
        }
    }
}

pub fn write_g2_output<F: Copy, const NUM_COL: usize>(
    lv: &mut [F; NUM_COL],
    output: &G2Output<F>,
    cur_col: &mut usize,
) {
    let orinigal_col = *cur_col;
    write_fq2(lv, output.lambda, cur_col);
    write_fq2(lv, output.new_x, cur_col); // 2*N_LIMBS * 3
    write_fq2(lv, output.new_y, cur_col);
    write_modulus_aux_zero(lv, &output.aux_zeros[0], cur_col); // (5*N_LIMBS-1)*2
    write_modulus_aux_zero(lv, &output.aux_zeros[1], cur_col);
    write_modulus_aux(lv, &output.auxs[0], cur_col); // (6*N_LIMBS-1)*4
    write_modulus_aux(lv, &output.auxs[1], cur_col);
    write_modulus_aux(lv, &output.auxs[2], cur_col);
    write_modulus_aux(lv, &output.auxs[3], cur_col);
    lv[*cur_col] = output.quot_sign_zeros[0];
    *cur_col += 1;
    lv[*cur_col] = output.quot_sign_zeros[1];
    *cur_col += 1;
    lv[*cur_col] = output.quot_signs[0];
    *cur_col += 1;
    lv[*cur_col] = output.quot_signs[1];
    *cur_col += 1;
    lv[*cur_col] = output.quot_signs[2];
    *cur_col += 1;
    lv[*cur_col] = output.quot_signs[3];
    *cur_col += 1;
    assert!(*cur_col == orinigal_col + 40 * N_LIMBS);
}

pub fn read_g2_output<F: Copy + Debug, const NUM_COL: usize>(
    lv: &[F; NUM_COL],
    cur_col: &mut usize,
) -> G2Output<F> {
    let orinigal_col = *cur_col;
    let lambda = read_fq2(lv, cur_col);
    let new_x = read_fq2(lv, cur_col);
    let new_y = read_fq2(lv, cur_col);
    let aux_zeros_0 = read_modulus_aux_zero(lv, cur_col);
    let aux_zeros_1 = read_modulus_aux_zero(lv, cur_col);
    let auxs_0 = read_modulus_aux(lv, cur_col);
    let auxs_1 = read_modulus_aux(lv, cur_col);
    let auxs_2 = read_modulus_aux(lv, cur_col);
    let auxs_3 = read_modulus_aux(lv, cur_col);
    let quot_sign_zeros_0 = lv[*cur_col];
    *cur_col += 1;
    let quot_sign_zeros_1 = lv[*cur_col];
    *cur_col += 1;
    let quot_signs_0 = lv[*cur_col];
    *cur_col += 1;
    let quot_signs_1 = lv[*cur_col];
    *cur_col += 1;
    let quot_signs_2 = lv[*cur_col];
    *cur_col += 1;
    let quot_signs_3 = lv[*cur_col];
    *cur_col += 1;
    assert!(*cur_col == orinigal_col + 40 * N_LIMBS);

    G2Output {
        lambda,
        new_x,
        new_y,
        aux_zeros: [aux_zeros_0, aux_zeros_1],
        auxs: [auxs_0, auxs_1, auxs_2, auxs_3],
        quot_sign_zeros: [quot_sign_zeros_0, quot_sign_zeros_1],
        quot_signs: [quot_signs_0, quot_signs_1, quot_signs_2, quot_signs_3],
    }
}

pub fn generate_g2_double<F: RichField>(x: [[F; N_LIMBS]; 2], y: [[F; N_LIMBS]; 2]) -> G2Output<F> {
    let modulus = bn254_base_modulus_bigint();
    // restore
    let x_fq = columns_to_fq2(x);
    let y_fq = columns_to_fq2(y);

    let lambda_fq: Fq2 = ((Fq2::from(3) * x_fq * x_fq) / (Fq2::from(2) * y_fq)).into();

    let x_i64 = x.map(positive_column_to_i64);
    let y_i64 = y.map(positive_column_to_i64);

    let lambda_i64: [[_; N_LIMBS]; 2] = fq2_to_columns(lambda_fq);
    let lambda = lambda_i64.map(i64_to_column_positive);

    let lambda_y = pol_mul_fq2(lambda_i64, y_i64);
    let lambda_y_double = pol_mul_scalar_fq2(lambda_y, 2);

    let x_sq = pol_mul_fq2(x_i64, x_i64);
    let x_sq_triple = pol_mul_scalar_fq2(x_sq, 3);

    let zero_pol = pol_sub_fq2(lambda_y_double, x_sq_triple);

    let mut aux_zeros = vec![];
    let mut quot_sign_zeros = vec![];
    for i in 0..2 {
        let (quot_sign_zero, aux_zero) = generate_modular_zero::<F>(&modulus, zero_pol[i]);
        aux_zeros.push(aux_zero);
        quot_sign_zeros.push(quot_sign_zero);
    }

    let double_x = pol_mul_scalar_fq2(x_i64, 2);
    let double_x = to_wide_fq2(double_x);
    let lambda_sq = pol_mul_fq2(lambda_i64, lambda_i64);
    let new_x_input = pol_sub_fq2(lambda_sq, double_x);

    let mut auxs = vec![];
    let mut quot_signs = vec![];
    let mut new_x_coeffs = vec![];
    for i in 0..2 {
        let (new_x, quot_sign_x, aux_x) = generate_modular_op::<F>(&modulus, new_x_input[i]);
        auxs.push(aux_x);
        quot_signs.push(quot_sign_x);
        new_x_coeffs.push(new_x);
    }
    let new_x_i64: [[_; N_LIMBS]; 2] = new_x_coeffs
        .iter()
        .cloned()
        .map(positive_column_to_i64)
        .collect_vec()
        .try_into()
        .unwrap();

    let x_minus_new_x = pol_sub_fq2(x_i64, new_x_i64);
    let lambda_mul_x1_minus_new_x = pol_mul_fq2(lambda_i64, x_minus_new_x);

    let y_wide = to_wide_fq2(y_i64);
    let new_y_input = pol_sub_fq2(lambda_mul_x1_minus_new_x, y_wide);

    let mut new_y_coeffs = vec![];
    for i in 0..2 {
        let (new_y, quot_sign_y, aux_y) = generate_modular_op::<F>(&modulus, new_y_input[i]);
        auxs.push(aux_y);
        quot_signs.push(quot_sign_y);
        new_y_coeffs.push(new_y);
    }

    let aux_zeros: [ModulusAuxZero<F>; 2] = aux_zeros.try_into().unwrap();
    let quot_sign_zeros: [F; 2] = quot_sign_zeros.try_into().unwrap();
    let auxs: [ModulusAux<F>; 4] = auxs.try_into().unwrap();
    let quot_signs: [F; 4] = quot_signs.try_into().unwrap();

    let new_x: [[_; N_LIMBS]; 2] = new_x_coeffs.try_into().unwrap();
    let new_y: [[_; N_LIMBS]; 2] = new_y_coeffs.try_into().unwrap();

    G2Output {
        lambda,
        new_x,
        new_y,
        aux_zeros,
        auxs,
        quot_sign_zeros,
        quot_signs,
    }
}

pub fn eval_g2_double<P: PackedField>(
    yield_constr: &mut ConstraintConsumer<P>,
    filter: P,
    x: [[P; N_LIMBS]; 2],
    y: [[P; N_LIMBS]; 2],
    output: &G2Output<P>,
) {
    let modulus = bn254_base_modulus_packfield();

    let lambda_y = pol_mul_fq2(output.lambda, y);
    let lambda_y_double = pol_mul_scalar_fq2(lambda_y, P::Scalar::from_canonical_u64(2).into());

    let x_sq = pol_mul_fq2(x, x);
    let x_sq_triple = pol_mul_scalar_fq2(x_sq, P::Scalar::from_canonical_u64(3).into());
    let zero_pol = pol_sub_fq2(lambda_y_double, x_sq_triple);
    (0..2).for_each(|i| {
        eval_modular_zero(
            yield_constr,
            filter,
            modulus,
            zero_pol[i],
            output.quot_sign_zeros[i],
            &output.aux_zeros[i],
        )
    });

    let double_x = pol_mul_scalar_fq2(x, P::Scalar::from_canonical_u64(2).into());
    let double_x = to_wide_fq2(double_x);
    let lambda_sq = pol_mul_fq2(output.lambda, output.lambda);
    let new_x_input = pol_sub_fq2(lambda_sq, double_x);

    (0..2).for_each(|i| {
        eval_modular_op::<P>(
            yield_constr,
            filter,
            modulus,
            new_x_input[i],
            output.new_x[i],
            output.quot_signs[i],
            &output.auxs[i],
        )
    });

    let x_minus_new_x = pol_sub_fq2(x, output.new_x);
    let lambda_mul_x1_minus_new_x = pol_mul_fq2(output.lambda, x_minus_new_x);
    let y_wide = to_wide_fq2(y);
    let new_y_input = pol_sub_fq2(lambda_mul_x1_minus_new_x, y_wide);
    (0..2).for_each(|i| {
        eval_modular_op::<P>(
            yield_constr,
            filter,
            modulus,
            new_y_input[i],
            output.new_y[i],
            output.quot_signs[i + 2],
            &output.auxs[i + 2],
        )
    });
}

pub fn eval_g2_double_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    filter: ExtensionTarget<D>,
    x: [[ExtensionTarget<D>; N_LIMBS]; 2],
    y: [[ExtensionTarget<D>; N_LIMBS]; 2],
    output: &G2Output<ExtensionTarget<D>>,
) {
    let modulus = bn254_base_modulus_packfield();
    let modulus = modulus.map(|x| builder.constant_extension(x));

    let lambda_y = pol_mul_fq2_circuit(builder, output.lambda, y);
    let lambda_y_double =
        pol_mul_scalar_fq2_circuit(builder, lambda_y, F::Extension::from_canonical_u64(2));

    let x_sq = pol_mul_fq2_circuit(builder, x, x);
    let x_sq_triple =
        pol_mul_scalar_fq2_circuit(builder, x_sq, F::Extension::from_canonical_u64(3));
    let zero_pol = pol_sub_fq2_circuit(builder, lambda_y_double, x_sq_triple);
    (0..2).for_each(|i| {
        eval_modular_zero_circuit(
            builder,
            yield_constr,
            filter,
            modulus,
            zero_pol[i],
            output.quot_sign_zeros[i],
            &output.aux_zeros[i],
        )
    });

    let double_x = pol_mul_scalar_fq2_circuit(builder, x, F::Extension::from_canonical_u64(2));
    let double_x = to_wide_fq2_circuit(builder, double_x);
    let lambda_sq = pol_mul_fq2_circuit(builder, output.lambda, output.lambda);
    let new_x_input = pol_sub_fq2_circuit(builder, lambda_sq, double_x);

    (0..2).for_each(|i| {
        eval_modular_op_circuit(
            builder,
            yield_constr,
            filter,
            modulus,
            new_x_input[i],
            output.new_x[i],
            output.quot_signs[i],
            &output.auxs[i],
        )
    });

    let x_minus_new_x = pol_sub_fq2_circuit(builder, x, output.new_x);
    let lambda_mul_x1_minus_new_x = pol_mul_fq2_circuit(builder, output.lambda, x_minus_new_x);
    let y_wide = to_wide_fq2_circuit(builder, y);
    let new_y_input = pol_sub_fq2_circuit(builder, lambda_mul_x1_minus_new_x, y_wide);
    (0..2).for_each(|i| {
        eval_modular_op_circuit(
            builder,
            yield_constr,
            filter,
            modulus,
            new_y_input[i],
            output.new_y[i],
            output.quot_signs[i + 2],
            &output.auxs[i + 2],
        )
    });
}

pub fn generate_g2_add<F: RichField>(
    a_x: [[F; N_LIMBS]; 2],
    a_y: [[F; N_LIMBS]; 2],
    b_x: [[F; N_LIMBS]; 2],
    b_y: [[F; N_LIMBS]; 2],
) -> G2Output<F> {
    let modulus = bn254_base_modulus_bigint();
    // restore
    let a_x_fq2 = columns_to_fq2(a_x);
    let a_y_fq2 = columns_to_fq2(a_y);
    let b_x_fq2 = columns_to_fq2(b_x);
    let b_y_fq2 = columns_to_fq2(b_y);
    let lambda_fq2: Fq2 = ((b_y_fq2 - a_y_fq2) / (b_x_fq2 - a_x_fq2)).into();

    let a_x_i64 = a_x.map(positive_column_to_i64);
    let a_y_i64 = a_y.map(positive_column_to_i64);
    let b_x_i64 = b_x.map(positive_column_to_i64);
    let b_y_i64 = b_y.map(positive_column_to_i64);
    let lambda_i64 = fq2_to_columns(lambda_fq2);
    let lambda: [[F; N_LIMBS]; 2] = lambda_i64.map(i64_to_column_positive);

    let delta_x = pol_sub_fq2(b_x_i64, a_x_i64);
    let delta_y = pol_sub_fq2(b_y_i64, a_y_i64);
    let delta_y = to_wide_fq2(delta_y);
    let lambda_delta_x = pol_mul_fq2(lambda_i64, delta_x);
    let zero_pol = pol_sub_fq2(lambda_delta_x, delta_y);

    let mut aux_zeros = vec![];
    let mut quot_sign_zeros = vec![];

    for i in 0..2 {
        let (quot_sign_zero, aux_zero) = generate_modular_zero::<F>(&modulus, zero_pol[i]);
        aux_zeros.push(aux_zero);
        quot_sign_zeros.push(quot_sign_zero);
    }

    let x1_add_x2 = pol_add_fq2(a_x_i64, b_x_i64);
    let x1_add_x2 = to_wide_fq2(x1_add_x2);
    let lambda_sq = pol_mul_fq2(lambda_i64, lambda_i64);
    let new_x_input = pol_sub_fq2(lambda_sq, x1_add_x2);

    let mut auxs = vec![];
    let mut quot_signs = vec![];
    let mut new_x_coeffs = vec![];

    for i in 0..2 {
        let (new_x, quot_sign_x, aux_x) = generate_modular_op::<F>(&modulus, new_x_input[i]);
        auxs.push(aux_x);
        quot_signs.push(quot_sign_x);
        new_x_coeffs.push(new_x);
    }
    let new_x: [[F; N_LIMBS]; 2] = new_x_coeffs.try_into().unwrap();

    let new_x_i64 = new_x.map(positive_column_to_i64);

    let x1_minus_new_x = pol_sub_fq2(a_x_i64, new_x_i64);
    let lambda_mul_x1_minus_new_x = pol_mul_fq2(lambda_i64, x1_minus_new_x);

    let y_wide = to_wide_fq2(a_y_i64);
    let new_y_input = pol_sub_fq2(lambda_mul_x1_minus_new_x, y_wide);

    let mut new_y_coeffs = vec![];
    for i in 0..2 {
        let (new_y, quot_sign_y, aux_y) = generate_modular_op::<F>(&modulus, new_y_input[i]);
        auxs.push(aux_y);
        quot_signs.push(quot_sign_y);
        new_y_coeffs.push(new_y);
    }
    let new_y: [[F; N_LIMBS]; 2] = new_y_coeffs.try_into().unwrap();

    let aux_zeros: [ModulusAuxZero<F>; 2] = aux_zeros.try_into().unwrap();
    let quot_sign_zeros: [F; 2] = quot_sign_zeros.try_into().unwrap();
    let auxs: [ModulusAux<F>; 4] = auxs.try_into().unwrap();
    let quot_signs: [F; 4] = quot_signs.try_into().unwrap();

    G2Output {
        lambda,
        new_x,
        new_y,
        aux_zeros,
        auxs,
        quot_sign_zeros,
        quot_signs,
    }
}

pub fn eval_g2_add<P: PackedField>(
    yield_constr: &mut ConstraintConsumer<P>,
    filter: P,
    a_x: [[P; N_LIMBS]; 2],
    a_y: [[P; N_LIMBS]; 2],
    b_x: [[P; N_LIMBS]; 2],
    b_y: [[P; N_LIMBS]; 2],
    output: &G2Output<P>,
) {
    let modulus = bn254_base_modulus_packfield();
    let delta_x = pol_sub_fq2(b_x, a_x);
    let delta_y = pol_sub_fq2(b_y, a_y);
    let delta_y = to_wide_fq2(delta_y);
    let lambda_delta_x = pol_mul_fq2(output.lambda, delta_x);
    let zero_pol = pol_sub_fq2(lambda_delta_x, delta_y);
    (0..2).for_each(|i| {
        eval_modular_zero(
            yield_constr,
            filter,
            modulus,
            zero_pol[i],
            output.quot_sign_zeros[i],
            &output.aux_zeros[i],
        )
    });
    let x1_add_x2 = pol_add_fq2(a_x, b_x);
    let x1_add_x2 = to_wide_fq2(x1_add_x2);
    let lambda_sq = pol_mul_fq2(output.lambda, output.lambda);
    let new_x_input = pol_sub_fq2(lambda_sq, x1_add_x2);
    (0..2).for_each(|i| {
        eval_modular_op::<P>(
            yield_constr,
            filter,
            modulus,
            new_x_input[i],
            output.new_x[i],
            output.quot_signs[i],
            &output.auxs[i],
        )
    });

    let x1_minus_new_x = pol_sub_fq2(a_x, output.new_x);
    let lambda_mul_x1_minus_new_x = pol_mul_fq2(output.lambda, x1_minus_new_x);
    let y_wide = to_wide_fq2(a_y);
    let new_y_input = pol_sub_fq2(lambda_mul_x1_minus_new_x, y_wide);
    (0..2).for_each(|i| {
        eval_modular_op::<P>(
            yield_constr,
            filter,
            modulus,
            new_y_input[i],
            output.new_y[i],
            output.quot_signs[i + 2],
            &output.auxs[i + 2],
        )
    });
}

pub fn eval_g2_add_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    filter: ExtensionTarget<D>,
    a_x: [[ExtensionTarget<D>; N_LIMBS]; 2],
    a_y: [[ExtensionTarget<D>; N_LIMBS]; 2],
    b_x: [[ExtensionTarget<D>; N_LIMBS]; 2],
    b_y: [[ExtensionTarget<D>; N_LIMBS]; 2],
    output: &G2Output<ExtensionTarget<D>>,
) {
    let modulus = bn254_base_modulus_packfield();
    let modulus = modulus.map(|x| builder.constant_extension(x));

    let delta_x = pol_sub_fq2_circuit(builder, b_x, a_x);
    let delta_y = pol_sub_fq2_circuit(builder, b_y, a_y);
    let delta_y = to_wide_fq2_circuit(builder, delta_y);
    let lambda_delta_x = pol_mul_fq2_circuit(builder, output.lambda, delta_x);
    let zero_pol = pol_sub_fq2_circuit(builder, lambda_delta_x, delta_y);
    (0..2).for_each(|i| {
        eval_modular_zero_circuit(
            builder,
            yield_constr,
            filter,
            modulus,
            zero_pol[i],
            output.quot_sign_zeros[i],
            &output.aux_zeros[i],
        )
    });
    let x1_add_x2 = pol_add_fq2_circuit(builder, a_x, b_x);
    let x1_add_x2 = to_wide_fq2_circuit(builder, x1_add_x2);
    let lambda_sq = pol_mul_fq2_circuit(builder, output.lambda, output.lambda);
    let new_x_input = pol_sub_fq2_circuit(builder, lambda_sq, x1_add_x2);
    (0..2).for_each(|i| {
        eval_modular_op_circuit(
            builder,
            yield_constr,
            filter,
            modulus,
            new_x_input[i],
            output.new_x[i],
            output.quot_signs[i],
            &output.auxs[i],
        )
    });

    let x1_minus_new_x = pol_sub_fq2_circuit(builder, a_x, output.new_x);
    let lambda_mul_x1_minus_new_x = pol_mul_fq2_circuit(builder, output.lambda, x1_minus_new_x);
    let y_wide = to_wide_fq2_circuit(builder, a_y);
    let new_y_input = pol_sub_fq2_circuit(builder, lambda_mul_x1_minus_new_x, y_wide);
    (0..2).for_each(|i| {
        eval_modular_op_circuit(
            builder,
            yield_constr,
            filter,
            modulus,
            new_y_input[i],
            output.new_y[i],
            output.quot_signs[i + 2],
            &output.auxs[i + 2],
        )
    });
}

const ROWS: usize = 1 << 9;
const MAIN_COLS: usize = 48 * N_LIMBS + 2 + BITS_LEN;
const START_RANGE_CHECK: usize = 8 * N_LIMBS;
const NUM_RANGE_CHECK: usize = 40 * N_LIMBS - 6;
const END_RANGE_CHECK: usize = START_RANGE_CHECK + NUM_RANGE_CHECK;
const IS_SQ_COL: usize = 48 * N_LIMBS;
// const IS_NOOP_COL: usize = 48 * N_LIMBS + 1;
const IS_MUL_COL: usize = 48 * N_LIMBS + 2;

#[derive(Clone, Copy)]
pub struct G2Stark<F: RichField + Extendable<D>, const D: usize> {
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> G2Stark<F, D> {
    pub fn new() -> Self {
        Self {
            _phantom: PhantomData,
        }
    }

    pub fn generate_trace(&self) -> Vec<PolynomialValues<F>> {
        let mut rng = rand::thread_rng();

        let mut rows = vec![];

        for _ in 0..ROWS {
            let is_add = F::ZERO;
            let is_double = F::ONE;

            let a_g2 = G2Affine::rand(&mut rng);
            let b_g2 = G2Affine::rand(&mut rng);

            let a_x = fq2_to_columns(a_g2.x).map(|x| x.map(F::from_canonical_i64));
            let a_y = fq2_to_columns(a_g2.y).map(|x| x.map(F::from_canonical_i64));
            let b_x = fq2_to_columns(b_g2.x).map(|x| x.map(F::from_canonical_i64));
            let b_y = fq2_to_columns(b_g2.y).map(|x| x.map(F::from_canonical_i64));

            let output = if is_add == F::ONE {
                let output = generate_g2_add(a_x, a_y, b_x, b_y);
                let expected: G2Affine = (a_g2 + b_g2).into();
                let new_x = columns_to_fq2(output.new_x);
                let new_y = columns_to_fq2(output.new_y);
                let new_g2 = G2Affine::new(new_x, new_y);
                assert!(new_g2 == expected);
                output
            } else {
                let output = generate_g2_double(a_x, a_y);
                let expected: G2Affine = (a_g2 + a_g2).into();
                let new_x = columns_to_fq2(output.new_x);
                let new_y = columns_to_fq2(output.new_y);
                let new_g2 = G2Affine::new(new_x, new_y);
                assert!(new_g2 == expected);
                output
            };

            let mut lv = [F::ZERO; MAIN_COLS];
            let mut cur_col = 0;
            write_fq2(&mut lv, a_x, &mut cur_col); // N_LIMBS
            write_fq2(&mut lv, a_y, &mut cur_col); // N_LIMBS
            write_fq2(&mut lv, b_x, &mut cur_col); // N_LIMBS
            write_fq2(&mut lv, b_y, &mut cur_col); // N_LIMBS
            write_g2_output(&mut lv, &output, &mut cur_col); // 40*N_LIMBS
            lv[IS_MUL_COL] = is_add;
            lv[IS_SQ_COL] = is_double;

            rows.push(lv);
        }

        let mut trace_cols = transpose(&rows.iter().map(|v| v.to_vec()).collect_vec());

        generate_split_u16_range_check(START_RANGE_CHECK..END_RANGE_CHECK, &mut trace_cols);

        trace_cols
            .into_iter()
            .map(|column| PolynomialValues::new(column))
            .collect()
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D> for G2Stark<F, D> {
    const COLUMNS: usize = MAIN_COLS + 1 + 6 * NUM_RANGE_CHECK;
    const PUBLIC_INPUTS: usize = 0;

    fn eval_packed_generic<FE, P, const D2: usize>(
        &self,
        vars: StarkEvaluationVars<FE, P, { Self::COLUMNS }, { Self::PUBLIC_INPUTS }>,
        yield_constr: &mut ConstraintConsumer<P>,
    ) where
        FE: FieldExtension<D2, BaseField = F>,
        P: PackedField<Scalar = FE>,
    {
        eval_split_u16_range_check(
            vars,
            yield_constr,
            MAIN_COLS,
            START_RANGE_CHECK..END_RANGE_CHECK,
        );

        let lv = vars.local_values;

        let mut cur_col = 0;
        let a_x = read_fq2(&lv, &mut cur_col);
        let a_y = read_fq2(&lv, &mut cur_col);
        let b_x = read_fq2(&lv, &mut cur_col);
        let b_y = read_fq2(&lv, &mut cur_col);
        let output = read_g2_output(&lv, &mut cur_col);
        let is_add = lv[IS_MUL_COL];
        let is_double = lv[IS_SQ_COL];

        eval_g2_add(yield_constr, is_add, a_x, a_y, b_x, b_y, &output);
        eval_g2_double(yield_constr, is_double, a_x, a_y, &output);
    }

    fn eval_ext_circuit(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        vars: StarkEvaluationTargets<D, { Self::COLUMNS }, { Self::PUBLIC_INPUTS }>,
        yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    ) {
        eval_split_u16_range_check_circuit(
            builder,
            vars,
            yield_constr,
            MAIN_COLS,
            START_RANGE_CHECK..END_RANGE_CHECK,
        );
        let lv = vars.local_values;

        let mut cur_col = 0;
        let a_x = read_fq2(&lv, &mut cur_col);
        let a_y = read_fq2(&lv, &mut cur_col);
        let b_x = read_fq2(&lv, &mut cur_col);
        let b_y = read_fq2(&lv, &mut cur_col);
        let output = read_g2_output(&lv, &mut cur_col);
        let is_add = lv[IS_MUL_COL];
        let is_double = lv[IS_SQ_COL];

        eval_g2_add_circuit(builder, yield_constr, is_add, a_x, a_y, b_x, b_y, &output);
        eval_g2_double_circuit(builder, yield_constr, is_double, a_x, a_y, &output);
    }

    fn constraint_degree(&self) -> usize {
        3
    }

    fn permutation_pairs(&self) -> Vec<PermutationPair> {
        split_u16_range_check_pairs(MAIN_COLS, START_RANGE_CHECK..END_RANGE_CHECK)
    }
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use plonky2::{
        iop::witness::PartialWitness,
        plonk::{
            circuit_builder::CircuitBuilder,
            circuit_data::CircuitConfig,
            config::{GenericConfig, PoseidonGoldilocksConfig},
        },
        util::timing::TimingTree,
    };

    use crate::{
        config::StarkConfig,
        develop::g2::G2Stark,
        prover::prove,
        recursive_verifier::{
            add_virtual_stark_proof_with_pis, set_stark_proof_with_pis_target,
            verify_stark_proof_circuit,
        },
        verifier::verify_stark_proof,
    };

    #[test]
    fn test_g2_mul() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type S = G2Stark<F, D>;
        let inner_config = StarkConfig::standard_fast_config();
        let stark = S::new();
        let trace = stark.generate_trace();

        println!("start stark proof generation");
        let now = Instant::now();
        let pi = vec![];
        let inner_proof = prove::<F, C, S, D>(
            stark,
            &inner_config,
            trace,
            pi.try_into().unwrap(),
            &mut TimingTree::default(),
        )
        .unwrap();
        verify_stark_proof(stark, inner_proof.clone(), &inner_config).unwrap();
        println!("end stark proof generation: {:?}", now.elapsed());

        let circuit_config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(circuit_config);
        let mut pw = PartialWitness::new();
        let degree_bits = inner_proof.proof.recover_degree_bits(&inner_config);
        let pt = add_virtual_stark_proof_with_pis(&mut builder, stark, &inner_config, degree_bits);
        set_stark_proof_with_pis_target(&mut pw, &pt, &inner_proof);
        verify_stark_proof_circuit::<F, C, S, D>(&mut builder, stark, &pt, &inner_config);
        let data = builder.build::<C>();

        println!("start plonky2 proof generation");
        let now = Instant::now();
        let _proof = data.prove(pw).unwrap();
        println!("end plonky2 proof generation: {:?}", now.elapsed());
    }
}

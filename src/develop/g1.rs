use core::marker::PhantomData;

use ark_bn254::{g1, Fq, G1Affine};
use ark_std::UniformRand;
use itertools::Itertools;
use plonky2::field::types::Field as plonky2_field;
use plonky2::iop::ext_target::ExtensionTarget;
use plonky2::{
    field::{
        extension::{Extendable, FieldExtension},
        packed::PackedField,
        polynomial::PolynomialValues,
    },
    hash::hash_types::RichField,
    plonk::circuit_builder::CircuitBuilder,
    util::transpose,
};

use crate::develop::modular_zero::{generate_modular_zero, write_modulus_aux_zero};
use crate::develop::range_check::{eval_split_u16_range_check, eval_split_u16_range_check_circuit};
use crate::develop::utils::{
    columns_to_fq, fq_to_columns, i64_to_column_positive, pol_add, pol_mul_wide, pol_sub,
    pol_sub_normal, positive_column_to_i64,
};
use crate::{
    constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer},
    develop::constants::N_LIMBS,
    develop::modular::write_modulus_aux,
    permutation::PermutationPair,
    stark::Stark,
    vars::{StarkEvaluationTargets, StarkEvaluationVars},
};

use crate::develop::modular::{
    bn254_base_modulus_bigint, eval_modular_op_circuit, generate_modular_op, read_modulus_aux,
    write_u256,
};

use super::modular::{bn254_base_modulus_packfield, eval_modular_op, read_u256, ModulusAux};
use super::modular_zero::{
    eval_modular_zero, eval_modular_zero_circuit, read_modulus_aux_zero, ModulusAuxZero,
};
use super::range_check::{generate_split_u16_range_check, split_u16_range_check_pairs};
use super::utils::{
    pol_add_ext_circuit, pol_mul_scalar, pol_mul_scalar_ext_circuit, pol_mul_wide_ext_circuit,
    pol_sub_ext_circuit, pol_sub_normal_ext_circuit,
};

pub struct G1Output<F> {
    pub lambda: [F; N_LIMBS],
    pub new_x: [F; N_LIMBS],
    pub new_y: [F; N_LIMBS],
    pub aux_zero: ModulusAuxZero<F>,
    pub aux_x: ModulusAux<F>,
    pub aux_y: ModulusAux<F>,
    pub quot_sign_zero: F,
    pub quot_sign_x: F,
    pub quot_sign_y: F,
}

impl<F: RichField + Default> Default for G1Output<F> {
    fn default() -> Self {
        Self {
            lambda: [F::ZERO; N_LIMBS],
            new_x: [F::ZERO; N_LIMBS],
            new_y: [F::ZERO; N_LIMBS],
            aux_zero: ModulusAuxZero::default(),
            aux_x: ModulusAux::default(),
            aux_y: ModulusAux::default(),
            quot_sign_zero: F::ONE,
            quot_sign_x: F::ONE,
            quot_sign_y: F::ONE,
        }
    }
}

pub fn generate_g1_add<F: RichField>(
    a_x: [F; N_LIMBS],
    a_y: [F; N_LIMBS],
    b_x: [F; N_LIMBS],
    b_y: [F; N_LIMBS],
) -> G1Output<F> {
    let modulus = bn254_base_modulus_bigint();
    // restore
    let a_x_fq = columns_to_fq(&a_x);
    let a_y_fq = columns_to_fq(&a_y);
    let b_x_fq = columns_to_fq(&b_x);
    let b_y_fq = columns_to_fq(&b_y);
    let lambda_fq: Fq = ((b_y_fq - a_y_fq) / (b_x_fq - a_x_fq)).into();

    let a_x_i64 = positive_column_to_i64(a_x);
    let a_y_i64 = positive_column_to_i64(a_y);
    let b_x_i64 = positive_column_to_i64(b_x);
    let b_y_i64 = positive_column_to_i64(b_y);
    let lambda_i64: [_; N_LIMBS] = fq_to_columns(lambda_fq);
    let lambda = i64_to_column_positive(lambda_i64);

    let delta_x = pol_sub_normal(b_x_i64, a_x_i64);
    let delta_y = pol_sub(b_y_i64, a_y_i64);
    let lambda_delta_x = pol_mul_wide(lambda_i64, delta_x);
    let zero_pol = pol_sub_normal(lambda_delta_x, delta_y);
    let (quot_sign_zero, aux_zero) = generate_modular_zero::<F>(&modulus, zero_pol);

    let x1_add_x2 = pol_add(a_x_i64, b_x_i64);
    let lambda_sq = pol_mul_wide(lambda_i64, lambda_i64);
    let new_x_input = pol_sub_normal(lambda_sq, x1_add_x2);

    let (new_x, quot_sign_x, aux_x) = generate_modular_op::<F>(&modulus, new_x_input);
    let new_x_i64 = positive_column_to_i64(new_x);

    let x1_minus_new_x = pol_sub_normal(a_x_i64, new_x_i64);
    let lambda_mul_x1_minus_new_x = pol_mul_wide(lambda_i64, x1_minus_new_x);

    let mut y1_wide = [0i64; 2 * N_LIMBS - 1];
    y1_wide[0..N_LIMBS].copy_from_slice(&a_y_i64);
    let new_y_input = pol_sub_normal(lambda_mul_x1_minus_new_x, y1_wide);
    let (new_y, quot_sign_y, aux_y) = generate_modular_op::<F>(&modulus, new_y_input);

    G1Output {
        lambda,
        new_x,
        new_y,
        aux_zero,
        aux_x,
        aux_y,
        quot_sign_zero,
        quot_sign_x,
        quot_sign_y,
    }
}

pub fn eval_g1_add<P: PackedField>(
    yield_constr: &mut ConstraintConsumer<P>,
    filter: P,
    a_x: [P; N_LIMBS],
    a_y: [P; N_LIMBS],
    b_x: [P; N_LIMBS],
    b_y: [P; N_LIMBS],
    add_o: &G1Output<P>,
) {
    let modulus = bn254_base_modulus_packfield();
    let delta_x = pol_sub_normal(b_x, a_x);
    let delta_y = pol_sub(b_y, a_y);
    let lambda_delta_x = pol_mul_wide(add_o.lambda, delta_x);
    let zero_pol = pol_sub_normal(lambda_delta_x, delta_y);
    eval_modular_zero(
        yield_constr,
        filter,
        modulus,
        zero_pol,
        add_o.quot_sign_zero,
        &add_o.aux_zero,
    );

    let x1_add_x2 = pol_add(a_x, b_x);
    let lambda_sq = pol_mul_wide(add_o.lambda, add_o.lambda);
    let new_x_input = pol_sub_normal(lambda_sq, x1_add_x2);
    eval_modular_op(
        yield_constr,
        filter,
        modulus,
        new_x_input,
        add_o.new_x,
        add_o.quot_sign_x,
        &add_o.aux_x,
    );

    let x1_minus_new_x = pol_sub_normal(a_x, add_o.new_x);
    let lambda_mul_x1_minus_new_x = pol_mul_wide(add_o.lambda, x1_minus_new_x);

    let mut y1_wide = [P::ZEROS; 2 * N_LIMBS - 1];
    y1_wide[0..N_LIMBS].copy_from_slice(&a_y);
    let new_y_input = pol_sub_normal(lambda_mul_x1_minus_new_x, y1_wide);
    eval_modular_op(
        yield_constr,
        filter,
        modulus,
        new_y_input,
        add_o.new_y,
        add_o.quot_sign_y,
        &add_o.aux_y,
    );
}

pub fn eval_g1_add_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    filter: ExtensionTarget<D>,
    a_x: [ExtensionTarget<D>; N_LIMBS],
    a_y: [ExtensionTarget<D>; N_LIMBS],
    b_x: [ExtensionTarget<D>; N_LIMBS],
    b_y: [ExtensionTarget<D>; N_LIMBS],
    add_o: &G1Output<ExtensionTarget<D>>,
) {
    let modulus = bn254_base_modulus_packfield();
    let modulus = modulus.map(|x| builder.constant_extension(x));

    let delta_x = pol_sub_normal_ext_circuit(builder, b_x, a_x);
    let delta_y = pol_sub_ext_circuit(builder, b_y, a_y);
    let lambda_delta_x = pol_mul_wide_ext_circuit(builder, add_o.lambda, delta_x);
    let zero_pol = pol_sub_normal_ext_circuit(builder, lambda_delta_x, delta_y);
    eval_modular_zero_circuit(
        builder,
        yield_constr,
        filter,
        modulus,
        zero_pol,
        add_o.quot_sign_zero,
        &add_o.aux_zero,
    );

    let x1_add_x2 = pol_add_ext_circuit(builder, a_x, b_x);
    let lambda_sq = pol_mul_wide_ext_circuit(builder, add_o.lambda, add_o.lambda);
    let new_x_input = pol_sub_normal_ext_circuit(builder, lambda_sq, x1_add_x2);
    eval_modular_op_circuit(
        builder,
        yield_constr,
        filter,
        modulus,
        new_x_input,
        add_o.new_x,
        add_o.quot_sign_x,
        &add_o.aux_x,
    );

    let x1_minus_new_x = pol_sub_normal_ext_circuit(builder, a_x, add_o.new_x);
    let lambda_mul_x1_minus_new_x = pol_mul_wide_ext_circuit(builder, add_o.lambda, x1_minus_new_x);

    let mut y1_wide = [builder.zero_extension(); 2 * N_LIMBS - 1];
    y1_wide[0..N_LIMBS].copy_from_slice(&a_y);
    let new_y_input = pol_sub_normal_ext_circuit(builder, lambda_mul_x1_minus_new_x, y1_wide);
    eval_modular_op_circuit(
        builder,
        yield_constr,
        filter,
        modulus,
        new_y_input,
        add_o.new_y,
        add_o.quot_sign_y,
        &add_o.aux_y,
    );
}

pub fn eval_g1_double<P: PackedField>(
    yield_constr: &mut ConstraintConsumer<P>,
    filter: P,
    x: [P; N_LIMBS],
    y: [P; N_LIMBS],
    double_o: &G1Output<P>,
) {
    let modulus = bn254_base_modulus_packfield();
    let lambda_y = pol_mul_wide(double_o.lambda, y);
    let lambda_y_double = pol_mul_scalar(lambda_y, P::Scalar::from_canonical_u64(2).into());
    let x_sq = pol_mul_wide(x, x);
    let x_sq_triple = pol_mul_scalar(x_sq, P::Scalar::from_canonical_u64(3).into());

    let zero_pol = pol_sub_normal(lambda_y_double, x_sq_triple);
    eval_modular_zero(
        yield_constr,
        filter,
        modulus,
        zero_pol,
        double_o.quot_sign_zero,
        &double_o.aux_zero,
    );

    let x1_add_x2 = pol_add(x, x);
    let lambda_sq = pol_mul_wide(double_o.lambda, double_o.lambda);
    let new_x_input = pol_sub_normal(lambda_sq, x1_add_x2);
    eval_modular_op(
        yield_constr,
        filter,
        modulus,
        new_x_input,
        double_o.new_x,
        double_o.quot_sign_x,
        &double_o.aux_x,
    );

    let x1_minus_new_x = pol_sub_normal(x, double_o.new_x);
    let lambda_mul_x1_minus_new_x = pol_mul_wide(double_o.lambda, x1_minus_new_x);

    let mut y1_wide = [P::ZEROS; 2 * N_LIMBS - 1];
    y1_wide[0..N_LIMBS].copy_from_slice(&y);
    let new_y_input = pol_sub_normal(lambda_mul_x1_minus_new_x, y1_wide);
    eval_modular_op(
        yield_constr,
        filter,
        modulus,
        new_y_input,
        double_o.new_y,
        double_o.quot_sign_y,
        &double_o.aux_y,
    );
}

pub fn eval_g1_double_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    filter: ExtensionTarget<D>,
    x: [ExtensionTarget<D>; N_LIMBS],
    y: [ExtensionTarget<D>; N_LIMBS],
    double_o: &G1Output<ExtensionTarget<D>>,
) {
    let modulus = bn254_base_modulus_packfield();
    let modulus = modulus.map(|x| builder.constant_extension(x));

    let lambda_y = pol_mul_wide_ext_circuit(builder, double_o.lambda, y);
    let lambda_y_double = pol_mul_scalar_ext_circuit(
        builder,
        lambda_y,
        F::Extension::from_canonical_u64(2).into(),
    );
    let x_sq = pol_mul_wide_ext_circuit(builder, x, x);
    let x_sq_triple =
        pol_mul_scalar_ext_circuit(builder, x_sq, F::Extension::from_canonical_u64(3).into());

    let zero_pol = pol_sub_normal_ext_circuit(builder, lambda_y_double, x_sq_triple);
    eval_modular_zero_circuit(
        builder,
        yield_constr,
        filter,
        modulus,
        zero_pol,
        double_o.quot_sign_zero,
        &double_o.aux_zero,
    );

    let x1_add_x2 = pol_add_ext_circuit(builder, x, x);
    let lambda_sq = pol_mul_wide_ext_circuit(builder, double_o.lambda, double_o.lambda);
    let new_x_input = pol_sub_normal_ext_circuit(builder, lambda_sq, x1_add_x2);
    eval_modular_op_circuit(
        builder,
        yield_constr,
        filter,
        modulus,
        new_x_input,
        double_o.new_x,
        double_o.quot_sign_x,
        &double_o.aux_x,
    );

    let x1_minus_new_x = pol_sub_normal_ext_circuit(builder, x, double_o.new_x);
    let lambda_mul_x1_minus_new_x =
        pol_mul_wide_ext_circuit(builder, double_o.lambda, x1_minus_new_x);

    let mut y1_wide = [builder.zero_extension(); 2 * N_LIMBS - 1];
    y1_wide[0..N_LIMBS].copy_from_slice(&y);
    let new_y_input = pol_sub_normal_ext_circuit(builder, lambda_mul_x1_minus_new_x, y1_wide);
    eval_modular_op_circuit(
        builder,
        yield_constr,
        filter,
        modulus,
        new_y_input,
        double_o.new_y,
        double_o.quot_sign_y,
        &double_o.aux_y,
    );
}

pub fn generate_g1_double<F: RichField>(x: [F; N_LIMBS], y: [F; N_LIMBS]) -> G1Output<F> {
    let modulus = bn254_base_modulus_bigint();
    // restore
    let x_fq = columns_to_fq(&x);
    let y_fq = columns_to_fq(&y);

    let lambda_fq: Fq = ((Fq::from(3) * x_fq * x_fq) / (Fq::from(2) * y_fq)).into();

    let x_i64 = positive_column_to_i64(x);
    let y_i64 = positive_column_to_i64(y);

    let lambda_i64: [_; N_LIMBS] = fq_to_columns(lambda_fq);
    let lambda = i64_to_column_positive(lambda_i64);

    let lambda_y = pol_mul_wide(lambda_i64, y_i64);
    let lambda_y_double = pol_mul_scalar(lambda_y, 2);

    let x_sq = pol_mul_wide(x_i64, x_i64);
    let x_sq_triple = pol_mul_scalar(x_sq, 3);

    let zero_pol = pol_sub_normal(lambda_y_double, x_sq_triple);
    let (quot_sign_zero, aux_zero) = generate_modular_zero::<F>(&modulus, zero_pol);

    let mut x_wide = [0i64; 2 * N_LIMBS - 1];
    x_wide[0..N_LIMBS].copy_from_slice(&x_i64);

    let double_x = pol_mul_scalar(x_wide, 2);
    let lambda_sq = pol_mul_wide(lambda_i64, lambda_i64);
    let new_x_input = pol_sub_normal(lambda_sq, double_x);
    let (new_x, quot_sign_x, aux_x) = generate_modular_op::<F>(&modulus, new_x_input);
    let new_x_i64 = positive_column_to_i64(new_x);

    let x_minus_new_x = pol_sub_normal(x_i64, new_x_i64);
    let lambda_mul_x1_minus_new_x = pol_mul_wide(lambda_i64, x_minus_new_x);

    let mut y_wide = [0i64; 2 * N_LIMBS - 1];
    y_wide[0..N_LIMBS].copy_from_slice(&y_i64);
    let new_y_input = pol_sub_normal(lambda_mul_x1_minus_new_x, y_wide);
    let (new_y, quot_sign_y, aux_y) = generate_modular_op::<F>(&modulus, new_y_input);

    G1Output {
        lambda,
        new_x,
        new_y,
        aux_zero,
        aux_x,
        aux_y,
        quot_sign_zero,
        quot_sign_x,
        quot_sign_y,
    }
}

const MAIN_COLS: usize = 24 * N_LIMBS + 2;
const ROWS: usize = 1 << 9;

const START_RANGE_CHECK: usize = 4 * N_LIMBS;
const NUM_RANGE_CHECKS: usize = 20 * N_LIMBS - 4;
const END_RANGE_CHECK: usize = START_RANGE_CHECK + NUM_RANGE_CHECKS;

#[derive(Clone, Copy)]
pub struct G1Stark<F: RichField + Extendable<D>, const D: usize> {
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> G1Stark<F, D> {
    pub fn new() -> Self {
        Self {
            _phantom: PhantomData,
        }
    }

    pub fn generate_trace(&self) -> Vec<PolynomialValues<F>> {
        let mut rng = rand::thread_rng();

        let mut rows = vec![];

        for _ in 0..ROWS {
            let is_add = F::ONE;
            let is_double = F::ZERO;

            let a_g1 = g1::G1Affine::rand(&mut rng);
            let b_g1 = g1::G1Affine::rand(&mut rng);

            let a_x = fq_to_columns(a_g1.x).map(|x| F::from_canonical_i64(x));
            let a_y = fq_to_columns(a_g1.y).map(|x| F::from_canonical_i64(x));
            let b_x = fq_to_columns(b_g1.x).map(|x| F::from_canonical_i64(x));
            let b_y = fq_to_columns(b_g1.y).map(|x| F::from_canonical_i64(x));

            let output = if is_add == F::ONE {
                assert!(is_double == F::ZERO);
                let add_o = generate_g1_add(a_x, a_y, b_x, b_y);
                let new_x_fq = columns_to_fq(&add_o.new_x);
                let new_y_fq = columns_to_fq(&add_o.new_y);
                let output_expected: G1Affine = (a_g1 + b_g1).into();
                assert!(output_expected.x == new_x_fq && output_expected.y == new_y_fq);
                add_o
            } else {
                assert!(is_double == F::ONE && is_add == F::ZERO);
                let double_o = generate_g1_double(a_x, a_y);
                let new_x_fq = columns_to_fq(&double_o.new_x);
                let new_y_fq = columns_to_fq(&double_o.new_y);
                let output_expected: G1Affine = (a_g1 + a_g1).into();
                assert!(output_expected.x == new_x_fq && output_expected.y == new_y_fq);
                double_o
            };

            let mut lv = [F::ZERO; MAIN_COLS];
            let mut cur_col = 0;
            write_u256(&mut lv, &a_x, &mut cur_col); // N_LIMBS
            write_u256(&mut lv, &a_y, &mut cur_col); // N_LIMBS
            write_u256(&mut lv, &b_x, &mut cur_col); // N_LIMBS
            write_u256(&mut lv, &b_y, &mut cur_col); // N_LIMBS
            write_u256(&mut lv, &output.lambda, &mut cur_col); // N_LIMBS
            write_u256(&mut lv, &output.new_x, &mut cur_col); // N_LIMBS
            write_u256(&mut lv, &output.new_y, &mut cur_col); // N_LIMBS

            // 5*N_LIMBS - 1
            write_modulus_aux_zero(&mut lv, &output.aux_zero, &mut cur_col);
            // 12*N_LIMBS - 2
            write_modulus_aux(&mut lv, &output.aux_x, &mut cur_col);
            write_modulus_aux(&mut lv, &output.aux_y, &mut cur_col);
            // 3
            lv[cur_col] = output.quot_sign_zero;
            cur_col += 1;
            lv[cur_col] = output.quot_sign_x;
            cur_col += 1;
            lv[cur_col] = output.quot_sign_y;
            cur_col += 1;
            // filter, 1
            lv[cur_col] = is_add;
            cur_col += 1;

            lv[cur_col] = is_double;
            cur_col += 1;

            // MAIN_COLS = 7*N_LIMBS + 17*N_LIMBS - 3 + 3 + 1 = 24*N_LIMBS  + 1
            // START_RANGE_CHECK = 4*N_LIMBS
            // NUM_RANGE_CHECKS = 20*N_LIMBS - 3
            assert!(cur_col == MAIN_COLS);

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

impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D> for G1Stark<F, D> {
    const COLUMNS: usize = MAIN_COLS + 1 + 6 * NUM_RANGE_CHECKS;
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

        let lv = vars.local_values.clone();

        let mut cur_col = 0;
        let a_x = read_u256(&lv, &mut cur_col);
        let a_y = read_u256(&lv, &mut cur_col);
        let b_x = read_u256(&lv, &mut cur_col);
        let b_y = read_u256(&lv, &mut cur_col);
        let lambda = read_u256(&lv, &mut cur_col);
        let new_x = read_u256(&lv, &mut cur_col);
        let new_y = read_u256(&lv, &mut cur_col);
        let aux_zero = read_modulus_aux_zero(&lv, &mut cur_col);
        let aux_x = read_modulus_aux(&lv, &mut cur_col);
        let aux_y = read_modulus_aux(&lv, &mut cur_col);

        let quot_sign_zero = lv[cur_col];
        cur_col += 1;
        let quot_sign_x = lv[cur_col];
        cur_col += 1;
        let quot_sign_y = lv[cur_col];
        cur_col += 1;

        let is_add = lv[cur_col];
        cur_col += 1;
        let is_double = lv[cur_col];
        cur_col += 1;
        assert!(cur_col == MAIN_COLS);

        let output = G1Output {
            lambda,
            new_x,
            new_y,
            aux_zero,
            aux_x,
            aux_y,
            quot_sign_zero,
            quot_sign_x,
            quot_sign_y,
        };
        eval_g1_add(yield_constr, is_add, a_x, a_y, b_x, b_y, &output);
        eval_g1_double(yield_constr, is_double, a_x, a_y, &output);
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

        let lv = vars.local_values.clone();

        let mut cur_col = 0;
        let a_x = read_u256(&lv, &mut cur_col);
        let a_y = read_u256(&lv, &mut cur_col);
        let b_x = read_u256(&lv, &mut cur_col);
        let b_y = read_u256(&lv, &mut cur_col);
        let lambda = read_u256(&lv, &mut cur_col);
        let new_x = read_u256(&lv, &mut cur_col);
        let new_y = read_u256(&lv, &mut cur_col);
        let aux_zero = read_modulus_aux_zero(&lv, &mut cur_col);
        let aux_x = read_modulus_aux(&lv, &mut cur_col);
        let aux_y = read_modulus_aux(&lv, &mut cur_col);

        let quot_sign_zero = lv[cur_col];
        cur_col += 1;
        let quot_sign_x = lv[cur_col];
        cur_col += 1;
        let quot_sign_y = lv[cur_col];
        cur_col += 1;

        let is_add = lv[cur_col];
        cur_col += 1;
        let is_double = lv[cur_col];
        cur_col += 1;
        assert!(cur_col == MAIN_COLS);

        let output = G1Output {
            lambda,
            new_x,
            new_y,
            aux_zero,
            aux_x,
            aux_y,
            quot_sign_zero,
            quot_sign_x,
            quot_sign_y,
        };

        eval_g1_add_circuit(builder, yield_constr, is_add, a_x, a_y, b_x, b_y, &output);
        eval_g1_double_circuit(builder, yield_constr, is_double, a_x, a_y, &output);
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
        develop::g1::G1Stark,
        prover::prove,
        recursive_verifier::{
            add_virtual_stark_proof_with_pis, set_stark_proof_with_pis_target,
            verify_stark_proof_circuit,
        },
        verifier::verify_stark_proof,
    };

    #[test]
    fn test_g1_mul() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type S = G1Stark<F, D>;
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

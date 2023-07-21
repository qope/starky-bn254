//    a      |      b      |   output   |  flags   | rotate_witness |  io_pulses   |     lookups         |
// 4*N_LIMBS |  4*N_LIMBS  | 40*N_LIMBS |   14     |       2        |  1+4*NUM_IO  | 1+2*NUM_RANGE_CHECK |
//<------------------------------------------------>main_cols: 48*N_LIMBS + 14
//<----------------------------------->range_check(start: 0, end: 48*N_LIMBS-6))

const NUM_IO: usize = 1 << 7;
const PUBLIC_INPUTS: usize = 13 * NUM_INPUT_LIMBS * NUM_IO;
const COLUMNS: usize = START_LOOKUPS + 1 + 2 * NUM_RANGE_CHECK;

const MAIN_COLS: usize = 48 * N_LIMBS + 14;
const START_FLAGS: usize = 48 * N_LIMBS;
const IS_FINAL_COL: usize = START_FLAGS;
const START_IO_PULSES: usize = START_FLAGS + 16;
const START_LOOKUPS: usize = START_IO_PULSES + 1 + 4 * NUM_IO;

const START_RANGE_CHECK: usize = 0;
const NUM_RANGE_CHECK: usize = 48 * N_LIMBS - 6;
const END_RANGE_CHECK: usize = START_RANGE_CHECK + NUM_RANGE_CHECK;

use std::marker::PhantomData;

use ark_bn254::{Fq2, Fr, G2Affine};
use itertools::Itertools;
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
use starky::{
    constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer},
    permutation::PermutationPair,
    stark::Stark,
    vars::{StarkEvaluationTargets, StarkEvaluationVars},
};

use crate::{
    constants::N_LIMBS,
    flags::{
        eval_flags, eval_flags_circuit, generate_flags_first_row, generate_flags_next_row,
        INPUT_LIMB_BITS, NUM_INPUT_LIMBS,
    },
    fq2::{read_fq2, write_fq2},
    g1_exp::get_pulse_positions,
    g2::{
        eval_g2_add, eval_g2_add_circuit, eval_g2_double, eval_g2_double_circuit, generate_g2_add,
        generate_g2_double, read_g2_output, write_g2_output, G2Output,
    },
    instruction::{
        fq2_equal_transition, fq2_equal_transition_circuit, vec_equal, vec_equal_circuit,
    },
    pulse::{
        eval_periodic_pulse, eval_periodic_pulse_circuit, eval_pulse, eval_pulse_circuit,
        generate_periodic_pulse_witness, generate_pulse, get_pulse_col,
    },
    range_check::{
        eval_u16_range_check, eval_u16_range_check_circuit, generate_u16_range_check,
        u16_range_check_pairs,
    },
    utils::{
        columns_to_fq2, fq2_to_columns, fq_to_u32_columns, i64_to_column_positive, read_u32_fq,
        u16_columns_to_u32_columns, u16_columns_to_u32_columns_circuit, u32_digits_to_biguint,
    },
};

pub struct G2ExpIONative {
    pub x: G2Affine,
    pub offset: G2Affine,
    pub exp_val: [u32; NUM_INPUT_LIMBS],
    pub output: G2Affine,
}

pub struct G2ExpIO<F> {
    pub x: [[F; NUM_INPUT_LIMBS]; 4],
    pub offset: [[F; NUM_INPUT_LIMBS]; 4],
    pub exp_val: [F; NUM_INPUT_LIMBS],
    pub output: [[F; NUM_INPUT_LIMBS]; 4],
}

pub fn g2_exp_io_to_columns<F: RichField>(input: &G2ExpIONative) -> [F; 13 * NUM_INPUT_LIMBS] {
    let exp_val = input.exp_val.map(F::from_canonical_u32);
    let mut columns = vec![];
    columns.extend(fq_to_u32_columns::<F>(input.x.x.c0));
    columns.extend(fq_to_u32_columns::<F>(input.x.x.c1));
    columns.extend(fq_to_u32_columns::<F>(input.x.y.c0));
    columns.extend(fq_to_u32_columns::<F>(input.x.y.c1));
    columns.extend(fq_to_u32_columns::<F>(input.offset.x.c0));
    columns.extend(fq_to_u32_columns::<F>(input.offset.x.c1));
    columns.extend(fq_to_u32_columns::<F>(input.offset.y.c0));
    columns.extend(fq_to_u32_columns::<F>(input.offset.y.c1));
    columns.extend(exp_val);
    columns.extend(fq_to_u32_columns::<F>(input.output.x.c0));
    columns.extend(fq_to_u32_columns::<F>(input.output.x.c1));
    columns.extend(fq_to_u32_columns::<F>(input.output.y.c0));
    columns.extend(fq_to_u32_columns::<F>(input.output.y.c1));
    columns.try_into().unwrap()
}

pub fn read_g2_exp_io<F: Clone + core::fmt::Debug>(lv: &[F], cur_col: &mut usize) -> G2ExpIO<F> {
    let x_x_c0 = read_u32_fq(lv, cur_col);
    let x_x_c1 = read_u32_fq(lv, cur_col);
    let x_y_c0 = read_u32_fq(lv, cur_col);
    let x_y_c1 = read_u32_fq(lv, cur_col);
    let offset_x_c0 = read_u32_fq(lv, cur_col);
    let offset_x_c1 = read_u32_fq(lv, cur_col);
    let offset_y_c0 = read_u32_fq(lv, cur_col);
    let offset_y_c1 = read_u32_fq(lv, cur_col);
    let exp_val = read_u32_fq(lv, cur_col);
    let output_x_c0 = read_u32_fq(lv, cur_col);
    let output_x_c1 = read_u32_fq(lv, cur_col);
    let output_y_c0 = read_u32_fq(lv, cur_col);
    let output_y_c1 = read_u32_fq(lv, cur_col);
    G2ExpIO {
        x: [x_x_c0, x_x_c1, x_y_c0, x_y_c1],
        offset: [offset_x_c0, offset_x_c1, offset_y_c0, offset_y_c1],
        exp_val,
        output: [output_x_c0, output_x_c1, output_y_c0, output_y_c1],
    }
}

pub fn generate_g2_exp_first_row<F: RichField>(
    lv: &mut [F],
    start_flag_col: usize,
    x: G2Affine,
    offset: G2Affine,
) {
    let is_add_col = start_flag_col + 4;
    let a = x;
    let b = offset;
    let a_x: [[F; N_LIMBS]; 2] = fq2_to_columns(a.x).map(i64_to_column_positive);
    let a_y: [[F; N_LIMBS]; 2] = fq2_to_columns(a.y).map(i64_to_column_positive);
    let b_x: [[F; N_LIMBS]; 2] = fq2_to_columns(b.x).map(i64_to_column_positive);
    let b_y: [[F; N_LIMBS]; 2] = fq2_to_columns(b.y).map(i64_to_column_positive);
    let is_add = lv[is_add_col];
    let output = if is_add == F::ONE {
        generate_g2_add(a_x, a_y, b_x, b_y)
    } else {
        G2Output::default()
    };
    let mut cur_col = 0;
    write_fq2(lv, a_x, &mut cur_col);
    write_fq2(lv, a_y, &mut cur_col);
    write_fq2(lv, b_x, &mut cur_col);
    write_fq2(lv, b_y, &mut cur_col);
    write_g2_output(lv, &output, &mut cur_col);
}

pub fn generate_g2_exp_next_row<F: RichField>(lv: &[F], nv: &mut [F], start_flag_col: usize) {
    let is_double_col = start_flag_col + 2;
    let is_add_col = start_flag_col + 4;

    let mut cur_col = 0;
    let a_x = read_fq2(lv, &mut cur_col);
    let a_y = read_fq2(lv, &mut cur_col);
    let b_x = read_fq2(lv, &mut cur_col);
    let b_y = read_fq2(lv, &mut cur_col);
    let output = read_g2_output(lv, &mut cur_col);
    let is_double = lv[is_double_col];
    let is_add = lv[is_add_col];
    let next_is_double = nv[is_double_col];
    let next_is_add = nv[is_add_col];

    // calc next a, b
    let (next_a_x, next_a_y, next_b_x, next_b_y) = if is_double == F::ONE {
        (output.new_x, output.new_y, b_x, b_y)
    } else if is_add == F::ONE {
        (a_x, a_y, output.new_x, output.new_y)
    } else {
        (a_x, a_y, b_x, b_y)
    };

    // calc next output
    let next_output = if next_is_double == F::ONE {
        generate_g2_double(next_a_x, next_a_y)
    } else if next_is_add == F::ONE {
        generate_g2_add(next_a_x, next_a_y, next_b_x, next_b_y)
    } else {
        G2Output::default()
    };
    cur_col = 0;
    write_fq2(nv, next_a_x, &mut cur_col);
    write_fq2(nv, next_a_y, &mut cur_col);
    write_fq2(nv, next_b_x, &mut cur_col);
    write_fq2(nv, next_b_y, &mut cur_col);
    write_g2_output(nv, &next_output, &mut cur_col);
}

#[derive(Clone, Copy)]
pub struct G2ExpStark<F: RichField + Extendable<D>, const D: usize> {
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> G2ExpStark<F, D> {
    pub fn new() -> Self {
        Self {
            _phantom: PhantomData,
        }
    }

    pub fn generate_trace_for_one_block(
        &self,
        x: G2Affine,
        offset: G2Affine,
        exp_val: [u32; NUM_INPUT_LIMBS],
    ) -> Vec<Vec<F>> {
        let num_rows = 2 * INPUT_LIMB_BITS * NUM_INPUT_LIMBS;
        let mut lv = vec![F::ZERO; MAIN_COLS];
        generate_flags_first_row(&mut lv, START_FLAGS, exp_val);
        generate_g2_exp_first_row(&mut lv, START_FLAGS, x, offset);
        let mut rows = vec![lv.clone()];
        for i in 0..num_rows - 1 {
            let mut nv = vec![F::ZERO; lv.len()];
            generate_flags_next_row(&lv, &mut nv, i, START_FLAGS);
            generate_g2_exp_next_row(&lv, &mut nv, START_FLAGS);
            rows.push(nv.clone());
            lv = nv;
        }
        let output = {
            let last_row = rows.last().unwrap();
            let mut cur_col = 4 * N_LIMBS;
            let b_x = read_fq2(last_row, &mut cur_col);
            let b_y = read_fq2(last_row, &mut cur_col);
            let b_x_fq2: Fq2 = columns_to_fq2(b_x);
            let b_y_fq2: Fq2 = columns_to_fq2(b_y);
            G2Affine::new(b_x_fq2, b_y_fq2)
        };
        // assertion
        let exp_val_fr: Fr = u32_digits_to_biguint(&exp_val).into();
        let expected: G2Affine = (x * exp_val_fr + offset).into();
        assert!(output == expected);

        rows
    }

    pub fn generate_trace(&self, inputs: &[G2ExpIONative]) -> Vec<PolynomialValues<F>> {
        assert!(inputs.len() == NUM_IO);

        let mut rows = vec![];
        for input in inputs.clone() {
            let row = self.generate_trace_for_one_block(input.x, input.offset, input.exp_val);
            rows.extend(row);
        }
        let mut trace_cols = transpose(&rows.iter().map(|v| v.to_vec()).collect_vec());

        let rotation_period = 2 * INPUT_LIMB_BITS;
        generate_periodic_pulse_witness(
            &mut trace_cols,
            START_FLAGS + 1,
            rotation_period,
            rotation_period - 2,
        );

        generate_pulse(&mut trace_cols, get_pulse_positions());
        generate_u16_range_check(START_RANGE_CHECK..END_RANGE_CHECK, &mut trace_cols);

        trace_cols
            .into_iter()
            .map(|column| PolynomialValues::new(column))
            .collect()
    }

    pub fn generate_public_inputs(&self, inputs: &[G2ExpIONative]) -> [F; PUBLIC_INPUTS] {
        inputs
            .iter()
            .flat_map(|input| g2_exp_io_to_columns::<F>(input))
            .collect_vec()
            .try_into()
            .unwrap()
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D> for G2ExpStark<F, D> {
    const COLUMNS: usize = COLUMNS;
    const PUBLIC_INPUTS: usize = PUBLIC_INPUTS;

    fn eval_packed_generic<FE, P, const D2: usize>(
        &self,
        vars: StarkEvaluationVars<FE, P>,
        yield_constr: &mut ConstraintConsumer<P>,
    ) where
        FE: FieldExtension<D2, BaseField = F>,
        P: PackedField<Scalar = FE>,
    {
        let is_final_col = IS_FINAL_COL;
        let is_double_col = START_FLAGS + 2;
        let is_add_col = START_FLAGS + 4;
        let start_limbs_col = START_FLAGS + 6;

        let lv = vars.local_values;
        let nv = vars.next_values;

        let mut cur_col = 0;
        let a_x = read_fq2(lv, &mut cur_col);
        let a_y = read_fq2(lv, &mut cur_col);
        let b_x = read_fq2(lv, &mut cur_col);
        let b_y = read_fq2(lv, &mut cur_col);
        let output = read_g2_output(lv, &mut cur_col);
        let is_add = lv[is_add_col];
        let is_double = lv[is_double_col];
        let is_final = lv[is_final_col];
        let is_not_final = P::ONES - is_final;

        // constraints for is_final
        let mut sum_is_output = P::ZEROS;
        for i in (0..2 * NUM_IO).skip(1).step_by(2) {
            sum_is_output = sum_is_output + lv[get_pulse_col(START_IO_PULSES, i)];
        }
        yield_constr.constraint(is_final - sum_is_output);

        // public inputs
        let pi: &[P] = &vars
            .public_inputs
            .into_iter()
            .map(|&x| x.into())
            .collect_vec();
        cur_col = 0;
        for i in (0..2 * NUM_IO).step_by(2) {
            let g2_exp_io = read_g2_exp_io(pi, &mut cur_col);
            let is_ith_input = lv[get_pulse_col(START_IO_PULSES, i)];
            let is_ith_output = lv[get_pulse_col(START_IO_PULSES, i + 1)];
            let x_x = a_x.map(u16_columns_to_u32_columns);
            let x_y = a_y.map(u16_columns_to_u32_columns);
            let b_x = b_x.map(u16_columns_to_u32_columns);
            let b_y = b_y.map(u16_columns_to_u32_columns);
            vec_equal(yield_constr, is_ith_input, &g2_exp_io.x[0], &x_x[0]);
            vec_equal(yield_constr, is_ith_input, &g2_exp_io.x[1], &x_x[1]);
            vec_equal(yield_constr, is_ith_input, &g2_exp_io.x[2], &x_y[0]);
            vec_equal(yield_constr, is_ith_input, &g2_exp_io.x[3], &x_y[1]);

            vec_equal(yield_constr, is_ith_input, &g2_exp_io.offset[0], &b_x[0]);
            vec_equal(yield_constr, is_ith_input, &g2_exp_io.offset[1], &b_x[1]);
            vec_equal(yield_constr, is_ith_input, &g2_exp_io.offset[2], &b_y[0]);
            vec_equal(yield_constr, is_ith_input, &g2_exp_io.offset[3], &b_y[1]);

            vec_equal(yield_constr, is_ith_output, &g2_exp_io.output[0], &b_x[0]);
            vec_equal(yield_constr, is_ith_output, &g2_exp_io.output[1], &b_x[1]);
            vec_equal(yield_constr, is_ith_output, &g2_exp_io.output[2], &b_y[0]);
            vec_equal(yield_constr, is_ith_output, &g2_exp_io.output[3], &b_y[1]);
            let bit = is_add;
            let mut limbs = lv[start_limbs_col..start_limbs_col + NUM_INPUT_LIMBS].to_vec();
            limbs[0] = limbs[0] * P::Scalar::TWO + bit;
            vec_equal(yield_constr, is_ith_input, &g2_exp_io.exp_val, &limbs);
        }

        // transition
        cur_col = 0;
        let next_a_x = read_fq2(nv, &mut cur_col);
        let next_a_y = read_fq2(nv, &mut cur_col);
        let next_b_x = read_fq2(nv, &mut cur_col);
        let next_b_y = read_fq2(nv, &mut cur_col);
        // if is_double==F::ONE
        {
            fq2_equal_transition(
                yield_constr,
                is_not_final * is_double,
                next_a_x,
                output.new_x,
            );
            fq2_equal_transition(
                yield_constr,
                is_not_final * is_double,
                next_a_y,
                output.new_y,
            );
            fq2_equal_transition(yield_constr, is_not_final * is_double, next_b_x, b_x);
            fq2_equal_transition(yield_constr, is_not_final * is_double, next_b_y, b_y);
        }
        // if is_add==F::ONE
        {
            fq2_equal_transition(yield_constr, is_not_final * is_add, next_a_x, a_x);
            fq2_equal_transition(yield_constr, is_not_final * is_add, next_a_y, a_y);
            fq2_equal_transition(yield_constr, is_not_final * is_add, next_b_x, output.new_x);
            fq2_equal_transition(yield_constr, is_not_final * is_add, next_b_y, output.new_y);
        }
        // else
        {
            let is_double_nor_add = P::ONES - is_double - is_add;
            fq2_equal_transition(
                yield_constr,
                is_not_final * is_double_nor_add,
                next_a_x,
                a_x,
            );
            fq2_equal_transition(
                yield_constr,
                is_not_final * is_double_nor_add,
                next_a_y,
                a_y,
            );
            fq2_equal_transition(
                yield_constr,
                is_not_final * is_double_nor_add,
                next_b_x,
                b_x,
            );
            fq2_equal_transition(
                yield_constr,
                is_not_final * is_double_nor_add,
                next_b_y,
                b_y,
            );
        }
        eval_flags(yield_constr, lv, nv, START_FLAGS);
        eval_g2_add(yield_constr, is_add, a_x, a_y, b_x, b_y, &output);
        eval_g2_double(yield_constr, is_double, a_x, a_y, &output);

        // flags, pulses, and lookup
        eval_flags(
            yield_constr,
            vars.local_values,
            vars.next_values,
            START_FLAGS,
        );
        eval_periodic_pulse(
            yield_constr,
            vars.local_values,
            vars.next_values,
            START_FLAGS + 1,
            MAIN_COLS,
            2 * INPUT_LIMB_BITS,
            2 * INPUT_LIMB_BITS - 2,
        );
        eval_pulse(
            yield_constr,
            vars.local_values,
            vars.next_values,
            MAIN_COLS + 2,
            get_pulse_positions(),
        );
        eval_u16_range_check(
            vars,
            yield_constr,
            START_LOOKUPS,
            START_RANGE_CHECK..END_RANGE_CHECK,
        );
    }

    fn eval_ext_circuit(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        vars: StarkEvaluationTargets<D>,
        yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    ) {
        let one = builder.one_extension();
        let is_final_col = IS_FINAL_COL;
        let is_double_col = START_FLAGS + 2;
        let is_add_col = START_FLAGS + 4;
        let start_limbs_col = START_FLAGS + 6;

        let lv = vars.local_values;
        let nv = vars.next_values;

        let mut cur_col = 0;
        let a_x = read_fq2(lv, &mut cur_col);
        let a_y = read_fq2(lv, &mut cur_col);
        let b_x = read_fq2(lv, &mut cur_col);
        let b_y = read_fq2(lv, &mut cur_col);
        let output = read_g2_output(lv, &mut cur_col);
        let is_add = lv[is_add_col];
        let is_double = lv[is_double_col];
        let is_final = lv[is_final_col];
        let is_not_final = builder.sub_extension(one, is_final);

        // constraints for is_final
        let mut sum_is_output = builder.zero_extension();
        for i in (0..2 * NUM_IO).skip(1).step_by(2) {
            sum_is_output =
                builder.add_extension(sum_is_output, lv[get_pulse_col(START_IO_PULSES, i)]);
        }
        let diff = builder.sub_extension(is_final, sum_is_output);
        yield_constr.constraint(builder, diff);

        // public inputs
        cur_col = 0;
        for i in (0..2 * NUM_IO).step_by(2) {
            let g2_exp_io = read_g2_exp_io(vars.public_inputs, &mut cur_col);
            let is_ith_input = lv[get_pulse_col(START_IO_PULSES, i)];
            let is_ith_output = lv[get_pulse_col(START_IO_PULSES, i + 1)];
            let x_x = a_x.map(|x| u16_columns_to_u32_columns_circuit(builder, x));
            let x_y = a_y.map(|x| u16_columns_to_u32_columns_circuit(builder, x));
            let b_x = b_x.map(|x| u16_columns_to_u32_columns_circuit(builder, x));
            let b_y = b_y.map(|x| u16_columns_to_u32_columns_circuit(builder, x));
            vec_equal_circuit(
                builder,
                yield_constr,
                is_ith_input,
                &g2_exp_io.x[0],
                &x_x[0],
            );
            vec_equal_circuit(
                builder,
                yield_constr,
                is_ith_input,
                &g2_exp_io.x[1],
                &x_x[1],
            );
            vec_equal_circuit(
                builder,
                yield_constr,
                is_ith_input,
                &g2_exp_io.x[2],
                &x_y[0],
            );
            vec_equal_circuit(
                builder,
                yield_constr,
                is_ith_input,
                &g2_exp_io.x[3],
                &x_y[1],
            );
            vec_equal_circuit(
                builder,
                yield_constr,
                is_ith_input,
                &g2_exp_io.offset[0],
                &b_x[0],
            );
            vec_equal_circuit(
                builder,
                yield_constr,
                is_ith_input,
                &g2_exp_io.offset[1],
                &b_x[1],
            );
            vec_equal_circuit(
                builder,
                yield_constr,
                is_ith_input,
                &g2_exp_io.offset[2],
                &b_y[0],
            );
            vec_equal_circuit(
                builder,
                yield_constr,
                is_ith_input,
                &g2_exp_io.offset[3],
                &b_y[1],
            );
            vec_equal_circuit(
                builder,
                yield_constr,
                is_ith_output,
                &g2_exp_io.output[0],
                &b_x[0],
            );
            vec_equal_circuit(
                builder,
                yield_constr,
                is_ith_output,
                &g2_exp_io.output[1],
                &b_x[1],
            );
            vec_equal_circuit(
                builder,
                yield_constr,
                is_ith_output,
                &g2_exp_io.output[2],
                &b_y[0],
            );
            vec_equal_circuit(
                builder,
                yield_constr,
                is_ith_output,
                &g2_exp_io.output[3],
                &b_y[1],
            );
            let bit = is_add;
            let mut limbs = lv[start_limbs_col..start_limbs_col + NUM_INPUT_LIMBS].to_vec();
            let two = builder.two_extension();
            limbs[0] = builder.mul_add_extension(limbs[0], two, bit);
            vec_equal_circuit(
                builder,
                yield_constr,
                is_ith_input,
                &g2_exp_io.exp_val,
                &limbs,
            );
        }

        // transition
        cur_col = 0;
        let next_a_x = read_fq2(nv, &mut cur_col);
        let next_a_y = read_fq2(nv, &mut cur_col);
        let next_b_x = read_fq2(nv, &mut cur_col);
        let next_b_y = read_fq2(nv, &mut cur_col);
        // if is_double==F::ONE
        {
            let is_not_final_and_double = builder.mul_extension(is_not_final, is_double);
            fq2_equal_transition_circuit(
                builder,
                yield_constr,
                is_not_final_and_double,
                next_a_x,
                output.new_x,
            );
            fq2_equal_transition_circuit(
                builder,
                yield_constr,
                is_not_final_and_double,
                next_a_y,
                output.new_y,
            );
            fq2_equal_transition_circuit(
                builder,
                yield_constr,
                is_not_final_and_double,
                next_b_x,
                b_x,
            );
            fq2_equal_transition_circuit(
                builder,
                yield_constr,
                is_not_final_and_double,
                next_b_y,
                b_y,
            );
        }
        // if is_add==F::ONE
        {
            let is_not_final_and_add = builder.mul_extension(is_not_final, is_add);
            fq2_equal_transition_circuit(
                builder,
                yield_constr,
                is_not_final_and_add,
                next_a_x,
                a_x,
            );
            fq2_equal_transition_circuit(
                builder,
                yield_constr,
                is_not_final_and_add,
                next_a_y,
                a_y,
            );
            fq2_equal_transition_circuit(
                builder,
                yield_constr,
                is_not_final_and_add,
                next_b_x,
                output.new_x,
            );
            fq2_equal_transition_circuit(
                builder,
                yield_constr,
                is_not_final_and_add,
                next_b_y,
                output.new_y,
            );
        }
        // else
        {
            let is_double_or_add = builder.add_extension(is_double, is_add);
            let is_not_double_nor_add = builder.sub_extension(one, is_double_or_add);
            let is_not_final_and_not_double_nor_add =
                builder.mul_extension(is_not_final, is_not_double_nor_add);
            fq2_equal_transition_circuit(
                builder,
                yield_constr,
                is_not_final_and_not_double_nor_add,
                next_a_x,
                a_x,
            );
            fq2_equal_transition_circuit(
                builder,
                yield_constr,
                is_not_final_and_not_double_nor_add,
                next_a_y,
                a_y,
            );
            fq2_equal_transition_circuit(
                builder,
                yield_constr,
                is_not_final_and_not_double_nor_add,
                next_b_x,
                b_x,
            );
            fq2_equal_transition_circuit(
                builder,
                yield_constr,
                is_not_final_and_not_double_nor_add,
                next_b_y,
                b_y,
            );
        }
        eval_flags_circuit(builder, yield_constr, lv, nv, START_FLAGS);
        eval_g2_add_circuit(builder, yield_constr, is_add, a_x, a_y, b_x, b_y, &output);
        eval_g2_double_circuit(builder, yield_constr, is_double, a_x, a_y, &output);

        // flags, pulses, and lookup
        eval_flags_circuit(
            builder,
            yield_constr,
            vars.local_values,
            vars.next_values,
            START_FLAGS,
        );
        eval_periodic_pulse_circuit(
            builder,
            yield_constr,
            vars.local_values,
            vars.next_values,
            START_FLAGS + 1,
            MAIN_COLS,
            2 * INPUT_LIMB_BITS,
            2 * INPUT_LIMB_BITS - 2,
        );
        eval_pulse_circuit(
            builder,
            yield_constr,
            vars.local_values,
            vars.next_values,
            MAIN_COLS + 2,
            get_pulse_positions(),
        );
        eval_u16_range_check_circuit(
            builder,
            vars,
            yield_constr,
            START_LOOKUPS,
            START_RANGE_CHECK..END_RANGE_CHECK,
        );
    }

    fn constraint_degree(&self) -> usize {
        3
    }

    fn permutation_pairs(&self) -> Vec<PermutationPair> {
        u16_range_check_pairs(START_LOOKUPS, START_RANGE_CHECK..END_RANGE_CHECK)
    }
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use crate::{
        flags::NUM_INPUT_LIMBS,
        g2_exp::{G2ExpIONative, G2ExpStark, NUM_IO},
        utils::u32_digits_to_biguint,
    };
    use ark_bn254::{Fr, G2Affine};
    use ark_std::UniformRand;
    use itertools::Itertools;
    use plonky2::{
        iop::witness::PartialWitness,
        plonk::{
            circuit_builder::CircuitBuilder,
            circuit_data::CircuitConfig,
            config::{GenericConfig, PoseidonGoldilocksConfig},
        },
        util::timing::TimingTree,
    };
    use starky::{
        config::StarkConfig,
        prover::prove,
        recursive_verifier::{
            add_virtual_stark_proof_with_pis, set_stark_proof_with_pis_target,
            verify_stark_proof_circuit,
        },
        verifier::verify_stark_proof,
    };

    #[test]
    fn test_g2_exp() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let mut rng = rand::thread_rng();

        let inputs = (0..NUM_IO)
            .map(|_| {
                let exp_val: [u32; NUM_INPUT_LIMBS] = rand::random();
                let exp_val_fr: Fr = u32_digits_to_biguint(&exp_val).into();
                let x = G2Affine::rand(&mut rng);
                let offset = G2Affine::rand(&mut rng);
                let output: G2Affine = (x * exp_val_fr + offset).into();

                G2ExpIONative {
                    x,
                    offset,
                    exp_val,
                    output,
                }
            })
            .collect_vec();

        type S = G2ExpStark<F, D>;
        let inner_config = StarkConfig::standard_fast_config();
        let stark = S::new();

        println!("start stark proof generation");
        let now = Instant::now();
        let trace = stark.generate_trace(&inputs);
        let pi = stark.generate_public_inputs(&inputs);
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

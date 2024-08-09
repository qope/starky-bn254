//    a      |      b      |   output   |  flags   | rotate_witness |  io_pulses   |     lookups        |
// 2*N_LIMBS |  2*N_LIMBS  | 20*N_LIMBS |   14     |       2        |  1+4*NUM_IO  | 1+2*(20*N_LIMBS-3) |
//<------------------------------------------------>main_cols: 24*N_LIMBS + 14
//<----------------------------------->range_check(start: 0, end: 24*N_LIMBS-3))

fn constants(num_io: usize) -> ExpStarkConstants {
    let start_flags_col = 24 * N_LIMBS;
    let num_main_cols = start_flags_col + NUM_FLAGS_COLS;

    let start_periodic_pulse_col = num_main_cols;
    let start_io_pulses_col = start_periodic_pulse_col + 2;
    let start_lookups_col = start_io_pulses_col + 1 + 4 * num_io;

    let start_range_check_col = 0;
    let num_range_check_cols = 24 * N_LIMBS - 3;
    let end_range_check_col = start_range_check_col + num_range_check_cols;

    let num_columns = start_lookups_col + 1 + 2 * num_range_check_cols;
    let num_public_inputs = 7 * NUM_INPUT_LIMBS * num_io;

    ExpStarkConstants {
        num_columns,
        num_public_inputs,
        num_main_cols,
        num_io,
        start_flags_col,
        start_periodic_pulse_col,
        start_io_pulses_col,
        start_lookups_col,
        start_range_check_col,
        end_range_check_col,
        num_range_check_cols,
    }
}

use core::marker::PhantomData;

use ark_bn254::{Fr, G1Affine};
use itertools::Itertools;
use plonky2::{
    field::{
        extension::{Extendable, FieldExtension},
        packed::PackedField,
        polynomial::PolynomialValues,
    },
    hash::hash_types::RichField,
    iop::{target::Target, witness::WitnessWrite},
    plonk::circuit_builder::CircuitBuilder,
    util::transpose,
};

use starky::{
    config::StarkConfig,
    constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer},
    permutation::PermutationPair,
    stark::Stark,
    vars::{StarkEvaluationTargets, StarkEvaluationVars},
};

use crate::{
    constants::{ExpStarkConstants, N_LIMBS},
    curves::g1::muladd::{
        eval_g1_add, eval_g1_add_circuit, eval_g1_double, eval_g1_double_circuit, generate_g1_add,
        generate_g1_double, read_g1_output, write_g1_output, G1Output,
    },
    modular::modular::{read_u256, write_u256},
    utils::flags::{
        eval_flags, eval_flags_circuit, generate_flags_first_row, generate_flags_next_row,
        INPUT_LIMB_BITS, NUM_FLAGS_COLS, NUM_INPUT_LIMBS,
    },
    utils::{
        equals::{fq_equal_transition, fq_equal_transition_circuit, vec_equal, vec_equal_circuit},
        pulse::{
            eval_periodic_pulse, eval_periodic_pulse_circuit, eval_pulse, eval_pulse_circuit,
            generate_periodic_pulse_witness, generate_pulse, get_pulse_col,
        },
        range_check::{
            eval_u16_range_check, eval_u16_range_check_circuit, generate_u16_range_check,
            u16_range_check_pairs,
        },
        utils::{
            columns_to_fq, fq_to_columns, fq_to_u32_columns, read_u32_fq,
            u16_columns_to_u32_columns, u16_columns_to_u32_columns_circuit, u32_digits_to_biguint,
        },
    },
};

pub struct G1ExpIONative {
    pub x: G1Affine,
    pub offset: G1Affine,
    pub exp_val: [u32; NUM_INPUT_LIMBS],
    pub output: G1Affine,
}

pub const G1_EXP_IO_LEN: usize = 7 * NUM_INPUT_LIMBS;

#[derive(Clone, Debug)]
pub struct G1ExpIO<F> {
    pub x: [[F; NUM_INPUT_LIMBS]; 2],
    pub offset: [[F; NUM_INPUT_LIMBS]; 2],
    pub exp_val: [F; NUM_INPUT_LIMBS],
    pub output: [[F; NUM_INPUT_LIMBS]; 2],
}

impl G1ExpIO<Target> {
    pub fn set_witness<F: RichField, W: WitnessWrite<F>>(&self, pw: &mut W, value: &G1ExpIONative) {
        let x_x = fq_to_u32_columns(value.x.x);
        let x_y = fq_to_u32_columns(value.x.y);
        let offset_x = fq_to_u32_columns(value.offset.x);
        let offset_y = fq_to_u32_columns(value.offset.y);
        let exp_val = value.exp_val.map(F::from_canonical_u32);
        let output_x = fq_to_u32_columns(value.output.x);
        let output_y = fq_to_u32_columns(value.output.y);
        pw.set_target_arr(&self.x[0], &x_x);
        pw.set_target_arr(&self.x[1], &x_y);
        pw.set_target_arr(&self.offset[0], &offset_x);
        pw.set_target_arr(&self.offset[1], &offset_y);
        pw.set_target_arr(&self.exp_val, &exp_val);
        pw.set_target_arr(&self.output[0], &output_x);
        pw.set_target_arr(&self.output[1], &output_y);
    }
}

pub fn g1_exp_io_to_columns<F: RichField>(input: &G1ExpIONative) -> [F; 7 * NUM_INPUT_LIMBS] {
    let exp_val = input.exp_val.map(F::from_canonical_u32);
    let mut columns = vec![];
    columns.extend(fq_to_u32_columns::<F>(input.x.x));
    columns.extend(fq_to_u32_columns::<F>(input.x.y));
    columns.extend(fq_to_u32_columns::<F>(input.offset.x));
    columns.extend(fq_to_u32_columns::<F>(input.offset.y));
    columns.extend(exp_val);
    columns.extend(fq_to_u32_columns::<F>(input.output.x));
    columns.extend(fq_to_u32_columns::<F>(input.output.y));
    columns.try_into().unwrap()
}

pub fn read_g1_exp_io<F: Clone + core::fmt::Debug>(lv: &[F], cur_col: &mut usize) -> G1ExpIO<F> {
    let x_x = read_u32_fq(lv, cur_col);
    let x_y = read_u32_fq(lv, cur_col);
    let offset_x = read_u32_fq(lv, cur_col);
    let offset_y = read_u32_fq(lv, cur_col);
    let exp_val = read_u32_fq(lv, cur_col);
    let output_x = read_u32_fq(lv, cur_col);
    let output_y = read_u32_fq(lv, cur_col);
    G1ExpIO {
        x: [x_x, x_y],
        offset: [offset_x, offset_y],
        exp_val,
        output: [output_x, output_y],
    }
}

pub fn get_pulse_positions(num_io: usize) -> Vec<usize> {
    let num_rows_per_block = 2 * INPUT_LIMB_BITS * NUM_INPUT_LIMBS;
    let mut pulse_positions = vec![];
    for i in 0..num_io {
        pulse_positions.extend(vec![
            i * num_rows_per_block,
            i * num_rows_per_block + num_rows_per_block - 1,
        ]);
    }
    pulse_positions
}

pub fn generate_g1_exp_first_row<F: RichField>(
    lv: &mut [F],
    start_flag_col: usize,
    x: G1Affine,
    offset: G1Affine,
) {
    let is_add_col = start_flag_col + 4;
    let a = x;
    let b = offset;
    let a_x = fq_to_columns(a.x).map(|x| F::from_canonical_i64(x));
    let a_y = fq_to_columns(a.y).map(|x| F::from_canonical_i64(x));
    let b_x = fq_to_columns(b.x).map(|x| F::from_canonical_i64(x));
    let b_y = fq_to_columns(b.y).map(|x| F::from_canonical_i64(x));
    let is_add = lv[is_add_col];
    let output = if is_add == F::ONE {
        generate_g1_add(a_x, a_y, b_x, b_y)
    } else {
        G1Output::default()
    };
    let mut cur_col = 0;
    write_u256(lv, &a_x, &mut cur_col);
    write_u256(lv, &a_y, &mut cur_col);
    write_u256(lv, &b_x, &mut cur_col);
    write_u256(lv, &b_y, &mut cur_col);
    write_g1_output(lv, &output, &mut cur_col);
}

pub fn generate_g1_exp_next_row<F: RichField>(lv: &[F], nv: &mut [F], start_flag_col: usize) {
    let is_double_col = start_flag_col + 2;
    let is_add_col = start_flag_col + 4;

    let mut cur_col = 0;
    let a_x = read_u256(lv, &mut cur_col);
    let a_y = read_u256(lv, &mut cur_col);
    let b_x = read_u256(lv, &mut cur_col);
    let b_y = read_u256(lv, &mut cur_col);
    let output = read_g1_output(lv, &mut cur_col);
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
        generate_g1_double(next_a_x, next_a_y)
    } else if next_is_add == F::ONE {
        generate_g1_add(next_a_x, next_a_y, next_b_x, next_b_y)
    } else {
        G1Output::default()
    };
    cur_col = 0;
    write_u256(nv, &next_a_x, &mut cur_col);
    write_u256(nv, &next_a_y, &mut cur_col);
    write_u256(nv, &next_b_x, &mut cur_col);
    write_u256(nv, &next_b_y, &mut cur_col);
    write_g1_output(nv, &next_output, &mut cur_col);
}

#[derive(Clone, Copy)]
pub struct G1ExpStark<F: RichField + Extendable<D>, const D: usize> {
    pub num_io: usize,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> G1ExpStark<F, D> {
    pub fn new(num_io: usize) -> Self {
        Self {
            num_io,
            _phantom: PhantomData,
        }
    }

    pub fn constants(&self) -> ExpStarkConstants {
        constants(self.num_io)
    }

    pub fn config(&self) -> StarkConfig {
        let c = self.constants();
        StarkConfig::standard_fast_config(c.num_columns, c.num_public_inputs)
    }

    pub fn generate_trace_for_one_block(
        &self,
        x: G1Affine,
        offset: G1Affine,
        exp_val: [u32; NUM_INPUT_LIMBS],
    ) -> Vec<Vec<F>> {
        let num_rows = 2 * INPUT_LIMB_BITS * NUM_INPUT_LIMBS;
        let mut lv = vec![F::ZERO; self.constants().num_main_cols];
        generate_flags_first_row(&mut lv, self.constants().start_flags_col, exp_val);
        generate_g1_exp_first_row(&mut lv, self.constants().start_flags_col, x, offset);
        let mut rows = vec![lv.clone()];
        for i in 0..num_rows - 1 {
            let mut nv = vec![F::ZERO; lv.len()];
            generate_flags_next_row(&lv, &mut nv, i, self.constants().start_flags_col);
            generate_g1_exp_next_row(&lv, &mut nv, self.constants().start_flags_col);
            rows.push(nv.clone());
            lv = nv;
        }
        let output = {
            let last_row = rows.last().unwrap();
            let mut cur_col = 2 * N_LIMBS;
            let b_x = read_u256(last_row, &mut cur_col);
            let b_y = read_u256(last_row, &mut cur_col);
            let b_x_fq = columns_to_fq(&b_x);
            let b_y_fq = columns_to_fq(&b_y);
            G1Affine::new(b_x_fq, b_y_fq)
        };
        // assertion
        let exp_val_fr: Fr = u32_digits_to_biguint(&exp_val).into();
        let expected: G1Affine = (x * exp_val_fr + offset).into();
        assert!(output == expected);

        rows
    }

    pub fn generate_trace(&self, inputs: &[G1ExpIONative]) -> Vec<PolynomialValues<F>> {
        assert!(inputs.len() == self.constants().num_io);

        let mut rows = vec![];
        for input in inputs {
            let row = self.generate_trace_for_one_block(input.x, input.offset, input.exp_val);
            rows.extend(row);
        }
        let mut trace_cols = transpose(&rows.iter().map(|v| v.to_vec()).collect_vec());

        let rotation_period = 2 * INPUT_LIMB_BITS;
        generate_periodic_pulse_witness(
            &mut trace_cols,
            self.constants().start_flags_col + 1,
            rotation_period,
            rotation_period - 2,
        );

        generate_pulse(&mut trace_cols, get_pulse_positions(self.num_io));
        generate_u16_range_check(
            self.constants().start_range_check_col..self.constants().end_range_check_col,
            &mut trace_cols,
        );

        trace_cols
            .into_iter()
            .map(|column| PolynomialValues::new(column))
            .collect()
    }

    pub fn generate_public_inputs(&self, inputs: &[G1ExpIONative]) -> Vec<F> {
        inputs
            .iter()
            .flat_map(|input| g1_exp_io_to_columns::<F>(input))
            .collect_vec()
            .try_into()
            .unwrap()
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D> for G1ExpStark<F, D> {
    fn eval_packed_generic<FE, P, const D2: usize>(
        &self,
        vars: StarkEvaluationVars<FE, P>,
        yield_constr: &mut ConstraintConsumer<P>,
    ) where
        FE: FieldExtension<D2, BaseField = F>,
        P: PackedField<Scalar = FE>,
    {
        let c = self.constants();
        let is_final_col = c.start_flags_col;
        let is_double_col = c.start_flags_col + 2;
        let is_add_col = c.start_flags_col + 4;
        let start_limbs_col = c.start_flags_col + 6;

        let lv = vars.local_values;
        let nv = vars.next_values;

        let mut cur_col = 0;
        let a_x = read_u256(lv, &mut cur_col);
        let a_y = read_u256(lv, &mut cur_col);
        let b_x = read_u256(lv, &mut cur_col);
        let b_y = read_u256(lv, &mut cur_col);
        let output = read_g1_output(lv, &mut cur_col);
        let is_add = lv[is_add_col];
        let is_double = lv[is_double_col];
        let is_final = lv[is_final_col];
        let is_not_final = P::ONES - is_final;

        // constraints for is_final
        let mut sum_is_output = P::ZEROS;

        for i in (0..2 * self.num_io).skip(1).step_by(2) {
            sum_is_output = sum_is_output + lv[get_pulse_col(c.start_io_pulses_col, i)];
        }
        yield_constr.constraint(is_final - sum_is_output);

        // public inputs
        let pi: &[P] = &vars
            .public_inputs
            .into_iter()
            .map(|&x| x.into())
            .collect_vec();
        cur_col = 0;
        for i in (0..2 * self.num_io).step_by(2) {
            let g1_exp_io = read_g1_exp_io(pi, &mut cur_col);
            let is_ith_input = lv[get_pulse_col(c.start_io_pulses_col, i)];
            let is_ith_output = lv[get_pulse_col(c.start_io_pulses_col, i + 1)];
            let x_x = u16_columns_to_u32_columns(a_x);
            let x_y = u16_columns_to_u32_columns(a_y);
            let b_x = u16_columns_to_u32_columns(b_x);
            let b_y = u16_columns_to_u32_columns(b_y);
            vec_equal(yield_constr, is_ith_input, &g1_exp_io.x[0], &x_x);
            vec_equal(yield_constr, is_ith_input, &g1_exp_io.x[1], &x_y);
            vec_equal(yield_constr, is_ith_input, &g1_exp_io.offset[0], &b_x);
            vec_equal(yield_constr, is_ith_input, &g1_exp_io.offset[1], &b_y);
            vec_equal(yield_constr, is_ith_output, &g1_exp_io.output[0], &b_x);
            vec_equal(yield_constr, is_ith_output, &g1_exp_io.output[1], &b_y);
            let bit = is_add;
            let mut limbs = lv[start_limbs_col..start_limbs_col + NUM_INPUT_LIMBS].to_vec();
            limbs[0] = limbs[0] * P::Scalar::TWO + bit;
            vec_equal(yield_constr, is_ith_input, &g1_exp_io.exp_val, &limbs);
        }

        // transition
        cur_col = 0;
        let next_a_x = read_u256(nv, &mut cur_col);
        let next_a_y = read_u256(nv, &mut cur_col);
        let next_b_x = read_u256(nv, &mut cur_col);
        let next_b_y = read_u256(nv, &mut cur_col);
        // if is_double==F::ONE
        {
            fq_equal_transition(
                yield_constr,
                is_not_final * is_double,
                &next_a_x,
                &output.new_x,
            );
            fq_equal_transition(
                yield_constr,
                is_not_final * is_double,
                &next_a_y,
                &output.new_y,
            );
            fq_equal_transition(yield_constr, is_not_final * is_double, &next_b_x, &b_x);
            fq_equal_transition(yield_constr, is_not_final * is_double, &next_b_y, &b_y);
        }
        // if is_add==F::ONE
        {
            fq_equal_transition(yield_constr, is_not_final * is_add, &next_a_x, &a_x);
            fq_equal_transition(yield_constr, is_not_final * is_add, &next_a_y, &a_y);
            fq_equal_transition(
                yield_constr,
                is_not_final * is_add,
                &next_b_x,
                &output.new_x,
            );
            fq_equal_transition(
                yield_constr,
                is_not_final * is_add,
                &next_b_y,
                &output.new_y,
            );
        }
        // else
        {
            let is_double_nor_add = P::ONES - is_double - is_add;
            fq_equal_transition(
                yield_constr,
                is_not_final * is_double_nor_add,
                &next_a_x,
                &a_x,
            );
            fq_equal_transition(
                yield_constr,
                is_not_final * is_double_nor_add,
                &next_a_y,
                &a_y,
            );
            fq_equal_transition(
                yield_constr,
                is_not_final * is_double_nor_add,
                &next_b_x,
                &b_x,
            );
            fq_equal_transition(
                yield_constr,
                is_not_final * is_double_nor_add,
                &next_b_y,
                &b_y,
            );
        }
        eval_flags(yield_constr, lv, nv, c.start_flags_col);
        eval_g1_add(yield_constr, is_add, a_x, a_y, b_x, b_y, &output);
        eval_g1_double(yield_constr, is_double, a_x, a_y, &output);

        // flags, pulses, and lookup
        eval_flags(
            yield_constr,
            vars.local_values,
            vars.next_values,
            c.start_flags_col,
        );
        eval_periodic_pulse(
            yield_constr,
            vars.local_values,
            vars.next_values,
            c.start_flags_col + 1,
            c.start_periodic_pulse_col,
            2 * INPUT_LIMB_BITS,
            2 * INPUT_LIMB_BITS - 2,
        );
        eval_pulse(
            yield_constr,
            vars.local_values,
            vars.next_values,
            c.start_io_pulses_col,
            get_pulse_positions(c.num_io),
        );
        eval_u16_range_check(
            vars,
            yield_constr,
            c.start_lookups_col,
            c.start_range_check_col..c.end_range_check_col,
        );
    }

    fn eval_ext_circuit(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        vars: StarkEvaluationTargets<D>,
        yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    ) {
        let one = builder.one_extension();

        let c = self.constants();
        let is_final_col = c.start_flags_col;
        let is_double_col = c.start_flags_col + 2;
        let is_add_col = c.start_flags_col + 4;
        let start_limbs_col = c.start_flags_col + 6;

        let lv = vars.local_values;
        let nv = vars.next_values;

        let mut cur_col = 0;
        let a_x = read_u256(lv, &mut cur_col);
        let a_y = read_u256(lv, &mut cur_col);
        let b_x = read_u256(lv, &mut cur_col);
        let b_y = read_u256(lv, &mut cur_col);
        let output = read_g1_output(lv, &mut cur_col);
        let is_add = lv[is_add_col];
        let is_double = lv[is_double_col];
        let is_final = lv[is_final_col];
        let is_not_final = builder.sub_extension(one, is_final);

        // constraints for is_final
        let mut sum_is_output = builder.zero_extension();
        for i in (0..2 * self.num_io).skip(1).step_by(2) {
            sum_is_output =
                builder.add_extension(sum_is_output, lv[get_pulse_col(c.start_io_pulses_col, i)]);
        }
        let diff = builder.sub_extension(is_final, sum_is_output);
        yield_constr.constraint(builder, diff);

        // public inputs
        cur_col = 0;
        for i in (0..2 * c.num_io).step_by(2) {
            let g1_exp_io = read_g1_exp_io(vars.public_inputs, &mut cur_col);
            let is_ith_input = lv[get_pulse_col(c.start_io_pulses_col, i)];
            let is_ith_output = lv[get_pulse_col(c.start_io_pulses_col, i + 1)];
            let x_x = u16_columns_to_u32_columns_circuit(builder, a_x);
            let x_y = u16_columns_to_u32_columns_circuit(builder, a_y);
            let b_x = u16_columns_to_u32_columns_circuit(builder, b_x);
            let b_y = u16_columns_to_u32_columns_circuit(builder, b_y);
            vec_equal_circuit(builder, yield_constr, is_ith_input, &g1_exp_io.x[0], &x_x);
            vec_equal_circuit(builder, yield_constr, is_ith_input, &g1_exp_io.x[1], &x_y);
            vec_equal_circuit(
                builder,
                yield_constr,
                is_ith_input,
                &g1_exp_io.offset[0],
                &b_x,
            );
            vec_equal_circuit(
                builder,
                yield_constr,
                is_ith_input,
                &g1_exp_io.offset[1],
                &b_y,
            );
            vec_equal_circuit(
                builder,
                yield_constr,
                is_ith_output,
                &g1_exp_io.output[0],
                &b_x,
            );
            vec_equal_circuit(
                builder,
                yield_constr,
                is_ith_output,
                &g1_exp_io.output[1],
                &b_y,
            );
            let bit = is_add;
            let mut limbs = lv[start_limbs_col..start_limbs_col + NUM_INPUT_LIMBS].to_vec();
            let two = builder.two_extension();
            limbs[0] = builder.mul_add_extension(limbs[0], two, bit);
            vec_equal_circuit(
                builder,
                yield_constr,
                is_ith_input,
                &g1_exp_io.exp_val,
                &limbs,
            );
        }

        // transition
        cur_col = 0;
        let next_a_x = read_u256(nv, &mut cur_col);
        let next_a_y = read_u256(nv, &mut cur_col);
        let next_b_x = read_u256(nv, &mut cur_col);
        let next_b_y = read_u256(nv, &mut cur_col);
        // if is_double==F::ONE
        {
            let is_not_final_and_double = builder.mul_extension(is_not_final, is_double);
            fq_equal_transition_circuit(
                builder,
                yield_constr,
                is_not_final_and_double,
                &next_a_x,
                &output.new_x,
            );
            fq_equal_transition_circuit(
                builder,
                yield_constr,
                is_not_final_and_double,
                &next_a_y,
                &output.new_y,
            );
            fq_equal_transition_circuit(
                builder,
                yield_constr,
                is_not_final_and_double,
                &next_b_x,
                &b_x,
            );
            fq_equal_transition_circuit(
                builder,
                yield_constr,
                is_not_final_and_double,
                &next_b_y,
                &b_y,
            );
        }
        // if is_add==F::ONE
        {
            let is_not_final_and_add = builder.mul_extension(is_not_final, is_add);
            fq_equal_transition_circuit(
                builder,
                yield_constr,
                is_not_final_and_add,
                &next_a_x,
                &a_x,
            );
            fq_equal_transition_circuit(
                builder,
                yield_constr,
                is_not_final_and_add,
                &next_a_y,
                &a_y,
            );
            fq_equal_transition_circuit(
                builder,
                yield_constr,
                is_not_final_and_add,
                &next_b_x,
                &output.new_x,
            );
            fq_equal_transition_circuit(
                builder,
                yield_constr,
                is_not_final_and_add,
                &next_b_y,
                &output.new_y,
            );
        }
        // else
        {
            let is_double_or_add = builder.add_extension(is_double, is_add);
            let is_not_double_nor_add = builder.sub_extension(one, is_double_or_add);
            let is_not_final_and_not_double_nor_add =
                builder.mul_extension(is_not_final, is_not_double_nor_add);
            fq_equal_transition_circuit(
                builder,
                yield_constr,
                is_not_final_and_not_double_nor_add,
                &next_a_x,
                &a_x,
            );
            fq_equal_transition_circuit(
                builder,
                yield_constr,
                is_not_final_and_not_double_nor_add,
                &next_a_y,
                &a_y,
            );
            fq_equal_transition_circuit(
                builder,
                yield_constr,
                is_not_final_and_not_double_nor_add,
                &next_b_x,
                &b_x,
            );
            fq_equal_transition_circuit(
                builder,
                yield_constr,
                is_not_final_and_not_double_nor_add,
                &next_b_y,
                &b_y,
            );
        }
        eval_flags_circuit(builder, yield_constr, lv, nv, c.start_flags_col);
        eval_g1_add_circuit(builder, yield_constr, is_add, a_x, a_y, b_x, b_y, &output);
        eval_g1_double_circuit(builder, yield_constr, is_double, a_x, a_y, &output);

        // flags, pulses, and lookup
        eval_flags_circuit(
            builder,
            yield_constr,
            vars.local_values,
            vars.next_values,
            c.start_flags_col,
        );
        eval_periodic_pulse_circuit(
            builder,
            yield_constr,
            vars.local_values,
            vars.next_values,
            c.start_flags_col + 1,
            c.num_main_cols,
            2 * INPUT_LIMB_BITS,
            2 * INPUT_LIMB_BITS - 2,
        );
        eval_pulse_circuit(
            builder,
            yield_constr,
            vars.local_values,
            vars.next_values,
            c.start_io_pulses_col,
            get_pulse_positions(c.num_io),
        );
        eval_u16_range_check_circuit(
            builder,
            vars,
            yield_constr,
            c.start_lookups_col,
            c.start_range_check_col..c.end_range_check_col,
        );
    }

    fn constraint_degree(&self) -> usize {
        3
    }

    fn permutation_pairs(&self) -> Vec<PermutationPair> {
        let c = self.constants();
        u16_range_check_pairs(
            c.start_lookups_col,
            c.start_range_check_col..c.end_range_check_col,
        )
    }
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use super::*;
    use crate::{
        utils::flags::NUM_INPUT_LIMBS,
        utils::utils::{biguint_to_bits, bits_to_biguint, u32_digits_to_biguint},
    };
    use ark_bn254::{Fr, G1Affine};
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
        prover::prove,
        recursive_verifier::{
            add_virtual_stark_proof_with_pis, set_stark_proof_with_pis_target,
            verify_stark_proof_circuit,
        },
        verifier::verify_stark_proof,
    };

    #[test]
    fn test_biguint_to_bits() {
        let mut rng = rand::thread_rng();
        let exp_val = Fr::rand(&mut rng);
        let exp_bits = biguint_to_bits(&exp_val.into(), 256);
        let recovered: Fr = bits_to_biguint(&exp_bits).into();

        assert!(exp_val == recovered);
    }

    #[test]
    fn test_g1_exp_raw() {
        let num_io = 1 << 7;

        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let mut rng = rand::thread_rng();

        let inputs = (0..num_io)
            .map(|_| {
                let exp_val: [u32; NUM_INPUT_LIMBS] = rand::random();
                let exp_val_fr: Fr = u32_digits_to_biguint(&exp_val).into();
                let x = G1Affine::rand(&mut rng);
                let offset = G1Affine::rand(&mut rng);
                let output: G1Affine = (x * exp_val_fr + offset).into();

                G1ExpIONative {
                    x,
                    offset,
                    exp_val,
                    output,
                }
            })
            .collect_vec();

        let stark = G1ExpStark::<F, D>::new(num_io);
        let inner_config = stark.config();

        println!("start stark proof generation");
        let now = Instant::now();
        let trace = stark.generate_trace(&inputs);
        let pi = stark.generate_public_inputs(&inputs);
        let inner_proof = prove::<F, C, _, D>(
            stark,
            &inner_config,
            trace,
            pi.try_into().unwrap(),
            &mut TimingTree::default(),
        )
        .unwrap();
        verify_stark_proof(stark, inner_proof.clone(), &inner_config).unwrap();
        println!("end stark proof generation: {:?}", now.elapsed());

        let degree_bits = inner_proof.proof.recover_degree_bits(&inner_config);
        dbg!(degree_bits);

        let circuit_config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(circuit_config);
        let mut pw = PartialWitness::new();

        let pt = add_virtual_stark_proof_with_pis(&mut builder, stark, &inner_config, degree_bits);
        set_stark_proof_with_pis_target(&mut pw, &pt, &inner_proof);
        verify_stark_proof_circuit::<F, C, _, D>(&mut builder, stark, &pt, &inner_config);
        let data = builder.build::<C>();

        println!("start plonky2 proof generation");
        let now = Instant::now();
        let _proof = data.prove(pw).unwrap();
        println!("end plonky2 proof generation: {:?}", now.elapsed());
    }
}

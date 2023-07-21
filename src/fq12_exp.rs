//    a       |      b       |   output   |  flags   | rotate_witness |  io_pulses   |     lookups         |
// 12*N_LIMBS |  12*N_LIMBS  | 84*N_LIMBS |   14     |       2        |  1+4*NUM_IO  | 1+6*NUM_RANGE_CHECK |
//<------------------------------------------------>main_cols: 108*N_LIMBS + 14
//<----------------------------------->range_check(start: 0, end: 108*N_LIMBS-12))

const NUM_IO: usize = 16;
const PUBLIC_INPUTS: usize = 37 * NUM_INPUT_LIMBS * NUM_IO;
const COLUMNS: usize = START_LOOKUPS + 1 + 6 * NUM_RANGE_CHECK;

const MAIN_COLS: usize = START_FLAGS + 14;
const START_FLAGS: usize = 108 * N_LIMBS;
const IS_FINAL_COL: usize = START_FLAGS;
const START_IO_PULSES: usize = START_FLAGS + 16;
const START_LOOKUPS: usize = START_IO_PULSES + 1 + 4 * NUM_IO;

const START_RANGE_CHECK: usize = 0;
const NUM_RANGE_CHECK: usize = 24 * N_LIMBS - 3;
const END_RANGE_CHECK: usize = START_RANGE_CHECK + NUM_RANGE_CHECK;

use std::marker::PhantomData;

use ark_bn254::Fq12;
use ark_ff::Field;
use itertools::Itertools;
use plonky2::{
    field::{
        extension::{Extendable, FieldExtension},
        packed::PackedField,
        polynomial::PolynomialValues,
    },
    hash::hash_types::RichField,
    iop::ext_target::ExtensionTarget,
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
    fq12::{
        eval_fq12_mul, eval_fq12_mul_circuit, generate_fq12_mul, read_fq12, read_fq12_output,
        write_fq12, write_fq12_output, Fq12Output,
    },
    instruction::{vec_equal, vec_equal_circuit},
    native::MyFq12,
    pulse::{
        eval_periodic_pulse, eval_periodic_pulse_circuit, eval_pulse, eval_pulse_circuit,
        generate_periodic_pulse_witness, generate_pulse, get_pulse_col,
    },
    range_check::{
        eval_split_u16_range_check, eval_split_u16_range_check_circuit,
        generate_split_u16_range_check, split_u16_range_check_pairs,
    },
    utils::{
        columns_to_fq12, fq_to_columns, fq_to_u32_columns, i64_to_column_positive, read_u32_fq,
        u16_columns_to_u32_columns, u16_columns_to_u32_columns_circuit, u32_digits_to_biguint,
    },
};

pub fn fq12_equal_transition<P: PackedField>(
    yield_constr: &mut ConstraintConsumer<P>,
    filter: P,
    x: [[P; N_LIMBS]; 12],
    y: [[P; N_LIMBS]; 12],
) {
    (0..12).for_each(|i| {
        let x_i = x[i];
        let y_i = y[i];
        x_i.iter()
            .zip(y_i.iter())
            .for_each(|(&x, &y)| yield_constr.constraint_transition(filter * (x - y)));
    });
}

pub fn fq12_equal_transition_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    filter: ExtensionTarget<D>,
    x: [[ExtensionTarget<D>; N_LIMBS]; 12],
    y: [[ExtensionTarget<D>; N_LIMBS]; 12],
) {
    (0..12).for_each(|i| {
        let x_i = x[i];
        let y_i = y[i];
        x_i.iter().zip(y_i.iter()).for_each(|(&x, &y)| {
            let diff = builder.sub_extension(x, y);
            let t = builder.mul_extension(filter, diff);
            yield_constr.constraint_transition(builder, t);
        });
    });
}

pub struct Fq12ExpIONative {
    pub x: Fq12,
    pub offset: Fq12,
    pub exp_val: [u32; NUM_INPUT_LIMBS],
    pub output: Fq12,
}

// 37*NUM_INPUT_LIMBS
pub struct Fq12ExpIO<F> {
    pub x: [[F; NUM_INPUT_LIMBS]; 12],
    pub offset: [[F; NUM_INPUT_LIMBS]; 12],
    pub exp_val: [F; NUM_INPUT_LIMBS],
    pub output: [[F; NUM_INPUT_LIMBS]; 12],
}

pub fn fq12_exp_io_to_columns<F: RichField>(input: &Fq12ExpIONative) -> [F; 37 * NUM_INPUT_LIMBS] {
    let exp_val = input.exp_val.map(F::from_canonical_u32);
    let mut columns = vec![];
    let my_x: MyFq12 = input.x.into();
    let my_offset: MyFq12 = input.offset.into();
    let my_output: MyFq12 = input.output.into();
    my_x.coeffs.iter().for_each(|c| {
        columns.extend(fq_to_u32_columns::<F>(*c));
    });
    my_offset.coeffs.iter().for_each(|c| {
        columns.extend(fq_to_u32_columns::<F>(*c));
    });
    columns.extend(exp_val);
    my_output.coeffs.iter().for_each(|c| {
        columns.extend(fq_to_u32_columns::<F>(*c));
    });
    columns.try_into().unwrap()
}

pub fn read_fq12_exp_io<F: Clone + core::fmt::Debug>(
    lv: &[F],
    cur_col: &mut usize,
) -> Fq12ExpIO<F> {
    let x = [(); 12].map(|_| read_u32_fq(lv, cur_col));
    let offset = [(); 12].map(|_| read_u32_fq(lv, cur_col));
    let exp_val = read_u32_fq(lv, cur_col);
    let output = [(); 12].map(|_| read_u32_fq(lv, cur_col));
    Fq12ExpIO {
        x,
        offset,
        exp_val,
        output,
    }
}

pub fn generate_fq12_exp_first_row<F: RichField>(
    lv: &mut [F],
    start_flag_col: usize,
    x: Fq12,
    offset: Fq12,
) {
    let is_mul_col = start_flag_col + 4;
    let a: MyFq12 = x.into();
    let b: MyFq12 = offset.into();
    let a = a
        .coeffs
        .iter()
        .map(|c| fq_to_columns(*c))
        .map(i64_to_column_positive)
        .collect_vec()
        .try_into()
        .unwrap();
    let b = b
        .coeffs
        .iter()
        .map(|c| fq_to_columns(*c))
        .map(i64_to_column_positive)
        .collect_vec()
        .try_into()
        .unwrap();

    let is_mul = lv[is_mul_col];
    let output = if is_mul == F::ONE {
        generate_fq12_mul(a, b)
    } else {
        Fq12Output::default()
    };
    let mut cur_col = 0;
    write_fq12(lv, a, &mut cur_col);
    write_fq12(lv, b, &mut cur_col);
    write_fq12_output(lv, &output, &mut cur_col);
}

pub fn generate_fq12_exp_next_row<F: RichField>(lv: &[F], nv: &mut [F], start_flag_col: usize) {
    let is_sq_col = start_flag_col + 2;
    let is_mul_col = start_flag_col + 4;

    let mut cur_col = 0;
    let a = read_fq12(lv, &mut cur_col);
    let b = read_fq12(lv, &mut cur_col);
    let output = read_fq12_output(lv, &mut cur_col);
    let is_sq = lv[is_sq_col];
    let is_mul = lv[is_mul_col];
    let next_is_sq = nv[is_sq_col];
    let next_is_mul = nv[is_mul_col];

    // calc next a, b
    let (next_a, next_b) = if is_sq == F::ONE {
        (output.output, b)
    } else if is_mul == F::ONE {
        (a, output.output)
    } else {
        (a, b)
    };

    // calc next output
    let next_output = if next_is_sq == F::ONE {
        generate_fq12_mul(next_a, next_a)
    } else if next_is_mul == F::ONE {
        generate_fq12_mul(next_a, next_b)
    } else {
        Fq12Output::default()
    };
    cur_col = 0;
    write_fq12(nv, next_a, &mut cur_col);
    write_fq12(nv, next_b, &mut cur_col);
    write_fq12_output(nv, &next_output, &mut cur_col);
}

pub fn get_pulse_positions() -> Vec<usize> {
    let num_rows_per_block = 2 * INPUT_LIMB_BITS * NUM_INPUT_LIMBS;
    let mut pulse_positions = vec![];
    for i in 0..NUM_IO {
        pulse_positions.extend(vec![
            i * num_rows_per_block,
            i * num_rows_per_block + num_rows_per_block - 1,
        ]);
    }
    pulse_positions
}

#[derive(Clone, Copy)]
pub struct Fq12ExpStark<F: RichField + Extendable<D>, const D: usize> {
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> Fq12ExpStark<F, D> {
    pub fn new() -> Self {
        Self {
            _phantom: PhantomData,
        }
    }

    pub fn generate_trace_for_one_block(
        &self,
        x: Fq12,
        offset: Fq12,
        exp_val: [u32; NUM_INPUT_LIMBS],
    ) -> Vec<Vec<F>> {
        let num_rows = 2 * INPUT_LIMB_BITS * NUM_INPUT_LIMBS;
        let mut lv = vec![F::ZERO; MAIN_COLS];
        generate_flags_first_row(&mut lv, START_FLAGS, exp_val);
        generate_fq12_exp_first_row(&mut lv, START_FLAGS, x, offset);
        let mut rows = vec![lv.clone()];
        for i in 0..num_rows - 1 {
            let mut nv = vec![F::ZERO; lv.len()];
            generate_flags_next_row(&lv, &mut nv, i, START_FLAGS);
            generate_fq12_exp_next_row(&lv, &mut nv, START_FLAGS);
            rows.push(nv.clone());
            lv = nv;
        }
        let output = {
            let last_row = rows.last().unwrap();
            let mut cur_col = 12 * N_LIMBS;
            let b = read_fq12(last_row, &mut cur_col);
            columns_to_fq12(b)
        };
        // assertion
        let exp_val_biguint = u32_digits_to_biguint(&exp_val);
        let expected: Fq12 = offset * x.pow(&exp_val_biguint.to_u64_digits());
        assert!(output == expected);

        rows
    }

    pub fn generate_trace(&self, inputs: &[Fq12ExpIONative]) -> Vec<PolynomialValues<F>> {
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
        generate_split_u16_range_check(START_RANGE_CHECK..END_RANGE_CHECK, &mut trace_cols);

        trace_cols
            .into_iter()
            .map(|column| PolynomialValues::new(column))
            .collect()
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D> for Fq12ExpStark<F, D> {
    const COLUMNS: usize = COLUMNS;
    const PUBLIC_INPUTS: usize = PUBLIC_INPUTS;

    fn eval_packed_generic<FE, P, const D2: usize>(
        &self,
        vars: StarkEvaluationVars<FE, P, COLUMNS, PUBLIC_INPUTS>,
        yield_constr: &mut ConstraintConsumer<P>,
    ) where
        FE: FieldExtension<D2, BaseField = F>,
        P: PackedField<Scalar = FE>,
    {
        let is_final_col = IS_FINAL_COL;
        let is_sq_col = START_FLAGS + 2;
        let is_mul_col = START_FLAGS + 4;
        let start_limbs_col = START_FLAGS + 6;

        let lv = vars.local_values;
        let nv = vars.next_values;

        let mut cur_col = 0;
        let a = read_fq12(lv, &mut cur_col);
        let b = read_fq12(lv, &mut cur_col);
        let output = read_fq12_output(lv, &mut cur_col);
        let is_mul = lv[is_mul_col];
        let is_sq = lv[is_sq_col];
        let is_final = lv[is_final_col];
        let is_not_final = P::ONES - is_final;

        // constraints for is_final
        let mut sum_is_output = P::ZEROS;
        for i in (0..2 * NUM_IO).skip(1).step_by(2) {
            sum_is_output = sum_is_output + lv[get_pulse_col(START_IO_PULSES, i)];
        }
        yield_constr.constraint(is_final - sum_is_output);

        // public inputs
        let pi: &[P] = &vars.public_inputs.map(|x| x.into());
        cur_col = 0;
        for i in (0..2 * NUM_IO).step_by(2) {
            let fq12_exp_io = read_fq12_exp_io(pi, &mut cur_col);
            let is_ith_input = lv[get_pulse_col(START_IO_PULSES, i)];
            let is_ith_output = lv[get_pulse_col(START_IO_PULSES, i + 1)];
            let x = a.map(u16_columns_to_u32_columns);
            let b = b.map(u16_columns_to_u32_columns);
            (0..12).for_each(|i| {
                vec_equal(yield_constr, is_ith_input, &fq12_exp_io.x[i], &x[i]);
                vec_equal(yield_constr, is_ith_input, &fq12_exp_io.offset[i], &b[i]);
                vec_equal(yield_constr, is_ith_output, &fq12_exp_io.output[i], &b[i]);
            });
            let bit = is_mul;
            let mut limbs = lv[start_limbs_col..start_limbs_col + NUM_INPUT_LIMBS].to_vec();
            limbs[0] = limbs[0] * P::Scalar::TWO + bit;
            vec_equal(yield_constr, is_ith_input, &fq12_exp_io.exp_val, &limbs);
        }

        // transition
        cur_col = 0;
        let next_a = read_fq12(nv, &mut cur_col);
        let next_b = read_fq12(nv, &mut cur_col);
        // if is_double==F::ONE
        {
            fq12_equal_transition(yield_constr, is_not_final * is_sq, next_a, output.output);
            fq12_equal_transition(yield_constr, is_not_final * is_sq, next_b, b);
        }
        // if is_add==F::ONE
        {
            fq12_equal_transition(yield_constr, is_not_final * is_mul, next_a, a);
            fq12_equal_transition(yield_constr, is_not_final * is_mul, next_b, output.output);
        }
        // else
        {
            let is_sq_nor_mul = P::ONES - is_sq - is_mul;
            fq12_equal_transition(yield_constr, is_not_final * is_sq_nor_mul, next_a, a);
            fq12_equal_transition(yield_constr, is_not_final * is_sq_nor_mul, next_b, b);
        }
        eval_flags(yield_constr, lv, nv, START_FLAGS);
        eval_fq12_mul(yield_constr, is_sq, a, a, &output);
        eval_fq12_mul(yield_constr, is_mul, a, b, &output);

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
        eval_split_u16_range_check(
            vars,
            yield_constr,
            START_LOOKUPS,
            START_RANGE_CHECK..END_RANGE_CHECK,
        );
    }

    fn eval_ext_circuit(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        vars: StarkEvaluationTargets<D, COLUMNS, PUBLIC_INPUTS>,
        yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    ) {
        let one = builder.one_extension();
        let is_final_col = IS_FINAL_COL;
        let is_sq_col = START_FLAGS + 2;
        let is_mul_col = START_FLAGS + 4;
        let start_limbs_col = START_FLAGS + 6;

        let lv = vars.local_values;
        let nv = vars.next_values;

        let mut cur_col = 0;
        let a = read_fq12(lv, &mut cur_col);
        let b = read_fq12(lv, &mut cur_col);
        let output = read_fq12_output(lv, &mut cur_col);
        let is_mul = lv[is_mul_col];
        let is_sq = lv[is_sq_col];
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
            let fq12_exp_io = read_fq12_exp_io(vars.public_inputs, &mut cur_col);
            let is_ith_input = lv[get_pulse_col(START_IO_PULSES, i)];
            let is_ith_output = lv[get_pulse_col(START_IO_PULSES, i + 1)];
            let x = a.map(|x| u16_columns_to_u32_columns_circuit(builder, x));
            let b = b.map(|x| u16_columns_to_u32_columns_circuit(builder, x));
            (0..12).for_each(|i| {
                vec_equal_circuit(
                    builder,
                    yield_constr,
                    is_ith_input,
                    &fq12_exp_io.x[i],
                    &x[i],
                );
                vec_equal_circuit(
                    builder,
                    yield_constr,
                    is_ith_input,
                    &fq12_exp_io.offset[i],
                    &b[i],
                );
                vec_equal_circuit(
                    builder,
                    yield_constr,
                    is_ith_output,
                    &fq12_exp_io.output[i],
                    &b[i],
                );
            });
            let bit = is_mul;
            let mut limbs = lv[start_limbs_col..start_limbs_col + NUM_INPUT_LIMBS].to_vec();
            let two = builder.two_extension();
            limbs[0] = builder.mul_add_extension(limbs[0], two, bit);
            vec_equal_circuit(
                builder,
                yield_constr,
                is_ith_input,
                &fq12_exp_io.exp_val,
                &limbs,
            );
        }

        // transition
        cur_col = 0;
        let next_a = read_fq12(nv, &mut cur_col);
        let next_b = read_fq12(nv, &mut cur_col);
        // if is_sq==F::ONE
        {
            let is_not_final_and_sq = builder.mul_extension(is_not_final, is_sq);
            fq12_equal_transition_circuit(
                builder,
                yield_constr,
                is_not_final_and_sq,
                next_a,
                output.output,
            );
            fq12_equal_transition_circuit(builder, yield_constr, is_not_final_and_sq, next_b, b);
        }
        // if is_mul==F::ONE
        {
            let is_not_final_and_mul = builder.mul_extension(is_not_final, is_mul);
            fq12_equal_transition_circuit(builder, yield_constr, is_not_final_and_mul, next_a, a);
            fq12_equal_transition_circuit(
                builder,
                yield_constr,
                is_not_final_and_mul,
                next_b,
                output.output,
            );
        }
        // else
        {
            let is_sq_or_mul = builder.add_extension(is_sq, is_mul);
            let is_not_sq_nor_mul = builder.sub_extension(one, is_sq_or_mul);
            let is_not_final_and_not_sq_nor_mu =
                builder.mul_extension(is_not_final, is_not_sq_nor_mul);
            fq12_equal_transition_circuit(
                builder,
                yield_constr,
                is_not_final_and_not_sq_nor_mu,
                next_a,
                a,
            );
            fq12_equal_transition_circuit(
                builder,
                yield_constr,
                is_not_final_and_not_sq_nor_mu,
                next_b,
                b,
            );
        }
        eval_flags_circuit(builder, yield_constr, lv, nv, START_FLAGS);
        eval_fq12_mul_circuit(builder, yield_constr, is_sq, a, a, &output);
        eval_fq12_mul_circuit(builder, yield_constr, is_mul, a, b, &output);

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
        eval_split_u16_range_check_circuit(
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
        split_u16_range_check_pairs(START_LOOKUPS, START_RANGE_CHECK..END_RANGE_CHECK)
    }
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use crate::fq12_exp::{fq12_exp_io_to_columns, Fq12ExpIONative, Fq12ExpStark, NUM_IO};
    use ark_bn254::{Fq12, Fr};
    use ark_ff::Field;
    use ark_std::UniformRand;
    use itertools::Itertools;
    use num_bigint::BigUint;
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
    fn test_fq12_exp() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let mut rng = rand::thread_rng();

        let inputs = (0..NUM_IO)
            .map(|_| {
                let exp_val_fr: Fr = Fr::rand(&mut rng);
                let x = Fq12::rand(&mut rng);
                let offset = Fq12::rand(&mut rng);
                let exp_val_biguint: BigUint = exp_val_fr.into();
                let output: Fq12 = offset * x.pow(&exp_val_biguint.to_u64_digits());
                Fq12ExpIONative {
                    x,
                    offset,
                    exp_val: exp_val_biguint.to_u32_digits().try_into().unwrap(),
                    output,
                }
            })
            .collect_vec();
        let pi = inputs
            .iter()
            .flat_map(|input| fq12_exp_io_to_columns::<F>(input))
            .collect_vec();

        type S = Fq12ExpStark<F, D>;
        let inner_config = StarkConfig::standard_fast_config();
        let stark = S::new();

        println!("start stark proof generation");
        let now = Instant::now();
        let trace = stark.generate_trace(&inputs);
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

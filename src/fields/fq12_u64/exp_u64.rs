//    a       |      b       |   output   |  flag  |  io_pulses     |     lookups         |
// 12*N_LIMBS |  12*N_LIMBS  | 84*N_LIMBS |   6    |  1+4*c.num_io  | 1+6*NUM_RANGE_CHECK |
//<------------------------------------------------->main_cols: 108*N_LIMBS + 6
//                           <--------->range_check(start: 24*N_LIMBS, end: 108*N_LIMBS-12))

pub struct ExpU64StarkConstants {
    pub num_columns: usize,
    pub num_public_inputs: usize,
    pub num_main_cols: usize,
    pub num_io: usize,
    pub start_flags_col: usize,
    pub start_io_pulses_col: usize,
    pub start_lookups_col: usize,
    pub start_range_check_col: usize,
    pub end_range_check_col: usize,
    pub num_range_check_cols: usize,
}

fn constants(num_io: usize) -> ExpU64StarkConstants {
    let start_flags_col = 108 * N_LIMBS;
    let num_main_cols = start_flags_col + NUM_FLAGS_U64_COLS;

    let start_io_pulses_col = num_main_cols;
    let start_lookups_col = start_io_pulses_col + 1 + 4 * num_io;

    let start_range_check_col = 24 * N_LIMBS;
    let num_range_check_cols = 84 * N_LIMBS - 12;
    let end_range_check_col = start_range_check_col + num_range_check_cols;

    let num_columns = start_lookups_col + 1 + 6 * num_range_check_cols;
    let num_public_inputs = FQ12_EXP_U64_IO_LEN * num_io;

    ExpU64StarkConstants {
        num_columns,
        num_public_inputs,
        num_main_cols,
        num_io,
        start_flags_col,
        start_io_pulses_col,
        start_lookups_col,
        start_range_check_col,
        end_range_check_col,
        num_range_check_cols,
    }
}

use std::marker::PhantomData;

use super::flags_u64::{generate_flags_u64_first_row, generate_flags_u64_next_row};
use crate::{
    constants::N_LIMBS,
    fields::fq12::mul::{
        eval_fq12_mul, eval_fq12_mul_circuit, generate_fq12_mul, read_fq12, read_fq12_output,
        write_fq12, write_fq12_output, Fq12Output,
    },
    utils::equals::{fq12_equal_transition, fq12_equal_transition_circuit},
    utils::equals::{vec_equal, vec_equal_circuit},
    utils::pulse::{eval_pulse, eval_pulse_circuit, generate_pulse, get_pulse_col},
    utils::range_check::{
        eval_split_u16_range_check, eval_split_u16_range_check_circuit,
        generate_split_u16_range_check, split_u16_range_check_pairs,
    },
    utils::utils::{
        columns_to_fq12, fq_to_columns, fq_to_u16_columns, i64_to_column_positive, read_u16_fq,
    },
};
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
    plonk::circuit_builder::CircuitBuilder,
    util::transpose,
};

use plonky2_bn254::fields::native::MyFq12;
use starky::{
    config::StarkConfig,
    constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer},
    permutation::PermutationPair,
    stark::Stark,
    vars::{StarkEvaluationTargets, StarkEvaluationVars},
};

use super::flags_u64::{eval_flags_u64, eval_flags_u64_circuit, NUM_FLAGS_U64_COLS};

pub struct Fq12ExpU64IONative {
    pub x: Fq12,
    pub offset: Fq12,
    pub exp_val: u64,
    pub output: Fq12,
}

pub const FQ12_EXP_U64_IO_LEN: usize = 36 * N_LIMBS + 1;

// 36*N_LIMBS + NUM_INPUT_LIMBS
pub struct Fq12ExpU64IO<F> {
    pub x: [[F; N_LIMBS]; 12],
    pub offset: [[F; N_LIMBS]; 12],
    pub exp_val: F,
    pub output: [[F; N_LIMBS]; 12],
}

pub fn fq12_exp_u64_io_to_columns<F: RichField>(
    input: &Fq12ExpU64IONative,
) -> [F; FQ12_EXP_U64_IO_LEN] {
    let exp_val = F::from_canonical_u64(input.exp_val);
    let mut columns = vec![];
    let my_x: MyFq12 = input.x.into();
    let my_offset: MyFq12 = input.offset.into();
    let my_output: MyFq12 = input.output.into();
    my_x.coeffs.iter().for_each(|c| {
        columns.extend(fq_to_u16_columns::<F>(*c));
    });
    my_offset.coeffs.iter().for_each(|c| {
        columns.extend(fq_to_u16_columns::<F>(*c));
    });
    columns.push(exp_val);
    my_output.coeffs.iter().for_each(|c| {
        columns.extend(fq_to_u16_columns::<F>(*c));
    });
    columns.try_into().unwrap()
}

pub fn read_fq12_exp_u64_io<F: Clone + core::fmt::Debug>(
    lv: &[F],
    cur_col: &mut usize,
) -> Fq12ExpU64IO<F> {
    let x = [(); 12].map(|_| read_u16_fq(lv, cur_col));
    let offset = [(); 12].map(|_| read_u16_fq(lv, cur_col));
    let exp_val = lv[*cur_col].clone();
    *cur_col += 1;
    let output = [(); 12].map(|_| read_u16_fq(lv, cur_col));
    Fq12ExpU64IO {
        x,
        offset,
        exp_val,
        output,
    }
}

pub fn generate_fq12_exp_u64_first_row<F: RichField>(
    lv: &mut [F],
    start_flag_col: usize,
    x: Fq12,
    offset: Fq12,
) {
    let is_mul_col = start_flag_col + 3;
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

pub fn generate_fq12_exp_u64_next_row<F: RichField>(lv: &[F], nv: &mut [F], start_flag_col: usize) {
    let is_sq_col = start_flag_col + 1;
    let is_mul_col = start_flag_col + 3;

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

pub fn get_pulse_u64_positions(num_io: usize) -> Vec<usize> {
    let num_rows_per_block = 2 * 64;
    let mut pulse_positions = vec![];
    for i in 0..num_io {
        pulse_positions.extend(vec![
            i * num_rows_per_block,
            i * num_rows_per_block + num_rows_per_block - 1,
        ]);
    }
    pulse_positions
}

#[derive(Clone, Copy)]
pub struct Fq12ExpU64Stark<F: RichField + Extendable<D>, const D: usize> {
    pub num_io: usize,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> Fq12ExpU64Stark<F, D> {
    pub fn new(num_io: usize) -> Self {
        Self {
            num_io,
            _phantom: PhantomData,
        }
    }

    pub fn constants(&self) -> ExpU64StarkConstants {
        constants(self.num_io)
    }

    pub fn config(&self) -> StarkConfig {
        let c = self.constants();
        StarkConfig::standard_fast_config(c.num_columns, c.num_public_inputs)
    }

    pub fn generate_trace_for_one_block(&self, x: Fq12, offset: Fq12, exp_val: u64) -> Vec<Vec<F>> {
        let c = self.constants();
        let num_rows = 2 * 64;
        let mut lv = vec![F::ZERO; c.num_main_cols];
        generate_flags_u64_first_row(&mut lv, c.start_flags_col, exp_val);
        generate_fq12_exp_u64_first_row(&mut lv, c.start_flags_col, x, offset);
        let mut rows = vec![lv.clone()];
        for i in 0..num_rows - 1 {
            let mut nv = vec![F::ZERO; lv.len()];
            generate_flags_u64_next_row(&lv, &mut nv, i, c.start_flags_col);
            generate_fq12_exp_u64_next_row(&lv, &mut nv, c.start_flags_col);
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
        let expected: Fq12 = offset * x.pow(&[exp_val]);
        assert!(output == expected);

        rows
    }

    pub fn generate_trace(&self, inputs: &[Fq12ExpU64IONative]) -> Vec<PolynomialValues<F>> {
        let c = self.constants();
        assert!(inputs.len() == c.num_io);

        let mut rows = vec![];
        for input in inputs {
            let row = self.generate_trace_for_one_block(input.x, input.offset, input.exp_val);
            rows.extend(row);
        }
        let mut trace_cols = transpose(&rows.iter().map(|v| v.to_vec()).collect_vec());

        generate_pulse(&mut trace_cols, get_pulse_u64_positions(c.num_io));
        generate_split_u16_range_check(
            c.start_range_check_col..c.end_range_check_col,
            &mut trace_cols,
        );

        trace_cols
            .into_iter()
            .map(|column| PolynomialValues::new(column))
            .collect()
    }

    pub fn generate_public_inputs(&self, inputs: &[Fq12ExpU64IONative]) -> Vec<F> {
        inputs
            .iter()
            .flat_map(|input| fq12_exp_u64_io_to_columns::<F>(input))
            .collect_vec()
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D> for Fq12ExpU64Stark<F, D> {
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
        let is_sq_col = c.start_flags_col + 1;
        let is_mul_col = c.start_flags_col + 3;
        let exp_val_col = c.start_flags_col + 5;

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
        for i in (0..2 * c.num_io).skip(1).step_by(2) {
            sum_is_output = sum_is_output + lv[get_pulse_col(c.start_io_pulses_col, i)];
        }
        yield_constr.constraint(is_final - sum_is_output);

        // public inputs
        let pi: &[P] = &vars.public_inputs.iter().map(|&x| x.into()).collect_vec();
        cur_col = 0;
        for i in (0..2 * c.num_io).step_by(2) {
            let fq12_exp_io = read_fq12_exp_u64_io(pi, &mut cur_col);
            let is_ith_input = lv[get_pulse_col(c.start_io_pulses_col, i)];
            let is_ith_output = lv[get_pulse_col(c.start_io_pulses_col, i + 1)];
            (0..12).for_each(|i| {
                vec_equal(yield_constr, is_ith_input, &fq12_exp_io.x[i], &a[i]);
                vec_equal(yield_constr, is_ith_input, &fq12_exp_io.offset[i], &b[i]);
                vec_equal(yield_constr, is_ith_output, &fq12_exp_io.output[i], &b[i]);
            });
            let bit = is_mul;
            let recovered = lv[exp_val_col] * P::Scalar::TWO + bit;
            yield_constr.constraint(is_ith_input * (fq12_exp_io.exp_val - recovered));
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
        eval_flags_u64(yield_constr, lv, nv, c.start_flags_col);
        eval_fq12_mul(yield_constr, is_sq, a, a, &output);
        eval_fq12_mul(yield_constr, is_mul, a, b, &output);

        // flags and lookup
        eval_flags_u64(
            yield_constr,
            vars.local_values,
            vars.next_values,
            c.start_flags_col,
        );
        eval_pulse(
            yield_constr,
            vars.local_values,
            vars.next_values,
            c.start_io_pulses_col,
            get_pulse_u64_positions(c.num_io),
        );
        eval_split_u16_range_check(
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
        let is_sq_col = c.start_flags_col + 1;
        let is_mul_col = c.start_flags_col + 3;
        let exp_val_col = c.start_flags_col + 5;

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
        for i in (0..2 * c.num_io).skip(1).step_by(2) {
            sum_is_output =
                builder.add_extension(sum_is_output, lv[get_pulse_col(c.start_io_pulses_col, i)]);
        }
        let diff = builder.sub_extension(is_final, sum_is_output);
        yield_constr.constraint(builder, diff);

        // public inputs
        cur_col = 0;
        for i in (0..2 * c.num_io).step_by(2) {
            let fq12_exp_io = read_fq12_exp_u64_io(vars.public_inputs, &mut cur_col);
            let is_ith_input = lv[get_pulse_col(c.start_io_pulses_col, i)];
            let is_ith_output = lv[get_pulse_col(c.start_io_pulses_col, i + 1)];
            (0..12).for_each(|i| {
                vec_equal_circuit(
                    builder,
                    yield_constr,
                    is_ith_input,
                    &fq12_exp_io.x[i],
                    &a[i],
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
            let two = builder.two_extension();
            let recovered = builder.mul_add_extension(lv[exp_val_col], two, bit);
            let diff = builder.sub_extension(fq12_exp_io.exp_val, recovered);
            let t = builder.mul_extension(is_ith_input, diff);
            yield_constr.constraint(builder, t);
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
        eval_flags_u64_circuit(builder, yield_constr, lv, nv, c.start_flags_col);
        eval_fq12_mul_circuit(builder, yield_constr, is_sq, a, a, &output);
        eval_fq12_mul_circuit(builder, yield_constr, is_mul, a, b, &output);

        // flags, pulses, and lookup
        eval_flags_u64_circuit(
            builder,
            yield_constr,
            vars.local_values,
            vars.next_values,
            c.start_flags_col,
        );
        eval_pulse_circuit(
            builder,
            yield_constr,
            vars.local_values,
            vars.next_values,
            c.start_io_pulses_col,
            get_pulse_u64_positions(c.num_io),
        );
        eval_split_u16_range_check_circuit(
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
        split_u16_range_check_pairs(
            c.start_lookups_col,
            c.start_range_check_col..c.end_range_check_col,
        )
    }
}

mod tests {
    use std::time::Instant;

    use crate::fields::fq12_u64::exp_u64::{Fq12ExpU64IONative, Fq12ExpU64Stark};
    use ark_bn254::Fq12;
    use ark_ff::Field;
    use ark_std::UniformRand;
    use plonky2::{
        field::types::{PrimeField64, Sample},
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
    fn test_fq12_exp_u64_raw() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let mut rng = rand::thread_rng();

        let num_io = 1 << 4;
        let inputs = (0..num_io)
            .map(|_| {
                let exp_val_f = F::sample(&mut rng);
                let x = Fq12::rand(&mut rng);
                let offset = Fq12::rand(&mut rng);
                let exp_val = exp_val_f.to_canonical_u64();
                let output: Fq12 = offset * x.pow(&[exp_val]);
                Fq12ExpU64IONative {
                    x,
                    offset,
                    exp_val,
                    output,
                }
            })
            .collect::<Vec<_>>();

        type S = Fq12ExpU64Stark<F, D>;
        let stark = S::new(num_io);
        let inner_config = stark.config();

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

        dbg!(degree_bits);
        println!("start plonky2 proof generation");
        let now = Instant::now();
        let _proof = data.prove(pw).unwrap();
        println!("end plonky2 proof generation: {:?}", now.elapsed());
    }
}

//    a      |      b      |   output   |  flags   | rotate_witness |  io_pulses   |     lookups        |
// 2*N_LIMBS |  2*N_LIMBS  | 20*N_LIMBS |   14     |       2        |  1+4*NUM_IO  | 1+2*(20*N_LIMBS-3) |
//<------------------------------------------------>main_cols: 24*N_LIMBS + 14
//                          <--------->range_check(start: 4*N_LIMBS, end: 24*N_LIMBS-3))

const NUM_IO: usize = 1 << 7;
const PUBLIC_INPUTS: usize = 0;
const COLUMNS: usize = START_LOOKUPS + 1 + 2 * NUM_RANGE_CHECK;

const MAIN_COLS: usize = 24 * N_LIMBS + 14;
const START_FLAGS: usize = 24 * N_LIMBS;
const IS_FINAL_COL: usize = START_FLAGS;
const START_IO_PULSES: usize = START_FLAGS + 16;
const START_LOOKUPS: usize = START_IO_PULSES + 1 + 4 * NUM_IO;

const START_RANGE_CHECK: usize = 4 * N_LIMBS;
const NUM_RANGE_CHECK: usize = 20 * N_LIMBS - 3;
const END_RANGE_CHECK: usize = START_RANGE_CHECK + NUM_RANGE_CHECK;

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
    g1::{
        eval_g1_add, eval_g1_add_circuit, eval_g1_double, eval_g1_double_circuit, generate_g1_add,
        generate_g1_double, read_g1output, write_g1output, G1Output,
    },
    instruction::{fq_equal_transition, fq_equal_transition_circuit},
    modular::{read_u256, write_u256},
    pulse::{
        eval_periodic_pulse, eval_periodic_pulse_circuit, eval_pulse, eval_pulse_circuit,
        generate_periodic_pulse_witness, generate_pulse,
    },
    range_check::{
        eval_u16_range_check, eval_u16_range_check_circuit, generate_u16_range_check,
        u16_range_check_pairs,
    },
    utils::{columns_to_fq, fq_to_columns, u32_digits_to_biguint},
};

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
    write_g1output(lv, &output, &mut cur_col);
}

pub fn generate_g1_exp_next_row<F: RichField>(lv: &[F], nv: &mut [F], start_flag_col: usize) {
    let is_double_col = start_flag_col + 2;
    let is_add_col = start_flag_col + 4;

    let mut cur_col = 0;
    let a_x = read_u256(lv, &mut cur_col);
    let a_y = read_u256(lv, &mut cur_col);
    let b_x = read_u256(lv, &mut cur_col);
    let b_y = read_u256(lv, &mut cur_col);
    let output = read_g1output(lv, &mut cur_col);
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
    write_g1output(nv, &next_output, &mut cur_col);
}

#[derive(Clone, Copy)]
pub struct G1ExpStark<F: RichField + Extendable<D>, const D: usize> {
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> G1ExpStark<F, D> {
    pub fn new() -> Self {
        Self {
            _phantom: PhantomData,
        }
    }

    pub fn generate_trace_for_one_block(
        &self,
        x: G1Affine,
        offset: G1Affine,
        exp_val: [u32; NUM_INPUT_LIMBS],
    ) -> (G1Affine, Vec<Vec<F>>) {
        let num_rows = 2 * INPUT_LIMB_BITS * NUM_INPUT_LIMBS;
        let mut lv = vec![F::ZERO; MAIN_COLS];
        generate_flags_first_row(&mut lv, START_FLAGS, exp_val);
        generate_g1_exp_first_row(&mut lv, START_FLAGS, x, offset);
        let mut rows = vec![lv.clone()];
        for i in 0..num_rows - 1 {
            let mut nv = vec![F::ZERO; lv.len()];
            generate_flags_next_row(&lv, &mut nv, i, START_FLAGS);
            generate_g1_exp_next_row(&lv, &mut nv, START_FLAGS);
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

        (output, rows)
    }

    pub fn generate_trace(
        &self,
        offset: G1Affine,
        inputs: Vec<(G1Affine, [u32; NUM_INPUT_LIMBS])>,
    ) -> Vec<PolynomialValues<F>> {
        assert!(inputs.len() == NUM_IO);

        let mut rows = vec![];
        let mut offset = offset;
        for input in inputs.clone() {
            let (output, row) = self.generate_trace_for_one_block(input.0, offset, input.1);
            offset = output;
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
}

impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D> for G1ExpStark<F, D> {
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
        let is_double_col = START_FLAGS + 2;
        let is_add_col = START_FLAGS + 4;

        let lv = vars.local_values;
        let nv = vars.next_values;

        let mut cur_col = 0;
        let a_x = read_u256(lv, &mut cur_col);
        let a_y = read_u256(lv, &mut cur_col);
        let b_x = read_u256(lv, &mut cur_col);
        let b_y = read_u256(lv, &mut cur_col);
        let output = read_g1output(lv, &mut cur_col);
        let is_add = lv[is_add_col];
        let is_double = lv[is_double_col];
        let is_final = lv[is_final_col];
        let is_not_final = P::ONES - is_final;

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
        eval_flags(yield_constr, lv, nv, START_FLAGS);
        eval_g1_add(yield_constr, is_add, a_x, a_y, b_x, b_y, &output);
        eval_g1_double(yield_constr, is_double, a_x, a_y, &output);

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
        vars: StarkEvaluationTargets<D, COLUMNS, PUBLIC_INPUTS>,
        yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    ) {
        let one = builder.one_extension();
        let is_final_col = IS_FINAL_COL;
        let is_double_col = START_FLAGS + 2;
        let is_add_col = START_FLAGS + 4;

        let lv = vars.local_values;
        let nv = vars.next_values;

        let mut cur_col = 0;
        let a_x = read_u256(lv, &mut cur_col);
        let a_y = read_u256(lv, &mut cur_col);
        let b_x = read_u256(lv, &mut cur_col);
        let b_y = read_u256(lv, &mut cur_col);
        let output = read_g1output(lv, &mut cur_col);
        let is_add = lv[is_add_col];
        let is_double = lv[is_double_col];
        let is_final = lv[is_final_col];
        let is_not_final = builder.sub_extension(one, is_final);

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
        eval_flags_circuit(builder, yield_constr, lv, nv, START_FLAGS);
        eval_g1_add_circuit(builder, yield_constr, is_add, a_x, a_y, b_x, b_y, &output);
        eval_g1_double_circuit(builder, yield_constr, is_double, a_x, a_y, &output);

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
        constants::BITS_LEN,
        g1_exp::{G1ExpStark, NUM_IO},
        utils::{biguint_to_bits, bits_to_biguint},
    };
    use ark_bn254::{Fr, G1Affine};
    use ark_std::UniformRand;
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
    fn test_biguint_to_bits() {
        let mut rng = rand::thread_rng();
        let exp_val = Fr::rand(&mut rng);
        let exp_bits = biguint_to_bits(&exp_val.into(), BITS_LEN);
        let recovered: Fr = bits_to_biguint(&exp_bits).into();

        assert!(exp_val == recovered);
    }

    #[test]
    fn test_new_g1_exp() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let mut rng = rand::thread_rng();
        let exp_val: Fr = Fr::rand(&mut rng);
        let exp_val_biguint: BigUint = exp_val.into();
        let x = G1Affine::rand(&mut rng);
        let offset = G1Affine::rand(&mut rng);

        type S = G1ExpStark<F, D>;
        let inner_config = StarkConfig::standard_fast_config();
        let stark = S::new();
        let trace = stark.generate_trace(
            offset,
            vec![(x, exp_val_biguint.to_u32_digits().try_into().unwrap()); NUM_IO],
        );

        println!("start stark proof generation");
        let now = Instant::now();
        let inner_proof =
            prove::<F, C, S, D>(stark, &inner_config, trace, [], &mut TimingTree::default())
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

        // dbg!(degree_bits);
    }
}

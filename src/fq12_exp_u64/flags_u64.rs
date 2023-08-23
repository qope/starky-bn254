// generate flags
// in the case of val0 = 1101, val1 = 1011
//| f | a | b | b'| bit | val0
//----------------------------
//| 0 | 0 | 1 | 1 |  1  | 101  <- public input (1 + 2*101 = val0, val1)
//| 0 | 1 | 0 | 0 |  1  | 101  <- split
//| 0 | 0 | 1 | 1 |  1  | 01
//| 0 | 1 | 0 | 0 |  1  | 01   <- split
//| 0 | 0 | 1 | 0 |  0  | 1
//| 0 | 1 | 0 | 0 |  0  | 1    <- split
//| 0 | 0 | 1 | 1 |  1  | 0
//| 1 | 1 | 0 | 0 |  1  | 0    <- split (<- output)

// f = is_final
// b' = filetered_bit (= b * bit)

// overall, we need 2*bits_len rows.
// split vals at r = 2*i + 1
// we need 1 limb col

pub const NUM_FLAGS_U64_COLS: usize = 6;

use plonky2::{
    field::packed::PackedField,
    field::{extension::Extendable, types::Field},
    hash::hash_types::RichField,
    iop::ext_target::ExtensionTarget,
    plonk::circuit_builder::CircuitBuilder,
};
use starky::constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer};

// generate flags for the first row
// 6 cols are generated
pub fn generate_flags_u64_first_row<F: RichField>(
    lv: &mut [F],
    start_flag_col: usize,
    exp_val: u64,
) {
    let is_final_col = start_flag_col;
    let a_col = start_flag_col + 1;
    let b_col = start_flag_col + 2;
    let filtered_bit_col = start_flag_col + 3;
    let bit_col = start_flag_col + 4;
    let val_col = start_flag_col + 5;

    let first_bit = exp_val % 2;
    let rest = (exp_val - first_bit) / 2;

    lv[is_final_col] = F::ZERO;
    lv[a_col] = F::ZERO;
    lv[b_col] = F::ONE;
    lv[filtered_bit_col] = F::from_canonical_u64(first_bit);
    lv[bit_col] = F::from_canonical_u64(first_bit);
    lv[val_col] = F::from_canonical_u64(rest);
}

pub fn generate_flags_u64_next_row<F: RichField>(
    lv: &[F],
    nv: &mut [F],
    cur_row: usize,
    start_flag_col: usize,
) {
    let is_final_col = start_flag_col;
    let a_col = start_flag_col + 1;
    let b_col = start_flag_col + 2;
    let filtered_bit_col = start_flag_col + 3;
    let bit_col = start_flag_col + 4;
    let val_col = start_flag_col + 5;

    nv[a_col] = F::ONE - lv[a_col];
    nv[b_col] = F::ONE - lv[b_col];

    let num_rows = 2 * 64;
    if cur_row == num_rows - 2 {
        nv[is_final_col] = F::ONE;
    } else {
        nv[is_final_col] = F::ZERO;
    }

    if lv[a_col] == F::ONE {
        // split
        let first_limb = lv[val_col].to_canonical_u64();
        let next_bit = first_limb % 2;
        let next_first_limb = (first_limb - next_bit) / 2;
        nv[bit_col] = F::from_canonical_u64(next_bit);
        nv[val_col] = F::from_canonical_u64(next_first_limb);
    } else {
        // no split
        nv[bit_col] = lv[bit_col];
        nv[val_col] = lv[val_col];
    }

    nv[filtered_bit_col] = nv[bit_col] * nv[b_col];
}

pub fn eval_flags_u64<P: PackedField>(
    yield_constr: &mut ConstraintConsumer<P>,
    lv: &[P],
    nv: &[P],
    start_flag_col: usize,
) {
    let is_final_col = start_flag_col;
    let a_col = start_flag_col + 1;
    let b_col = start_flag_col + 2;
    let filtered_bit_col = start_flag_col + 3;
    let bit_col = start_flag_col + 4;
    let val_col = start_flag_col + 5;

    // initial condition
    yield_constr.constraint_first_row(lv[a_col]);
    yield_constr.constraint_first_row(lv[b_col] - P::ONES);

    // constraint
    // bit_col is should be 0 or 1.
    let bit = lv[bit_col];
    yield_constr.constraint(bit * bit - bit);
    // filtered_col is multiplication of bit_col and b_col.
    yield_constr.constraint(bit * lv[b_col] - lv[filtered_bit_col]);

    // transition
    yield_constr.constraint_transition(lv[a_col] + nv[a_col] - P::ONES);
    yield_constr.constraint_transition(lv[b_col] + nv[b_col] - P::ONES);
    // split: first_limb = next_bit + 2*next_first_limb
    let first_limb = lv[val_col];
    let next_first_limb = nv[val_col];
    let next_bit = nv[bit_col];
    let is_split = lv[a_col];
    let is_final = lv[is_final_col];
    let is_not_final = P::ONES - is_final;
    yield_constr.constraint_transition(
        is_not_final * is_split * (first_limb - P::Scalar::TWO * next_first_limb - next_bit),
    );
    // not split: first_limb = next_first_limb and next_bit = bit
    let is_not_split = P::ONES - is_split;
    let is_not_final = P::ONES - is_final;
    yield_constr.constraint_transition(is_not_split * (next_bit - bit));
    yield_constr
        .constraint_transition(is_not_final * is_not_split * (first_limb - next_first_limb));
}

pub fn eval_flags_u64_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    lv: &[ExtensionTarget<D>],
    nv: &[ExtensionTarget<D>],
    start_flag_col: usize,
) {
    let one = builder.one_extension();
    let is_final_col = start_flag_col;
    let a_col = start_flag_col + 1;
    let b_col = start_flag_col + 2;
    let filtered_bit_col = start_flag_col + 3;
    let bit_col = start_flag_col + 4;
    let val_col = start_flag_col + 5;

    // initial condition
    yield_constr.constraint_first_row(builder, lv[a_col]);
    let diff = builder.sub_extension(lv[b_col], one);
    yield_constr.constraint_first_row(builder, diff);

    // constraint
    // bit_col is should be 0 or 1.
    let bit = lv[bit_col];
    let t = builder.mul_sub_extension(bit, bit, bit);
    yield_constr.constraint(builder, t);
    // filtered_col is multiplication of bit_col and b_col.
    let t = builder.mul_sub_extension(bit, lv[b_col], lv[filtered_bit_col]);
    yield_constr.constraint(builder, t);

    // transition
    let sum = builder.add_extension(lv[a_col], nv[a_col]);
    let diff = builder.sub_extension(sum, one);
    yield_constr.constraint_transition(builder, diff);
    let sum = builder.add_extension(lv[b_col], nv[b_col]);
    let diff = builder.sub_extension(sum, one);
    yield_constr.constraint_transition(builder, diff);
    // split: first_limb = next_bit + 2*next_first_limb
    let first_limb = lv[val_col];
    let next_first_limb = nv[val_col];
    let next_bit = nv[bit_col];
    let is_split = lv[a_col];
    let is_final = lv[is_final_col];
    let is_not_final = builder.sub_extension(one, is_final);
    let two = builder.two_extension();
    let double_next_first_limb = builder.mul_extension(two, next_first_limb);
    let sum = builder.add_extension(double_next_first_limb, next_bit);
    let diff = builder.sub_extension(first_limb, sum);
    let is_split_and_not_final = builder.mul_extension(is_split, is_not_final);
    let t = builder.mul_extension(is_split_and_not_final, diff);
    yield_constr.constraint_transition(builder, t);
    // not split: first_limb = next_first_limb and next_bit = bit
    let is_not_split = builder.sub_extension(one, is_split);
    let is_not_final = builder.sub_extension(one, is_final);
    let diff = builder.sub_extension(next_bit, bit);
    let t = builder.mul_extension(is_not_split, diff);
    yield_constr.constraint_transition(builder, t);
    let diff = builder.sub_extension(first_limb, next_first_limb);
    let t = builder.mul_extension(is_not_final, is_not_split);
    let t = builder.mul_extension(t, diff);
    yield_constr.constraint_transition(builder, t);
}

#[cfg(test)]
mod tests {
    use std::{marker::PhantomData, time::Instant};

    use bitvec::prelude::*;
    use itertools::Itertools;
    use plonky2::{
        field::{
            extension::{Extendable, FieldExtension},
            packed::PackedField,
            polynomial::PolynomialValues,
            types::{Field, PrimeField64},
        },
        hash::hash_types::RichField,
        iop::witness::PartialWitness,
        plonk::{
            circuit_builder::CircuitBuilder,
            circuit_data::CircuitConfig,
            config::{GenericConfig, PoseidonGoldilocksConfig},
        },
        util::{timing::TimingTree, transpose},
    };
    use rand::Rng;
    use starky::{
        config::StarkConfig,
        constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer},
        prover::prove,
        recursive_verifier::{
            add_virtual_stark_proof_with_pis, set_stark_proof_with_pis_target,
            verify_stark_proof_circuit,
        },
        stark::Stark,
        vars::{StarkEvaluationTargets, StarkEvaluationVars},
        verifier::verify_stark_proof,
    };

    use crate::pulse::{eval_pulse, eval_pulse_circuit, generate_pulse, get_pulse_col};

    use super::{
        eval_flags_u64, eval_flags_u64_circuit, generate_flags_u64_first_row,
        generate_flags_u64_next_row,
    };

    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    #[test]
    fn test_flag_u64_native() {
        let start_flag_col = 0;
        let filtered_bit_col = start_flag_col + 3;

        let exp_val: u64 = rand::random();
        let mut lv = vec![F::ZERO; MAIN_COLS];

        let num_rows = 2 * 64;
        generate_flags_u64_first_row(&mut lv, 0, exp_val);
        let mut rows = vec![lv.clone()];
        for i in 0..num_rows - 1 {
            let mut nv = vec![F::ZERO; MAIN_COLS];
            generate_flags_u64_next_row(&lv, &mut nv, i, start_flag_col);
            rows.push(nv.clone());
            lv = nv;
        }
        assert!(rows.len() == num_rows);

        // assertions
        let mut filtered_bits = vec![];
        for cur_row in (0..num_rows).step_by(2) {
            filtered_bits.push(rows[cur_row][filtered_bit_col]);
        }
        let filtered_bits = filtered_bits
            .into_iter()
            .map(|x| x.to_canonical_u64() == 1u64)
            .collect_vec();
        let exp_bits = exp_val.view_bits::<Lsb0>().iter().map(|b| *b).collect_vec();
        assert!(exp_bits == filtered_bits);
    }

    const MAIN_COLS: usize = 6;
    const START_FLAG_COL: usize = 0;
    const NUM_INPUTS: usize = 1 << 4;
    const COLUMNS: usize = MAIN_COLS + 1 + 4 * NUM_INPUTS;
    const PUBLIC_INPUTS: usize = 0;

    #[derive(Clone, Copy)]
    pub struct FlagStark<F: RichField + Extendable<D>, const D: usize> {
        _phantom: PhantomData<F>,
    }

    impl<F: RichField + Extendable<D>, const D: usize> FlagStark<F, D> {
        pub fn new() -> Self {
            Self {
                _phantom: PhantomData,
            }
        }

        pub fn generate_trace_rows_for_one_block(&self, exp_val: u64) -> Vec<Vec<F>> {
            let mut lv = vec![F::ZERO; START_FLAG_COL + 6];
            let num_rows = 2 * 64;
            generate_flags_u64_first_row(&mut lv, 0, exp_val);
            let mut rows = vec![lv.clone()];
            for i in 0..num_rows - 1 {
                let mut nv = vec![F::ZERO; lv.len()];
                generate_flags_u64_next_row(&lv, &mut nv, i, START_FLAG_COL);
                rows.push(nv.clone());
                lv = nv;
            }
            rows
        }

        pub fn generate_trace(&self, inputs: Vec<u64>) -> Vec<PolynomialValues<F>> {
            let mut rows = vec![];
            for input in inputs.clone() {
                rows.extend(self.generate_trace_rows_for_one_block(input));
            }
            let mut trace_cols = transpose(&rows.iter().map(|v| v.to_vec()).collect_vec());

            let num_rows_per_block = 2 * 64;
            let mut pulse_positions = vec![];
            for i in 0..inputs.len() {
                pulse_positions.extend(vec![
                    i * num_rows_per_block,
                    i * num_rows_per_block + num_rows_per_block - 1,
                ]);
            }
            generate_pulse(&mut trace_cols, pulse_positions);
            trace_cols
                .into_iter()
                .map(|column| PolynomialValues::new(column))
                .collect()
        }
    }

    impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D> for FlagStark<F, D> {
        fn eval_packed_generic<FE, P, const D2: usize>(
            &self,
            vars: StarkEvaluationVars<FE, P>,
            yield_constr: &mut ConstraintConsumer<P>,
        ) where
            FE: FieldExtension<D2, BaseField = F>,
            P: PackedField<Scalar = FE>,
        {
            let num_rows_per_block = 2 * 64;
            let mut pulse_positions = vec![];
            for i in 0..NUM_INPUTS {
                pulse_positions.extend(vec![
                    i * num_rows_per_block,
                    i * num_rows_per_block + num_rows_per_block - 1,
                ]);
            }
            // constraints for is_final
            let mut output = P::ZEROS;
            for i in (0..2 * NUM_INPUTS).skip(1).step_by(2) {
                output = output + vars.local_values[get_pulse_col(MAIN_COLS, i)];
            }
            let is_final = vars.local_values[START_FLAG_COL];
            yield_constr.constraint(is_final - output);

            eval_flags_u64(
                yield_constr,
                vars.local_values,
                vars.next_values,
                START_FLAG_COL,
            );
            eval_pulse(
                yield_constr,
                vars.local_values,
                vars.next_values,
                MAIN_COLS,
                pulse_positions,
            );
        }

        fn eval_ext_circuit(
            &self,
            builder: &mut CircuitBuilder<F, D>,
            vars: StarkEvaluationTargets<D>,
            yield_constr: &mut RecursiveConstraintConsumer<F, D>,
        ) {
            let num_rows_per_block = 2 * 64;
            let mut pulse_positions = vec![];
            for i in 0..NUM_INPUTS {
                pulse_positions.extend(vec![
                    i * num_rows_per_block,
                    i * num_rows_per_block + num_rows_per_block - 1,
                ]);
            }

            // constraints for is_final
            let mut output = builder.zero_extension();
            for i in (0..2 * NUM_INPUTS).skip(1).step_by(2) {
                output =
                    builder.add_extension(output, vars.local_values[get_pulse_col(MAIN_COLS, i)]);
            }
            let is_final = vars.local_values[START_FLAG_COL];
            let diff = builder.sub_extension(is_final, output);
            yield_constr.constraint(builder, diff);

            eval_flags_u64_circuit(
                builder,
                yield_constr,
                vars.local_values,
                vars.next_values,
                START_FLAG_COL,
            );
            eval_pulse_circuit(
                builder,
                yield_constr,
                vars.local_values,
                vars.next_values,
                MAIN_COLS,
                pulse_positions,
            );
        }

        fn constraint_degree(&self) -> usize {
            3
        }
    }

    #[test]
    fn test_flag_u64_stark() {
        let mut rng = rand::thread_rng();
        let inputs = (0..NUM_INPUTS).map(|_| rng.gen()).collect_vec();

        type S = FlagStark<F, D>;
        let inner_config = StarkConfig::standard_fast_config(COLUMNS, PUBLIC_INPUTS);
        let stark = S::new();
        let trace = stark.generate_trace(inputs);
        let inner_proof = prove::<F, C, S, D>(
            stark,
            &inner_config,
            trace,
            vec![],
            &mut TimingTree::default(),
        )
        .unwrap();
        verify_stark_proof(stark, inner_proof.clone(), &inner_config).unwrap();

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

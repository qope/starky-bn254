// generate flags
// in the case of val0 = 1101, val1 = 1011
//| f | r | a | b | b'| bit | val0 | val1
//--------------------------------------
//| 0 | 0 | 0 | 1 | 1 |  1  | 101  |val1 <- public input (1 + 2*101 = val0, val1)
//| 0 | 0 | 1 | 0 | 0 |  1  | 101  |val1 <- split
//| 0 | 0 | 0 | 1 | 1 |  1  | 01   |val1
//| 0 | 0 | 1 | 0 | 0 |  1  | 01   |val1 <- split
//| 0 | 0 | 0 | 1 | 0 |  0  | 1    |val1
//| 0 | 0 | 1 | 0 | 0 |  0  | 1    |val1 <- split
//| 0 | 1 | 0 | 1 | 1 |  1  | 0    |val1 <- rotate (r=8-2)
//| 0 | 0 | 1 | 0 | 0 |  1  | val1 | 0   <- split (<- output)
//| 0 | 0 | 0 | 1 | 1 |  1  | 011  | 0
//| 0 | 0 | 1 | 0 | 0 |  1  | 011  | 0   <- split
//| 0 | 0 | 0 | 1 | 0 |  0  | 11   | 0
//| 0 | 0 | 1 | 0 | 0 |  0  | 11   | 0   <- split
//| 0 | 0 | 0 | 1 | 1 |  1  | 1    | 0
//| 0 | 0 | 1 | 0 | 0 |  1  | 1    | 0   <- split
//| 0 | 1 | 0 | 1 | 1 |  1  | 0    | 0   <- rotate (r=16-2)
//| 1 | 0 | 1 | 0 | 0 |  1  | 0    | 0   <- public output <- split

// f = is_final
// r = is_rotate
// b' = filetered_bit (= b * bit)

// overall, we need 2*bits_len rows.
// split vals at r = 2*i + 1, and rotate at r = 2*limb_bits*(i+1) - 2
// we need 8 limbs cols

use plonky2::{
    field::packed::PackedField,
    field::{extension::Extendable, types::Field},
    hash::hash_types::RichField,
    iop::ext_target::ExtensionTarget,
    plonk::circuit_builder::CircuitBuilder,
};
use starky::constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer};

const NUM_INPUT_LIMBS: usize = 8;
const INPUT_LIMB_BITS: usize = 32;

// generate flags for the first row
// 5 + NUM_INPUT_LIMBS cols are generated
pub fn generate_flags_first_row<F: RichField>(
    lv: &mut [F],
    start_flag_col: usize,
    limbs: [u32; NUM_INPUT_LIMBS],
) {
    let is_final = start_flag_col;
    let is_rotate_col = start_flag_col + 1;
    let a_col = start_flag_col + 2;
    let b_col = start_flag_col + 3;
    let filtered_bit_col = start_flag_col + 4;
    let bit_col = start_flag_col + 5;
    let start_limbs = start_flag_col + 6;
    let end_limbs = start_limbs + NUM_INPUT_LIMBS;

    let first_limb = limbs[0];
    let first_bit = first_limb % 2;
    let rest = (first_limb - first_bit) / 2;
    let mut new_limbs = limbs;
    new_limbs[0] = rest;

    lv[is_final] = F::ZERO;
    lv[is_rotate_col] = F::ZERO;
    lv[a_col] = F::ZERO;
    lv[b_col] = F::ONE;
    lv[filtered_bit_col] = F::from_canonical_u32(first_bit);
    lv[bit_col] = F::from_canonical_u32(first_bit);
    for (i, col) in (start_limbs..end_limbs).enumerate() {
        lv[col] = F::from_canonical_u32(new_limbs[i]);
    }
}

pub fn generate_flags_next_row<F: RichField>(
    lv: &[F],
    nv: &mut [F],
    cur_row: usize,
    start_flag_col: usize,
) {
    let is_final = start_flag_col;
    let is_rotate_col = start_flag_col + 1;
    let a_col = start_flag_col + 2;
    let b_col = start_flag_col + 3;
    let filtered_bit_col = start_flag_col + 4;
    let bit_col = start_flag_col + 5;
    let start_limbs = start_flag_col + 6;
    let end_limbs = start_limbs + NUM_INPUT_LIMBS;

    nv[a_col] = F::ONE - lv[a_col];
    nv[b_col] = F::ONE - lv[b_col];

    let num_rows = 2 * INPUT_LIMB_BITS * NUM_INPUT_LIMBS;
    if cur_row == num_rows - 2 {
        nv[is_final] = F::ONE;
    } else {
        nv[is_final] = F::ZERO;
    }

    if cur_row % (2 * INPUT_LIMB_BITS) == 2 * INPUT_LIMB_BITS - 3 {
        nv[is_rotate_col] = F::ONE; // is_rotate_col is one at r = 2*INPUT_LIMB_BITS*(i+1) - 2
    } else {
        nv[is_rotate_col] = F::ZERO;
    }

    if lv[a_col] == F::ONE {
        // split
        let first_limb = lv[start_limbs].to_canonical_u64();
        let next_bit = first_limb % 2;
        let next_first_limb = (first_limb - next_bit) / 2;
        nv[bit_col] = F::from_canonical_u64(next_bit);
        nv[start_limbs] = F::from_canonical_u64(next_first_limb);
    } else {
        // no split
        nv[bit_col] = lv[bit_col];
        nv[start_limbs] = lv[start_limbs];
    }

    if lv[is_rotate_col] == F::ONE {
        // rotate
        for col in start_limbs + 1..end_limbs {
            nv[col - 1] = lv[col];
        }
        nv[end_limbs - 1] = F::ZERO;
    } else {
        // no rotate
        for col in start_limbs + 1..end_limbs {
            nv[col] = lv[col]; // copy limbs except for the first limb
        }
    }
    nv[filtered_bit_col] = nv[bit_col] * nv[b_col];
}

pub fn eval_flags<P: PackedField, const N: usize>(
    yield_constr: &mut ConstraintConsumer<P>,
    lv: &[P; N],
    nv: &[P; N],
    start_flag_col: usize,
) {
    let is_final_col = start_flag_col;
    let is_rotate_col = start_flag_col + 1;
    let a_col = start_flag_col + 2;
    let b_col = start_flag_col + 3;
    let filtered_bit_col = start_flag_col + 4;
    let bit_col = start_flag_col + 5;
    let start_limbs = start_flag_col + 6;
    let end_limbs = start_limbs + NUM_INPUT_LIMBS;

    // initial condition
    yield_constr.constraint_first_row(lv[a_col]);
    yield_constr.constraint_first_row(lv[b_col] - P::ONES);

    // constraint
    // bit_col is should be 0 or 1.
    let bit = lv[bit_col];
    yield_constr.constraint(bit * bit - bit);
    // filtered_col is multiplication of bit_col and b_col.
    yield_constr.constraint(bit * lv[b_col] - lv[filtered_bit_col]);
    // this is optional
    yield_constr.constraint(lv[is_rotate_col] * lv[a_col]);
    yield_constr.constraint(lv[is_final_col] * lv[is_rotate_col]);

    // transition
    yield_constr.constraint_transition(lv[a_col] + nv[a_col] - P::ONES);
    yield_constr.constraint_transition(lv[b_col] + nv[b_col] - P::ONES);
    // split: first_limb = next_bit + 2*next_first_limb
    let first_limb = lv[start_limbs];
    let next_first_limb = nv[start_limbs];
    let next_bit = nv[bit_col];
    let is_split = lv[a_col];
    let is_final = lv[is_final_col];
    let is_not_final = P::ONES - is_final;
    yield_constr.constraint_transition(
        is_not_final * is_split * (first_limb - P::Scalar::TWO * next_first_limb - next_bit),
    );
    // not split: first_limb = next_first_limb and next_bit = bit
    let is_not_split = P::ONES - is_split;
    let is_rotate = lv[is_rotate_col];
    let is_not_rotate_nor_final = P::ONES - is_rotate - is_final;
    yield_constr.constraint_transition(is_not_split * (next_bit - bit));
    yield_constr.constraint_transition(
        is_not_rotate_nor_final * is_not_split * (first_limb - next_first_limb),
    );
    // rotate
    for col in start_limbs + 1..end_limbs {
        yield_constr.constraint_transition(is_rotate * (nv[col - 1] - lv[col]));
    }
    yield_constr.constraint_transition(is_rotate * nv[end_limbs - 1]);
    // not rotate
    for col in start_limbs + 1..end_limbs {
        yield_constr.constraint_transition(is_not_rotate_nor_final * (nv[col] - lv[col]));
    }
}

pub fn eval_flags_circuit<F: RichField + Extendable<D>, const D: usize, const N: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    lv: &[ExtensionTarget<D>; N],
    nv: &[ExtensionTarget<D>; N],
    start_flag_col: usize,
) {
    let one = builder.one_extension();
    let is_final_col = start_flag_col;
    let is_rotate_col = start_flag_col + 1;
    let a_col = start_flag_col + 2;
    let b_col = start_flag_col + 3;
    let filtered_bit_col = start_flag_col + 4;
    let bit_col = start_flag_col + 5;
    let start_limbs = start_flag_col + 6;
    let end_limbs = start_limbs + NUM_INPUT_LIMBS;

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
    // this is optional
    let t = builder.mul_extension(lv[is_rotate_col], lv[a_col]);
    yield_constr.constraint(builder, t);
    let t = builder.mul_extension(lv[is_final_col], lv[is_rotate_col]);
    yield_constr.constraint(builder, t);

    // transition
    let sum = builder.add_extension(lv[a_col], nv[a_col]);
    let diff = builder.sub_extension(sum, one);
    yield_constr.constraint_transition(builder, diff);
    let sum = builder.add_extension(lv[b_col], nv[b_col]);
    let diff = builder.sub_extension(sum, one);
    yield_constr.constraint_transition(builder, diff);
    // split: first_limb = next_bit + 2*next_first_limb
    let first_limb = lv[start_limbs];
    let next_first_limb = nv[start_limbs];
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
    let is_rotate = lv[is_rotate_col];
    let is_rotate_or_final = builder.add_extension(is_rotate, is_final);
    let is_not_rotate_nor_final = builder.sub_extension(one, is_rotate_or_final);
    let diff = builder.sub_extension(next_bit, bit);
    let t = builder.mul_extension(is_not_split, diff);
    yield_constr.constraint_transition(builder, t);
    let diff = builder.sub_extension(first_limb, next_first_limb);
    let t = builder.mul_extension(is_not_rotate_nor_final, is_not_split);
    let t = builder.mul_extension(t, diff);
    yield_constr.constraint_transition(builder, t);
    // rotate
    for col in start_limbs + 1..end_limbs {
        let diff = builder.sub_extension(nv[col - 1], lv[col]);
        let t = builder.mul_extension(is_rotate, diff);
        yield_constr.constraint_transition(builder, t);
    }
    let t = builder.mul_extension(is_rotate, nv[end_limbs - 1]);
    yield_constr.constraint_transition(builder, t);
    // not rotate
    for col in start_limbs + 1..end_limbs {
        let diff = builder.sub_extension(nv[col], lv[col]);
        let t = builder.mul_extension(is_not_rotate_nor_final, diff);
        yield_constr.constraint_transition(builder, t);
    }
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

    use crate::flags::{INPUT_LIMB_BITS, NUM_INPUT_LIMBS};

    use super::{
        eval_flags, eval_flags_circuit, generate_flags_first_row, generate_flags_next_row,
    };

    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    #[test]
    fn test_flag_native() {
        let start_flag_col = 0;
        // let is_final = start_flag_col;
        // let is_rotate_col = start_flag_col + 1;
        // let a_col = start_flag_col + 2;
        // let b_col = start_flag_col + 3;
        let filtered_bit_col = start_flag_col + 4;
        // let bit_col = start_flag_col + 5;
        // let start_limbs = start_flag_col + 6;
        // let end_limbs = start_limbs + NUM_INPUT_LIMBS;

        let input_limbs: [u32; NUM_INPUT_LIMBS] = rand::random();
        let mut lv = vec![F::ZERO; MAIN_COLS];

        let num_rows = 2 * INPUT_LIMB_BITS * NUM_INPUT_LIMBS;
        generate_flags_first_row(&mut lv, 0, input_limbs);
        let mut rows = vec![lv.clone()];
        for i in 0..num_rows - 1 {
            let mut nv = vec![F::ZERO; MAIN_COLS];
            generate_flags_next_row(&lv, &mut nv, i, start_flag_col);
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
        let mut bits = vec![];
        for limb in input_limbs {
            let limb_bits = limb.view_bits::<Lsb0>().iter().map(|b| *b).collect_vec();
            bits.extend(limb_bits);
        }

        assert!(bits == filtered_bits);

        // for row in rows {
        //     dbg!(&row[start_limbs]);
        // }
    }

    const MAIN_COLS: usize = 6 + NUM_INPUT_LIMBS;
    const COLUMNS: usize = MAIN_COLS;
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

        pub fn generate_trace_rows_for_one_block(
            &self,
            input_limbs: [u32; NUM_INPUT_LIMBS],
        ) -> Vec<Vec<F>> {
            let start_flag_col = 0;
            let mut lv = vec![F::ZERO; MAIN_COLS];
            let num_rows = 2 * INPUT_LIMB_BITS * NUM_INPUT_LIMBS;
            generate_flags_first_row(&mut lv, 0, input_limbs);
            let mut rows = vec![lv.clone()];
            for i in 0..num_rows - 1 {
                let mut nv = vec![F::ZERO; lv.len()];
                generate_flags_next_row(&lv, &mut nv, i, start_flag_col);
                rows.push(nv.clone());
                lv = nv;
            }
            rows
        }

        pub fn generate_trace(
            &self,
            inputs: Vec<[u32; NUM_INPUT_LIMBS]>,
        ) -> Vec<PolynomialValues<F>> {
            let mut rows = vec![];
            for input in inputs {
                rows.extend(self.generate_trace_rows_for_one_block(input));
            }
            let trace_cols = transpose(&rows.iter().map(|v| v.to_vec()).collect_vec());
            trace_cols
                .into_iter()
                .map(|column| PolynomialValues::new(column))
                .collect()
        }
    }

    impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D> for FlagStark<F, D> {
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
            eval_flags(yield_constr, vars.local_values, vars.next_values, 0);
        }

        fn eval_ext_circuit(
            &self,
            builder: &mut CircuitBuilder<F, D>,
            vars: StarkEvaluationTargets<D, COLUMNS, PUBLIC_INPUTS>,
            yield_constr: &mut RecursiveConstraintConsumer<F, D>,
        ) {
            eval_flags_circuit(
                builder,
                yield_constr,
                vars.local_values,
                vars.next_values,
                0,
            );
        }

        fn constraint_degree(&self) -> usize {
            3
        }
    }

    #[test]
    fn test_flag_stark() {
        let mut rng = rand::thread_rng();
        let inputs = (0..2).map(|_| [rng.gen(); NUM_INPUT_LIMBS]).collect_vec();

        type S = FlagStark<F, D>;
        let inner_config = StarkConfig::standard_fast_config();
        let stark = S::new();
        let trace = stark.generate_trace(inputs);
        let inner_proof =
            prove::<F, C, S, D>(stark, &inner_config, trace, [], &mut TimingTree::default())
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

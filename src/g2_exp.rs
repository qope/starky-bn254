use core::marker::PhantomData;

use ark_bn254::{Fr, G2Affine};
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

use crate::{g2::generate_g2_add, utils::bits_to_biguint};
use starky::{
    constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer},
    permutation::PermutationPair,
    stark::Stark,
    vars::{StarkEvaluationTargets, StarkEvaluationVars},
};

use super::{
    constants::{BITS_LEN, N_LIMBS},
    fq2::{read_fq2, write_fq2},
    g2::{
        eval_g2_add, eval_g2_add_circuit, eval_g2_double, eval_g2_double_circuit,
        generate_g2_double, read_g2_output, write_g2_output, G2Output,
    },
    instruction::{
        eval_pow_instruction, eval_pow_instruction_cirucuit, fq2_equal_first,
        fq2_equal_first_circuit, fq2_equal_last, fq2_equal_last_circuit, fq2_equal_transition,
        fq2_equal_transition_circuit, generate_initial_pow_instruction,
        generate_next_pow_instruction, read_instruction,
    },
    range_check::{
        eval_split_u16_range_check, eval_split_u16_range_check_circuit,
        generate_split_u16_range_check, split_u16_range_check_pairs,
    },
    utils::{columns_to_fq2, fq2_to_columns, i64_to_column_positive},
};

const ROWS: usize = 1 << 9;
const MAIN_COLS: usize = 48 * N_LIMBS + 2 + BITS_LEN;
const START_RANGE_CHECK: usize = 8 * N_LIMBS;
const NUM_RANGE_CHECK: usize = 40 * N_LIMBS - 6;
const END_RANGE_CHECK: usize = START_RANGE_CHECK + NUM_RANGE_CHECK;
const IS_SQ_COL: usize = 48 * N_LIMBS;
const IS_NOOP_COL: usize = 48 * N_LIMBS + 1;
const IS_MUL_COL: usize = 48 * N_LIMBS + 2;

const COLUMNS: usize = MAIN_COLS + 1 + 6 * NUM_RANGE_CHECK;
const PUBLIC_INPUTS: usize = 12 * N_LIMBS + BITS_LEN;

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

    pub fn generate_trace(
        &self,
        x: G2Affine,
        offset: G2Affine,
        x_exp: G2Affine,
        exp_bits: [bool; BITS_LEN],
    ) -> Vec<PolynomialValues<F>> {
        let exp_val = bits_to_biguint(&exp_bits);
        let exp_val: Fr = exp_val.into();
        let exp_bits = exp_bits.map(|b| F::from_bool(b));
        let a_g2 = x;
        let b_g2 = offset;
        let expected: G2Affine = (a_g2 * exp_val + b_g2).into();
        assert!(expected == x_exp);

        let a_x: [[F; N_LIMBS]; 2] = fq2_to_columns(a_g2.x).map(i64_to_column_positive);
        let a_y: [[F; N_LIMBS]; 2] = fq2_to_columns(a_g2.y).map(i64_to_column_positive);
        let b_x: [[F; N_LIMBS]; 2] = fq2_to_columns(b_g2.x).map(i64_to_column_positive);
        let b_y: [[F; N_LIMBS]; 2] = fq2_to_columns(b_g2.y).map(i64_to_column_positive);
        let mut lv = [F::ZERO; MAIN_COLS];
        let mut cur_col = 0;
        write_fq2(&mut lv, a_x, &mut cur_col);
        write_fq2(&mut lv, a_y, &mut cur_col);
        write_fq2(&mut lv, b_x, &mut cur_col);
        write_fq2(&mut lv, b_y, &mut cur_col);

        generate_initial_pow_instruction(
            &mut lv,
            IS_SQ_COL,
            IS_MUL_COL,
            IS_NOOP_COL,
            exp_bits.try_into().unwrap(),
        );

        let mut rows = vec![];
        for _ in 0..ROWS {
            let mut cur_col = 0;
            let a_x = read_fq2(&lv, &mut cur_col);
            let a_y = read_fq2(&lv, &mut cur_col);
            let b_x = read_fq2(&lv, &mut cur_col);
            let b_y = read_fq2(&lv, &mut cur_col);

            let is_add = lv[IS_MUL_COL];
            let is_double = lv[IS_SQ_COL];
            let is_noop = lv[IS_NOOP_COL];

            assert!(is_add + is_double + is_noop == F::ONE);
            let output = if is_add == F::ONE {
                generate_g2_add(a_x, a_y, b_x, b_y)
            } else if is_double == F::ONE {
                generate_g2_double(a_x, a_y)
            } else {
                G2Output::default()
            };

            let mut cur_col = 0;
            write_fq2(&mut lv, a_x, &mut cur_col); // N_LIMBS
            write_fq2(&mut lv, a_y, &mut cur_col); // N_LIMBS
            write_fq2(&mut lv, b_x, &mut cur_col); // N_LIMBS
            write_fq2(&mut lv, b_y, &mut cur_col); // N_LIMBS
            write_g2_output(&mut lv, &output, &mut cur_col); // 40*N_LIMBS

            let mut nv = [F::ZERO; MAIN_COLS];
            cur_col = 0;

            if is_double == F::ONE {
                write_fq2(&mut nv, output.new_x, &mut cur_col);
                write_fq2(&mut nv, output.new_y, &mut cur_col);
                write_fq2(&mut nv, b_x, &mut cur_col);
                write_fq2(&mut nv, b_y, &mut cur_col);
            } else if is_add == F::ONE {
                write_fq2(&mut nv, a_x, &mut cur_col);
                write_fq2(&mut nv, a_y, &mut cur_col);
                write_fq2(&mut nv, output.new_x, &mut cur_col);
                write_fq2(&mut nv, output.new_y, &mut cur_col);
            } else {
                write_fq2(&mut nv, a_x, &mut cur_col);
                write_fq2(&mut nv, a_y, &mut cur_col);
                write_fq2(&mut nv, b_x, &mut cur_col);
                write_fq2(&mut nv, b_y, &mut cur_col);
            }

            generate_next_pow_instruction(&lv, &mut nv, IS_SQ_COL, IS_MUL_COL, IS_NOOP_COL);

            rows.push(lv);
            lv = nv;
        }

        cur_col = 4 * N_LIMBS;
        let new_x = read_fq2(&lv, &mut cur_col);
        let new_y = read_fq2(&lv, &mut cur_col);
        let new_x = columns_to_fq2(new_x);
        let new_y = columns_to_fq2(new_y);
        let new_g2 = G2Affine::new(new_x, new_y);
        assert!(new_g2 == expected);

        let mut trace_cols = transpose(&rows.iter().map(|v| v.to_vec()).collect_vec());

        generate_split_u16_range_check(START_RANGE_CHECK..END_RANGE_CHECK, &mut trace_cols);

        trace_cols
            .into_iter()
            .map(|column| PolynomialValues::new(column))
            .collect()
    }

    pub fn generate_public_inputs(
        x: G2Affine,
        x_exp: G2Affine,
        offset: G2Affine,
        exp_bits: [bool; BITS_LEN],
    ) -> [F; 12 * N_LIMBS + BITS_LEN] {
        let mut pi = [F::ZERO; 12 * N_LIMBS + BITS_LEN];
        let x_c0 = fq2_to_columns(x.x).map(i64_to_column_positive);
        let x_c1 = fq2_to_columns(x.y).map(i64_to_column_positive);
        let offset_c0 = fq2_to_columns(offset.x).map(i64_to_column_positive);
        let offset_c1 = fq2_to_columns(offset.y).map(i64_to_column_positive);
        let x_exp_c0 = fq2_to_columns(x_exp.x).map(i64_to_column_positive);
        let x_exp_c1 = fq2_to_columns(x_exp.y).map(i64_to_column_positive);
        let exp_bits = exp_bits.map(|b| F::from_bool(b));
        let mut cur_col = 0;
        write_fq2(&mut pi, x_c0, &mut cur_col);
        write_fq2(&mut pi, x_c1, &mut cur_col);
        write_fq2(&mut pi, offset_c0, &mut cur_col);
        write_fq2(&mut pi, offset_c1, &mut cur_col);
        write_fq2(&mut pi, x_exp_c0, &mut cur_col);
        write_fq2(&mut pi, x_exp_c1, &mut cur_col);
        for i in 0..BITS_LEN {
            pi[cur_col] = exp_bits[i];
            cur_col += 1;
        }
        assert!(cur_col == 12 * N_LIMBS + BITS_LEN);
        pi
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D> for G2ExpStark<F, D> {
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
        let is_noop = lv[IS_NOOP_COL];
        cur_col = IS_MUL_COL;
        let bits: [_; BITS_LEN] = read_instruction(lv, &mut cur_col);
        eval_g2_add(yield_constr, is_add, a_x, a_y, b_x, b_y, &output);
        eval_g2_double(yield_constr, is_double, a_x, a_y, &output);

        // public inputs
        let pi = vars.public_inputs;
        let pi: [P; PUBLIC_INPUTS] = pi.map(|x| x.into());
        cur_col = 0;
        let pi_a_x = read_fq2(&pi, &mut cur_col);
        let pi_a_y = read_fq2(&pi, &mut cur_col);
        let pi_b_x = read_fq2(&pi, &mut cur_col);
        let pi_b_y = read_fq2(&pi, &mut cur_col);
        let pi_final_x = read_fq2(&pi, &mut cur_col);
        let pi_final_y = read_fq2(&pi, &mut cur_col);
        let pi_bits: [_; BITS_LEN] = read_instruction(&pi, &mut cur_col);
        fq2_equal_first(yield_constr, pi_a_x, a_x);
        fq2_equal_first(yield_constr, pi_a_y, a_y);
        fq2_equal_first(yield_constr, pi_b_x, b_x);
        fq2_equal_first(yield_constr, pi_b_y, b_y);
        fq2_equal_last(yield_constr, pi_final_x, b_x);
        fq2_equal_last(yield_constr, pi_final_y, b_y);
        for i in 0..BITS_LEN {
            yield_constr.constraint_first_row(pi_bits[i] - bits[i]);
        }

        let nv = vars.next_values;

        cur_col = 0;
        let next_a_x = read_fq2(&nv, &mut cur_col);
        let next_a_y = read_fq2(&nv, &mut cur_col);
        let next_b_x = read_fq2(&nv, &mut cur_col);
        let next_b_y = read_fq2(&nv, &mut cur_col);

        // if is_double == F::ONE
        fq2_equal_transition(yield_constr, is_double, next_a_x, output.new_x);
        fq2_equal_transition(yield_constr, is_double, next_a_y, output.new_y);
        fq2_equal_transition(yield_constr, is_double, next_b_x, b_x);
        fq2_equal_transition(yield_constr, is_double, next_b_y, b_y);

        // if is_add == F::ONE
        fq2_equal_transition(yield_constr, is_add, next_a_x, a_x);
        fq2_equal_transition(yield_constr, is_add, next_a_y, a_y);
        fq2_equal_transition(yield_constr, is_add, next_b_x, output.new_x);
        fq2_equal_transition(yield_constr, is_add, next_b_y, output.new_y);

        // is is_noop == F::ONE
        fq2_equal_transition(yield_constr, is_noop, next_a_x, a_x);
        fq2_equal_transition(yield_constr, is_noop, next_a_y, a_y);
        fq2_equal_transition(yield_constr, is_noop, next_b_x, b_x);
        fq2_equal_transition(yield_constr, is_noop, next_b_y, b_y);

        eval_pow_instruction(yield_constr, lv, nv, IS_SQ_COL, IS_MUL_COL, IS_NOOP_COL);
    }

    fn eval_ext_circuit(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        vars: StarkEvaluationTargets<D, COLUMNS, PUBLIC_INPUTS>,
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
        let is_noop = lv[IS_NOOP_COL];
        cur_col = IS_MUL_COL;
        let bits: [_; BITS_LEN] = read_instruction(lv, &mut cur_col);
        eval_g2_add_circuit(builder, yield_constr, is_add, a_x, a_y, b_x, b_y, &output);
        eval_g2_double_circuit(builder, yield_constr, is_double, a_x, a_y, &output);

        // public inputs
        let pi = vars.public_inputs;
        cur_col = 0;
        let pi_a_x = read_fq2(&pi, &mut cur_col);
        let pi_a_y = read_fq2(&pi, &mut cur_col);
        let pi_b_x = read_fq2(&pi, &mut cur_col);
        let pi_b_y = read_fq2(&pi, &mut cur_col);
        let pi_final_x = read_fq2(&pi, &mut cur_col);
        let pi_final_y = read_fq2(&pi, &mut cur_col);
        let pi_bits: [_; BITS_LEN] = read_instruction(&pi, &mut cur_col);
        fq2_equal_first_circuit(builder, yield_constr, pi_a_x, a_x);
        fq2_equal_first_circuit(builder, yield_constr, pi_a_y, a_y);
        fq2_equal_first_circuit(builder, yield_constr, pi_b_x, b_x);
        fq2_equal_first_circuit(builder, yield_constr, pi_b_y, b_y);
        fq2_equal_last_circuit(builder, yield_constr, pi_final_x, b_x);
        fq2_equal_last_circuit(builder, yield_constr, pi_final_y, b_y);
        for i in 0..BITS_LEN {
            let diff = builder.sub_extension(pi_bits[i], bits[i]);
            yield_constr.constraint_first_row(builder, diff);
        }

        let nv = vars.next_values;

        cur_col = 0;
        let next_a_x = read_fq2(&nv, &mut cur_col);
        let next_a_y = read_fq2(&nv, &mut cur_col);
        let next_b_x = read_fq2(&nv, &mut cur_col);
        let next_b_y = read_fq2(&nv, &mut cur_col);

        // if is_double == F::ONE
        fq2_equal_transition_circuit(builder, yield_constr, is_double, next_a_x, output.new_x);
        fq2_equal_transition_circuit(builder, yield_constr, is_double, next_a_y, output.new_y);
        fq2_equal_transition_circuit(builder, yield_constr, is_double, next_b_x, b_x);
        fq2_equal_transition_circuit(builder, yield_constr, is_double, next_b_y, b_y);

        // if is_add == F::ONE
        fq2_equal_transition_circuit(builder, yield_constr, is_add, next_a_x, a_x);
        fq2_equal_transition_circuit(builder, yield_constr, is_add, next_a_y, a_y);
        fq2_equal_transition_circuit(builder, yield_constr, is_add, next_b_x, output.new_x);
        fq2_equal_transition_circuit(builder, yield_constr, is_add, next_b_y, output.new_y);

        // is is_noop == F::ONE
        fq2_equal_transition_circuit(builder, yield_constr, is_noop, next_a_x, a_x);
        fq2_equal_transition_circuit(builder, yield_constr, is_noop, next_a_y, a_y);
        fq2_equal_transition_circuit(builder, yield_constr, is_noop, next_b_x, b_x);
        fq2_equal_transition_circuit(builder, yield_constr, is_noop, next_b_y, b_y);

        eval_pow_instruction_cirucuit(
            builder,
            yield_constr,
            lv,
            nv,
            IS_SQ_COL,
            IS_MUL_COL,
            IS_NOOP_COL,
        );
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

    use crate::{constants::BITS_LEN, g2_exp::G2ExpStark, utils::biguint_to_bits};
    use ark_bn254::{Fr, G2Affine};
    use ark_std::UniformRand;
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
        let mut rng = rand::thread_rng();
        let exp_val: Fr = Fr::rand(&mut rng);
        let exp_bits: [bool; BITS_LEN] = biguint_to_bits(&exp_val.into(), BITS_LEN)
            .try_into()
            .unwrap();
        let x = G2Affine::rand(&mut rng);
        let offset = G2Affine::rand(&mut rng);
        let x_exp: G2Affine = (x * exp_val + offset).into();

        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type S = G2ExpStark<F, D>;
        let inner_config = StarkConfig::standard_fast_config();
        let stark = S::new();
        let trace = stark.generate_trace(x, offset, x_exp, exp_bits);

        println!("start stark proof generation");
        let now = Instant::now();
        let pi = S::generate_public_inputs(x, x_exp, offset, exp_bits);
        let inner_proof =
            prove::<F, C, S, D>(stark, &inner_config, trace, pi, &mut TimingTree::default())
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

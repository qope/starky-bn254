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

use crate::instruction::{
    eval_pow_instruction, eval_pow_instruction_cirucuit, fq_equal_first, fq_equal_first_circuit,
    fq_equal_last, fq_equal_last_circuit, fq_equal_transition, fq_equal_transition_circuit,
    generate_initial_pow_instruction, generate_next_pow_instruction,
};
use crate::modular::write_modulus_aux;
use crate::modular_zero::write_modulus_aux_zero;
use crate::range_check::{eval_split_u16_range_check, eval_split_u16_range_check_circuit};
use crate::utils::{columns_to_fq, fq_to_columns};
use crate::{constants::BITS_LEN, constants::N_LIMBS, utils::bits_to_biguint};
use crate::{
    g1::{
        eval_g1_add, eval_g1_add_circuit, eval_g1_double, eval_g1_double_circuit, generate_g1_add,
        generate_g1_double, G1Output,
    },
    instruction::read_instruction,
};

use starky::{
    constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer},
    permutation::PermutationPair,
    stark::Stark,
    vars::{StarkEvaluationTargets, StarkEvaluationVars},
};

use super::modular_zero::read_modulus_aux_zero;
use super::range_check::{generate_split_u16_range_check, split_u16_range_check_pairs};
use super::{modular::read_u256, utils::i64_to_column_positive};
use crate::modular::{read_modulus_aux, write_u256};

const MAIN_COLS: usize = 24 * N_LIMBS + 2 + BITS_LEN;
const ROWS: usize = 1 << 9;

const IS_SQ_COL: usize = 24 * N_LIMBS;
const IS_NOOP_COL: usize = 24 * N_LIMBS + 1;
const IS_MUL_COL: usize = 24 * N_LIMBS + 2;

const START_RANGE_CHECK: usize = 4 * N_LIMBS;
const NUM_RANGE_CHECKS: usize = 20 * N_LIMBS - 4;
const END_RANGE_CHECK: usize = START_RANGE_CHECK + NUM_RANGE_CHECKS;

const COLUMNS: usize = MAIN_COLS + 1 + 6 * NUM_RANGE_CHECKS;
const PUBLIC_INPUTS: usize = 6 * N_LIMBS + BITS_LEN;

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

    pub fn generate_trace(
        &self,
        x: G1Affine,
        offset: G1Affine,
        x_exp_plus_offset: G1Affine,
        exp_bits: [bool; BITS_LEN],
    ) -> Vec<PolynomialValues<F>> {
        let exp_val = bits_to_biguint(&exp_bits);
        let exp_val: Fr = exp_val.into();
        let exp_bits = exp_bits.map(|b| F::from_bool(b));
        let a_g1 = x;
        let b_g1 = offset;
        let expected: G1Affine = (a_g1 * exp_val + b_g1).into();
        assert!(expected == x_exp_plus_offset);

        let a_x = fq_to_columns(a_g1.x).map(|x| F::from_canonical_i64(x));
        let a_y = fq_to_columns(a_g1.y).map(|x| F::from_canonical_i64(x));
        let b_x = fq_to_columns(b_g1.x).map(|x| F::from_canonical_i64(x));
        let b_y = fq_to_columns(b_g1.y).map(|x| F::from_canonical_i64(x));

        let mut lv = [F::ZERO; MAIN_COLS];
        let mut cur_col = 0;
        write_u256(&mut lv, &a_x, &mut cur_col);
        write_u256(&mut lv, &a_y, &mut cur_col);
        write_u256(&mut lv, &b_x, &mut cur_col);
        write_u256(&mut lv, &b_y, &mut cur_col);

        generate_initial_pow_instruction(&mut lv, IS_SQ_COL, IS_MUL_COL, IS_NOOP_COL, exp_bits);

        let mut rows = vec![];
        for _ in 0..ROWS {
            let mut cur_col = 0;
            let a_x = read_u256(&lv, &mut cur_col);
            let a_y = read_u256(&lv, &mut cur_col);
            let b_x = read_u256(&lv, &mut cur_col);
            let b_y = read_u256(&lv, &mut cur_col);

            let is_add = lv[IS_MUL_COL];
            let is_double = lv[IS_SQ_COL];
            let is_noop = lv[IS_NOOP_COL];

            assert!(is_add + is_double + is_noop == F::ONE);

            let output = if is_add == F::ONE {
                generate_g1_add(a_x, a_y, b_x, b_y)
            } else if is_double == F::ONE {
                generate_g1_double(a_x, a_y)
            } else {
                G1Output::default()
            };

            cur_col = 4 * N_LIMBS;
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
            assert!(cur_col == 24 * N_LIMBS);

            // next row
            let mut nv = [F::ZERO; MAIN_COLS];
            cur_col = 0;
            if is_double == F::ONE {
                write_u256(&mut nv, &output.new_x, &mut cur_col);
                write_u256(&mut nv, &output.new_y, &mut cur_col);
                write_u256(&mut nv, &b_x, &mut cur_col);
                write_u256(&mut nv, &b_y, &mut cur_col);
            } else if is_add == F::ONE {
                write_u256(&mut nv, &a_x, &mut cur_col);
                write_u256(&mut nv, &a_y, &mut cur_col);
                write_u256(&mut nv, &output.new_x, &mut cur_col);
                write_u256(&mut nv, &output.new_y, &mut cur_col);
            } else {
                write_u256(&mut nv, &a_x, &mut cur_col);
                write_u256(&mut nv, &a_y, &mut cur_col);
                write_u256(&mut nv, &b_x, &mut cur_col);
                write_u256(&mut nv, &b_y, &mut cur_col);
            }

            generate_next_pow_instruction(&lv, &mut nv, IS_SQ_COL, IS_MUL_COL, IS_NOOP_COL);

            rows.push(lv);
            lv = nv;
        }

        cur_col = 2 * N_LIMBS;
        let b_x = read_u256(&lv, &mut cur_col);
        let b_y = read_u256(&lv, &mut cur_col);
        let b_x_fq = columns_to_fq(&b_x);
        let b_y_fq = columns_to_fq(&b_y);
        let result = G1Affine::new(b_x_fq, b_y_fq);
        assert!(result == expected);

        let mut trace_cols = transpose(&rows.iter().map(|v| v.to_vec()).collect_vec());

        generate_split_u16_range_check(START_RANGE_CHECK..END_RANGE_CHECK, &mut trace_cols);

        trace_cols
            .into_iter()
            .map(|column| PolynomialValues::new(column))
            .collect()
    }

    pub fn generate_public_inputs(
        x: G1Affine,
        x_exp: G1Affine,
        offset: G1Affine,
        exp_bits: [bool; BITS_LEN],
    ) -> [F; 6 * N_LIMBS + BITS_LEN] {
        let mut pi = [F::ZERO; 6 * N_LIMBS + BITS_LEN];
        let x_columns = fq_to_columns(x.x);
        let y_columns = fq_to_columns(x.y);
        let x_exp_x_columns = fq_to_columns(x_exp.x);
        let x_exp_y_columns = fq_to_columns(x_exp.y);
        let offset_x_columns = fq_to_columns(offset.x);
        let offset_y_columns = fq_to_columns(offset.y);
        let x_f = i64_to_column_positive(x_columns);
        let y_f = i64_to_column_positive(y_columns);
        let x_exp_x_f = i64_to_column_positive(x_exp_x_columns);
        let x_exp_y_f = i64_to_column_positive(x_exp_y_columns);
        let offset_x_f = i64_to_column_positive(offset_x_columns);
        let offset_y_f = i64_to_column_positive(offset_y_columns);
        let exp_bits_f = exp_bits.map(|b| F::from_bool(b));
        let mut cur_col = 0;
        write_u256(&mut pi, &x_f, &mut cur_col);
        write_u256(&mut pi, &y_f, &mut cur_col);
        write_u256(&mut pi, &offset_x_f, &mut cur_col);
        write_u256(&mut pi, &offset_y_f, &mut cur_col);
        write_u256(&mut pi, &x_exp_x_f, &mut cur_col);
        write_u256(&mut pi, &x_exp_y_f, &mut cur_col);
        for i in 0..BITS_LEN {
            pi[cur_col] = exp_bits_f[i];
            cur_col += 1;
        }
        assert!(cur_col == 6 * N_LIMBS + BITS_LEN);
        pi
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
        eval_split_u16_range_check(
            vars,
            yield_constr,
            MAIN_COLS,
            START_RANGE_CHECK..END_RANGE_CHECK,
        );

        let lv = vars.local_values;

        let mut cur_col = 0;
        let a_x = read_u256(lv, &mut cur_col);
        let a_y = read_u256(lv, &mut cur_col);
        let b_x = read_u256(lv, &mut cur_col);
        let b_y = read_u256(lv, &mut cur_col);
        let lambda = read_u256(lv, &mut cur_col);
        let new_x = read_u256(lv, &mut cur_col);
        let new_y = read_u256(lv, &mut cur_col);
        let aux_zero = read_modulus_aux_zero(lv, &mut cur_col);
        let aux_x = read_modulus_aux(lv, &mut cur_col);
        let aux_y = read_modulus_aux(lv, &mut cur_col);

        let quot_sign_zero = lv[cur_col];
        cur_col += 1;
        let quot_sign_x = lv[cur_col];
        cur_col += 1;
        let quot_sign_y = lv[cur_col];
        cur_col += 1;

        assert!(cur_col == 24 * N_LIMBS);

        let is_add = lv[IS_MUL_COL];
        let is_double = lv[IS_SQ_COL];
        let is_noop = lv[IS_NOOP_COL];

        cur_col = IS_MUL_COL;
        let bits: [_; BITS_LEN] = read_instruction(lv, &mut cur_col);

        // assert!(cur_col == MAIN_COLS);
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

        // public inputs
        let pi = vars.public_inputs;
        let pi: [P; PUBLIC_INPUTS] = pi.map(|x| x.into());
        cur_col = 0;
        let pi_a_x = read_u256(&pi, &mut cur_col);
        let pi_a_y = read_u256(&pi, &mut cur_col);
        let pi_b_x = read_u256(&pi, &mut cur_col);
        let pi_b_y = read_u256(&pi, &mut cur_col);
        let pi_final_x = read_u256(&pi, &mut cur_col);
        let pi_final_y = read_u256(&pi, &mut cur_col);
        let pi_bits: [_; BITS_LEN] = read_instruction(&pi, &mut cur_col);
        fq_equal_first(yield_constr, pi_a_x, a_x);
        fq_equal_first(yield_constr, pi_a_y, a_y);
        fq_equal_first(yield_constr, pi_b_x, b_x);
        fq_equal_first(yield_constr, pi_b_y, b_y);
        fq_equal_last(yield_constr, pi_final_x, b_x);
        fq_equal_last(yield_constr, pi_final_y, b_y);
        for i in 0..BITS_LEN {
            yield_constr.constraint_first_row(pi_bits[i] - bits[i]);
        }

        // transition
        let nv = vars.next_values;
        let mut cur_col = 0;
        let next_a_x = read_u256(nv, &mut cur_col);
        let next_a_y = read_u256(nv, &mut cur_col);
        let next_b_x = read_u256(nv, &mut cur_col);
        let next_b_y = read_u256(nv, &mut cur_col);

        // if is_double
        fq_equal_transition(yield_constr, is_double, &next_a_x, &new_x);
        fq_equal_transition(yield_constr, is_double, &next_a_y, &new_y);
        fq_equal_transition(yield_constr, is_double, &next_b_x, &b_x);
        fq_equal_transition(yield_constr, is_double, &next_b_y, &b_y);
        // if is_add
        fq_equal_transition(yield_constr, is_add, &next_a_x, &a_x);
        fq_equal_transition(yield_constr, is_add, &next_a_y, &a_y);
        fq_equal_transition(yield_constr, is_add, &next_b_x, &new_x);
        fq_equal_transition(yield_constr, is_add, &next_b_y, &new_y);
        // if is_noop
        fq_equal_transition(yield_constr, is_noop, &next_a_x, &a_x);
        fq_equal_transition(yield_constr, is_noop, &next_a_y, &a_y);
        fq_equal_transition(yield_constr, is_noop, &next_b_x, &b_x);
        fq_equal_transition(yield_constr, is_noop, &next_b_y, &b_y);

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
        let a_x = read_u256(lv, &mut cur_col);
        let a_y = read_u256(lv, &mut cur_col);
        let b_x = read_u256(lv, &mut cur_col);
        let b_y = read_u256(lv, &mut cur_col);
        let lambda = read_u256(lv, &mut cur_col);
        let new_x = read_u256(lv, &mut cur_col);
        let new_y = read_u256(lv, &mut cur_col);
        let aux_zero = read_modulus_aux_zero(lv, &mut cur_col);
        let aux_x = read_modulus_aux(lv, &mut cur_col);
        let aux_y = read_modulus_aux(lv, &mut cur_col);

        let quot_sign_zero = lv[cur_col];
        cur_col += 1;
        let quot_sign_x = lv[cur_col];
        cur_col += 1;
        let quot_sign_y = lv[cur_col];
        cur_col += 1;

        assert!(cur_col == 24 * N_LIMBS);
        cur_col = IS_MUL_COL;
        let bits: [_; BITS_LEN] = read_instruction(lv, &mut cur_col);

        let is_add = lv[IS_MUL_COL];
        let is_double = lv[IS_SQ_COL];
        let is_noop = lv[IS_NOOP_COL];

        // assert!(cur_col == MAIN_COLS);
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

        // public inputs
        let pi = vars.public_inputs;
        cur_col = 0;
        let pi_a_x = read_u256(pi, &mut cur_col);
        let pi_a_y = read_u256(pi, &mut cur_col);
        let pi_b_x = read_u256(pi, &mut cur_col);
        let pi_b_y = read_u256(pi, &mut cur_col);
        let pi_final_x = read_u256(pi, &mut cur_col);
        let pi_final_y = read_u256(pi, &mut cur_col);
        let pi_bits: [_; BITS_LEN] = read_instruction(&pi, &mut cur_col);
        fq_equal_first_circuit(builder, yield_constr, pi_a_x, a_x);
        fq_equal_first_circuit(builder, yield_constr, pi_a_y, a_y);
        fq_equal_first_circuit(builder, yield_constr, pi_b_x, b_x);
        fq_equal_first_circuit(builder, yield_constr, pi_b_y, b_y);
        fq_equal_last_circuit(builder, yield_constr, pi_final_x, b_x);
        fq_equal_last_circuit(builder, yield_constr, pi_final_y, b_y);
        for i in 0..BITS_LEN {
            let diff = builder.sub_extension(pi_bits[i], bits[i]);
            yield_constr.constraint_first_row(builder, diff);
        }

        // transition
        let nv = vars.next_values;
        let mut cur_col = 0;
        let next_a_x = read_u256(nv, &mut cur_col);
        let next_a_y = read_u256(nv, &mut cur_col);
        let next_b_x = read_u256(nv, &mut cur_col);
        let next_b_y = read_u256(nv, &mut cur_col);

        // if is_double
        fq_equal_transition_circuit(builder, yield_constr, is_double, &next_a_x, &new_x);
        fq_equal_transition_circuit(builder, yield_constr, is_double, &next_a_y, &new_y);
        fq_equal_transition_circuit(builder, yield_constr, is_double, &next_b_x, &b_x);
        fq_equal_transition_circuit(builder, yield_constr, is_double, &next_b_y, &b_y);
        // if is_add
        fq_equal_transition_circuit(builder, yield_constr, is_add, &next_a_x, &a_x);
        fq_equal_transition_circuit(builder, yield_constr, is_add, &next_a_y, &a_y);
        fq_equal_transition_circuit(builder, yield_constr, is_add, &next_b_x, &new_x);
        fq_equal_transition_circuit(builder, yield_constr, is_add, &next_b_y, &new_y);
        // if is_noop
        fq_equal_transition_circuit(builder, yield_constr, is_noop, &next_a_x, &a_x);
        fq_equal_transition_circuit(builder, yield_constr, is_noop, &next_a_y, &a_y);
        fq_equal_transition_circuit(builder, yield_constr, is_noop, &next_b_x, &b_x);
        fq_equal_transition_circuit(builder, yield_constr, is_noop, &next_b_y, &b_y);

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

    use crate::{
        constants::BITS_LEN,
        g1_exp::G1ExpStark,
        utils::{biguint_to_bits, bits_to_biguint},
    };
    use ark_bn254::{Fr, G1Affine};
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
    fn test_biguint_to_bits() {
        let mut rng = rand::thread_rng();
        let exp_val = Fr::rand(&mut rng);
        let exp_bits = biguint_to_bits(&exp_val.into(), BITS_LEN);
        let recovered: Fr = bits_to_biguint(&exp_bits).into();

        assert!(exp_val == recovered);
    }

    #[test]
    fn test_g1_exp() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let mut rng = rand::thread_rng();
        let exp_val: Fr = Fr::rand(&mut rng);
        let exp_bits: [bool; BITS_LEN] = biguint_to_bits(&exp_val.into(), BITS_LEN)
            .try_into()
            .unwrap();
        let x = G1Affine::rand(&mut rng);
        let offset = G1Affine::rand(&mut rng);
        let x_exp: G1Affine = (x * exp_val + offset).into();

        type S = G1ExpStark<F, D>;
        let inner_config = StarkConfig::standard_fast_config();
        let stark = S::new();
        let trace = stark.generate_trace(x, offset, x_exp, exp_bits);

        println!("start stark proof generation");
        let now = Instant::now();
        let pi = S::generate_public_inputs(x, x_exp, offset, exp_bits);
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
        verify_stark_proof_circuit::<F, C, S, D>(&mut builder, stark, pt, &inner_config);
        let data = builder.build::<C>();

        println!("start plonky2 proof generation");
        let now = Instant::now();
        let _proof = data.prove(pw).unwrap();
        println!("end plonky2 proof generation: {:?}", now.elapsed());

        dbg!(degree_bits);
    }
}

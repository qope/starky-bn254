use core::fmt;
use core::marker::PhantomData;

use ark_bn254::{g1, Fq, Fq12, Fr, G1Affine};
use ark_ff::Field;
use ark_std::{UniformRand, Zero};
use itertools::Itertools;
use num::Signed;
use num_bigint::{BigInt, BigUint, Sign};
use plonky2::field::types::{Field as plonky2_field, PrimeField64};
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

use crate::develop::constants::LIMB_BITS;
use crate::develop::fq12::{
    generate_fq12_modular_op, pol_mul_fq12, pol_mul_fq12_ext_circuit, read_fq12, write_fq12,
};
use crate::develop::modular_zero::{generate_modular_zero, write_modulus_aux_zero};
use crate::develop::range_check::{
    eval_u16_range_check, eval_u16_range_check_circuit, generate_u16_range_check,
};
use crate::develop::utils::{
    bigint_to_columns, biguint_to_bits, columns_to_bigint, columns_to_fq, columns_to_fq12,
    fq12_to_columns, fq_to_columns, i64_to_column_positive, pol_add, pol_add_normal, pol_mul_wide,
    pol_mul_wide2, pol_remove_root_2exp, pol_sub, pol_sub_assign, pol_sub_normal,
    positive_column_to_i64,
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
    write_u256, AUX_COEFF_ABS_MAX,
};

use super::modular::{bn254_base_modulus_packfield, eval_modular_op, read_u256, ModulusAux};
use super::modular_zero::{eval_modular_zero, read_modulus_aux_zero};
use super::range_check::u16_range_check_pairs;
use super::utils::{
    pol_add_assign, pol_add_assign_ext_circuit, pol_adjoin_root, pol_adjoin_root_ext_circuit,
    pol_mul_wide2_ext_circuit, pol_sub_assign_ext_circuit,
};

const MAIN_COLS: usize = 24 * N_LIMBS + 1;
const ROWS: usize = 1 << 8;

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
        let modulus = bn254_base_modulus_bigint();

        let mut rows = vec![];

        for _ in 0..ROWS {
            let a_g1 = g1::G1Affine::rand(&mut rng);
            let b_g1 = g1::G1Affine::rand(&mut rng);
            let output_expected: G1Affine = (a_g1 + b_g1).into();

            let lambda_fq: Fq = ((b_g1.y - a_g1.y) / (b_g1.x - a_g1.x)).into();

            let a_x_i64 = fq_to_columns(a_g1.x);
            let a_y_i64 = fq_to_columns(a_g1.y);
            let b_x_i64 = fq_to_columns(b_g1.x);
            let b_y_i64 = fq_to_columns(b_g1.y);
            let lambda_i64 = fq_to_columns(lambda_fq);

            let delta_x = pol_sub_normal(b_x_i64, a_x_i64);
            let delta_y = pol_sub(b_y_i64, a_y_i64);
            let lambda_delta_x = pol_mul_wide(lambda_i64, delta_x);
            let zero_pol = pol_sub_normal(lambda_delta_x, delta_y);
            let (quot_sign_zero, aux_zero) = generate_modular_zero(&modulus, zero_pol);

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

            let mut lv = [F::ZERO; MAIN_COLS];

            let mut cur_col = 0;
            let a_x = i64_to_column_positive(a_x_i64);
            let a_y = i64_to_column_positive(a_y_i64);
            let b_x = i64_to_column_positive(b_x_i64);
            let b_y = i64_to_column_positive(b_y_i64);
            let lambda = i64_to_column_positive(lambda_i64);

            let new_x_fq = columns_to_fq(&new_x);
            let new_y_fq = columns_to_fq(&new_y);
            assert!(output_expected.x == new_x_fq && output_expected.y == new_y_fq);

            write_u256(&mut lv, &a_x, &mut cur_col); // N_LIMBS
            write_u256(&mut lv, &a_y, &mut cur_col); // N_LIMBS
            write_u256(&mut lv, &b_x, &mut cur_col); // N_LIMBS
            write_u256(&mut lv, &b_y, &mut cur_col); // N_LIMBS
            write_u256(&mut lv, &lambda, &mut cur_col); // N_LIMBS
            write_u256(&mut lv, &new_x, &mut cur_col); // N_LIMBS
            write_u256(&mut lv, &new_y, &mut cur_col); // N_LIMBS

            // 5*N_LIMBS - 1
            write_modulus_aux_zero(&mut lv, &aux_zero, &mut cur_col);

            // 12*N_LIMBS - 2
            write_modulus_aux(&mut lv, &aux_x, &mut cur_col);
            write_modulus_aux(&mut lv, &aux_y, &mut cur_col);

            // 3
            lv[cur_col] = quot_sign_zero;
            cur_col += 1;
            lv[cur_col] = quot_sign_x;
            cur_col += 1;
            lv[cur_col] = quot_sign_y;
            cur_col += 1;

            // filter, 1
            lv[cur_col] = F::ONE;
            cur_col += 1;

            // MAIN_COLS = 7*N_LIMBS + 17*N_LIMBS - 3 + 3 + 1 = 24*N_LIMBS  + 1
            assert!(cur_col == MAIN_COLS);

            rows.push(lv);
        }

        let mut trace_cols = transpose(&rows.iter().map(|v| v.to_vec()).collect_vec());

        trace_cols
            .into_iter()
            .map(|column| PolynomialValues::new(column))
            .collect()
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D> for G1Stark<F, D> {
    const COLUMNS: usize = MAIN_COLS;
    const PUBLIC_INPUTS: usize = 0;

    fn eval_packed_generic<FE, P, const D2: usize>(
        &self,
        vars: StarkEvaluationVars<FE, P, { Self::COLUMNS }, { Self::PUBLIC_INPUTS }>,
        yield_constr: &mut ConstraintConsumer<P>,
    ) where
        FE: FieldExtension<D2, BaseField = F>,
        P: PackedField<Scalar = FE>,
    {
        let modulus = bn254_base_modulus_packfield();
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

        let filter = lv[cur_col];
        cur_col += 1;
        assert!(cur_col == MAIN_COLS);

        let delta_x = pol_sub_normal(b_x, a_x);
        let delta_y = pol_sub(b_y, a_y);
        let lambda_delta_x = pol_mul_wide(lambda, delta_x);
        let zero_pol = pol_sub_normal(lambda_delta_x, delta_y);
        eval_modular_zero(
            yield_constr,
            filter,
            modulus,
            zero_pol,
            quot_sign_zero,
            aux_zero,
        );

        let x1_add_x2 = pol_add(a_x, b_x);
        let lambda_sq = pol_mul_wide(lambda, lambda);
        let new_x_input = pol_sub_normal(lambda_sq, x1_add_x2);
        eval_modular_op(
            yield_constr,
            filter,
            modulus,
            new_x_input,
            new_x,
            quot_sign_x,
            &aux_x,
        );

        let x1_minus_new_x = pol_sub_normal(a_x, new_x);
        let lambda_mul_x1_minus_new_x = pol_mul_wide(lambda, x1_minus_new_x);

        let mut y1_wide = [P::ZEROS; 2 * N_LIMBS - 1];
        y1_wide[0..N_LIMBS].copy_from_slice(&a_y);
        let new_y_input = pol_sub_normal(lambda_mul_x1_minus_new_x, y1_wide);
        eval_modular_op(
            yield_constr,
            filter,
            modulus,
            new_y_input,
            new_y,
            quot_sign_y,
            &aux_y,
        );
    }

    fn eval_ext_circuit(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        vars: StarkEvaluationTargets<D, { Self::COLUMNS }, { Self::PUBLIC_INPUTS }>,
        yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    ) {
        todo!()
    }

    fn constraint_degree(&self) -> usize {
        3
    }

    // fn permutation_pairs(&self) -> Vec<PermutationPair> {
    //     u16_range_check_pairs(MAIN_COLS, START_RANGE_CHECK..END_RANGE_CHECK)
    // }
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
        develop::{fq12_exp::Fq12ExpStark, g1::G1Stark},
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

        // let circuit_config = CircuitConfig::standard_recursion_config();
        // let mut builder = CircuitBuilder::<F, D>::new(circuit_config);
        // let mut pw = PartialWitness::new();
        // let degree_bits = inner_proof.proof.recover_degree_bits(&inner_config);
        // let pt = add_virtual_stark_proof_with_pis(&mut builder, stark, &inner_config, degree_bits);
        // set_stark_proof_with_pis_target(&mut pw, &pt, &inner_proof);
        // verify_stark_proof_circuit::<F, C, S, D>(&mut builder, stark, pt, &inner_config);
        // let data = builder.build::<C>();

        // println!("start plonky2 proof generation");
        // let now = Instant::now();
        // let _proof = data.prove(pw).unwrap();
        // println!("end plonky2 proof generation: {:?}", now.elapsed());
    }
}

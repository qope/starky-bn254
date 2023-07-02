use core::ops::*;

use plonky2::{
    field::extension::Extendable, hash::hash_types::RichField, iop::ext_target::ExtensionTarget,
    plonk::circuit_builder::CircuitBuilder,
};

use crate::{
    constants::N_LIMBS,
    util::{
        pol_add_assign, pol_add_assign_ext_circuit, pol_add_wide, pol_add_wide_ext_circuit,
        pol_mul_const, pol_mul_const_ext_circuit, pol_mul_wide, pol_mul_wide_ext_circuit,
        pol_sub_assign, pol_sub_assign_ext_circuit, pol_sub_wide, pol_sub_wide_ext_circuit,
    },
};

pub fn pol_mul_fq12<T>(
    a_coeffs: Vec<[T; N_LIMBS]>,
    b_coeffs: Vec<[T; N_LIMBS]>,
    xi: T,
) -> Vec<[T; 2 * N_LIMBS - 1]>
where
    T: Add<Output = T> + AddAssign + Sub<Output = T> + SubAssign + Mul<Output = T> + Copy + Default,
{
    let mut a0b0_coeffs: Vec<[T; 2 * N_LIMBS - 1]> = Vec::with_capacity(11);
    let mut a0b1_coeffs: Vec<[T; 2 * N_LIMBS - 1]> = Vec::with_capacity(11);
    let mut a1b0_coeffs: Vec<[T; 2 * N_LIMBS - 1]> = Vec::with_capacity(11);
    let mut a1b1_coeffs: Vec<[T; 2 * N_LIMBS - 1]> = Vec::with_capacity(11);
    for i in 0..6 {
        for j in 0..6 {
            let coeff00 = pol_mul_wide(a_coeffs[i], b_coeffs[j]);
            let coeff01 = pol_mul_wide(a_coeffs[i], b_coeffs[j + 6]);
            let coeff10 = pol_mul_wide(a_coeffs[i + 6], b_coeffs[j]);
            let coeff11 = pol_mul_wide(a_coeffs[i + 6], b_coeffs[j + 6]);
            if i + j < a0b0_coeffs.len() {
                pol_add_assign(&mut a0b0_coeffs[i + j], &coeff00);
                pol_add_assign(&mut a0b1_coeffs[i + j], &coeff01);
                pol_add_assign(&mut a1b0_coeffs[i + j], &coeff10);
                pol_add_assign(&mut a1b1_coeffs[i + j], &coeff11);
            } else {
                a0b0_coeffs.push(coeff00);
                a0b1_coeffs.push(coeff01);
                a1b0_coeffs.push(coeff10);
                a1b1_coeffs.push(coeff11);
            }
        }
    }

    let mut a0b0_minus_a1b1: Vec<[T; 2 * N_LIMBS - 1]> = Vec::with_capacity(11);
    let mut a0b1_plus_a1b0: Vec<[T; 2 * N_LIMBS - 1]> = Vec::with_capacity(11);
    for i in 0..11 {
        let a0b0_minus_a1b1_entry = pol_sub_wide(a0b0_coeffs[i], a1b1_coeffs[i]);
        let a0b1_plus_a1b0_entry = pol_add_wide(a0b1_coeffs[i], a1b0_coeffs[i]);
        a0b0_minus_a1b1.push(a0b0_minus_a1b1_entry);
        a0b1_plus_a1b0.push(a0b1_plus_a1b0_entry);
    }

    let mut out_coeffs: Vec<[T; 2 * N_LIMBS - 1]> = Vec::with_capacity(12);
    for i in 0..6 {
        if i < 5 {
            let nine_times_a0b0_minus_a1b1 = pol_mul_const(a0b0_minus_a1b1[i + 6], xi);
            let mut coeff = pol_add_wide(a0b0_minus_a1b1[i], nine_times_a0b0_minus_a1b1);
            pol_sub_assign(&mut coeff, &a0b1_plus_a1b0[i + 6]);
            out_coeffs.push(coeff);
        } else {
            out_coeffs.push(a0b0_minus_a1b1[i].clone());
        }
    }
    for i in 0..6 {
        if i < 5 {
            let mut coeff = pol_add_wide(a0b1_plus_a1b0[i], a0b0_minus_a1b1[i + 6]);
            let nine_times_a0b1_plus_a1b0 = pol_mul_const(a0b1_plus_a1b0[i + 6], xi);
            pol_add_assign(&mut coeff, &nine_times_a0b1_plus_a1b0);
            out_coeffs.push(coeff);
        } else {
            out_coeffs.push(a0b1_plus_a1b0[i].clone());
        }
    }
    out_coeffs
}

pub fn pol_mul_fq12_ext_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a_coeffs: Vec<[ExtensionTarget<D>; N_LIMBS]>,
    b_coeffs: Vec<[ExtensionTarget<D>; N_LIMBS]>,
    xi: F::Extension,
) -> Vec<[ExtensionTarget<D>; 2 * N_LIMBS - 1]> {
    let mut a0b0_coeffs: Vec<[ExtensionTarget<D>; 2 * N_LIMBS - 1]> = Vec::with_capacity(11);
    let mut a0b1_coeffs: Vec<[ExtensionTarget<D>; 2 * N_LIMBS - 1]> = Vec::with_capacity(11);
    let mut a1b0_coeffs: Vec<[ExtensionTarget<D>; 2 * N_LIMBS - 1]> = Vec::with_capacity(11);
    let mut a1b1_coeffs: Vec<[ExtensionTarget<D>; 2 * N_LIMBS - 1]> = Vec::with_capacity(11);
    for i in 0..6 {
        for j in 0..6 {
            let coeff00 = pol_mul_wide_ext_circuit(builder, a_coeffs[i], b_coeffs[j]);
            let coeff01 = pol_mul_wide_ext_circuit(builder, a_coeffs[i], b_coeffs[j + 6]);
            let coeff10 = pol_mul_wide_ext_circuit(builder, a_coeffs[i + 6], b_coeffs[j]);
            let coeff11 = pol_mul_wide_ext_circuit(builder, a_coeffs[i + 6], b_coeffs[j + 6]);
            if i + j < a0b0_coeffs.len() {
                pol_add_assign_ext_circuit(builder, &mut a0b0_coeffs[i + j], &coeff00);
                pol_add_assign_ext_circuit(builder, &mut a0b1_coeffs[i + j], &coeff01);
                pol_add_assign_ext_circuit(builder, &mut a1b0_coeffs[i + j], &coeff10);
                pol_add_assign_ext_circuit(builder, &mut a1b1_coeffs[i + j], &coeff11);
            } else {
                a0b0_coeffs.push(coeff00);
                a0b1_coeffs.push(coeff01);
                a1b0_coeffs.push(coeff10);
                a1b1_coeffs.push(coeff11);
            }
        }
    }

    let mut a0b0_minus_a1b1: Vec<[ExtensionTarget<D>; 2 * N_LIMBS - 1]> = Vec::with_capacity(11);
    let mut a0b1_plus_a1b0: Vec<[ExtensionTarget<D>; 2 * N_LIMBS - 1]> = Vec::with_capacity(11);
    for i in 0..11 {
        let a0b0_minus_a1b1_entry =
            pol_sub_wide_ext_circuit(builder, a0b0_coeffs[i], a1b1_coeffs[i]);
        let a0b1_plus_a1b0_entry =
            pol_add_wide_ext_circuit(builder, a0b1_coeffs[i], a1b0_coeffs[i]);
        a0b0_minus_a1b1.push(a0b0_minus_a1b1_entry);
        a0b1_plus_a1b0.push(a0b1_plus_a1b0_entry);
    }

    let mut out_coeffs: Vec<[ExtensionTarget<D>; 2 * N_LIMBS - 1]> = Vec::with_capacity(12);
    for i in 0..6 {
        if i < 5 {
            let nine_times_a0b0_minus_a1b1 =
                pol_mul_const_ext_circuit(builder, a0b0_minus_a1b1[i + 6], xi);
            let mut coeff =
                pol_add_wide_ext_circuit(builder, a0b0_minus_a1b1[i], nine_times_a0b0_minus_a1b1);
            pol_sub_assign_ext_circuit(builder, &mut coeff, &a0b1_plus_a1b0[i + 6]);
            out_coeffs.push(coeff);
        } else {
            out_coeffs.push(a0b0_minus_a1b1[i].clone());
        }
    }
    for i in 0..6 {
        if i < 5 {
            let mut coeff =
                pol_add_wide_ext_circuit(builder, a0b1_plus_a1b0[i], a0b0_minus_a1b1[i + 6]);
            let nine_times_a0b1_plus_a1b0 =
                pol_mul_const_ext_circuit(builder, a0b1_plus_a1b0[i + 6], xi);
            pol_add_assign_ext_circuit(builder, &mut coeff, &nine_times_a0b1_plus_a1b0);
            out_coeffs.push(coeff);
        } else {
            out_coeffs.push(a0b1_plus_a1b0[i].clone());
        }
    }
    out_coeffs
}

#[cfg(test)]
mod tests {
    use core::marker::PhantomData;

    use ark_bn254::{Fq, Fq12};
    use ark_std::UniformRand;
    use itertools::Itertools;
    use num::FromPrimitive;
    use num_bigint::{BigInt, BigUint};
    use plonky2::{
        field::{
            extension::{Extendable, FieldExtension},
            packed::PackedField,
            polynomial::PolynomialValues,
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

    use crate::{
        config::StarkConfig,
        constants::{LIMB_BITS, N_LIMBS},
        constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer},
        develop::{
            fq12::{pol_mul_fq12, pol_mul_fq12_ext_circuit},
            modular::{read_quot, write_modulus_aux, write_quot, write_u256},
        },
        lookup::{eval_lookups, eval_lookups_circuit, generate_range_checks},
        permutation::PermutationPair,
        prover::prove,
        recursive_verifier::{
            add_virtual_stark_proof_with_pis, set_stark_proof_with_pis_target,
            verify_stark_proof_circuit,
        },
        stark::Stark,
        util::{
            bigint_to_columns, columns_to_fq12, fq12_to_columns, pol_sub_assign,
            pol_sub_assign_ext_circuit,
        },
        vars::{StarkEvaluationTargets, StarkEvaluationVars},
        verifier::verify_stark_proof,
    };

    use crate::develop::modular::{
        generate_modular_op, modular_constr_poly, modular_constr_poly_ext_circuit,
        read_modulus_aux, read_u256, ModulusAux,
    };

    const RANGE32_COLS: usize = 96 * N_LIMBS - 24;
    const MAIN_COLS: usize = RANGE32_COLS + 25 * N_LIMBS + 1;
    const TABLE_COL: usize = MAIN_COLS;

    #[derive(Clone, Copy)]
    pub struct Fq12Stark<F: RichField + Extendable<D>, const D: usize> {
        _phantom: PhantomData<F>,
    }

    impl<F: RichField + Extendable<D>, const D: usize> Fq12Stark<F, D> {
        pub fn new() -> Self {
            Self {
                _phantom: PhantomData,
            }
        }

        pub fn generate_trace(&self) -> Vec<PolynomialValues<F>> {
            let mut rng = rand::thread_rng();
            let neg_one: BigUint = Fq::from(-1).into();
            let modulus_biguint: BigUint = neg_one + BigUint::from_usize(1).unwrap();
            let modulus_bigint: BigInt = modulus_biguint.into();
            let modulus: [F; N_LIMBS] =
                bigint_to_columns(&modulus_bigint).map(|x| F::from_canonical_i64(x));

            let mut rows = vec![];

            for _ in 0..1 << 2 {
                let input0_fq12 = Fq12::rand(&mut rng);
                let input1_fq12 = Fq12::rand(&mut rng);
                let output_expected: Fq12 = input0_fq12 * input1_fq12;

                let input0_limbs = fq12_to_columns(input0_fq12);
                let input1_limbs = fq12_to_columns(input1_fq12);

                let pol_input = pol_mul_fq12(input0_limbs.clone(), input1_limbs.clone(), 9);

                let input0_coeffs = input0_limbs
                    .iter()
                    .map(|coeff| coeff.map(|x| F::from_canonical_i64(x)))
                    .collect_vec();
                let input1_coeffs = input1_limbs
                    .iter()
                    .map(|coeff| coeff.map(|x| F::from_canonical_i64(x)))
                    .collect_vec();

                let mut output_coeffs = vec![];
                let mut auxs = vec![];
                let mut quots = vec![];

                for i in 0..12 {
                    let (output, quot, aux) =
                        generate_modular_op::<F>(modulus_bigint.clone(), pol_input[i]);
                    output_coeffs.push(output);
                    auxs.push(aux);
                    quots.push(quot);
                }

                let output_actual = columns_to_fq12(&output_coeffs);

                assert!(output_expected == output_actual);

                let mut lv = [F::ZERO; MAIN_COLS];

                let mut cur_col = 0;

                input0_coeffs
                    .iter()
                    .for_each(|coeff| write_u256(&mut lv, coeff, &mut cur_col));

                input1_coeffs
                    .iter()
                    .for_each(|coeff| write_u256(&mut lv, coeff, &mut cur_col));
                output_coeffs
                    .iter()
                    .for_each(|coeff| write_u256(&mut lv, coeff, &mut cur_col));
                auxs.iter().for_each(|aux| {
                    write_modulus_aux::<_, MAIN_COLS, N_LIMBS>(&mut lv, aux, &mut cur_col);
                });

                quots.iter().for_each(|quot| {
                    write_quot(&mut lv, quot, &mut cur_col);
                });

                write_u256(&mut lv, &modulus, &mut cur_col);

                lv[cur_col] = F::ONE;
                cur_col += 1;

                assert!(cur_col == MAIN_COLS);

                auxs.iter().for_each(|aux| {
                    let ModulusAux {
                        out_aux_red,
                        aux_input_lo,
                        aux_input_hi,
                    } = aux;
                    assert!(out_aux_red
                        .iter()
                        .all(|x| x.to_canonical_u64() < (1 << LIMB_BITS)));
                    assert!(aux_input_lo
                        .iter()
                        .all(|x| x.to_canonical_u64() < (1 << LIMB_BITS)));
                    assert!(aux_input_hi
                        .iter()
                        .all(|x| x.to_canonical_u64() < (1 << LIMB_BITS)));
                });
                rows.push(lv);
            }

            let range_max = 1 << LIMB_BITS;
            let padded_len = rows.len().next_power_of_two();
            for _ in rows.len()..std::cmp::max(padded_len, range_max) {
                rows.push([F::ZERO; MAIN_COLS]);
            }

            let mut trace_cols = transpose(&rows.iter().map(|v| v.to_vec()).collect_vec());

            let range_check_cols = trace_cols[0..RANGE32_COLS].to_vec();
            let (table, pairs) = generate_range_checks(range_max, &range_check_cols);

            trace_cols.push(table);
            pairs.iter().for_each(|(c_perm, t_perm)| {
                trace_cols.push(c_perm.to_vec());
                trace_cols.push(t_perm.to_vec());
            });

            trace_cols
                .into_iter()
                .map(|column| PolynomialValues::new(column))
                .collect()
        }
    }

    impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D> for Fq12Stark<F, D> {
        const COLUMNS: usize = MAIN_COLS + 1 + 2 * RANGE32_COLS;
        const PUBLIC_INPUTS: usize = 0;

        fn eval_packed_generic<FE, P, const D2: usize>(
            &self,
            vars: StarkEvaluationVars<FE, P, { Self::COLUMNS }, { Self::PUBLIC_INPUTS }>,
            yield_constr: &mut ConstraintConsumer<P>,
        ) where
            FE: FieldExtension<D2, BaseField = F>,
            P: PackedField<Scalar = FE>,
        {
            let lv = vars.local_values.clone();

            for i in (MAIN_COLS + 1..MAIN_COLS + 1 + 2 * RANGE32_COLS).step_by(2) {
                eval_lookups(vars, yield_constr, i, i + 1);
            }

            let mut cur_col = 0;

            let input0_coeffs = (0..12)
                .map(|_| read_u256::<_, N_LIMBS>(&lv, &mut cur_col))
                .collect_vec();
            let input1_coeffs = (0..12)
                .map(|_| read_u256::<_, N_LIMBS>(&lv, &mut cur_col))
                .collect_vec();
            let output_coeffs = (0..12)
                .map(|_| read_u256::<_, N_LIMBS>(&lv, &mut cur_col))
                .collect_vec();

            let auxs = (0..12)
                .map(|_| read_modulus_aux::<_, N_LIMBS>(&lv, &mut cur_col))
                .collect_vec();

            let quots = (0..12)
                .map(|_| read_quot::<_, { 2 * N_LIMBS }>(&lv, &mut cur_col))
                .collect_vec();
            let modulus: [_; N_LIMBS] = read_u256(&lv, &mut cur_col);

            let filter = lv[cur_col];
            cur_col += 1;

            assert!(cur_col == MAIN_COLS);

            let xi: P = P::ONES
                + P::ONES
                + P::ONES
                + P::ONES
                + P::ONES
                + P::ONES
                + P::ONES
                + P::ONES
                + P::ONES;
            let input_coeffs = pol_mul_fq12(input0_coeffs, input1_coeffs, xi);

            for i in 0..12 {
                let ModulusAux {
                    out_aux_red,
                    aux_input_lo,
                    aux_input_hi,
                } = auxs[i];

                let constr_poly = modular_constr_poly::<P>(
                    yield_constr,
                    filter,
                    modulus,
                    output_coeffs[i],
                    out_aux_red,
                    quots[i],
                    aux_input_lo,
                    aux_input_hi,
                );

                let mut constr_poly_copy = constr_poly;
                pol_sub_assign(&mut constr_poly_copy, &input_coeffs[i]);
                for &c in constr_poly_copy.iter() {
                    yield_constr.constraint(filter * c);
                }
            }
        }

        fn eval_ext_circuit(
            &self,
            builder: &mut CircuitBuilder<F, D>,
            vars: StarkEvaluationTargets<D, { Self::COLUMNS }, { Self::PUBLIC_INPUTS }>,
            yield_constr: &mut RecursiveConstraintConsumer<F, D>,
        ) {
            let lv = vars.local_values.clone();

            for i in (MAIN_COLS + 1..MAIN_COLS + 1 + 2 * RANGE32_COLS).step_by(2) {
                eval_lookups_circuit(builder, vars, yield_constr, i, i + 1);
            }

            let mut cur_col = 0;

            let input0_coeffs = (0..12)
                .map(|_| read_u256::<_, N_LIMBS>(&lv, &mut cur_col))
                .collect_vec();
            let input1_coeffs = (0..12)
                .map(|_| read_u256::<_, N_LIMBS>(&lv, &mut cur_col))
                .collect_vec();
            let output_coeffs = (0..12)
                .map(|_| read_u256::<_, N_LIMBS>(&lv, &mut cur_col))
                .collect_vec();

            let auxs = (0..12)
                .map(|_| read_modulus_aux::<_, N_LIMBS>(&lv, &mut cur_col))
                .collect_vec();

            let quots = (0..12)
                .map(|_| read_quot::<_, { 2 * N_LIMBS }>(&lv, &mut cur_col))
                .collect_vec();
            let modulus: [_; N_LIMBS] = read_u256(&lv, &mut cur_col);

            let filter = lv[cur_col];
            cur_col += 1;

            assert!(cur_col == MAIN_COLS);

            let mut nine = [F::ZERO; D];
            nine[0] = F::from_canonical_usize(9);
            let xi = F::Extension::from_basefield_array(nine);
            let input_coeffs = pol_mul_fq12_ext_circuit(builder, input0_coeffs, input1_coeffs, xi);

            for i in 0..12 {
                let ModulusAux {
                    out_aux_red,
                    aux_input_lo,
                    aux_input_hi,
                } = auxs[i];

                let constr_poly = modular_constr_poly_ext_circuit(
                    builder,
                    yield_constr,
                    filter,
                    modulus,
                    output_coeffs[i],
                    out_aux_red,
                    quots[i],
                    aux_input_lo,
                    aux_input_hi,
                );

                let mut constr_poly_copy = constr_poly;
                pol_sub_assign_ext_circuit(builder, &mut constr_poly_copy, &input_coeffs[i]);
                for &c in constr_poly_copy.iter() {
                    let t = builder.mul_extension(filter, c);
                    yield_constr.constraint(builder, t);
                }
            }
        }

        fn constraint_degree(&self) -> usize {
            3
        }

        fn permutation_pairs(&self) -> Vec<PermutationPair> {
            let mut pairs = (0..RANGE32_COLS)
                .map(|i| PermutationPair::singletons(i, MAIN_COLS + 1 + 2 * i))
                .collect_vec();
            let pairs_table = (0..RANGE32_COLS)
                .map(|i| PermutationPair::singletons(TABLE_COL, MAIN_COLS + 2 + 2 * i))
                .collect_vec();

            pairs.extend(pairs_table);

            pairs
        }
    }

    #[test]
    fn test_fq12_stark() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type S = Fq12Stark<F, D>;

        let inner_config = StarkConfig::standard_fast_config();

        let stark = S::new();
        let trace = stark.generate_trace();
        let public_inputs = vec![];
        let inner_proof = prove::<F, C, S, D>(
            stark,
            &inner_config,
            trace,
            public_inputs.try_into().unwrap(),
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

        verify_stark_proof_circuit::<F, C, S, D>(&mut builder, stark, pt, &inner_config);

        let data = builder.build::<C>();
        let _proof = data.prove(pw).unwrap();
    }
}

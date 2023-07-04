use core::fmt::Debug;
use core::ops::*;
use itertools::Itertools;
use num_bigint::BigInt;
use plonky2::{
    field::{extension::Extendable, types::PrimeField64},
    hash::hash_types::RichField,
    iop::ext_target::ExtensionTarget,
    plonk::circuit_builder::CircuitBuilder,
};

use crate::{
    develop::constants::N_LIMBS,
    develop::{
        modular::write_u256,
        utils::{
            pol_add_assign, pol_add_assign_ext_circuit, pol_add_wide, pol_add_wide_ext_circuit,
            pol_mul_const, pol_mul_const_ext_circuit, pol_mul_wide, pol_mul_wide_ext_circuit,
            pol_sub_assign, pol_sub_assign_ext_circuit, pol_sub_wide, pol_sub_wide_ext_circuit,
        },
    },
};

use super::modular::{generate_modular_op, read_u256, ModulusAux};

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

/// 12*N_LIMBS
pub fn write_fq12<F: Copy, const NUM_COL: usize>(
    lv: &mut [F; NUM_COL],
    input: &Vec<[F; N_LIMBS]>,
    cur_col: &mut usize,
) {
    assert!(input.len() == 12);
    input
        .iter()
        .for_each(|coeff| write_u256(lv, coeff, cur_col));
}

/// 12*N_LIMBS
pub fn read_fq12<F: Copy + Debug, const NUM_COL: usize>(
    lv: &[F; NUM_COL],
    cur_col: &mut usize,
) -> Vec<[F; N_LIMBS]> {
    (0..12).map(|_| read_u256(lv, cur_col)).collect_vec()
}

pub fn generate_fq12_modular_op<F: PrimeField64>(
    modulus: BigInt,
    input: &Vec<[i64; 2 * N_LIMBS - 1]>,
) -> (Vec<[F; N_LIMBS]>, Vec<ModulusAux<F>>, Vec<[F; 2 * N_LIMBS]>) {
    assert!(input.len() == 12);
    let mut outputs = vec![];
    let mut auxs = vec![];
    let mut quots = vec![];
    for i in 0..12 {
        let (output, quot, aux) = generate_modular_op::<F>(modulus.clone(), input[i]);
        outputs.push(output);
        auxs.push(aux);
        quots.push(quot);
    }
    (outputs, auxs, quots)
}

#[cfg(test)]
mod tests {
    use core::{marker::PhantomData, ops::Range};

    use ark_bn254::{Fq, Fq12};
    use ark_std::UniformRand;
    use itertools::Itertools;
    use plonky2::{
        field::{
            extension::{Extendable, FieldExtension},
            packed::PackedField,
            polynomial::PolynomialValues,
            types::Field,
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
        constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer},
        develop::constants::{LIMB_BITS, N_LIMBS},
        develop::{
            fq12::{generate_fq12_modular_op, pol_mul_fq12, pol_mul_fq12_ext_circuit, write_fq12},
            modular::{
                bn254_base_modulus_packfield, eval_modular_lookup, eval_modular_lookup_circuit,
                eval_modular_op, eval_modular_op_circuit, generate_modular_range_check,
                modular_permutation_pairs, read_quot, write_modulus_aux, write_quot, write_u256,
            },
        },
        develop::{
            modular::bn254_base_modulus_bigint,
            utils::{
                bigint_to_columns, columns_to_fq12, fq12_to_columns, pol_sub_assign,
                pol_sub_assign_ext_circuit,
            },
        },
        lookup::{eval_lookups, eval_lookups_circuit},
        permutation::PermutationPair,
        prover::prove,
        recursive_verifier::{
            add_virtual_stark_proof_with_pis, set_stark_proof_with_pis_target,
            verify_stark_proof_circuit,
        },
        stark::Stark,
        vars::{StarkEvaluationTargets, StarkEvaluationVars},
        verifier::verify_stark_proof,
    };

    use crate::develop::modular::{
        generate_modular_op, modular_constr_poly, modular_constr_poly_ext_circuit,
        read_modulus_aux, read_u256, ModulusAux,
    };

    use super::read_fq12;

    const MAIN_COLS: usize = 168 * N_LIMBS - 47;
    const ROWS: usize = 1 << 9;

    const NUM_RANGE_CHECK_UNSIGNED: usize = 144 * N_LIMBS - 48;
    const NUM_RANGE_CHECK_SIGNED: usize = 24 * N_LIMBS;

    const RANGE_CHECK_UNSIGNED: Range<usize> = 0..NUM_RANGE_CHECK_UNSIGNED;
    const RANGE_CHECK_SIGNED: Range<usize> =
        NUM_RANGE_CHECK_UNSIGNED..NUM_RANGE_CHECK_UNSIGNED + NUM_RANGE_CHECK_SIGNED;

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
            let xi = 9;

            let mut rows = vec![];

            for _ in 0..ROWS {
                let x_fq12 = Fq12::rand(&mut rng);
                let y_fq12 = Fq12::rand(&mut rng);
                let output_expected: Fq12 = x_fq12 * y_fq12;

                let x_i64 = fq12_to_columns(x_fq12);
                let y_i64 = fq12_to_columns(y_fq12);

                let pol_input = pol_mul_fq12(x_i64.clone(), y_i64.clone(), xi);

                let x = x_i64
                    .iter()
                    .map(|coeff| coeff.map(|x| F::from_canonical_i64(x)))
                    .collect_vec();
                let y = y_i64
                    .iter()
                    .map(|coeff| coeff.map(|x| F::from_canonical_i64(x)))
                    .collect_vec();

                let (z, auxs, quots) =
                    generate_fq12_modular_op(bn254_base_modulus_bigint(), &pol_input);

                let output_actual = columns_to_fq12(&z);

                assert!(output_expected == output_actual);

                let mut lv = [F::ZERO; MAIN_COLS];

                let mut cur_col = 0;

                write_fq12(&mut lv, &x, &mut cur_col); // 12*N_LIMBS
                write_fq12(&mut lv, &y, &mut cur_col); // 12*N_LIMBS
                write_fq12(&mut lv, &z, &mut cur_col); // 12*N_LIMBS

                // 12*(9*N_LIMBS - 4) = 108*N_LIMBS - 48
                auxs.iter().for_each(|aux| {
                    write_modulus_aux(&mut lv, aux, &mut cur_col);
                });
                // 12*2*N_LIMBS = 24*N_LIMBS
                quots.iter().for_each(|quot| {
                    write_quot(&mut lv, quot, &mut cur_col);
                });

                lv[cur_col] = F::ONE;
                cur_col += 1;

                // MAIN_COLS = 3*12*N_LIMBS + 108*N_LIMBS - 48 + 24*N_LIMBS  + 1= 168*N_LIMBS - 47
                // UNSIGNED_RANGE_CHECK = 3*12*N_LIMBS + 108*N_LIMBS - 48 = 144*N_LIMBS - 48
                assert!(cur_col == MAIN_COLS);

                rows.push(lv);
            }

            let mut trace_cols = transpose(&rows.iter().map(|v| v.to_vec()).collect_vec());

            generate_modular_range_check(RANGE_CHECK_UNSIGNED, RANGE_CHECK_SIGNED, &mut trace_cols);

            trace_cols
                .into_iter()
                .map(|column| PolynomialValues::new(column))
                .collect()
        }
    }

    impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D> for Fq12Stark<F, D> {
        const COLUMNS: usize =
            MAIN_COLS + 2 + 2 * NUM_RANGE_CHECK_UNSIGNED + 2 * NUM_RANGE_CHECK_SIGNED;
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

            eval_modular_lookup(
                vars,
                yield_constr,
                MAIN_COLS,
                NUM_RANGE_CHECK_UNSIGNED,
                NUM_RANGE_CHECK_SIGNED,
            );

            let mut cur_col = 0;

            let x = read_fq12(&lv, &mut cur_col);
            let y = read_fq12(&lv, &mut cur_col);
            let z = read_fq12(&lv, &mut cur_col);

            let auxs = (0..12)
                .map(|_| read_modulus_aux(&lv, &mut cur_col))
                .collect_vec();
            let quots = (0..12).map(|_| read_quot(&lv, &mut cur_col)).collect_vec();

            let filter = lv[cur_col];
            cur_col += 1;

            assert!(cur_col == MAIN_COLS);

            let xi: P = P::Scalar::from_canonical_u32(9).into();
            let input = pol_mul_fq12(x, y, xi);

            let modulus = bn254_base_modulus_packfield();
            (0..12).for_each(|i| {
                eval_modular_op(
                    yield_constr,
                    filter,
                    modulus,
                    input[i],
                    z[i],
                    quots[i],
                    &auxs[i],
                )
            });
        }

        fn eval_ext_circuit(
            &self,
            builder: &mut CircuitBuilder<F, D>,
            vars: StarkEvaluationTargets<D, { Self::COLUMNS }, { Self::PUBLIC_INPUTS }>,
            yield_constr: &mut RecursiveConstraintConsumer<F, D>,
        ) {
            let lv = vars.local_values.clone();

            eval_modular_lookup_circuit(
                builder,
                vars,
                yield_constr,
                MAIN_COLS,
                NUM_RANGE_CHECK_UNSIGNED,
                NUM_RANGE_CHECK_SIGNED,
            );

            let mut cur_col = 0;

            let x = read_fq12(&lv, &mut cur_col);
            let y = read_fq12(&lv, &mut cur_col);
            let z = read_fq12(&lv, &mut cur_col);

            let auxs = (0..12)
                .map(|_| read_modulus_aux(&lv, &mut cur_col))
                .collect_vec();
            let quots = (0..12).map(|_| read_quot(&lv, &mut cur_col)).collect_vec();

            let filter = lv[cur_col];
            cur_col += 1;

            assert!(cur_col == MAIN_COLS);

            let xi = F::Extension::from_canonical_u32(9);
            let input = pol_mul_fq12_ext_circuit(builder, x, y, xi);

            let modulus = bn254_base_modulus_packfield();
            let modulus = modulus.map(|x| builder.constant_extension(x));
            (0..12).for_each(|i| {
                eval_modular_op_circuit(
                    builder,
                    yield_constr,
                    filter,
                    modulus,
                    input[i],
                    z[i],
                    quots[i],
                    &auxs[i],
                )
            });
        }

        fn constraint_degree(&self) -> usize {
            3
        }

        fn permutation_pairs(&self) -> Vec<PermutationPair> {
            modular_permutation_pairs(MAIN_COLS, RANGE_CHECK_UNSIGNED, RANGE_CHECK_SIGNED)
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

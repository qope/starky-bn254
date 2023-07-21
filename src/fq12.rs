use core::fmt::Debug;
use core::ops::*;
use itertools::Itertools;
use plonky2::{
    field::{extension::Extendable, packed::PackedField, types::Field, types::PrimeField64},
    hash::hash_types::RichField,
    iop::ext_target::ExtensionTarget,
    plonk::circuit_builder::CircuitBuilder,
};
use starky::constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer};

use crate::{
    constants::N_LIMBS,
    modular::{
        bn254_base_modulus_bigint, bn254_base_modulus_packfield, eval_modular_op,
        eval_modular_op_circuit, read_modulus_aux, write_modulus_aux, write_u256,
    },
    utils::{
        pol_add_assign, pol_add_assign_ext_circuit, pol_add_wide, pol_add_wide_ext_circuit,
        pol_mul_scalar, pol_mul_scalar_ext_circuit, pol_mul_wide, pol_mul_wide_ext_circuit,
        pol_sub_assign, pol_sub_assign_ext_circuit, pol_sub_wide, pol_sub_wide_ext_circuit,
        positive_column_to_i64,
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
            let nine_times_a0b0_minus_a1b1 = pol_mul_scalar(a0b0_minus_a1b1[i + 6], xi);
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
            let nine_times_a0b1_plus_a1b0 = pol_mul_scalar(a0b1_plus_a1b0[i + 6], xi);
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
                pol_mul_scalar_ext_circuit(builder, a0b0_minus_a1b1[i + 6], xi);
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
                pol_mul_scalar_ext_circuit(builder, a0b1_plus_a1b0[i + 6], xi);
            pol_add_assign_ext_circuit(builder, &mut coeff, &nine_times_a0b1_plus_a1b0);
            out_coeffs.push(coeff);
        } else {
            out_coeffs.push(a0b1_plus_a1b0[i].clone());
        }
    }
    out_coeffs
}

/// 12*N_LIMBS
pub fn write_fq12<F: Copy>(lv: &mut [F], input: [[F; N_LIMBS]; 12], cur_col: &mut usize) {
    assert!(input.len() == 12);
    input
        .iter()
        .for_each(|coeff| write_u256(lv, coeff, cur_col));
}

/// 12*N_LIMBS
pub fn read_fq12<F: Copy + Debug>(lv: &[F], cur_col: &mut usize) -> [[F; N_LIMBS]; 12] {
    (0..12)
        .map(|_| read_u256(lv, cur_col))
        .collect_vec()
        .try_into()
        .unwrap()
}

//
pub struct Fq12Output<F> {
    pub output: [[F; N_LIMBS]; 12],
    pub auxs: [ModulusAux<F>; 12],
    pub quot_signs: [F; 12],
}

impl<F: RichField + Default> Default for Fq12Output<F> {
    fn default() -> Self {
        Self {
            output: [[F::ZERO; N_LIMBS]; 12],
            auxs: [ModulusAux::<F>::default(); 12],
            quot_signs: [F::ONE; 12],
        }
    }
}

pub fn generate_fq12_mul<F: PrimeField64>(
    x: [[F; N_LIMBS]; 12],
    y: [[F; N_LIMBS]; 12],
) -> Fq12Output<F> {
    let xi = 9;
    let modulus = bn254_base_modulus_bigint();
    let x_i64 = x.map(positive_column_to_i64);
    let y_i64 = y.map(positive_column_to_i64);
    let pol_input = pol_mul_fq12(x_i64.to_vec(), y_i64.to_vec(), xi);
    let mut outputs = vec![];
    let mut auxs = vec![];
    let mut quot_signs = vec![];
    for i in 0..12 {
        let (output, quot_sign, aux) = generate_modular_op::<F>(&modulus, pol_input[i]);
        outputs.push(output);
        auxs.push(aux);
        quot_signs.push(quot_sign);
    }
    Fq12Output {
        output: outputs.try_into().unwrap(),
        auxs: auxs.try_into().unwrap(),
        quot_signs: quot_signs.try_into().unwrap(),
    }
}

/// 84*N_LIMBS
/// range_check: 84*N_LIMBS - 12
pub fn write_fq12_output<F: Copy>(lv: &mut [F], output: &Fq12Output<F>, cur_col: &mut usize) {
    // 12*N_LIMBS
    write_fq12(lv, output.output, cur_col);
    // 12*(6*N_LIMBS - 1) = 72*N_LIMBS - 12
    output.auxs.iter().for_each(|aux| {
        write_modulus_aux(lv, aux, cur_col);
    });
    // 12
    output.quot_signs.iter().for_each(|&sign| {
        lv[*cur_col] = sign;
        *cur_col += 1;
    });
}

/// 84*N_LIMBS
pub fn read_fq12_output<F: Copy + core::fmt::Debug>(
    lv: &[F],
    cur_col: &mut usize,
) -> Fq12Output<F> {
    let output = read_fq12(lv, cur_col);
    let auxs = (0..12).map(|_| read_modulus_aux(lv, cur_col)).collect_vec();
    let quot_signs = (0..12)
        .map(|_| {
            let sign = lv[*cur_col];
            *cur_col += 1;
            sign
        })
        .collect_vec();
    Fq12Output {
        output,
        auxs: auxs.try_into().unwrap(),
        quot_signs: quot_signs.try_into().unwrap(),
    }
}

pub fn eval_fq12_mul<P: PackedField>(
    yield_constr: &mut ConstraintConsumer<P>,
    filter: P,
    x: [[P; N_LIMBS]; 12],
    y: [[P; N_LIMBS]; 12],
    output: &Fq12Output<P>,
) {
    let xi = P::Scalar::from_canonical_u32(9).into();
    let input = pol_mul_fq12(x.to_vec(), y.to_vec(), xi);
    let modulus = bn254_base_modulus_packfield();
    (0..12).for_each(|i| {
        eval_modular_op(
            yield_constr,
            filter,
            modulus,
            input[i],
            output.output[i],
            output.quot_signs[i],
            &output.auxs[i],
        )
    });
}

pub fn eval_fq12_mul_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    filter: ExtensionTarget<D>,
    x: [[ExtensionTarget<D>; N_LIMBS]; 12],
    y: [[ExtensionTarget<D>; N_LIMBS]; 12],
    output: &Fq12Output<ExtensionTarget<D>>,
) {
    let xi = F::Extension::from_canonical_u32(9);
    let input = pol_mul_fq12_ext_circuit(builder, x.to_vec(), y.to_vec(), xi);
    let modulus: [F::Extension; N_LIMBS] = bn254_base_modulus_packfield();
    let modulus = modulus.map(|x| builder.constant_extension(x));
    (0..12).for_each(|i| {
        eval_modular_op_circuit(
            builder,
            yield_constr,
            filter,
            modulus,
            input[i],
            output.output[i],
            output.quot_signs[i],
            &output.auxs[i],
        )
    });
}

#[cfg(test)]
mod tests {
    use core::marker::PhantomData;

    use ark_bn254::Fq12;
    use ark_std::UniformRand;
    use itertools::Itertools;
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

    use starky::{
        config::StarkConfig,
        constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer},
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

    use crate::{
        constants::N_LIMBS,
        fq12::{
            eval_fq12_mul, eval_fq12_mul_circuit, generate_fq12_mul, read_fq12_output, write_fq12,
            write_fq12_output,
        },
        range_check::{
            eval_split_u16_range_check, eval_split_u16_range_check_circuit,
            generate_split_u16_range_check, split_u16_range_check_pairs,
        },
        utils::{columns_to_fq12, fq12_to_columns, i64_to_column_positive},
    };

    use super::read_fq12;

    const MAIN_COLS: usize = 108 * N_LIMBS + 1;
    const START_RANGE_CHECK: usize = 24 * N_LIMBS;
    const NUM_RANGE_CHECK: usize = 84 * N_LIMBS - 12;
    const END_RANGE_CHECK: usize = START_RANGE_CHECK + NUM_RANGE_CHECK;

    const COLUMNS: usize = MAIN_COLS + 1 + 6 * NUM_RANGE_CHECK;
    const PUBLIC_INPUTS: usize = 0;

    const ROWS: usize = 512;

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
            let mut rows = vec![];
            for _ in 0..ROWS {
                let x_fq12 = Fq12::rand(&mut rng);
                let y_fq12 = Fq12::rand(&mut rng);
                let output_expected: Fq12 = x_fq12 * y_fq12;

                let x = fq12_to_columns(x_fq12).map(i64_to_column_positive);
                let y = fq12_to_columns(y_fq12).map(i64_to_column_positive);
                let fq12_output = generate_fq12_mul(x, y);
                let output_actual = columns_to_fq12(fq12_output.output);
                assert!(output_expected == output_actual);

                let mut lv = [F::ZERO; MAIN_COLS];

                let mut cur_col = 0;

                write_fq12(&mut lv, x, &mut cur_col); // 12*N_LIMBS
                write_fq12(&mut lv, y, &mut cur_col); // 12*N_LIMBS
                write_fq12_output(&mut lv, &fq12_output, &mut cur_col); // 84*N_LIMBS

                // filter
                lv[cur_col] = F::ONE;
                cur_col += 1;

                // MAIN_COLS = 2*12*N_LIMBS + 84*N_LIMBS + 1 = 108*N_LIMBS  + 1
                // START_RANGE_CHECK = 24*N_LIMBS
                // NUM_RANGE_CHECK = 84*N_LIMBS - 12
                assert!(cur_col == MAIN_COLS);

                rows.push(lv);
            }

            let mut trace_cols = transpose(&rows.iter().map(|v| v.to_vec()).collect_vec());

            generate_split_u16_range_check(START_RANGE_CHECK..END_RANGE_CHECK, &mut trace_cols);

            trace_cols
                .into_iter()
                .map(|column| PolynomialValues::new(column))
                .collect()
        }
    }

    impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D> for Fq12Stark<F, D> {
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
            let lv = vars.local_values;
            eval_split_u16_range_check(
                vars,
                yield_constr,
                MAIN_COLS,
                START_RANGE_CHECK..END_RANGE_CHECK,
            );

            let mut cur_col = 0;
            let x = read_fq12(lv, &mut cur_col);
            let y = read_fq12(lv, &mut cur_col);
            let output = read_fq12_output(lv, &mut cur_col);
            let filter = lv[cur_col];
            cur_col += 1;
            assert!(cur_col == MAIN_COLS);

            eval_fq12_mul(yield_constr, filter, x, y, &output);
        }

        fn eval_ext_circuit(
            &self,
            builder: &mut CircuitBuilder<F, D>,
            vars: StarkEvaluationTargets<D, COLUMNS, PUBLIC_INPUTS>,
            yield_constr: &mut RecursiveConstraintConsumer<F, D>,
        ) {
            let lv = vars.local_values;

            eval_split_u16_range_check_circuit(
                builder,
                vars,
                yield_constr,
                MAIN_COLS,
                START_RANGE_CHECK..END_RANGE_CHECK,
            );

            let mut cur_col = 0;
            let x = read_fq12(lv, &mut cur_col);
            let y = read_fq12(lv, &mut cur_col);
            let output = read_fq12_output(lv, &mut cur_col);
            let filter = lv[cur_col];
            cur_col += 1;
            assert!(cur_col == MAIN_COLS);

            eval_fq12_mul_circuit(builder, yield_constr, filter, x, y, &output);
        }

        fn constraint_degree(&self) -> usize {
            3
        }

        fn permutation_pairs(&self) -> Vec<PermutationPair> {
            split_u16_range_check_pairs(MAIN_COLS, START_RANGE_CHECK..END_RANGE_CHECK)
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
        let mut pw = PartialWitness::<F>::new();
        let degree_bits = inner_proof.proof.recover_degree_bits(&inner_config);
        dbg!(degree_bits);
        let pt = add_virtual_stark_proof_with_pis(&mut builder, stark, &inner_config, degree_bits);
        set_stark_proof_with_pis_target(&mut pw, &pt, &inner_proof);
        verify_stark_proof_circuit::<F, C, S, D>(&mut builder, stark, &pt, &inner_config);
        let data = builder.build::<C>();
        let _proof = data.prove(pw).unwrap();
    }
}

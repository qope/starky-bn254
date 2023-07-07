use core::fmt;

use ark_bn254::Fq;
use itertools::Itertools;
use num::{FromPrimitive, Signed, Zero};
use num_bigint::{BigInt, BigUint, Sign};
use plonky2::field::types::Field;
use plonky2::iop::ext_target::ExtensionTarget;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::{
    field::{extension::Extendable, packed::PackedField, types::PrimeField64},
    hash::hash_types::RichField,
};

use crate::constraint_consumer::RecursiveConstraintConsumer;
use crate::develop::utils::{
    pol_add_assign_ext_circuit, pol_adjoin_root_ext_circuit, pol_mul_wide2_ext_circuit,
};
use crate::{
    constraint_consumer::ConstraintConsumer,
    develop::utils::{
        bigint_to_columns, columns_to_bigint, pol_add_assign, pol_adjoin_root, pol_mul_wide2,
        pol_remove_root_2exp, pol_sub_assign,
    },
};

use super::addcy::{eval_ext_circuit_addcy, eval_packed_generic_addcy};
use super::utils::pol_sub_assign_ext_circuit;

use crate::develop::constants::{LIMB_BITS, N_LIMBS};

pub const AUX_COEFF_ABS_MAX: i64 = 1 << 29;

#[derive(Default, Copy, Clone, Debug)]
pub struct ModulusAux<F> {
    pub out_aux_red: [F; N_LIMBS],
    pub quot_abs: [F; N_LIMBS + 1],
    pub aux_input_lo: [F; 2 * N_LIMBS - 1],
    pub aux_input_hi: [F; 2 * N_LIMBS - 1],
}

pub fn generate_modular_op<F: PrimeField64>(
    modulus: &BigInt,
    pol_input: [i64; 2 * N_LIMBS - 1],
) -> ([F; N_LIMBS], F, ModulusAux<F>) {
    let modulus_limbs = bigint_to_columns(modulus);

    let mut constr_poly = [0i64; 2 * N_LIMBS];
    constr_poly[..2 * N_LIMBS - 1].copy_from_slice(&pol_input);
    // two_exp_256 == 2^256
    let mut two_exp_256 = BigInt::zero();
    two_exp_256.set_bit(256, true);

    let input = columns_to_bigint(&constr_poly);
    let mut output = &input % modulus;
    if output.sign() == Sign::Minus {
        output += modulus;
    }
    let output_limbs = bigint_to_columns::<N_LIMBS>(&output);
    let quot = (&input - &output) / modulus;

    let quot_sign = match quot.sign() {
        Sign::Minus => F::NEG_ONE,
        Sign::NoSign => F::ONE, // if quot == 0 then quot_sign == 1
        Sign::Plus => F::ONE,
    };

    let quot_limbs = bigint_to_columns::<{ N_LIMBS + 1 }>(&quot);
    let quot_abs_limbs = bigint_to_columns::<{ N_LIMBS + 1 }>(&quot.abs());
    // 0 <= out_aux_red < 2^256 という制約を課す(つまりout_aux_redのlimbには2^16のrange checkを課す)
    // out_aux_red = 2^256 - modulus + outputより、output < modulusが成り立つ
    let out_aux_red = bigint_to_columns::<N_LIMBS>(&(two_exp_256 - modulus + output));

    // operation(a(x), b(x)) - c(x) - s(x)*m(x).
    pol_sub_assign(&mut constr_poly, &output_limbs);
    let prod: [i64; 2 * N_LIMBS] = pol_mul_wide2(quot_limbs, modulus_limbs);
    pol_sub_assign(&mut constr_poly, &prod);

    // aux_limbs = constr/ (x- β)
    let mut aux_limbs = pol_remove_root_2exp::<LIMB_BITS, _, { 2 * N_LIMBS }>(constr_poly);
    assert!(aux_limbs[31] == 0);

    for c in aux_limbs.iter_mut() {
        *c += AUX_COEFF_ABS_MAX;
    }
    assert!(aux_limbs.iter().all(|&c| c.abs() <= 2 * AUX_COEFF_ABS_MAX));

    let aux_input_lo = aux_limbs[..2 * N_LIMBS - 1]
        .iter()
        .map(|&c| F::from_canonical_u16(c as u16))
        .collect_vec();
    let aux_input_hi = aux_limbs[..2 * N_LIMBS - 1]
        .iter()
        .map(|&c| F::from_canonical_u16((c >> LIMB_BITS) as u16))
        .collect_vec();

    let output = output_limbs.map(|x| F::from_canonical_u64(x as u64));
    let quot_abs = quot_abs_limbs.map(|x| F::from_canonical_i64(x));
    let aux = ModulusAux {
        out_aux_red: out_aux_red.map(|x| F::from_canonical_i64(x)),
        quot_abs,
        aux_input_lo: aux_input_lo.try_into().unwrap(),
        aux_input_hi: aux_input_hi.try_into().unwrap(),
    };
    (output, quot_sign, aux)
}

pub fn modular_constr_poly<P: PackedField>(
    yield_constr: &mut ConstraintConsumer<P>,
    filter: P,
    modulus: [P; N_LIMBS],
    output: [P; N_LIMBS],
    quot_sign: P,
    aux: &ModulusAux<P>,
) -> [P; 2 * N_LIMBS] {
    let mut is_less_than = [P::ZEROS; N_LIMBS];
    is_less_than[0] = P::ONES;
    // modulus + out_aux_red  = output + 2^256
    // constraint of "output < modulus"
    eval_packed_generic_addcy(
        yield_constr,
        filter,
        &modulus,
        &aux.out_aux_red,
        &output,
        &is_less_than,
    );

    yield_constr.constraint(filter * (quot_sign * quot_sign - P::ONES));
    let quot = aux
        .quot_abs
        .iter()
        .map(|&limb| quot_sign * limb)
        .collect_vec();

    // prod = q(x) * m(x)
    let prod = pol_mul_wide2(quot.try_into().unwrap(), modulus);

    // constr_poly = c(x) + q(x) * m(x)
    let mut constr_poly: [_; 2 * N_LIMBS] = prod;
    pol_add_assign(&mut constr_poly, &output);

    let base = P::Scalar::from_canonical_u64(1 << LIMB_BITS);
    let offset = P::Scalar::from_canonical_u64(AUX_COEFF_ABS_MAX as u64);

    // constr_poly = c(x) + q(x) * m(x) + (x - β) * s(x)
    let mut aux_poly = [P::ZEROS; 2 * N_LIMBS];
    aux_poly[..2 * N_LIMBS - 1]
        .iter_mut()
        .enumerate()
        .for_each(|(i, c)| {
            *c = aux.aux_input_lo[i] - offset;
            *c += base * aux.aux_input_hi[i];
        });

    pol_add_assign(&mut constr_poly, &pol_adjoin_root(aux_poly, base));

    constr_poly
}

pub fn modular_constr_poly_ext_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    filter: ExtensionTarget<D>,
    modulus: [ExtensionTarget<D>; N_LIMBS],
    output: [ExtensionTarget<D>; N_LIMBS],
    quot_sign: ExtensionTarget<D>,
    aux: &ModulusAux<ExtensionTarget<D>>,
) -> [ExtensionTarget<D>; 2 * N_LIMBS] {
    let one = builder.one_extension();
    let zero = builder.zero_extension();
    let mut is_less_than = [zero; N_LIMBS];
    is_less_than[0] = one;
    eval_ext_circuit_addcy(
        builder,
        yield_constr,
        filter,
        &modulus,
        &aux.out_aux_red,
        &output,
        &is_less_than,
    );

    let one = builder.one_extension();
    let diff = builder.mul_sub_extension(quot_sign, quot_sign, one);
    let t = builder.mul_extension(filter, diff);
    yield_constr.constraint(builder, t);

    let quot = aux
        .quot_abs
        .iter()
        .map(|&limb| builder.mul_extension(quot_sign, limb))
        .collect_vec();

    let prod = pol_mul_wide2_ext_circuit(builder, quot.try_into().unwrap(), modulus);

    let mut constr_poly = prod;
    pol_add_assign_ext_circuit(builder, &mut constr_poly, &output);

    let offset =
        builder.constant_extension(F::Extension::from_canonical_u64(AUX_COEFF_ABS_MAX as u64));
    let zero = builder.zero_extension();
    let mut aux_poly = [zero; 2 * N_LIMBS];

    let base = F::from_canonical_u64(1u64 << LIMB_BITS);
    aux_poly[..2 * N_LIMBS - 1]
        .iter_mut()
        .enumerate()
        .for_each(|(i, c)| {
            *c = builder.sub_extension(aux.aux_input_lo[i], offset);
            *c = builder.mul_const_add_extension(base, aux.aux_input_hi[i], *c);
        });

    let base = builder.constant_extension(base.into());
    let t = pol_adjoin_root_ext_circuit(builder, aux_poly, base);
    pol_add_assign_ext_circuit(builder, &mut constr_poly, &t);

    constr_poly
}

pub fn eval_modular_op<P: PackedField>(
    yield_constr: &mut ConstraintConsumer<P>,
    filter: P,
    modulus: [P; N_LIMBS],
    input: [P; 2 * N_LIMBS - 1],
    output: [P; N_LIMBS],
    quot_sign: P,
    aux: &ModulusAux<P>,
) {
    let constr_poly = modular_constr_poly(yield_constr, filter, modulus, output, quot_sign, &aux);
    let mut constr_poly_copy = constr_poly;
    pol_sub_assign(&mut constr_poly_copy, &input);
    for &c in constr_poly_copy.iter() {
        yield_constr.constraint(filter * c);
    }
}

pub fn eval_modular_op_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    filter: ExtensionTarget<D>,
    modulus: [ExtensionTarget<D>; N_LIMBS],
    input: [ExtensionTarget<D>; 2 * N_LIMBS - 1],
    output: [ExtensionTarget<D>; N_LIMBS],
    quot_sign: ExtensionTarget<D>,
    aux: &ModulusAux<ExtensionTarget<D>>,
) {
    let constr_poly = modular_constr_poly_ext_circuit(
        builder,
        yield_constr,
        filter,
        modulus,
        output,
        quot_sign,
        &aux,
    );
    let mut constr_poly_copy = constr_poly;
    pol_sub_assign_ext_circuit(builder, &mut constr_poly_copy, &input);
    for &c in constr_poly_copy.iter() {
        let t = builder.mul_extension(filter, c);
        yield_constr.constraint(builder, t);
    }
}

/// N_LIMBS
pub fn write_u256<F: Copy, const NUM_COL: usize>(
    lv: &mut [F; NUM_COL],
    input: &[F; N_LIMBS],
    cur_col: &mut usize,
) {
    lv[*cur_col..*cur_col + N_LIMBS].copy_from_slice(input);
    *cur_col += N_LIMBS;
}

/// N_LIMBS
pub fn read_u256<F: Clone + fmt::Debug>(lv: &[F], cur_col: &mut usize) -> [F; N_LIMBS] {
    let output = lv[*cur_col..*cur_col + N_LIMBS].to_vec();
    *cur_col += N_LIMBS;
    output.try_into().unwrap()
}

/// 6 * N_LIMBS - 1
pub fn write_modulus_aux<F: Copy, const NUM_COL: usize>(
    lv: &mut [F; NUM_COL],
    aux: &ModulusAux<F>,
    cur_col: &mut usize,
) {
    lv[*cur_col..*cur_col + N_LIMBS].copy_from_slice(&aux.out_aux_red);
    lv[*cur_col + N_LIMBS..*cur_col + 2 * N_LIMBS + 1].copy_from_slice(&aux.quot_abs);
    lv[*cur_col + 2 * N_LIMBS + 1..*cur_col + 4 * N_LIMBS].copy_from_slice(&aux.aux_input_lo);
    lv[*cur_col + 4 * N_LIMBS..*cur_col + 6 * N_LIMBS - 1].copy_from_slice(&aux.aux_input_hi);
    *cur_col += 6 * N_LIMBS - 1;
}

/// 6 * N_LIMBS - 1
pub fn read_modulus_aux<F: Copy + fmt::Debug>(lv: &[F], cur_col: &mut usize) -> ModulusAux<F> {
    let out_aux_red = lv[*cur_col..*cur_col + N_LIMBS].to_vec();
    let quot_abs = lv[*cur_col + N_LIMBS..*cur_col + 2 * N_LIMBS + 1].to_vec();
    let aux_input_lo = lv[*cur_col + 2 * N_LIMBS + 1..*cur_col + 4 * N_LIMBS].to_vec();
    let aux_input_hi = lv[*cur_col + 4 * N_LIMBS..*cur_col + 6 * N_LIMBS - 1].to_vec();

    *cur_col += 6 * N_LIMBS - 1;

    ModulusAux {
        out_aux_red: out_aux_red.try_into().unwrap(),
        quot_abs: quot_abs.try_into().unwrap(),
        aux_input_lo: aux_input_lo.try_into().unwrap(),
        aux_input_hi: aux_input_hi.try_into().unwrap(),
    }
}

pub fn bn254_base_modulus_bigint() -> BigInt {
    let neg_one: BigUint = Fq::from(-1).into();
    let modulus_biguint: BigUint = neg_one + BigUint::from_usize(1).unwrap();
    let modulus_bigint: BigInt = modulus_biguint.into();
    modulus_bigint
}

pub fn bn254_base_modulus_packfield<P: PackedField>() -> [P; N_LIMBS] {
    let modulus_column: [P; N_LIMBS] = bigint_to_columns(&bn254_base_modulus_bigint())
        .map(|x| P::Scalar::from_canonical_u64(x as u64).into());
    modulus_column
}

#[cfg(test)]
mod tests {
    use core::marker::PhantomData;

    use ark_bn254::Fq;
    use ark_std::UniformRand;
    use itertools::Itertools;
    use num_bigint::BigUint;
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
        constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer},
        develop::{
            constants::{LIMB_BITS, N_LIMBS},
            modular::{eval_modular_op, eval_modular_op_circuit},
            range_check::{
                eval_split_u16_range_check, eval_split_u16_range_check_circuit,
                generate_split_u16_range_check, split_u16_range_check_pairs,
            },
        },
        develop::{
            modular::{bn254_base_modulus_bigint, bn254_base_modulus_packfield},
            utils::{columns_to_bigint, pol_mul_wide, pol_mul_wide_ext_circuit},
        },
        develop::{
            modular::{write_modulus_aux, write_u256},
            utils::fq_to_columns,
        },
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

    use super::{generate_modular_op, read_modulus_aux, read_u256};

    const MAIN_COLS: usize = 9 * N_LIMBS + 1;
    const ROWS: usize = 512;

    const START_RANGE_CHECK: usize = 2 * N_LIMBS;
    const NUM_RANGE_CHECK: usize = 7 * N_LIMBS - 1;
    const END_RANGE_CHECK: usize = START_RANGE_CHECK + NUM_RANGE_CHECK;

    #[derive(Clone, Copy)]
    pub struct ModularStark<F: RichField + Extendable<D>, const D: usize> {
        _phantom: PhantomData<F>,
    }

    impl<F: RichField + Extendable<D>, const D: usize> ModularStark<F, D> {
        pub fn new() -> Self {
            Self {
                _phantom: PhantomData,
            }
        }

        pub fn generate_trace(&self) -> Vec<PolynomialValues<F>> {
            let mut rng = rand::thread_rng();

            let mut rows = vec![];

            for _ in 0..ROWS {
                let input0_fq = Fq::rand(&mut rng);
                let input1_fq = Fq::rand(&mut rng);
                let output_fq: Fq = input0_fq * input1_fq;
                let output_expected: BigUint = output_fq.into();

                let input0_limbs: [i64; N_LIMBS] = fq_to_columns(input0_fq);
                let input1_limbs: [i64; N_LIMBS] = fq_to_columns(input1_fq);

                let input0 = input0_limbs.map(|x| F::from_canonical_u64(x as u64));
                let input1 = input1_limbs.map(|x| F::from_canonical_u64(x as u64));

                let pol_input = pol_mul_wide(input0_limbs, input1_limbs);

                let (output, quot_sign, aux) =
                    generate_modular_op::<F>(&bn254_base_modulus_bigint(), pol_input);

                let output_actual = columns_to_bigint(&output.map(|a| a.to_canonical_u64() as i64));
                assert!(output_expected == output_actual.to_biguint().unwrap());

                let mut lv = [F::ZERO; MAIN_COLS];

                let mut cur_col = 0;

                write_u256(&mut lv, &input0, &mut cur_col); // N_LIMBS
                write_u256(&mut lv, &input1, &mut cur_col); // N_LIMBS
                write_u256(&mut lv, &output, &mut cur_col); // N_LIMBS
                write_modulus_aux(&mut lv, &aux, &mut cur_col); // 6*N_LIMBS - 1

                lv[cur_col] = quot_sign;
                cur_col += 1;

                lv[cur_col] = F::ONE;
                cur_col += 1;

                assert!(cur_col == MAIN_COLS); // 9*N_LIMBS + 1
                assert!(lv.iter().all(|x| x.to_canonical_u64() < (1 << LIMB_BITS)));
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

    impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D> for ModularStark<F, D> {
        const COLUMNS: usize = MAIN_COLS + 1 + 6 * NUM_RANGE_CHECK;
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

            eval_split_u16_range_check(
                vars,
                yield_constr,
                MAIN_COLS,
                START_RANGE_CHECK..END_RANGE_CHECK,
            );

            let mut cur_col = 0;

            let input0: [P; N_LIMBS] = read_u256(&lv, &mut cur_col);
            let input1: [P; N_LIMBS] = read_u256(&lv, &mut cur_col);
            let output = read_u256(&lv, &mut cur_col);

            let aux = read_modulus_aux(&lv, &mut cur_col);

            let quot_sign = lv[cur_col];
            cur_col += 1;

            let filter = lv[cur_col];
            cur_col += 1;
            assert!(cur_col == MAIN_COLS);

            let input = pol_mul_wide(input0, input1);
            eval_modular_op(
                yield_constr,
                filter,
                bn254_base_modulus_packfield(),
                input,
                output,
                quot_sign,
                &aux,
            );
        }

        fn eval_ext_circuit(
            &self,
            builder: &mut CircuitBuilder<F, D>,
            vars: StarkEvaluationTargets<D, { Self::COLUMNS }, { Self::PUBLIC_INPUTS }>,
            yield_constr: &mut RecursiveConstraintConsumer<F, D>,
        ) {
            let lv = vars.local_values.clone();

            eval_split_u16_range_check_circuit(
                builder,
                vars,
                yield_constr,
                MAIN_COLS,
                START_RANGE_CHECK..END_RANGE_CHECK,
            );

            let mut cur_col = 0;

            let input0 = read_u256(&lv, &mut cur_col);
            let input1 = read_u256(&lv, &mut cur_col);
            let output = read_u256(&lv, &mut cur_col);
            let aux = read_modulus_aux(&lv, &mut cur_col);

            let quot_sign = lv[cur_col];
            cur_col += 1;

            let filter = lv[cur_col];
            cur_col += 1;
            assert!(cur_col == MAIN_COLS);

            let modulus: [F::Extension; N_LIMBS] = bn254_base_modulus_packfield();
            let modulus = modulus.map(|x| builder.constant_extension(x));

            let input = pol_mul_wide_ext_circuit(builder, input0, input1);
            eval_modular_op_circuit(
                builder,
                yield_constr,
                filter,
                modulus,
                input,
                output,
                quot_sign,
                &aux,
            );
        }

        fn constraint_degree(&self) -> usize {
            3
        }

        fn permutation_pairs(&self) -> Vec<PermutationPair> {
            split_u16_range_check_pairs(MAIN_COLS, START_RANGE_CHECK..END_RANGE_CHECK)
        }
    }

    #[test]
    fn test_modular_stark() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type S = ModularStark<F, D>;
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

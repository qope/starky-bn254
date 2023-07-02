use core::fmt;

use itertools::Itertools;
use num::Zero;
use num_bigint::{BigInt, Sign};
use plonky2::field::types::Field;
use plonky2::iop::ext_target::ExtensionTarget;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::{
    field::{extension::Extendable, packed::PackedField, types::PrimeField64},
    hash::hash_types::RichField,
};

use crate::constraint_consumer::RecursiveConstraintConsumer;
use crate::util::{
    pol_add_assign_ext_circuit, pol_adjoin_root_ext_circuit, pol_mul_wide2_ext_circuit,
};
use crate::{
    constraint_consumer::ConstraintConsumer,
    util::{
        bigint_to_columns, columns_to_bigint, pol_add_assign, pol_adjoin_root, pol_mul_wide2,
        pol_remove_root_2exp, pol_sub_assign,
    },
};

use super::addcy::{eval_ext_circuit_addcy, eval_packed_generic_addcy};

use crate::constants::{LIMB_BITS, N_LIMBS};

pub const AUX_COEFF_ABS_MAX: i64 = 1 << 30;

pub struct ModulusAux<F> {
    pub out_aux_red: [F; N_LIMBS],
    pub aux_input_lo: [F; 2 * N_LIMBS - 1],
    pub aux_input_hi: [F; 2 * N_LIMBS - 1],
}

pub fn generate_modular_op<F: PrimeField64>(
    modulus: BigInt,
    pol_input: [i64; 2 * N_LIMBS - 1],
) -> ([F; N_LIMBS], [F; 2 * N_LIMBS], ModulusAux<F>) {
    let modulus_limbs = bigint_to_columns(&modulus);

    let mut constr_poly = [0i64; 2 * N_LIMBS];
    constr_poly[..2 * N_LIMBS - 1].copy_from_slice(&pol_input);
    // two_exp_256 == 2^256
    let mut two_exp_256 = BigInt::zero();
    two_exp_256.set_bit(256, true);

    let input = columns_to_bigint(&constr_poly);
    let mut output = &input % &modulus;
    if output.sign() == Sign::Minus {
        output += &modulus;
    }
    let output_limbs = bigint_to_columns::<N_LIMBS>(&output);
    let quot = (&input - &output) / &modulus;
    let quot_limbs = bigint_to_columns::<{ 2 * N_LIMBS }>(&quot);
    // 0 <= out_aux_red < 2^256 という制約を課す(つまりout_aux_redのlimbには2^16のrange checkを課す)
    // out_aux_red = 2^256 - modulus + outputより、output < modulusが成り立つ
    let out_aux_red = bigint_to_columns::<N_LIMBS>(&(two_exp_256 - modulus + output));

    // operation(a(x), b(x)) - c(x) - s(x)*m(x).
    pol_sub_assign(&mut constr_poly, &output_limbs);
    let prod = pol_mul_wide2(quot_limbs, modulus_limbs);
    pol_sub_assign(&mut constr_poly, &prod[0..2 * N_LIMBS]);

    debug_assert!(&prod[2 * N_LIMBS..].iter().all(|&x| x == 0i64));
    // aux_limbs = constr/ (x- β)
    // これはrange checkを課さない
    let mut aux_limbs = pol_remove_root_2exp::<LIMB_BITS, _, { 2 * N_LIMBS }>(constr_poly);

    for c in aux_limbs.iter_mut() {
        // offset value c + 2^20.
        *c += AUX_COEFF_ABS_MAX;
    }
    debug_assert!(aux_limbs.iter().all(|&c| c.abs() <= 2 * AUX_COEFF_ABS_MAX));

    let aux_input_lo = aux_limbs[..2 * N_LIMBS - 1]
        .iter()
        .map(|&c| F::from_canonical_u16(c as u16))
        .collect_vec();

    let aux_input_hi = aux_limbs[..2 * N_LIMBS - 1]
        .iter()
        .map(|&c| F::from_canonical_u16((c >> 16) as u16))
        .collect_vec();

    let output = output_limbs.map(|x| F::from_canonical_u64(x as u64));
    let quot = quot_limbs.map(|x| F::from_noncanonical_i64(x));
    let aux = ModulusAux {
        out_aux_red: out_aux_red.map(|x| F::from_canonical_i64(x)),
        aux_input_lo: aux_input_lo.try_into().unwrap(),
        aux_input_hi: aux_input_hi.try_into().unwrap(),
    };
    (output, quot, aux)
}

pub fn modular_constr_poly<P: PackedField>(
    yield_constr: &mut ConstraintConsumer<P>,
    filter: P,
    modulus: [P; N_LIMBS],
    output: [P; N_LIMBS],
    out_aux_red: [P; N_LIMBS],
    quot: [P; 2 * N_LIMBS],
    aux_input_lo: [P; 2 * N_LIMBS - 1],
    aux_input_hi: [P; 2 * N_LIMBS - 1],
) -> [P; 2 * N_LIMBS] {
    let mut is_less_than = [P::ZEROS; N_LIMBS];
    is_less_than[0] = P::ONES;
    // ここで modulus + out_aux_red  = output + is_less_than*2^256
    // という制約を掛ける
    eval_packed_generic_addcy(
        yield_constr,
        filter,
        &modulus,
        &out_aux_red,
        &output,
        &is_less_than,
    );

    // prod = q(x) * m(x)
    let prod = pol_mul_wide2(quot, modulus);
    // higher order terms must be zero
    for &x in prod[2 * N_LIMBS..].iter() {
        yield_constr.constraint(filter * x);
    }

    // constr_poly = c(x) + q(x) * m(x)
    let mut constr_poly: [_; 2 * N_LIMBS] = prod[0..2 * N_LIMBS].try_into().unwrap();
    pol_add_assign(&mut constr_poly, &output);

    let base = P::Scalar::from_canonical_u64(1 << LIMB_BITS);
    let offset = P::Scalar::from_canonical_u64(AUX_COEFF_ABS_MAX as u64);

    // constr_poly = c(x) + q(x) * m(x) + (x - β) * s(x)
    let mut aux = [P::ZEROS; 2 * N_LIMBS];
    aux[..2 * N_LIMBS - 1]
        .iter_mut()
        .enumerate()
        .for_each(|(i, c)| {
            *c = aux_input_lo[i] - offset;
            *c += base * aux_input_hi[i];
        });

    pol_add_assign(&mut constr_poly, &pol_adjoin_root(aux, base));

    constr_poly
}

pub fn modular_constr_poly_ext_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    filter: ExtensionTarget<D>,
    modulus: [ExtensionTarget<D>; N_LIMBS],
    output: [ExtensionTarget<D>; N_LIMBS],
    out_aux_red: [ExtensionTarget<D>; N_LIMBS],
    quot: [ExtensionTarget<D>; 2 * N_LIMBS],
    aux_input_lo: [ExtensionTarget<D>; 2 * N_LIMBS - 1],
    aux_input_hi: [ExtensionTarget<D>; 2 * N_LIMBS - 1],
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
        &out_aux_red,
        &output,
        &is_less_than,
    );

    let prod = pol_mul_wide2_ext_circuit(builder, quot, modulus);
    for &x in prod[2 * N_LIMBS..].iter() {
        let t = builder.mul_extension(filter, x);
        yield_constr.constraint(builder, t);
    }

    let mut constr_poly: [_; 2 * N_LIMBS] = prod[0..2 * N_LIMBS].try_into().unwrap();
    pol_add_assign_ext_circuit(builder, &mut constr_poly, &output);

    let offset =
        builder.constant_extension(F::Extension::from_canonical_u64(AUX_COEFF_ABS_MAX as u64));
    let zero = builder.zero_extension();
    let mut aux = [zero; 2 * N_LIMBS];

    let base = F::from_canonical_u64(1u64 << LIMB_BITS);
    aux[..2 * N_LIMBS - 1]
        .iter_mut()
        .enumerate()
        .for_each(|(i, c)| {
            *c = builder.sub_extension(aux_input_lo[i], offset);
            *c = builder.mul_const_add_extension(base, aux_input_hi[i], *c);
        });

    let base = builder.constant_extension(base.into());
    let t = pol_adjoin_root_ext_circuit(builder, aux, base);
    pol_add_assign_ext_circuit(builder, &mut constr_poly, &t);

    constr_poly
}

pub fn write_u256<F: Copy, const NUM_COL: usize, const N_LIMBS: usize>(
    lv: &mut [F; NUM_COL],
    input: &[F; N_LIMBS],
    cur_col: &mut usize,
) {
    lv[*cur_col..*cur_col + N_LIMBS].copy_from_slice(input);
    *cur_col += N_LIMBS;
}

pub fn read_u256<F: Clone + fmt::Debug, const N_LIMBS: usize>(
    lv: &[F],
    cur_col: &mut usize,
) -> [F; N_LIMBS] {
    let output = lv[*cur_col..*cur_col + N_LIMBS].to_vec();
    *cur_col += N_LIMBS;
    output.try_into().unwrap()
}

pub fn write_quot<F: Copy, const N: usize, const M: usize>(
    lv: &mut [F; N],
    quot: &[F; M],
    cur_col: &mut usize,
) {
    lv[*cur_col..*cur_col + M].copy_from_slice(quot);
    *cur_col += M;
}

pub fn read_quot<F: Clone + fmt::Debug, const M: usize>(lv: &[F], cur_col: &mut usize) -> [F; M] {
    let output = lv[*cur_col..*cur_col + M].to_vec();
    *cur_col += M;
    output.try_into().unwrap()
}

pub fn write_modulus_aux<F: Copy, const NUM_COL: usize, const N_LIMBS: usize>(
    lv: &mut [F; NUM_COL],
    aux: &ModulusAux<F>,
    cur_col: &mut usize,
) {
    lv[*cur_col..*cur_col + N_LIMBS].copy_from_slice(&aux.out_aux_red);
    lv[*cur_col + N_LIMBS..*cur_col + 3 * N_LIMBS - 1].copy_from_slice(&aux.aux_input_lo);
    lv[*cur_col + 3 * N_LIMBS - 1..*cur_col + 5 * N_LIMBS - 2].copy_from_slice(&aux.aux_input_hi);
    *cur_col += 5 * N_LIMBS - 2;
}

pub fn read_modulus_aux<F: Copy + fmt::Debug, const N_LIMBS: usize>(
    lv: &[F],
    cur_col: &mut usize,
) -> ModulusAux<F> {
    let out_aux_red = lv[*cur_col..*cur_col + N_LIMBS].to_vec();
    let aux_input_lo = lv[*cur_col + N_LIMBS..*cur_col + 3 * N_LIMBS - 1].to_vec();
    let aux_input_hi = lv[*cur_col + 3 * N_LIMBS - 1..*cur_col + 5 * N_LIMBS - 2].to_vec();

    *cur_col += 5 * N_LIMBS - 2;

    ModulusAux {
        out_aux_red: out_aux_red.try_into().unwrap(),
        aux_input_lo: aux_input_lo.try_into().unwrap(),
        aux_input_hi: aux_input_hi.try_into().unwrap(),
    }
}

#[cfg(test)]
mod tests {
    use core::marker::PhantomData;

    use ark_bn254::Fq;
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
        iop::{ext_target::ExtensionTarget, witness::PartialWitness},
        plonk::{
            circuit_builder::CircuitBuilder,
            circuit_data::CircuitConfig,
            config::{GenericConfig, PoseidonGoldilocksConfig},
        },
        util::{timing::TimingTree, transpose},
    };

    use crate::{
        config::StarkConfig,
        constants::LIMB_BITS,
        constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer},
        develop::modular::{read_quot, write_modulus_aux, write_quot, write_u256},
        lookup::{eval_lookups, eval_lookups_circuit, generate_range_checks},
        permutation::PermutationPair,
        prover::prove,
        recursive_verifier::{
            add_virtual_stark_proof_with_pis, set_stark_proof_with_pis_target,
            verify_stark_proof_circuit,
        },
        stark::Stark,
        util::{
            bigint_to_columns, columns_to_bigint, pol_mul_wide, pol_mul_wide_ext_circuit,
            pol_sub_assign, pol_sub_assign_ext_circuit,
        },
        vars::{StarkEvaluationTargets, StarkEvaluationVars},
        verifier::verify_stark_proof,
    };

    use super::{
        generate_modular_op, modular_constr_poly, modular_constr_poly_ext_circuit,
        read_modulus_aux, read_u256, ModulusAux, N_LIMBS,
    };

    const NUM_ARITH_COLUMS: usize = 11 * N_LIMBS - 1;
    const TABLE_COL: usize = NUM_ARITH_COLUMS;

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

            for _ in 0..1 << 2 {
                let input0_fq = Fq::rand(&mut rng);
                let input1_fq = Fq::rand(&mut rng);
                let output_fq: Fq = input0_fq * input1_fq;
                let output_expected_biguint: BigUint = output_fq.into();
                let output_expected: BigInt = output_expected_biguint.into();
                let input0_biguint: BigUint = input0_fq.into();
                let input1_biguint: BigUint = input1_fq.into();

                let neg_one: BigUint = Fq::from(-1).into();
                let modulus_biguint: BigUint = neg_one + BigUint::from_usize(1).unwrap();
                let modulus_bigint: BigInt = modulus_biguint.into();

                let input0_limbs: [i64; N_LIMBS] = bigint_to_columns(&input0_biguint.into());
                let input1_limbs: [i64; N_LIMBS] = bigint_to_columns(&input1_biguint.into());

                let input0 = input0_limbs.map(|x| F::from_canonical_u64(x as u64));
                let input1 = input1_limbs.map(|x| F::from_canonical_u64(x as u64));

                let modulus: [F; N_LIMBS] =
                    bigint_to_columns(&modulus_bigint).map(|x| F::from_canonical_i64(x));

                let pol_input = pol_mul_wide(input0_limbs, input1_limbs);

                let (output, quot, aux) = generate_modular_op::<F>(modulus_bigint, pol_input);

                let output_actual = columns_to_bigint(&output.map(|a| a.to_canonical_u64() as i64));
                assert!(output_expected == output_actual);

                let mut lv = [F::ZERO; NUM_ARITH_COLUMS];

                let mut cur_col = 0;

                write_u256(&mut lv, &input0, &mut cur_col);
                write_u256(&mut lv, &input1, &mut cur_col);
                write_u256(&mut lv, &modulus, &mut cur_col);
                write_u256(&mut lv, &output, &mut cur_col);
                write_modulus_aux::<_, NUM_ARITH_COLUMS, N_LIMBS>(&mut lv, &aux, &mut cur_col);
                write_quot(&mut lv, &quot, &mut cur_col);
                lv[cur_col] = F::ONE;
                cur_col += 1;

                assert!(cur_col == NUM_ARITH_COLUMS);
                assert!(lv.iter().all(|x| x.to_canonical_u64() < (1 << LIMB_BITS)));
                rows.push(lv);
            }

            let range_max = 1 << LIMB_BITS;
            let padded_len = rows.len().next_power_of_two();
            for _ in rows.len()..std::cmp::max(padded_len, range_max) {
                rows.push([F::ZERO; NUM_ARITH_COLUMS]);
            }

            let mut trace_cols = transpose(&rows.iter().map(|v| v.to_vec()).collect_vec());
            let (table, pairs) = generate_range_checks(range_max, &trace_cols);

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

    impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D> for ModularStark<F, D> {
        const COLUMNS: usize = NUM_ARITH_COLUMS + 1 + 2 * NUM_ARITH_COLUMS;
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

            for i in (NUM_ARITH_COLUMS + 1..3 * NUM_ARITH_COLUMS + 1).step_by(2) {
                eval_lookups(vars, yield_constr, i, i + 1);
            }

            let mut cur_col = 0;

            let input0: [P; N_LIMBS] = read_u256(&lv, &mut cur_col);
            let input1: [P; N_LIMBS] = read_u256(&lv, &mut cur_col);
            let modulus = read_u256(&lv, &mut cur_col);
            let output = read_u256(&lv, &mut cur_col);

            let ModulusAux {
                out_aux_red,
                aux_input_lo,
                aux_input_hi,
            } = read_modulus_aux::<P, N_LIMBS>(&lv, &mut cur_col);
            let quot = read_quot(&lv, &mut cur_col);

            let filter = lv[cur_col];
            cur_col += 1;
            assert!(cur_col == NUM_ARITH_COLUMS);

            let constr_poly = modular_constr_poly::<P>(
                yield_constr,
                filter,
                modulus,
                output,
                out_aux_red,
                quot,
                aux_input_lo,
                aux_input_hi,
            );

            let mul_input = pol_mul_wide(input0, input1);

            let mut constr_poly_copy = constr_poly;
            pol_sub_assign(&mut constr_poly_copy, &mul_input);
            for &c in constr_poly_copy.iter() {
                yield_constr.constraint(filter * c);
            }
        }

        fn eval_ext_circuit(
            &self,
            builder: &mut CircuitBuilder<F, D>,
            vars: StarkEvaluationTargets<D, { Self::COLUMNS }, { Self::PUBLIC_INPUTS }>,
            yield_constr: &mut RecursiveConstraintConsumer<F, D>,
        ) {
            let lv = vars.local_values.clone();

            for i in (NUM_ARITH_COLUMS + 1..3 * NUM_ARITH_COLUMS + 1).step_by(2) {
                eval_lookups_circuit(builder, vars, yield_constr, i, i + 1);
            }

            let mut cur_col = 0;

            let input0: [ExtensionTarget<D>; N_LIMBS] = read_u256(&lv, &mut cur_col);
            let input1: [ExtensionTarget<D>; N_LIMBS] = read_u256(&lv, &mut cur_col);
            let modulus: [ExtensionTarget<D>; N_LIMBS] = read_u256(&lv, &mut cur_col);
            let output: [ExtensionTarget<D>; N_LIMBS] = read_u256(&lv, &mut cur_col);

            let ModulusAux {
                out_aux_red,
                aux_input_lo,
                aux_input_hi,
            } = read_modulus_aux::<_, N_LIMBS>(&lv, &mut cur_col);
            let quot = read_quot(&lv, &mut cur_col);

            let filter = lv[cur_col];
            cur_col += 1;
            assert!(cur_col == NUM_ARITH_COLUMS);

            let constr_poly = modular_constr_poly_ext_circuit::<F, D>(
                builder,
                yield_constr,
                filter,
                modulus,
                output,
                out_aux_red,
                quot,
                aux_input_lo,
                aux_input_hi,
            );

            let mul_input = pol_mul_wide_ext_circuit(builder, input0, input1);

            let mut constr_poly_copy = constr_poly;
            pol_sub_assign_ext_circuit(builder, &mut constr_poly_copy, &mul_input);
            for &c in constr_poly_copy.iter() {
                let t = builder.mul_extension(filter, c);
                yield_constr.constraint(builder, t);
            }
        }

        fn constraint_degree(&self) -> usize {
            3
        }

        fn permutation_pairs(&self) -> Vec<PermutationPair> {
            let mut pairs = (0..NUM_ARITH_COLUMS)
                .map(|i| PermutationPair::singletons(i, NUM_ARITH_COLUMS + 1 + 2 * i))
                .collect_vec();
            let pairs_table = (0..NUM_ARITH_COLUMS)
                .map(|i| PermutationPair::singletons(TABLE_COL, NUM_ARITH_COLUMS + 2 + 2 * i))
                .collect_vec();

            pairs.extend(pairs_table);

            pairs
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

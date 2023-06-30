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

use crate::columns::{LIMB_BITS, N_LIMBS};
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

pub const AUX_COEFF_ABS_MAX: i64 = 1 << 20;

pub struct ModularOpWitness<F: PrimeField64> {
    pub output: [F; N_LIMBS],
    pub out_aux_red: [F; N_LIMBS],
    pub quot: [F; 2 * N_LIMBS],
    pub aux_input_lo: [F; 2 * N_LIMBS - 1],
    pub aux_input_hi: [F; 2 * N_LIMBS - 1],
}

pub fn generate_modular_op<F: PrimeField64>(
    modulus: BigInt,
    pol_input: [i64; 2 * N_LIMBS - 1],
) -> ModularOpWitness<F> {
    let modulus_limbs = bigint_to_columns(&modulus);

    let mut constr_poly = [0i64; 2 * N_LIMBS];
    constr_poly[..2 * N_LIMBS - 1].copy_from_slice(&pol_input);
    // two_exp_256 == 2^256
    let mut two_exp_256 = BigInt::zero();
    two_exp_256.set_bit(256, true);

    let input = columns_to_bigint(&constr_poly);
    // 例えば、-2 % 3 = -2 となるので、これを一旦プラスに変換する必要がある。
    let mut output = &input % &modulus;
    if output.sign() == Sign::Minus {
        output += &modulus;
    }
    let output_limbs = bigint_to_columns::<N_LIMBS>(&output);

    let quot = (&input - &output) / &modulus; // マイナスになる場合もある
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

    ModularOpWitness {
        output: output_limbs.map(|x| F::from_canonical_u64(x as u64)), // outputは必ず正の数になる
        quot: quot_limbs.map(|x| F::from_noncanonical_i64(x)), // quotは負の数になる可能性がある
        out_aux_red: out_aux_red.map(|x| F::from_canonical_u64(x as u64)),
        aux_input_lo: aux_input_lo.try_into().unwrap(),
        aux_input_hi: aux_input_hi.try_into().unwrap(),
    }
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

#[cfg(test)]
mod tests {
    use core::marker::PhantomData;

    use num::FromPrimitive;
    use num_bigint::BigInt;
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
        util::timing::TimingTree,
    };

    use crate::{
        columns::N_LIMBS,
        config::StarkConfig,
        constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer},
        prover::prove,
        recursive_verifier::{
            add_virtual_stark_proof_with_pis, set_stark_proof_with_pis_target,
            verify_stark_proof_circuit,
        },
        stark::Stark,
        util::{
            bigint_to_columns, bn254_modulus_limbs, columns_to_bigint, pol_mul_wide,
            pol_mul_wide_ext_circuit, pol_sub_assign, pol_sub_assign_ext_circuit,
            trace_rows_to_poly_values,
        },
        vars::{StarkEvaluationTargets, StarkEvaluationVars},
        verifier::verify_stark_proof,
    };

    use super::{
        generate_modular_op, modular_constr_poly, modular_constr_poly_ext_circuit, ModularOpWitness,
    };

    const NUM_COLUMS: usize = 11 * N_LIMBS - 2;

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
            let mut rows = vec![];

            for _ in 0..1 << 16 {
                let input0 = BigInt::from_u128(123).unwrap();
                let input1 = BigInt::from_u128(434).unwrap();

                let input0_limbs: [i64; N_LIMBS] = bigint_to_columns(&input0);
                let input1_limbs: [i64; N_LIMBS] = bigint_to_columns(&input1);

                let modulus_limbs = bn254_modulus_limbs();
                let modulus_bigint = columns_to_bigint(&modulus_limbs.map(|x| x as i64));

                let pol_input = pol_mul_wide(input0_limbs, input1_limbs);

                let ModularOpWitness {
                    output,
                    out_aux_red,
                    quot,
                    aux_input_lo,
                    aux_input_hi,
                } = generate_modular_op::<F>(modulus_bigint, pol_input);

                let mut lv = [F::ZERO; NUM_COLUMS];
                lv[0..N_LIMBS]
                    .copy_from_slice(&input0_limbs.map(|x| F::from_canonical_u64(x as u64)));
                lv[N_LIMBS..2 * N_LIMBS]
                    .copy_from_slice(&input1_limbs.map(|x| F::from_canonical_u64(x as u64)));
                lv[2 * N_LIMBS..3 * N_LIMBS]
                    .copy_from_slice(&modulus_limbs.map(|x| F::from_canonical_u64(x as u64)));

                lv[3 * N_LIMBS..4 * N_LIMBS].copy_from_slice(&output);
                lv[4 * N_LIMBS..5 * N_LIMBS].copy_from_slice(&out_aux_red);
                lv[5 * N_LIMBS..7 * N_LIMBS].copy_from_slice(&quot);
                lv[7 * N_LIMBS..9 * N_LIMBS - 1].copy_from_slice(&aux_input_lo);
                lv[9 * N_LIMBS - 1..11 * N_LIMBS - 2].copy_from_slice(&aux_input_hi);
                rows.push(lv);
            }
            trace_rows_to_poly_values(rows)
        }
    }

    impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D> for ModularStark<F, D> {
        const COLUMNS: usize = NUM_COLUMS;
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

            let input0: [P; N_LIMBS] = lv[0..N_LIMBS].to_vec().try_into().unwrap();
            let input1: [P; N_LIMBS] = lv[N_LIMBS..2 * N_LIMBS].to_vec().try_into().unwrap();
            let modulus = lv[2 * N_LIMBS..3 * N_LIMBS].to_vec().try_into().unwrap();
            let output = lv[3 * N_LIMBS..4 * N_LIMBS].to_vec().try_into().unwrap();
            let out_aux_red = lv[4 * N_LIMBS..5 * N_LIMBS].to_vec().try_into().unwrap();
            let quot = lv[5 * N_LIMBS..7 * N_LIMBS].to_vec().try_into().unwrap();
            let aux_input_lo = lv[7 * N_LIMBS..9 * N_LIMBS - 1]
                .to_vec()
                .try_into()
                .unwrap();
            let aux_input_hi = lv[9 * N_LIMBS - 1..11 * N_LIMBS - 2]
                .to_vec()
                .try_into()
                .unwrap();

            let filter = P::ONES;
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

            let input0 = lv[0..N_LIMBS].to_vec().try_into().unwrap();
            let input1 = lv[N_LIMBS..2 * N_LIMBS].to_vec().try_into().unwrap();
            let modulus = lv[2 * N_LIMBS..3 * N_LIMBS].to_vec().try_into().unwrap();
            let output = lv[3 * N_LIMBS..4 * N_LIMBS].to_vec().try_into().unwrap();
            let out_aux_red = lv[4 * N_LIMBS..5 * N_LIMBS].to_vec().try_into().unwrap();
            let quot = lv[5 * N_LIMBS..7 * N_LIMBS].to_vec().try_into().unwrap();
            let aux_input_lo = lv[7 * N_LIMBS..9 * N_LIMBS - 1]
                .to_vec()
                .try_into()
                .unwrap();
            let aux_input_hi = lv[9 * N_LIMBS - 1..11 * N_LIMBS - 2]
                .to_vec()
                .try_into()
                .unwrap();

            let filter = builder.one_extension();
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

        /// The maximum constraint degree.
        fn constraint_degree(&self) -> usize {
            3
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

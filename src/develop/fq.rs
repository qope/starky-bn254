use alloc::vec;
use core::{marker::PhantomData, ops::Range};
use ethereum_types::U256;
use num::Zero;
use num_bigint::{BigInt, Sign};
use plonky2::field::extension::FieldExtension;
use plonky2::field::types::Field;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::{
    field::{
        extension::Extendable, packed::PackedField, polynomial::PolynomialValues,
        types::PrimeField64,
    },
    hash::hash_types::RichField,
};

use crate::constraint_consumer::RecursiveConstraintConsumer;
use crate::stark::Stark;
use crate::util::{bn254_modulus_limbs, pol_add, pol_sub, read_value, trace_rows_to_poly_values};
use crate::vars::{StarkEvaluationTargets, StarkEvaluationVars};
use crate::{
    columns::{self, *},
    constraint_consumer::ConstraintConsumer,
    util::{
        bigint_to_columns, columns_to_bigint, pol_add_assign, pol_adjoin_root, pol_mul_wide,
        pol_mul_wide2, pol_remove_root_2exp, pol_sub_assign, read_value_i64_limbs, u256_to_array,
        BN_BASE,
    },
};

use super::addcy::eval_packed_generic_addcy;

pub fn generate_modular_op<F: PrimeField64>(
    lv: &mut [F],
    pol_input: [i64; 2 * N_LIMBS - 1],
    modulus_range: Range<usize>,
) -> ([F; N_LIMBS], [F; 2 * N_LIMBS]) {
    assert!(modulus_range.len() == N_LIMBS);
    let modulus_limbs = read_value_i64_limbs(lv, modulus_range);

    let modulus = columns_to_bigint(&modulus_limbs);

    // constr_poly is initialised to the input calculation as
    // polynomials, and is used as such for the BigInt reduction;
    // later, other values are added/subtracted, which is where its
    // meaning as the "constraint polynomial" comes in.
    let mut constr_poly = [0i64; 2 * N_LIMBS];
    constr_poly[..2 * N_LIMBS - 1].copy_from_slice(&pol_input);

    // two_exp_256 == 2^256
    let two_exp_256 = {
        let mut t = BigInt::zero();
        t.set_bit(256, true);
        t
    };

    let input = columns_to_bigint(&constr_poly);

    // modulus != 0 here, because, if the given modulus was zero, then
    // it was set to 1 or 2^256 above
    let mut output = &input % &modulus;
    // output will be -ve (but > -modulus) if input was -ve, so we can
    // add modulus to obtain a "canonical" +ve output.
    if output.sign() == Sign::Minus {
        output += &modulus;
    }
    let output_limbs = bigint_to_columns::<N_LIMBS>(&output);
    let quot = (&input - &output) / &modulus; // exact division; can be -ve
    let quot_limbs = bigint_to_columns::<{ 2 * N_LIMBS }>(&quot);

    // output < modulus here; the proof requires (output - modulus) % 2^256:
    // これがなぜ必要なのかわからない。別にこれが生の数である必要も無いし
    let out_aux_red = bigint_to_columns::<N_LIMBS>(&(two_exp_256 - modulus + output));

    // constr_poly is the array of coefficients of the polynomial
    //
    //   operation(a(x), b(x)) - c(x) - s(x)*m(x).
    //
    pol_sub_assign(&mut constr_poly, &output_limbs);
    let prod = pol_mul_wide2(quot_limbs, modulus_limbs);
    pol_sub_assign(&mut constr_poly, &prod[0..2 * N_LIMBS]);

    // Higher order terms of the product must be zero for valid quot and modulus:
    debug_assert!(&prod[2 * N_LIMBS..].iter().all(|&x| x == 0i64));

    // constr_poly must be zero when evaluated at x = β :=
    // 2^LIMB_BITS, hence it's divisible by (x - β). `aux_limbs` is
    // the result of removing that root.
    let mut aux_limbs = pol_remove_root_2exp::<LIMB_BITS, _, { 2 * N_LIMBS }>(constr_poly);

    for c in aux_limbs.iter_mut() {
        // we store the unsigned offset value c + 2^20.
        *c += AUX_COEFF_ABS_MAX;
    }
    debug_assert!(aux_limbs.iter().all(|&c| c.abs() <= 2 * AUX_COEFF_ABS_MAX));

    // nvで使うレンジ: MODULAR_AUX_INPUT_LO, 31 = (16*2 - 1)
    // MODULAR_AUX_INPUT_HI, 31
    // MODULAR_OUT_AUX_RED, 31

    for (i, &c) in MODULAR_AUX_INPUT_LO.zip(&aux_limbs[..2 * N_LIMBS - 1]) {
        // nv-> lv
        lv[i] = F::from_canonical_u16(c as u16);
    }
    for (i, &c) in MODULAR_AUX_INPUT_HI.zip(&aux_limbs[..2 * N_LIMBS - 1]) {
        // nv-> lv
        lv[i] = F::from_canonical_u16((c >> 16) as u16);
    }
    // nv-> lv
    lv[MODULAR_OUT_AUX_RED].copy_from_slice(&out_aux_red.map(F::from_canonical_i64));

    (
        output_limbs.map(F::from_canonical_i64),
        quot_limbs.map(F::from_noncanonical_i64),
    )
}

pub fn modular_constr_poly<P: PackedField>(
    lv: &[P],
    yield_constr: &mut ConstraintConsumer<P>,
    filter: P,
    out_aux_red: [P; N_LIMBS],
    output: [P; N_LIMBS],
    modulus: [P; N_LIMBS],
    quot: [P; 2 * N_LIMBS],
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
        yield_constr.constraint_transition(filter * x);
    }

    // constr_poly = c(x) + q(x) * m(x)
    let mut constr_poly: [_; 2 * N_LIMBS] = prod[0..2 * N_LIMBS].try_into().unwrap();
    pol_add_assign(&mut constr_poly, &output);

    let base = P::Scalar::from_canonical_u64(1 << LIMB_BITS);
    let offset = P::Scalar::from_canonical_u64(AUX_COEFF_ABS_MAX as u64);

    // constr_poly = c(x) + q(x) * m(x) + (x - β) * s(x)
    let mut aux = [P::ZEROS; 2 * N_LIMBS];
    for (c, i) in aux.iter_mut().zip(MODULAR_AUX_INPUT_LO) {
        // MODULAR_AUX_INPUT elements were offset by 2^20 in
        // generation, so we undo that here.
        *c = lv[i] - offset;
    }
    // add high 16-bits of aux input
    for (c, j) in aux.iter_mut().zip(MODULAR_AUX_INPUT_HI) {
        // 2^16を掛けて足し合わせることで復元できる
        // ここがマイナスの可能性がないのはなぜ？
        *c += base * lv[j];
    }

    pol_add_assign(&mut constr_poly, &pol_adjoin_root(aux, base));

    constr_poly
}

pub fn generate<F: PrimeField64>(lv: &mut [F], input0: U256, input1: U256) {
    debug_assert!(lv.len() == NUM_ARITH_COLUMNS);

    u256_to_array(&mut lv[MODULAR_INPUT_0], input0);
    u256_to_array(&mut lv[MODULAR_INPUT_1], input1);
    u256_to_array(&mut lv[MODULAR_MODULUS], BN_BASE);

    // Inputs are all in [0, 2^16), so the "as i64" conversion is safe.
    let input0_limbs = read_value_i64_limbs(lv, MODULAR_INPUT_0);
    let input1_limbs = read_value_i64_limbs(lv, MODULAR_INPUT_1);

    let pol_input = pol_mul_wide(input0_limbs, input1_limbs);

    let (out, quo_input) = generate_modular_op::<F>(lv, pol_input, MODULAR_MODULUS);
    lv[MODULAR_OUTPUT].copy_from_slice(&out);
    lv[MODULAR_QUO_INPUT].copy_from_slice(&quo_input);
}

pub fn eval_packed<P: PackedField>(
    lv: &[P; NUM_ARITH_COLUMNS],
    filter: P,
    yield_constr: &mut ConstraintConsumer<P>,
) {
    // Verify that the modulus is the BN254 modulus for the
    // {ADD,MUL,SUB}FP254 operations.
    let modulus = read_value::<N_LIMBS, _>(lv, MODULAR_MODULUS);
    for (&mi, bi) in modulus.iter().zip(bn254_modulus_limbs()) {
        yield_constr.constraint_transition(mi - P::Scalar::from_canonical_u16(bi));
    }

    let output = read_value::<N_LIMBS, _>(lv, MODULAR_OUTPUT);
    let quo_input = read_value::<{ 2 * N_LIMBS }, _>(lv, MODULAR_QUO_INPUT);
    let out_aux_red = read_value::<N_LIMBS, _>(lv, MODULAR_OUT_AUX_RED);

    // constr_poly has 2*N_LIMBS limbs
    let constr_poly = modular_constr_poly(
        lv,
        yield_constr,
        filter,
        out_aux_red,
        output,
        modulus,
        quo_input,
    );

    let input0 = read_value(lv, MODULAR_INPUT_0);
    let input1 = read_value(lv, MODULAR_INPUT_1);

    let mul_input = pol_mul_wide(input0, input1);

    let mut constr_poly_copy = constr_poly;
    pol_sub_assign(&mut constr_poly_copy, &mul_input);

    for &c in constr_poly_copy.iter() {
        yield_constr.constraint_transition(filter * c);
    }
}

#[derive(Clone, Copy)]
pub struct FqStark<F: RichField + Extendable<D>, const D: usize> {
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> FqStark<F, D> {
    pub fn new() -> Self {
        Self {
            _phantom: PhantomData,
        }
    }
    pub fn generate_trace(&self) -> Vec<PolynomialValues<F>> {
        let mut rows = vec![];

        for _ in 0..1 << 4 {
            let mut lv = [F::ZERO; NUM_ARITH_COLUMNS];
            let input0 = U256::from_dec_str("1").unwrap();
            let input1 = U256::from_dec_str("2").unwrap();
            generate(&mut lv, input0, input1);
            let mut constraint_consumer = ConstraintConsumer::new(
                vec![
                    F::from_canonical_u16(2),
                    F::from_canonical_u16(3),
                    F::from_canonical_u16(5),
                ],
                F::ONE,
                F::ZERO,
                F::ZERO,
            );
            eval_packed::<F>(&lv, F::ONE, &mut constraint_consumer);
            for &acc in &constraint_consumer.constraint_accs {
                assert_eq!(acc, F::ZERO);
            }
            rows.push(lv);
        }
        trace_rows_to_poly_values(rows)
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D> for FqStark<F, D> {
    const COLUMNS: usize = NUM_ARITH_COLUMNS;
    const PUBLIC_INPUTS: usize = 0;

    fn eval_packed_generic<FE, P, const D2: usize>(
        &self,
        vars: StarkEvaluationVars<FE, P, { Self::COLUMNS }, { Self::PUBLIC_INPUTS }>,
        yield_constr: &mut ConstraintConsumer<P>,
    ) where
        FE: FieldExtension<D2, BaseField = F>,
        P: PackedField<Scalar = FE>,
    {
        let lv = vars.local_values;
        eval_packed(&lv, P::ONES, yield_constr);
    }

    fn eval_ext_circuit(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        vars: StarkEvaluationTargets<D, { Self::COLUMNS }, { Self::PUBLIC_INPUTS }>,
        yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    ) {
        todo!()
    }

    /// The maximum constraint degree.
    fn constraint_degree(&self) -> usize {
        3
    }
}

#[cfg(test)]
mod tests {
    use plonky2::{
        plonk::config::{GenericConfig, PoseidonGoldilocksConfig},
        util::timing::TimingTree,
    };

    use crate::{
        config::StarkConfig, develop::fq::FqStark, prover::prove, verifier::verify_stark_proof,
    };

    #[test]
    fn test_should_work() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type S = FqStark<F, D>;

        let config = StarkConfig::standard_fast_config();

        let stark = S::new();
        let trace = stark.generate_trace();

        let public_inputs = vec![];
        let proof = prove::<F, C, S, D>(
            stark,
            &config,
            trace,
            public_inputs.try_into().unwrap(),
            &mut TimingTree::default(),
        )
        .unwrap();
        verify_stark_proof(stark, proof.clone(), &config).unwrap();
    }
}

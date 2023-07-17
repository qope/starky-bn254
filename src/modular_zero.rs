use core::fmt;

use ark_std::Zero;
use itertools::Itertools;
use num::Signed;
use num_bigint::{BigInt, Sign};
use plonky2::{
    field::{extension::Extendable, packed::PackedField, types::Field, types::PrimeField64},
    hash::hash_types::RichField,
    iop::ext_target::ExtensionTarget,
    plonk::circuit_builder::CircuitBuilder,
};

use crate::{
    constants::{LIMB_BITS, N_LIMBS},
    modular::AUX_COEFF_ABS_MAX,
    utils::{
        bigint_to_columns, columns_to_bigint, pol_mul_wide2, pol_remove_root_2exp, pol_sub_assign,
    },
};
use starky::constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer};

use super::utils::{
    pol_add_assign, pol_add_assign_ext_circuit, pol_adjoin_root, pol_adjoin_root_ext_circuit,
    pol_mul_wide2_ext_circuit, pol_sub_assign_ext_circuit,
};

#[derive(Default, Clone, Copy, Debug)]
pub struct ModulusAuxZero<F> {
    pub quot_abs: [F; N_LIMBS + 1],
    pub aux_input_lo: [F; 2 * N_LIMBS - 1],
    pub aux_input_hi: [F; 2 * N_LIMBS - 1],
}

pub fn generate_modular_zero<F: PrimeField64>(
    modulus: &BigInt,
    zero_pol: [i64; 2 * N_LIMBS - 1],
) -> (F, ModulusAuxZero<F>) {
    let modulus_limbs = bigint_to_columns(modulus);
    let input = columns_to_bigint(&zero_pol);
    assert!(&input % modulus == BigInt::zero());

    let quot = &input / modulus;

    let quot_sign = match quot.sign() {
        Sign::Minus => F::NEG_ONE,
        Sign::NoSign => F::ONE, // if quot == 0 then quot_sign == 1
        Sign::Plus => F::ONE,
    };

    let quot_limbs = bigint_to_columns::<{ N_LIMBS + 1 }>(&quot);
    let quot_abs_limbs = bigint_to_columns::<{ N_LIMBS + 1 }>(&quot.abs());
    // constr_poly = zero_pol  - s(x)*m(x).
    let mut constr_poly = [0i64; 2 * N_LIMBS];
    constr_poly[..2 * N_LIMBS - 1].copy_from_slice(&zero_pol);
    let prod: [i64; 2 * N_LIMBS] = pol_mul_wide2(quot_limbs, modulus_limbs);
    pol_sub_assign(&mut constr_poly, &prod);

    // aux_limbs = constr/(x- β)
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
    let quot_abs = quot_abs_limbs.map(|x| F::from_canonical_i64(x));
    let aux = ModulusAuxZero {
        quot_abs,
        aux_input_lo: aux_input_lo.try_into().unwrap(),
        aux_input_hi: aux_input_hi.try_into().unwrap(),
    };
    (quot_sign, aux)
}

pub fn eval_modular_zero<P: PackedField>(
    yield_constr: &mut ConstraintConsumer<P>,
    filter: P,
    modulus: [P; N_LIMBS],
    input: [P; 2 * N_LIMBS - 1],
    quot_sign: P,
    aux: &ModulusAuxZero<P>,
) {
    // validate quot_sign
    yield_constr.constraint(filter * (quot_sign * quot_sign - P::ONES));
    let quot = aux
        .quot_abs
        .iter()
        .map(|&limb| quot_sign * limb)
        .collect_vec();

    // constr_poly = q(x) * m(x)
    let mut constr_poly: [_; 2 * N_LIMBS] = pol_mul_wide2(quot.try_into().unwrap(), modulus);

    let base = P::Scalar::from_canonical_u64(1 << LIMB_BITS);
    let offset = P::Scalar::from_canonical_u64(AUX_COEFF_ABS_MAX as u64);

    // constr_poly = q(x) * m(x) + (x - β) * s(x)
    let mut aux_poly = [P::ZEROS; 2 * N_LIMBS];
    aux_poly[..2 * N_LIMBS - 1]
        .iter_mut()
        .enumerate()
        .for_each(|(i, c)| {
            *c = aux.aux_input_lo[i] - offset;
            *c += base * aux.aux_input_hi[i];
        });

    pol_add_assign(&mut constr_poly, &pol_adjoin_root(aux_poly, base));

    pol_sub_assign(&mut constr_poly, &input);
    for &c in constr_poly.iter() {
        yield_constr.constraint(filter * c);
    }
}

pub fn eval_modular_zero_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    filter: ExtensionTarget<D>,
    modulus: [ExtensionTarget<D>; N_LIMBS],
    input: [ExtensionTarget<D>; 2 * N_LIMBS - 1],
    quot_sign: ExtensionTarget<D>,
    aux: &ModulusAuxZero<ExtensionTarget<D>>,
) {
    // validate quot_sign
    let one = builder.one_extension();
    let diff = builder.mul_sub_extension(quot_sign, quot_sign, one);
    let t = builder.mul_extension(filter, diff);
    yield_constr.constraint(builder, t);

    let quot = aux
        .quot_abs
        .iter()
        .map(|&limb| builder.mul_extension(quot_sign, limb))
        .collect_vec();

    // constr_poly = q(x) * m(x)
    let mut constr_poly: [_; 2 * N_LIMBS] =
        pol_mul_wide2_ext_circuit(builder, quot.try_into().unwrap(), modulus);

    // constr_poly = q(x) * m(x) + (x - β) * s(x)
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

    // q(x) * m(x) + (x - β) * s(x) - zero_pol = 0
    pol_sub_assign_ext_circuit(builder, &mut constr_poly, &input);
    for &c in constr_poly.iter() {
        let t = builder.mul_extension(filter, c);
        yield_constr.constraint(builder, t);
    }
}

/// 5 * N_LIMBS - 1
pub fn write_modulus_aux_zero<F: Copy, const NUM_COL: usize>(
    lv: &mut [F; NUM_COL],
    aux: &ModulusAuxZero<F>,
    cur_col: &mut usize,
) {
    lv[*cur_col..*cur_col + N_LIMBS + 1].copy_from_slice(&aux.quot_abs);
    lv[*cur_col + N_LIMBS + 1..*cur_col + 3 * N_LIMBS].copy_from_slice(&aux.aux_input_lo);
    lv[*cur_col + 3 * N_LIMBS..*cur_col + 5 * N_LIMBS - 1].copy_from_slice(&aux.aux_input_hi);
    *cur_col += 5 * N_LIMBS - 1;
}

/// 5 * N_LIMBS - 1
pub fn read_modulus_aux_zero<F: Copy + fmt::Debug>(
    lv: &[F],
    cur_col: &mut usize,
) -> ModulusAuxZero<F> {
    let quot_abs = lv[*cur_col..*cur_col + N_LIMBS + 1].to_vec();
    let aux_input_lo = lv[*cur_col + N_LIMBS + 1..*cur_col + 3 * N_LIMBS].to_vec();
    let aux_input_hi = lv[*cur_col + 3 * N_LIMBS..*cur_col + 5 * N_LIMBS - 1].to_vec();

    *cur_col += 5 * N_LIMBS - 1;

    ModulusAuxZero {
        quot_abs: quot_abs.try_into().unwrap(),
        aux_input_lo: aux_input_lo.try_into().unwrap(),
        aux_input_hi: aux_input_hi.try_into().unwrap(),
    }
}

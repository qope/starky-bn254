use ark_bn254::Fq2;
use plonky2::hash::hash_types::RichField;

use crate::develop::constants::N_LIMBS;
use crate::develop::modular::ModulusAux;
use crate::develop::modular_zero::ModulusAuxZero;

use super::fq2::{pol_add_fq2, pol_mul_fq2, pol_sub_fq2, to_wide_fq2};
use super::modular::{bn254_base_modulus_bigint, generate_modular_op};
use super::modular_zero::generate_modular_zero;
use super::utils::{
    columns_to_fq2, fq2_to_columns, i64_to_column_positive, positive_column_to_i64,
};

pub struct G2Output<F> {
    pub lambda: [[F; N_LIMBS]; 2],
    pub new_x: [[F; N_LIMBS]; 2],
    pub new_y: [[F; N_LIMBS]; 2],
    pub aux_zeros: [ModulusAuxZero<F>; 2],
    pub auxs: [ModulusAux<F>; 4],
    pub quot_sign_zeros: [F; 2],
    pub quot_signs: [F; 4],
}

impl<F: RichField + Default> Default for G2Output<F> {
    fn default() -> Self {
        Self {
            lambda: [[F::ZERO; N_LIMBS]; 2],
            new_x: [[F::ZERO; N_LIMBS]; 2],
            new_y: [[F::ZERO; N_LIMBS]; 2],
            aux_zeros: [ModulusAuxZero::default(); 2],
            auxs: [ModulusAux::default(); 4],
            quot_sign_zeros: [F::ONE; 2],
            quot_signs: [F::ONE; 4],
        }
    }
}

pub fn generate_g2_add<F: RichField>(
    a_x: [[F; N_LIMBS]; 2],
    a_y: [[F; N_LIMBS]; 2],
    b_x: [[F; N_LIMBS]; 2],
    b_y: [[F; N_LIMBS]; 2],
) -> G2Output<F> {
    let modulus = bn254_base_modulus_bigint();
    // restore
    let a_x_fq2 = columns_to_fq2(a_x);
    let a_y_fq2 = columns_to_fq2(a_y);
    let b_x_fq2 = columns_to_fq2(b_x);
    let b_y_fq2 = columns_to_fq2(b_y);
    let lambda_fq2: Fq2 = ((b_y_fq2 - a_y_fq2) / (b_x_fq2 - a_x_fq2)).into();

    let a_x_i64 = a_x.map(positive_column_to_i64);
    let a_y_i64 = a_y.map(positive_column_to_i64);
    let b_x_i64 = b_x.map(positive_column_to_i64);
    let b_y_i64 = b_y.map(positive_column_to_i64);
    let lambda_i64 = fq2_to_columns(lambda_fq2);
    let lambda: [[F; N_LIMBS]; 2] = lambda_i64.map(i64_to_column_positive);

    let delta_x = pol_sub_fq2(b_x_i64, a_x_i64);
    let delta_y = pol_sub_fq2(b_y_i64, a_y_i64);
    let delta_y = to_wide_fq2(delta_y);
    let lambda_delta_x = pol_mul_fq2(lambda_i64, delta_x);
    let zero_pol = pol_sub_fq2(lambda_delta_x, delta_y);

    let mut aux_zeros = vec![];
    let mut quot_sign_zeros = vec![];

    for i in 0..2 {
        let (quot_sign_zero, aux_zero) = generate_modular_zero::<F>(&modulus, zero_pol[i]);
        aux_zeros.push(aux_zero);
        quot_sign_zeros.push(quot_sign_zero);
    }

    let x1_add_x2 = pol_add_fq2(a_x_i64, b_x_i64);
    let x1_add_x2 = to_wide_fq2(x1_add_x2);
    let lambda_sq = pol_mul_fq2(lambda_i64, lambda_i64);
    let new_x_input = pol_sub_fq2(lambda_sq, x1_add_x2);

    let mut auxs = vec![];
    let mut quot_signs = vec![];
    let mut new_x_coeffs = vec![];

    for i in 0..2 {
        let (new_x, quot_sign_x, aux_x) = generate_modular_op::<F>(&modulus, new_x_input[i]);
        auxs.push(aux_x);
        quot_signs.push(quot_sign_x);
        new_x_coeffs.push(new_x);
    }
    let new_x: [[F; N_LIMBS]; 2] = new_x_coeffs.try_into().unwrap();

    let new_x_i64 = new_x.map(positive_column_to_i64);

    let x1_minus_new_x = pol_sub_fq2(a_x_i64, new_x_i64);
    let lambda_mul_x1_minus_new_x = pol_mul_fq2(lambda_i64, x1_minus_new_x);

    let y_wide = to_wide_fq2(a_y_i64);
    let new_y_input = pol_sub_fq2(lambda_mul_x1_minus_new_x, y_wide);

    let mut new_y_coeffs = vec![];
    for i in 0..2 {
        let (new_y, quot_sign_y, aux_y) = generate_modular_op::<F>(&modulus, new_y_input[i]);
        auxs.push(aux_y);
        quot_signs.push(quot_sign_y);
        new_y_coeffs.push(new_y);
    }
    let new_y: [[F; N_LIMBS]; 2] = new_y_coeffs.try_into().unwrap();

    let aux_zeros: [ModulusAuxZero<F>; 2] = aux_zeros.try_into().unwrap();
    let quot_sign_zeros: [F; 2] = quot_sign_zeros.try_into().unwrap();
    let auxs: [ModulusAux<F>; 4] = auxs.try_into().unwrap();
    let quot_signs: [F; 4] = quot_signs.try_into().unwrap();

    G2Output {
        lambda,
        new_x,
        new_y,
        aux_zeros,
        auxs,
        quot_sign_zeros,
        quot_signs,
    }
}

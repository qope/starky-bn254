use core::ops::Range;

use ethereum_types::U256;
use itertools::Itertools;
use plonky2::field::types::PrimeField64;

use crate::{
    columns::N_LIMBS,
    util::{
        pol_add_assign, pol_add_wide, pol_mul_const, pol_mul_wide, pol_sub_assign, pol_sub_wide,
        read_value_i64_limbs, u256_to_array, BN_BASE,
    },
};

pub fn pol_mul_fq12(
    a_coeffs: Vec<[i64; N_LIMBS]>,
    b_coeffs: Vec<[i64; N_LIMBS]>,
) -> Vec<[i64; 2 * N_LIMBS - 1]> {
    let mut a0b0_coeffs: Vec<[i64; 2 * N_LIMBS - 1]> = Vec::with_capacity(11);
    let mut a0b1_coeffs: Vec<[i64; 2 * N_LIMBS - 1]> = Vec::with_capacity(11);
    let mut a1b0_coeffs: Vec<[i64; 2 * N_LIMBS - 1]> = Vec::with_capacity(11);
    let mut a1b1_coeffs: Vec<[i64; 2 * N_LIMBS - 1]> = Vec::with_capacity(11);
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
    let mut a0b0_minus_a1b1: Vec<[i64; 2 * N_LIMBS - 1]> = Vec::with_capacity(11);
    let mut a0b1_plus_a1b0: Vec<[i64; 2 * N_LIMBS - 1]> = Vec::with_capacity(11);
    for i in 0..11 {
        let a0b0_minus_a1b1_entry = pol_sub_wide(a0b0_coeffs[i], a1b1_coeffs[i]);
        let a0b1_plus_a1b0_entry = pol_add_wide(a0b1_coeffs[i], a1b0_coeffs[i]);
        a0b0_minus_a1b1.push(a0b0_minus_a1b1_entry);
        a0b1_plus_a1b0.push(a0b1_plus_a1b0_entry);
    }

    let mut out_coeffs: Vec<[i64; 2 * N_LIMBS - 1]> = Vec::with_capacity(12);
    for i in 0..6 {
        if i < 5 {
            let nine_times_a0b0_minus_a1b1 = pol_mul_const(a0b0_minus_a1b1[i], 9);
            let mut coeff = pol_add_wide(a0b0_minus_a1b1[i + 6], nine_times_a0b0_minus_a1b1);
            pol_sub_assign(&mut coeff, &a0b1_plus_a1b0[i + 6]);
            out_coeffs.push(coeff);
        } else {
            out_coeffs.push(a0b0_minus_a1b1[i].clone());
        }
    }
    for i in 0..6 {
        if i < 5 {
            let mut coeff = pol_add_wide(a0b1_plus_a1b0[i], a0b0_minus_a1b1[i + 6]);
            let nine_times_a0b1_plus_a1b0 = pol_mul_const(a0b1_plus_a1b0[i + 6], 9);
            pol_add_assign(&mut coeff, &nine_times_a0b1_plus_a1b0);
            out_coeffs.push(coeff);
        } else {
            out_coeffs.push(a0b1_plus_a1b0[i].clone());
        }
    }
    out_coeffs
}

pub enum Query {
    Input0,
    Input1,
    Modulus,
    Output,
    QuoInput,
    AuxRed,
}

pub fn get_place(query: Query, position: Option<usize>) -> Range<usize> {
    let input1_offset = 12 * N_LIMBS;
    let modulus_offset = input1_offset + 12 * N_LIMBS;
    let output_offset = modulus_offset + N_LIMBS;
    let quo_input_offset = output_offset + 12 * N_LIMBS;
    let aux_red_offset = quo_input_offset + 12 * (2 * N_LIMBS - 1);
    match query {
        Query::Input0 => match position {
            None => panic!(),
            Some(pos) => {
                assert!(pos < 12);
                N_LIMBS * pos..N_LIMBS * (pos + 1)
            }
        },
        Query::Input1 => match position {
            None => panic!(),
            Some(pos) => {
                assert!(pos < 12);
                input1_offset + N_LIMBS * pos..input1_offset + N_LIMBS * (pos + 1)
            }
        },
        Query::Modulus => modulus_offset..modulus_offset + N_LIMBS,
        Query::Output => match position {
            None => panic!(),
            Some(pos) => {
                assert!(pos < 12);
                output_offset + N_LIMBS * pos..output_offset + N_LIMBS * (pos + 1)
            }
        },
        Query::QuoInput => match position {
            None => panic!(),
            Some(pos) => {
                assert!(pos < 12);
                quo_input_offset + (2 * N_LIMBS - 1) * pos
                    ..quo_input_offset + (2 * N_LIMBS - 1) * (pos + 1)
            }
        },
        Query::AuxRed => match position {
            None => panic!(),
            Some(pos) => {
                assert!(pos < 12);
                aux_red_offset + N_LIMBS * pos..aux_red_offset + N_LIMBS * (pos + 1)
            }
        },
    };
    todo!()
}

pub fn generate_fq12<F: PrimeField64>(lv: &mut [F], input0: Vec<U256>, input1: Vec<U256>) {
    let input0_limbs_vec = input0
        .iter()
        .enumerate()
        .map(|(pos, x)| {
            let range = get_place(Query::Input0, Some(pos));
            u256_to_array(&mut lv[range.clone()], *x);
            read_value_i64_limbs(lv, range)
        })
        .collect_vec();
    let input1_limbs_vec = input1
        .iter()
        .enumerate()
        .map(|(pos, x)| {
            let range = get_place(Query::Input1, Some(pos));
            u256_to_array(&mut lv[range.clone()], *x);
            read_value_i64_limbs(lv, range)
        })
        .collect_vec();

    let modulus_range = get_place(Query::Modulus, None);
    u256_to_array(&mut lv[modulus_range], BN_BASE);

    let pol_input_vec = pol_mul_fq12(input0_limbs_vec, input1_limbs_vec);

    // pol_input_vec
    //     .iter()
    //     .enumerate()
    //     .for_each(|(pos, pol_input)| {
    //         let (out, quo_input) = generate_modular_op(lv, pol_input.clone(), modulus_range);
    //         let output_range = get_place(Query::Output, Some(pos));

    //         // lv[range].copy_from_slice(x);
    //     });

    //
    // lv[MODULAR_OUTPUT].copy_from_slice(&out);
    // lv[MODULAR_QUO_INPUT].copy_from_slice(&quo_input);
}

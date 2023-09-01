use ark_bn254::{Fq, Fq12, Fq2};
use bitvec::prelude::*;
use itertools::Itertools;
use num_bigint::{BigInt, BigUint, Sign};
use plonky2::field::extension::Extendable;
use plonky2::field::packed::PackedField;
use plonky2::field::polynomial::PolynomialValues;
use plonky2::field::types::{Field, PrimeField64};
use plonky2::hash::hash_types::RichField;
use plonky2::iop::ext_target::ExtensionTarget;
use plonky2::iop::target::Target;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::util::transpose;

use super::flags::NUM_INPUT_LIMBS;
use crate::constants::{LIMB_BITS, N_LIMBS};
use crate::fields::native::MyFq12;

pub fn is_power_of_two(num: usize) -> bool {
    num != 0 && num & (num - 1) == 0
}

pub fn fq_to_u32_columns<F: RichField>(x: Fq) -> [F; NUM_INPUT_LIMBS] {
    let x_biguint: BigUint = x.into();
    let mut x_u32_limbs = x_biguint.to_u32_digits();
    let to_pad = NUM_INPUT_LIMBS - x_u32_limbs.len();
    x_u32_limbs.extend(vec![0; to_pad]);
    let x_u32_limbs = x_u32_limbs
        .into_iter()
        .map(|x| F::from_canonical_u32(x))
        .collect_vec();
    x_u32_limbs.try_into().unwrap()
}

pub fn fq_to_u16_columns<F: RichField>(x: Fq) -> [F; N_LIMBS] {
    let columns = fq_to_columns(x);
    columns.map(|x| F::from_canonical_u16(x as u16))
}

pub fn read_u32_fq<F: Clone + core::fmt::Debug>(
    lv: &[F],
    cur_col: &mut usize,
) -> [F; NUM_INPUT_LIMBS] {
    let output = lv[*cur_col..*cur_col + NUM_INPUT_LIMBS].to_vec();
    *cur_col += NUM_INPUT_LIMBS;
    output.try_into().unwrap()
}

pub fn read_u16_fq<F: Clone + core::fmt::Debug>(lv: &[F], cur_col: &mut usize) -> [F; N_LIMBS] {
    let output = lv[*cur_col..*cur_col + N_LIMBS].to_vec();
    *cur_col += N_LIMBS;
    output.try_into().unwrap()
}

pub fn u16_columns_to_u32_columns<P: PackedField>(x: [P; N_LIMBS]) -> [P; NUM_INPUT_LIMBS] {
    let base = P::Scalar::from_canonical_u32(1 << LIMB_BITS);
    x.chunks(2)
        .map(|chunk| chunk[0] + base * chunk[1])
        .collect_vec()
        .try_into()
        .unwrap()
}

pub fn u16_columns_to_u32_columns_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    x: [ExtensionTarget<D>; N_LIMBS],
) -> [ExtensionTarget<D>; NUM_INPUT_LIMBS] {
    let base = builder.constant_extension(F::Extension::from_canonical_u32(1 << LIMB_BITS));
    x.chunks(2)
        .map(|chunk| builder.mul_add_extension(chunk[1], base, chunk[0]))
        .collect_vec()
        .try_into()
        .unwrap()
}
pub fn u16_columns_to_u32_columns_base_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    x: [Target; N_LIMBS],
) -> [Target; NUM_INPUT_LIMBS] {
    let base = builder.constant(F::from_canonical_u32(1 << LIMB_BITS));
    x.chunks(2)
        .map(|chunk| builder.mul_add(chunk[1], base, chunk[0]))
        .collect_vec()
        .try_into()
        .unwrap()
}

pub fn u32_digits_to_biguint(inputs: &[u32]) -> BigUint {
    let mut bits = vec![];
    for limb in inputs {
        let limb_bits = limb.view_bits::<Lsb0>().iter().map(|b| *b).collect_vec();
        bits.extend(limb_bits);
    }
    bits_to_biguint(&bits)
}

pub fn biguint_to_bits(x: &BigUint, len: usize) -> Vec<bool> {
    let limbs = x.to_bytes_le();
    let mut bits = vec![];
    for limb in limbs {
        let limb_bits = limb.view_bits::<Lsb0>().iter().map(|b| *b).collect_vec();
        bits.extend(limb_bits);
    }
    assert!(bits.len() <= len);
    let to_padd = vec![false; len - bits.len()];
    bits.extend(to_padd);
    bits
}

pub fn bits_to_biguint(bits: &[bool]) -> BigUint {
    let mut limbs = vec![];
    for chunk in bits.chunks(8) {
        let mut limb = 0u8;
        for (i, bit) in chunk.iter().enumerate() {
            if *bit {
                limb |= 1 << i;
            }
        }
        limbs.push(limb);
    }
    BigUint::from_bytes_le(&limbs)
}

pub fn columns_to_bigint<const N: usize>(limbs: &[i64; N]) -> BigInt {
    const BASE: i64 = 1i64 << LIMB_BITS;

    let mut pos_limbs_u32 = Vec::with_capacity(N / 2 + 1);
    let mut neg_limbs_u32 = Vec::with_capacity(N / 2 + 1);
    let mut cy = 0i64; // cy is necessary to handle ε > 0
    for i in 0..(N / 2) {
        let t = cy + limbs[2 * i] + BASE * limbs[2 * i + 1];
        pos_limbs_u32.push(if t > 0 { t as u32 } else { 0u32 });
        neg_limbs_u32.push(if t < 0 { -t as u32 } else { 0u32 });
        cy = t / (1i64 << 32); //　繰り上がり
    }
    if N & 1 != 0 {
        // If N is odd we need to add the last limb on its own
        let t = cy + limbs[N - 1];
        pos_limbs_u32.push(if t > 0 { t as u32 } else { 0u32 });
        neg_limbs_u32.push(if t < 0 { -t as u32 } else { 0u32 });
        cy = t / (1i64 << 32);
    }
    pos_limbs_u32.push(if cy > 0 { cy as u32 } else { 0u32 });
    neg_limbs_u32.push(if cy < 0 { -cy as u32 } else { 0u32 });

    let pos = BigInt::from_slice(Sign::Plus, &pos_limbs_u32);
    let neg = BigInt::from_slice(Sign::Plus, &neg_limbs_u32);
    pos - neg
}

pub fn bigint_to_columns<const N: usize>(num: &BigInt) -> [i64; N] {
    assert!(num.bits() <= 16 * N as u64);
    let mut output = [0i64; N];
    for (i, limb) in num.iter_u32_digits().enumerate() {
        output[2 * i] = limb as u16 as i64;
        if (limb >> LIMB_BITS) == 0 {
            continue;
        }
        output[2 * i + 1] = (limb >> LIMB_BITS) as u16 as i64;
    }
    if num.sign() == Sign::Minus {
        for c in output.iter_mut() {
            *c = -*c;
        }
    }
    output
}

pub fn fq_to_columns(x: Fq) -> [i64; N_LIMBS] {
    let x_biguint: BigUint = x.into();
    bigint_to_columns(&x_biguint.into())
}

pub fn fq12_to_columns(x: Fq12) -> [[i64; N_LIMBS]; 12] {
    let x_myfq12: MyFq12 = x.into();
    x_myfq12
        .coeffs
        .iter()
        .map(|c| fq_to_columns(c.clone()))
        .collect_vec()
        .try_into()
        .unwrap()
}

pub fn fq2_to_columns(x: Fq2) -> [[i64; N_LIMBS]; 2] {
    [x.c0, x.c1].map(|c| fq_to_columns(c.clone()))
}

pub fn columns_to_fq<F: PrimeField64, const N: usize>(column: &[F; N]) -> Fq {
    let column = column.map(|x| x.to_canonical_u64() as i64);
    let x = columns_to_bigint(&column);
    x.to_biguint().unwrap().into()
}

pub fn columns_to_fq2<F: PrimeField64>(column: [[F; N_LIMBS]; 2]) -> Fq2 {
    let coeffs = column
        .iter()
        .map(|column| columns_to_fq(column))
        .collect_vec();
    Fq2::new(coeffs[0], coeffs[1])
}

pub fn columns_to_fq12<F: PrimeField64, const N: usize>(column: [[F; N]; 12]) -> Fq12 {
    let coeffs = column
        .iter()
        .map(|column| columns_to_fq(column))
        .collect_vec();
    MyFq12 {
        coeffs: coeffs.try_into().unwrap(),
    }
    .into()
}

pub fn i64_to_column_positive<F: PrimeField64, const N: usize>(column: [i64; N]) -> [F; N] {
    column.map(|x| F::from_canonical_u64(x as u64))
}

pub fn positive_column_to_i64<F: PrimeField64, const N: usize>(column: [F; N]) -> [i64; N] {
    column.map(|x| x.to_canonical_u64() as i64)
}

/// A helper function to transpose a row-wise trace and put it in the format that `prove` expects.
pub fn trace_rows_to_poly_values<F: Field, const COLUMNS: usize>(
    trace_rows: Vec<[F; COLUMNS]>,
) -> Vec<PolynomialValues<F>> {
    let trace_row_vecs = trace_rows
        .into_iter()
        .map(|row| row.to_vec())
        .collect::<Vec<_>>();
    let trace_col_vecs: Vec<Vec<F>> = transpose(&trace_row_vecs);
    trace_col_vecs
        .into_iter()
        .map(|column| PolynomialValues::new(column))
        .collect()
}

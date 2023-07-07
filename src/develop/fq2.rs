use itertools::Itertools;
use plonky2::{
    field::extension::Extendable, hash::hash_types::RichField, iop::ext_target::ExtensionTarget,
    plonk::circuit_builder::CircuitBuilder,
};

use crate::develop::{
    modular::write_u256,
    utils::{pol_add_wide, pol_mul_wide, pol_sub_wide},
};
use core::fmt::Debug;

use super::{
    constants::N_LIMBS,
    modular::read_u256,
    utils::{
        pol_add_normal, pol_add_normal_ext_circuit, pol_add_wide_ext_circuit, pol_mul_scalar,
        pol_mul_scalar_ext_circuit, pol_mul_wide_ext_circuit, pol_sub_normal,
        pol_sub_normal_ext_circuit, pol_sub_wide_ext_circuit,
    },
};
use std::ops::*;

pub fn to_wide_fq2<T>(x: [[T; N_LIMBS]; 2]) -> [[T; 2 * N_LIMBS - 1]; 2]
where
    T: Default + Copy,
{
    let mut z = [[T::default(); 2 * N_LIMBS - 1]; 2];
    z[0][..N_LIMBS].copy_from_slice(&x[0]);
    z[1][..N_LIMBS].copy_from_slice(&x[1]);
    z
}

pub fn to_wide_fq2_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    x: [[ExtensionTarget<D>; N_LIMBS]; 2],
) -> [[ExtensionTarget<D>; 2 * N_LIMBS - 1]; 2] {
    let zero = builder.zero_extension();
    let mut z = [[zero; 2 * N_LIMBS - 1]; 2];
    z[0][..N_LIMBS].copy_from_slice(&x[0]);
    z[1][..N_LIMBS].copy_from_slice(&x[1]);
    z
}

pub fn pol_mul_fq2<T>(x: [[T; N_LIMBS]; 2], y: [[T; N_LIMBS]; 2]) -> [[T; 2 * N_LIMBS - 1]; 2]
where
    T: Add<Output = T> + AddAssign + Sub<Output = T> + SubAssign + Mul<Output = T> + Copy + Default,
{
    let x_c0 = x[0];
    let x_c1 = x[1];
    let y_c0 = y[0];
    let y_c1 = y[1];

    let x_c0_y_c0 = pol_mul_wide(x_c0, y_c0);
    let x_c1_y_c1 = pol_mul_wide(x_c1, y_c1);
    let z_c0 = pol_sub_wide(x_c0_y_c0, x_c1_y_c1);

    let x_c0_y_c1 = pol_mul_wide(x_c0, y_c1);
    let x_c1_y_c0 = pol_mul_wide(x_c1, y_c0);
    let z_c1 = pol_add_wide(x_c0_y_c1, x_c1_y_c0);
    [z_c0, z_c1]
}

pub fn pol_mul_fq2_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    x: [[ExtensionTarget<D>; N_LIMBS]; 2],
    y: [[ExtensionTarget<D>; N_LIMBS]; 2],
) -> [[ExtensionTarget<D>; 2 * N_LIMBS - 1]; 2] {
    let x_c0 = x[0];
    let x_c1 = x[1];
    let y_c0 = y[0];
    let y_c1 = y[1];

    let x_c0_y_c0 = pol_mul_wide_ext_circuit(builder, x_c0, y_c0);
    let x_c1_y_c1 = pol_mul_wide_ext_circuit(builder, x_c1, y_c1);
    let z_c0 = pol_sub_wide_ext_circuit(builder, x_c0_y_c0, x_c1_y_c1);

    let x_c0_y_c1 = pol_mul_wide_ext_circuit(builder, x_c0, y_c1);
    let x_c1_y_c0 = pol_mul_wide_ext_circuit(builder, x_c1, y_c0);
    let z_c1 = pol_add_wide_ext_circuit(builder, x_c0_y_c1, x_c1_y_c0);
    [z_c0, z_c1]
}

pub fn pol_sub_fq2<T, const N: usize>(x: [[T; N]; 2], y: [[T; N]; 2]) -> [[T; N]; 2]
where
    T: Add<Output = T> + AddAssign + Sub<Output = T> + SubAssign + Mul<Output = T> + Copy + Default,
{
    let x_c0 = x[0];
    let x_c1 = x[1];
    let y_c0 = y[0];
    let y_c1 = y[1];

    let z_c0 = pol_sub_normal(x_c0, y_c0);
    let z_c1 = pol_sub_normal(x_c1, y_c1);
    [z_c0, z_c1]
}

pub fn pol_sub_fq2_circuit<F: RichField + Extendable<D>, const D: usize, const N: usize>(
    builder: &mut CircuitBuilder<F, D>,
    x: [[ExtensionTarget<D>; N]; 2],
    y: [[ExtensionTarget<D>; N]; 2],
) -> [[ExtensionTarget<D>; N]; 2] {
    let x_c0 = x[0];
    let x_c1 = x[1];
    let y_c0 = y[0];
    let y_c1 = y[1];

    let z_c0 = pol_sub_normal_ext_circuit(builder, x_c0, y_c0);
    let z_c1 = pol_sub_normal_ext_circuit(builder, x_c1, y_c1);
    [z_c0, z_c1]
}

pub fn pol_add_fq2<T, const N: usize>(x: [[T; N]; 2], y: [[T; N]; 2]) -> [[T; N]; 2]
where
    T: Add<Output = T> + AddAssign + Sub<Output = T> + SubAssign + Mul<Output = T> + Copy + Default,
{
    let x_c0 = x[0];
    let x_c1 = x[1];
    let y_c0 = y[0];
    let y_c1 = y[1];

    let z_c0 = pol_add_normal(x_c0, y_c0);
    let z_c1 = pol_add_normal(x_c1, y_c1);
    [z_c0, z_c1]
}

pub fn pol_add_fq2_circuit<F: RichField + Extendable<D>, const D: usize, const N: usize>(
    builder: &mut CircuitBuilder<F, D>,
    x: [[ExtensionTarget<D>; N]; 2],
    y: [[ExtensionTarget<D>; N]; 2],
) -> [[ExtensionTarget<D>; N]; 2] {
    let x_c0 = x[0];
    let x_c1 = x[1];
    let y_c0 = y[0];
    let y_c1 = y[1];

    let z_c0 = pol_add_normal_ext_circuit(builder, x_c0, y_c0);
    let z_c1 = pol_add_normal_ext_circuit(builder, x_c1, y_c1);
    [z_c0, z_c1]
}

pub fn pol_mul_scalar_fq2<T, const N: usize>(x: [[T; N]; 2], c: T) -> [[T; N]; 2]
where
    T: Add<Output = T> + AddAssign + Sub<Output = T> + SubAssign + Mul<Output = T> + Copy + Default,
{
    let x_c0 = x[0];
    let x_c1 = x[1];

    let z_c0 = pol_mul_scalar(x_c0, c);
    let z_c1 = pol_mul_scalar(x_c1, c);
    [z_c0, z_c1]
}

pub fn pol_mul_scalar_fq2_circuit<F: RichField + Extendable<D>, const D: usize, const N: usize>(
    builder: &mut CircuitBuilder<F, D>,
    x: [[ExtensionTarget<D>; N]; 2],
    c: F::Extension,
) -> [[ExtensionTarget<D>; N]; 2] {
    let x_c0 = x[0];
    let x_c1 = x[1];

    let z_c0 = pol_mul_scalar_ext_circuit(builder, x_c0, c);
    let z_c1 = pol_mul_scalar_ext_circuit(builder, x_c1, c);
    [z_c0, z_c1]
}

/// 2*N_LIMBS
pub fn write_fq2<F: Copy, const NUM_COL: usize>(
    lv: &mut [F; NUM_COL],
    input: [[F; N_LIMBS]; 2],
    cur_col: &mut usize,
) {
    input
        .iter()
        .for_each(|coeff| write_u256(lv, coeff, cur_col));
}

/// 2*N_LIMBS
pub fn read_fq2<F: Copy + Debug, const NUM_COL: usize>(
    lv: &[F; NUM_COL],
    cur_col: &mut usize,
) -> [[F; N_LIMBS]; 2] {
    (0..2)
        .map(|_| read_u256(lv, cur_col))
        .collect_vec()
        .try_into()
        .unwrap()
}

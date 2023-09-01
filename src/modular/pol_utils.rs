use std::ops::{Add, AddAssign, Mul, Neg, Range, Shr, Sub, SubAssign};

use plonky2::{
    field::extension::Extendable, hash::hash_types::RichField, iop::ext_target::ExtensionTarget,
    plonk::circuit_builder::CircuitBuilder,
};

use crate::constants::N_LIMBS;

/// Return an array of `N` zeros of type T.
pub(crate) fn pol_zero<T, const N: usize>() -> [T; N]
where
    T: Copy + Default,
{
    // TODO: This should really be T::zero() from num::Zero, because
    // default() doesn't guarantee to initialise to zero (though in
    // our case it always does). However I couldn't work out how to do
    // that without touching half of the entire crate because it
    // involves replacing Field::is_zero() with num::Zero::is_zero()
    // which is used everywhere. Hence Default::default() it is.
    [T::default(); N]
}

/// a(x) += b(x), but must have deg(a) >= deg(b).
pub fn pol_add_assign<T>(a: &mut [T], b: &[T])
where
    T: AddAssign + Copy + Default,
{
    debug_assert!(a.len() >= b.len(), "expected {} >= {}", a.len(), b.len());
    for (a_item, b_item) in a.iter_mut().zip(b) {
        *a_item += *b_item;
    }
}

pub fn pol_add_assign_ext_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: &mut [ExtensionTarget<D>],
    b: &[ExtensionTarget<D>],
) {
    debug_assert!(a.len() >= b.len(), "expected {} >= {}", a.len(), b.len());
    for (a_item, b_item) in a.iter_mut().zip(b) {
        *a_item = builder.add_extension(*a_item, *b_item);
    }
}

/// Return a(x) + b(x); returned array is bigger than necessary to
/// make the interface consistent with `pol_mul_wide`.
pub fn pol_add<T>(a: [T; N_LIMBS], b: [T; N_LIMBS]) -> [T; 2 * N_LIMBS - 1]
where
    T: Add<Output = T> + Copy + Default,
{
    let mut sum = pol_zero();
    for i in 0..N_LIMBS {
        sum[i] = a[i] + b[i];
    }
    sum
}

pub fn pol_add_normal<T, const N: usize>(a: [T; N], b: [T; N]) -> [T; N]
where
    T: Add<Output = T> + Copy + Default,
{
    let mut sum = pol_zero();
    for i in 0..N {
        sum[i] = a[i] + b[i];
    }
    sum
}

pub fn pol_add_wide<T>(a: [T; 2 * N_LIMBS - 1], b: [T; 2 * N_LIMBS - 1]) -> [T; 2 * N_LIMBS - 1]
where
    T: Add<Output = T> + Copy + Default,
{
    let mut sum = pol_zero();
    for i in 0..2 * N_LIMBS - 1 {
        sum[i] = a[i] + b[i];
    }
    sum
}

pub fn pol_add_wide_ext_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: [ExtensionTarget<D>; 2 * N_LIMBS - 1],
    b: [ExtensionTarget<D>; 2 * N_LIMBS - 1],
) -> [ExtensionTarget<D>; 2 * N_LIMBS - 1] {
    let zero = builder.zero_extension();
    let mut diff = [zero; 2 * N_LIMBS - 1];
    for i in 0..2 * N_LIMBS - 1 {
        diff[i] = builder.add_extension(a[i], b[i]);
    }
    diff
}

pub fn pol_add_normal_ext_circuit<F: RichField + Extendable<D>, const D: usize, const N: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: [ExtensionTarget<D>; N],
    b: [ExtensionTarget<D>; N],
) -> [ExtensionTarget<D>; N] {
    let zero = builder.zero_extension();
    let mut diff = [zero; N];
    for i in 0..N {
        diff[i] = builder.add_extension(a[i], b[i]);
    }
    diff
}

pub fn pol_add_ext_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: [ExtensionTarget<D>; N_LIMBS],
    b: [ExtensionTarget<D>; N_LIMBS],
) -> [ExtensionTarget<D>; 2 * N_LIMBS - 1] {
    let zero = builder.zero_extension();
    let mut sum = [zero; 2 * N_LIMBS - 1];
    for i in 0..N_LIMBS {
        sum[i] = builder.add_extension(a[i], b[i]);
    }
    sum
}

/// Return a(x) - b(x); returned array is bigger than necessary to
/// make the interface consistent with `pol_mul_wide`.
pub fn pol_sub<T>(a: [T; N_LIMBS], b: [T; N_LIMBS]) -> [T; 2 * N_LIMBS - 1]
where
    T: Sub<Output = T> + Copy + Default,
{
    let mut diff = pol_zero();
    for i in 0..N_LIMBS {
        diff[i] = a[i] - b[i];
    }
    diff
}

pub fn pol_sub_normal<T, const N: usize>(a: [T; N], b: [T; N]) -> [T; N]
where
    T: Sub<Output = T> + Copy + Default,
{
    let mut diff = pol_zero();
    for i in 0..N {
        diff[i] = a[i] - b[i];
    }
    diff
}

pub fn pol_sub_wide<T>(a: [T; 2 * N_LIMBS - 1], b: [T; 2 * N_LIMBS - 1]) -> [T; 2 * N_LIMBS - 1]
where
    T: Sub<Output = T> + Copy + Default,
{
    let mut diff = pol_zero();
    for i in 0..2 * N_LIMBS - 1 {
        diff[i] = a[i] - b[i];
    }
    diff
}

pub fn pol_sub_wide_ext_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: [ExtensionTarget<D>; 2 * N_LIMBS - 1],
    b: [ExtensionTarget<D>; 2 * N_LIMBS - 1],
) -> [ExtensionTarget<D>; 2 * N_LIMBS - 1] {
    let zero = builder.zero_extension();
    let mut diff = [zero; 2 * N_LIMBS - 1];
    for i in 0..2 * N_LIMBS - 1 {
        diff[i] = builder.sub_extension(a[i], b[i]);
    }
    diff
}

pub fn pol_sub_normal_ext_circuit<F: RichField + Extendable<D>, const D: usize, const N: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: [ExtensionTarget<D>; N],
    b: [ExtensionTarget<D>; N],
) -> [ExtensionTarget<D>; N] {
    let zero = builder.zero_extension();
    let mut diff = [zero; N];
    for i in 0..N {
        diff[i] = builder.sub_extension(a[i], b[i]);
    }
    diff
}

pub fn pol_sub_ext_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: [ExtensionTarget<D>; N_LIMBS],
    b: [ExtensionTarget<D>; N_LIMBS],
) -> [ExtensionTarget<D>; 2 * N_LIMBS - 1] {
    let zero = builder.zero_extension();
    let mut diff = [zero; 2 * N_LIMBS - 1];
    for i in 0..N_LIMBS {
        diff[i] = builder.sub_extension(a[i], b[i]);
    }
    diff
}

/// a(x) -= b(x), but must have deg(a) >= deg(b).
pub fn pol_sub_assign<T>(a: &mut [T], b: &[T])
where
    T: SubAssign + Copy,
{
    debug_assert!(a.len() >= b.len(), "expected {} >= {}", a.len(), b.len());
    for (a_item, b_item) in a.iter_mut().zip(b) {
        *a_item -= *b_item;
    }
}

pub fn pol_sub_assign_ext_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: &mut [ExtensionTarget<D>],
    b: &[ExtensionTarget<D>],
) {
    debug_assert!(a.len() >= b.len(), "expected {} >= {}", a.len(), b.len());
    for (a_item, b_item) in a.iter_mut().zip(b) {
        *a_item = builder.sub_extension(*a_item, *b_item);
    }
}

/// Given polynomials a(x) and b(x), return a(x)*b(x).
///
/// NB: The caller is responsible for ensuring that no undesired
/// overflow occurs during the calculation of the coefficients of the
/// product.
pub fn pol_mul_wide<T>(a: [T; N_LIMBS], b: [T; N_LIMBS]) -> [T; 2 * N_LIMBS - 1]
where
    T: AddAssign + Copy + Mul<Output = T> + Default,
{
    let mut res = [T::default(); 2 * N_LIMBS - 1];
    for (i, &ai) in a.iter().enumerate() {
        for (j, &bj) in b.iter().enumerate() {
            res[i + j] += ai * bj;
        }
    }
    res
}

pub fn pol_mul_scalar<T, const N: usize>(a: [T; N], c: T) -> [T; N]
where
    T: Mul<Output = T> + Copy + Default,
{
    let mut muled = pol_zero();
    for i in 0..N {
        muled[i] = c * a[i];
    }
    muled
}

pub fn pol_mul_scalar_ext_circuit<F: RichField + Extendable<D>, const D: usize, const N: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: [ExtensionTarget<D>; N],
    c: F::Extension,
) -> [ExtensionTarget<D>; N] {
    let c = builder.constant_extension(c);
    let zero = builder.zero_extension();
    let mut res = [zero; N];
    for i in 0..N {
        res[i] = builder.mul_extension(a[i], c);
    }
    res
}

pub fn pol_mul_wide_ext_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: [ExtensionTarget<D>; N_LIMBS],
    b: [ExtensionTarget<D>; N_LIMBS],
) -> [ExtensionTarget<D>; 2 * N_LIMBS - 1] {
    let zero = builder.zero_extension();
    let mut res = [zero; 2 * N_LIMBS - 1];
    for (i, &ai) in a.iter().enumerate() {
        for (j, &bj) in b.iter().enumerate() {
            res[i + j] = builder.mul_add_extension(ai, bj, res[i + j]);
        }
    }
    res
}

pub fn pol_mul_wide2<T>(a: [T; N_LIMBS + 1], b: [T; N_LIMBS]) -> [T; 2 * N_LIMBS]
where
    T: AddAssign + Copy + Mul<Output = T> + Default,
{
    let mut res = [T::default(); 2 * N_LIMBS];
    for (i, &ai) in a.iter().enumerate() {
        for (j, &bj) in b.iter().enumerate() {
            res[i + j] += ai * bj;
        }
    }
    res
}

pub fn pol_mul_wide2_ext_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: [ExtensionTarget<D>; N_LIMBS + 1],
    b: [ExtensionTarget<D>; N_LIMBS],
) -> [ExtensionTarget<D>; 2 * N_LIMBS] {
    let zero = builder.zero_extension();
    let mut res = [zero; 2 * N_LIMBS];
    for (i, &ai) in a.iter().enumerate() {
        for (j, &bj) in b.iter().enumerate() {
            res[i + j] = builder.mul_add_extension(ai, bj, res[i + j]);
        }
    }
    res
}

/// Given a(x) and b(x), return a(x)*b(x) mod 2^256.
pub fn pol_mul_lo<T, const N: usize>(a: [T; N], b: [T; N]) -> [T; N]
where
    T: AddAssign + Copy + Default + Mul<Output = T>,
{
    let mut res = pol_zero();
    for deg in 0..N {
        // Invariant: i + j = deg
        for i in 0..=deg {
            let j = deg - i;
            res[deg] += a[i] * b[j];
        }
    }
    res
}

pub fn pol_mul_lo_ext_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: [ExtensionTarget<D>; N_LIMBS],
    b: [ExtensionTarget<D>; N_LIMBS],
) -> [ExtensionTarget<D>; N_LIMBS] {
    let zero = builder.zero_extension();
    let mut res = [zero; N_LIMBS];
    for deg in 0..N_LIMBS {
        for i in 0..=deg {
            let j = deg - i;
            res[deg] = builder.mul_add_extension(a[i], b[j], res[deg]);
        }
    }
    res
}

/// Adjoin M - N zeros to a, returning [a[0], a[1], ..., a[N-1], 0, 0, ..., 0].
pub fn pol_extend<T, const N: usize, const M: usize>(a: [T; N]) -> [T; M]
where
    T: Copy + Default,
{
    assert_eq!(M, 2 * N - 1);

    let mut zero_extend = pol_zero();
    zero_extend[..N].copy_from_slice(&a);
    zero_extend
}

/// Given polynomial a(x) = \sum_{i=0}^{N-2} a[i] x^i and an element
/// `root`, return b = (x - root) * a(x).
pub fn pol_adjoin_root<T, U, const N: usize>(a: [T; N], root: U) -> [T; N]
where
    T: Add<Output = T> + Copy + Default + Mul<Output = T> + Sub<Output = T>,
    U: Copy + Mul<T, Output = T> + Neg<Output = U>,
{
    // \sum_i res[i] x^i = (x - root) \sum_i a[i] x^i. Comparing
    // coefficients, res[0] = -root*a[0] and
    // res[i] = a[i-1] - root * a[i]

    let mut res = [T::default(); N];
    res[0] = -root * a[0];
    for deg in 1..N {
        res[deg] = a[deg - 1] - (root * a[deg]);
    }
    res
}

pub fn pol_adjoin_root_ext_circuit<F: RichField + Extendable<D>, const D: usize, const N: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: [ExtensionTarget<D>; N],
    root: ExtensionTarget<D>,
) -> [ExtensionTarget<D>; N] {
    let zero = builder.zero_extension();
    let mut res = [zero; N];
    // res[0] = NEG_ONE * root * a[0] + ZERO * zero
    res[0] = builder.mul_extension_with_const(F::NEG_ONE, root, a[0]);
    for deg in 1..N {
        // res[deg] = NEG_ONE * root * a[deg] + ONE * a[deg - 1]
        res[deg] = builder.arithmetic_extension(F::NEG_ONE, F::ONE, root, a[deg], a[deg - 1]);
    }
    res
}

/// Given polynomial a(x) = \sum_{i=0}^{N-1} a[i] x^i and a root of `a`
/// of the form 2^EXP, return q(x) satisfying a(x) = (x - root) * q(x).
///
/// NB: We do not verify that a(2^EXP) = 0; if this doesn't hold the
/// result is basically junk.
///
/// NB: The result could be returned in N-1 elements, but we return
/// N and set the last element to zero since the calling code
/// happens to require a result zero-extended to N elements.
pub fn pol_remove_root_2exp<const EXP: usize, T, const N: usize>(a: [T; N]) -> [T; N]
where
    T: Copy + Default + Neg<Output = T> + Shr<usize, Output = T> + Sub<Output = T>,
{
    // By assumption β := 2^EXP is a root of `a`, i.e. (x - β) divides
    // `a`; if we write
    //
    //    a(x) = \sum_{i=0}^{N-1} a[i] x^i
    //         = (x - β) \sum_{i=0}^{N-2} q[i] x^i
    //
    // then by comparing coefficients it is easy to see that
    //
    //   q[0] = -a[0] / β  and  q[i] = (q[i-1] - a[i]) / β
    //
    // for 0 < i <= N-1 (and the divisions are exact).

    let mut q = [T::default(); N];
    q[0] = -(a[0] >> EXP);

    // NB: Last element of q is deliberately left equal to zero.
    for deg in 1..N - 1 {
        q[deg] = (q[deg - 1] - a[deg]) >> EXP;
    }
    q
}

/// Read the range `value_idxs` of values from `lv` into an array of
/// length `N`. Panics if the length of the range is not `N`.
pub fn read_value<const N: usize, T: Copy>(lv: &[T], value_idxs: Range<usize>) -> [T; N] {
    lv[value_idxs].try_into().unwrap()
}

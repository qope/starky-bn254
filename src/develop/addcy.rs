use itertools::Itertools;
use plonky2::field::extension::Extendable;
use plonky2::field::packed::PackedField;
use plonky2::field::types::Field;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::ext_target::ExtensionTarget;
use plonky2::plonk::circuit_builder::CircuitBuilder;

use crate::{
    constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer},
    develop::constants::{LIMB_BITS, N_LIMBS},
};

/// 2^-8 mod (2^64 - 2^32 + 1)
const GOLDILOCKS_INVERSE_256: u64 = 18374686475393433601;

// 繰り上げの足し算を行う
pub fn eval_packed_generic_addcy<P: PackedField>(
    yield_constr: &mut ConstraintConsumer<P>,
    filter: P,
    x: &[P],
    y: &[P],
    z: &[P],
    given_cy: &[P],
) {
    // xとyとzの長さは同じ
    debug_assert!(
        x.len() == N_LIMBS && y.len() == N_LIMBS && z.len() == N_LIMBS && given_cy.len() == N_LIMBS
    );

    let overflow = P::Scalar::from_canonical_u64(1u64 << LIMB_BITS);
    let overflow_inv = P::Scalar::from_canonical_u64(GOLDILOCKS_INVERSE_256);
    assert!(
        overflow * overflow_inv == P::Scalar::ONE,
        "only works with LIMB_BITS=8 and F=Goldilocks"
    );

    // cyはP::zero
    let mut cy = P::ZEROS;
    for ((&xi, &yi), &zi) in x.iter().zip_eq(y).zip_eq(z) {
        // Verify that (xi + yi) - zi is either 0 or 2^LIMB_BITS
        let t = cy + xi + yi - zi;

        // tは0かoverflowかのどちらか
        yield_constr.constraint(filter * t * (overflow - t));

        cy = t * overflow_inv;
    }

    // given_cy[0]が0か1のどちらか
    yield_constr.constraint(filter * given_cy[0] * (given_cy[0] - P::ONES));

    // cyとgiven_cy[0]は等しい
    yield_constr.constraint(filter * (cy - given_cy[0]));

    // given_cyの高次の項は全て0
    for i in 1..N_LIMBS {
        yield_constr.constraint(filter * given_cy[i]);
    }
}

#[allow(clippy::needless_collect)]
pub fn eval_ext_circuit_addcy<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    filter: ExtensionTarget<D>,
    x: &[ExtensionTarget<D>],
    y: &[ExtensionTarget<D>],
    z: &[ExtensionTarget<D>],
    given_cy: &[ExtensionTarget<D>],
) {
    debug_assert!(
        x.len() == N_LIMBS && y.len() == N_LIMBS && z.len() == N_LIMBS && given_cy.len() == N_LIMBS
    );

    // 2^LIMB_BITS in the base field
    let overflow_base = F::from_canonical_u64(1 << LIMB_BITS);
    // 2^LIMB_BITS in the extension field as an ExtensionTarget
    let overflow = builder.constant_extension(F::Extension::from(overflow_base));
    // 2^-LIMB_BITS in the base field.
    let overflow_inv = F::from_canonical_u64(GOLDILOCKS_INVERSE_256);

    let mut cy = builder.zero_extension();
    for ((&xi, &yi), &zi) in x.iter().zip_eq(y).zip_eq(z) {
        // t0 = cy + xi + yi
        let t0 = builder.add_many_extension([cy, xi, yi]);
        // t  = t0 - zi
        let t = builder.sub_extension(t0, zi);
        // t1 = overflow - t
        let t1 = builder.sub_extension(overflow, t);
        // t2 = t * t1
        let t2 = builder.mul_extension(t, t1);

        let filtered_limb_constraint = builder.mul_extension(filter, t2);

        yield_constr.constraint(builder, filtered_limb_constraint);

        cy = builder.mul_const_extension(overflow_inv, t);
    }

    let good_cy = builder.sub_extension(cy, given_cy[0]);
    let cy_filter = builder.mul_extension(filter, good_cy);

    // Check given carry is one bit
    let bit_constr = builder.mul_sub_extension(given_cy[0], given_cy[0], given_cy[0]);
    let bit_filter = builder.mul_extension(filter, bit_constr);

    yield_constr.constraint(builder, bit_filter);
    yield_constr.constraint(builder, cy_filter);
    for i in 1..N_LIMBS {
        let t = builder.mul_extension(filter, given_cy[i]);
        yield_constr.constraint(builder, t);
    }
}

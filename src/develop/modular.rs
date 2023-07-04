use core::fmt;
use core::ops::Range;

use ark_bn254::Fq;
use itertools::Itertools;
use num::{FromPrimitive, Zero};
use num_bigint::{BigInt, BigUint, Sign};
use plonky2::field::types::Field;
use plonky2::iop::ext_target::ExtensionTarget;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::{
    field::{extension::Extendable, packed::PackedField, types::PrimeField64},
    hash::hash_types::RichField,
};

use crate::constraint_consumer::RecursiveConstraintConsumer;
use crate::develop::utils::{
    pol_add_assign_ext_circuit, pol_adjoin_root_ext_circuit, pol_mul_wide2_ext_circuit,
};
use crate::lookup::{eval_lookups, eval_lookups_circuit, permuted_cols};
use crate::permutation::PermutationPair;
use crate::vars::{StarkEvaluationTargets, StarkEvaluationVars};
use crate::{
    constraint_consumer::ConstraintConsumer,
    develop::utils::{
        bigint_to_columns, columns_to_bigint, pol_add_assign, pol_adjoin_root, pol_mul_wide2,
        pol_remove_root_2exp, pol_sub_assign,
    },
};

use super::addcy::{eval_ext_circuit_addcy, eval_packed_generic_addcy};

use crate::develop::constants::{LIMB_BITS, N_LIMBS};

pub const AUX_COEFF_ABS_MAX: i64 = 1 << 20;

pub struct ModulusAux<F> {
    pub out_aux_red: [F; N_LIMBS],
    pub aux_input0: [F; 2 * N_LIMBS - 1],
    pub aux_input1: [F; 2 * N_LIMBS - 1],
    pub aux_input2: [F; 2 * N_LIMBS - 1],
    pub aux_input3: [F; 2 * N_LIMBS - 1],
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

    let aux_input0 = aux_limbs[..2 * N_LIMBS - 1]
        .iter()
        .map(|&c| F::from_canonical_u8(c as u8))
        .collect_vec();
    let aux_input1 = aux_limbs[..2 * N_LIMBS - 1]
        .iter()
        .map(|&c| F::from_canonical_u8((c >> 8) as u8))
        .collect_vec();
    let aux_input2 = aux_limbs[..2 * N_LIMBS - 1]
        .iter()
        .map(|&c| F::from_canonical_u8((c >> 16) as u8))
        .collect_vec();
    let aux_input3 = aux_limbs[..2 * N_LIMBS - 1]
        .iter()
        .map(|&c| F::from_canonical_u8((c >> 24) as u8))
        .collect_vec();

    let output = output_limbs.map(|x| F::from_canonical_u64(x as u64));
    let quot = quot_limbs.map(|x| F::from_noncanonical_i64(x));
    let aux = ModulusAux {
        out_aux_red: out_aux_red.map(|x| F::from_canonical_i64(x)),
        aux_input0: aux_input0.try_into().unwrap(),
        aux_input1: aux_input1.try_into().unwrap(),
        aux_input2: aux_input2.try_into().unwrap(),
        aux_input3: aux_input3.try_into().unwrap(),
    };
    (output, quot, aux)
}

pub fn modular_constr_poly<P: PackedField>(
    yield_constr: &mut ConstraintConsumer<P>,
    filter: P,
    modulus: [P; N_LIMBS],
    output: [P; N_LIMBS],
    quot: [P; 2 * N_LIMBS],
    aux: &ModulusAux<P>,
) -> [P; 2 * N_LIMBS] {
    let mut is_less_than = [P::ZEROS; N_LIMBS];
    is_less_than[0] = P::ONES;
    // ここで modulus + out_aux_red  = output + is_less_than*2^256
    // という制約を掛ける
    eval_packed_generic_addcy(
        yield_constr,
        filter,
        &modulus,
        &aux.out_aux_red,
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
    let mut aux_poly = [P::ZEROS; 2 * N_LIMBS];
    aux_poly[..2 * N_LIMBS - 1]
        .iter_mut()
        .enumerate()
        .for_each(|(i, c)| {
            *c = aux.aux_input0[i] - offset;
            *c += base * aux.aux_input1[i];
            *c += base * base * aux.aux_input2[i];
            *c += base * base * base * aux.aux_input3[i];
        });

    pol_add_assign(&mut constr_poly, &pol_adjoin_root(aux_poly, base));

    constr_poly
}

pub fn modular_constr_poly_ext_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    filter: ExtensionTarget<D>,
    modulus: [ExtensionTarget<D>; N_LIMBS],
    output: [ExtensionTarget<D>; N_LIMBS],
    quot: [ExtensionTarget<D>; 2 * N_LIMBS],
    aux: &ModulusAux<ExtensionTarget<D>>,
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
        &aux.out_aux_red,
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
    let mut aux_poly = [zero; 2 * N_LIMBS];

    let base = F::from_canonical_u64(1u64 << LIMB_BITS);
    aux_poly[..2 * N_LIMBS - 1]
        .iter_mut()
        .enumerate()
        .for_each(|(i, c)| {
            *c = builder.sub_extension(aux.aux_input0[i], offset);
            *c = builder.mul_const_add_extension(base, aux.aux_input1[i], *c);
            *c = builder.mul_const_add_extension(base * base, aux.aux_input2[i], *c);
            *c = builder.mul_const_add_extension(base * base * base, aux.aux_input3[i], *c);
        });

    let base = builder.constant_extension(base.into());
    let t = pol_adjoin_root_ext_circuit(builder, aux_poly, base);
    pol_add_assign_ext_circuit(builder, &mut constr_poly, &t);

    constr_poly
}

/// N_LIMBS
pub fn write_u256<F: Copy, const NUM_COL: usize>(
    lv: &mut [F; NUM_COL],
    input: &[F; N_LIMBS],
    cur_col: &mut usize,
) {
    lv[*cur_col..*cur_col + N_LIMBS].copy_from_slice(input);
    *cur_col += N_LIMBS;
}

/// N_LIMBS
pub fn read_u256<F: Clone + fmt::Debug>(lv: &[F], cur_col: &mut usize) -> [F; N_LIMBS] {
    let output = lv[*cur_col..*cur_col + N_LIMBS].to_vec();
    *cur_col += N_LIMBS;
    output.try_into().unwrap()
}

/// 2 * N_LIMBS
pub fn write_quot<F: Copy, const N: usize>(
    lv: &mut [F; N],
    quot: &[F; 2 * N_LIMBS],
    cur_col: &mut usize,
) {
    lv[*cur_col..*cur_col + 2 * N_LIMBS].copy_from_slice(quot);
    *cur_col += 2 * N_LIMBS;
}

/// 2 * N_LIMBS
pub fn read_quot<F: Clone + fmt::Debug>(lv: &[F], cur_col: &mut usize) -> [F; 2 * N_LIMBS] {
    let output = lv[*cur_col..*cur_col + 2 * N_LIMBS].to_vec();
    *cur_col += 2 * N_LIMBS;
    output.try_into().unwrap()
}

/// 9 * N_LIMBS - 4
pub fn write_modulus_aux<F: Copy, const NUM_COL: usize>(
    lv: &mut [F; NUM_COL],
    aux: &ModulusAux<F>,
    cur_col: &mut usize,
) {
    lv[*cur_col..*cur_col + N_LIMBS].copy_from_slice(&aux.out_aux_red);
    lv[*cur_col + N_LIMBS..*cur_col + 3 * N_LIMBS - 1].copy_from_slice(&aux.aux_input0);
    lv[*cur_col + 3 * N_LIMBS - 1..*cur_col + 5 * N_LIMBS - 2].copy_from_slice(&aux.aux_input1);
    lv[*cur_col + 5 * N_LIMBS - 2..*cur_col + 7 * N_LIMBS - 3].copy_from_slice(&aux.aux_input2);
    lv[*cur_col + 7 * N_LIMBS - 3..*cur_col + 9 * N_LIMBS - 4].copy_from_slice(&aux.aux_input3);
    *cur_col += 9 * N_LIMBS - 4;
}

/// 9 * N_LIMBS - 4
pub fn read_modulus_aux<F: Copy + fmt::Debug>(lv: &[F], cur_col: &mut usize) -> ModulusAux<F> {
    let out_aux_red = lv[*cur_col..*cur_col + N_LIMBS].to_vec();
    let aux_input0 = lv[*cur_col + N_LIMBS..*cur_col + 3 * N_LIMBS - 1].to_vec();
    let aux_input1 = lv[*cur_col + 3 * N_LIMBS - 1..*cur_col + 5 * N_LIMBS - 2].to_vec();
    let aux_input2 = lv[*cur_col + 5 * N_LIMBS - 2..*cur_col + 7 * N_LIMBS - 3].to_vec();
    let aux_input3 = lv[*cur_col + 7 * N_LIMBS - 3..*cur_col + 9 * N_LIMBS - 4].to_vec();

    *cur_col += 9 * N_LIMBS - 4;

    ModulusAux {
        out_aux_red: out_aux_red.try_into().unwrap(),
        aux_input0: aux_input0.try_into().unwrap(),
        aux_input1: aux_input1.try_into().unwrap(),
        aux_input2: aux_input2.try_into().unwrap(),
        aux_input3: aux_input3.try_into().unwrap(),
    }
}

pub fn bn254_base_modulus_bigint() -> BigInt {
    let neg_one: BigUint = Fq::from(-1).into();
    let modulus_biguint: BigUint = neg_one + BigUint::from_usize(1).unwrap();
    let modulus_bigint: BigInt = modulus_biguint.into();
    modulus_bigint
}

pub fn bn254_base_modulus_packfield<P: PackedField>() -> [P; N_LIMBS] {
    let modulus_column: [P; N_LIMBS] = bigint_to_columns(&bn254_base_modulus_bigint())
        .map(|x| P::Scalar::from_canonical_u64(x as u64).into());
    modulus_column
}

pub fn generate_modular_range_check<F: PrimeField64>(
    range_check_unsigned: Range<usize>,
    range_check_signed: Range<usize>,
    trace_cols: &mut Vec<Vec<F>>,
) {
    assert!(trace_cols.iter().all(|col| col.len() == 1 << 9));

    let mut table_unsigned = vec![]; //0, ..., 255, ... , 255
    let mut table_signed = vec![]; //-255, ..., 0, ..., 255

    let range_max: u64 = (1 << 8) - 1;
    for i in 0..1 << 8 {
        table_unsigned.push(F::from_canonical_u64(i));
        table_signed.push(-F::from_canonical_u64(range_max - i));
    }
    for i in 1 << 8..1 << 9 {
        table_unsigned.push(F::from_canonical_u64(range_max));
        table_signed.push(F::from_canonical_u64(i - range_max));
    }
    table_signed[(1 << 9) - 1] = F::from_canonical_u64(range_max);

    trace_cols.push(table_unsigned.clone());

    for i in range_check_unsigned {
        let c = trace_cols[i].clone();
        let (col_perm, table_perm) = permuted_cols(&c, &table_unsigned);
        trace_cols.push(col_perm);
        trace_cols.push(table_perm);
    }

    trace_cols.push(table_signed.clone());

    for i in range_check_signed {
        let c = trace_cols[i].clone();
        let (col_perm, table_perm) = permuted_cols(&c, &table_signed);
        trace_cols.push(col_perm);
        trace_cols.push(table_perm);
    }
}

pub fn eval_modular_lookup<
    F: Field,
    P: PackedField<Scalar = F>,
    const COLS: usize,
    const PUBLIC_INPUTS: usize,
>(
    vars: StarkEvaluationVars<F, P, COLS, PUBLIC_INPUTS>,
    yield_constr: &mut ConstraintConsumer<P>,
    start_lookup_col: usize,
    num_range_unsigned_cols: usize,
    num_range_signed_cols: usize,
) {
    for i in (start_lookup_col + 1..start_lookup_col + 1 + num_range_unsigned_cols).step_by(2) {
        eval_lookups(vars, yield_constr, i, i + 1);
    }
    for i in (start_lookup_col + 2 + 2 * num_range_unsigned_cols
        ..start_lookup_col + 2 + 2 * num_range_unsigned_cols + 2 * num_range_signed_cols)
        .step_by(2)
    {
        eval_lookups(vars, yield_constr, i, i + 1);
    }
    let cur_table_unsigend = vars.local_values[start_lookup_col];
    let next_table_unsigend = vars.next_values[start_lookup_col];
    yield_constr.constraint_first_row(cur_table_unsigend);
    let incr = next_table_unsigend - cur_table_unsigend;
    yield_constr.constraint_transition(incr * incr - incr);
    let range_max = P::Scalar::from_canonical_u64(((1 << 8) - 1) as u64);
    yield_constr.constraint_last_row(cur_table_unsigend - range_max);

    let cur_table_sigend = vars.local_values[start_lookup_col + 1 + 2 * num_range_unsigned_cols];
    let next_table_sigend = vars.next_values[start_lookup_col + 1 + 2 * num_range_unsigned_cols];
    yield_constr.constraint_first_row(cur_table_sigend + range_max);
    let incr = next_table_sigend - cur_table_sigend;
    yield_constr.constraint_transition(incr * incr - incr);
    yield_constr.constraint_last_row(cur_table_sigend - range_max);
}

pub fn eval_modular_lookup_circuit<
    F: RichField + Extendable<D>,
    const D: usize,
    const COLS: usize,
    const PUBLIC_INPUTS: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    vars: StarkEvaluationTargets<D, COLS, PUBLIC_INPUTS>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    start_lookup_col: usize,
    num_range_unsigned_cols: usize,
    num_range_signed_cols: usize,
) {
    for i in (start_lookup_col + 1..start_lookup_col + 1 + num_range_unsigned_cols).step_by(2) {
        eval_lookups_circuit(builder, vars, yield_constr, i, i + 1);
    }
    for i in (start_lookup_col + 2 + 2 * num_range_unsigned_cols
        ..start_lookup_col + 2 + 2 * num_range_unsigned_cols + 2 * num_range_signed_cols)
        .step_by(2)
    {
        eval_lookups_circuit(builder, vars, yield_constr, i, i + 1);
    }
    let cur_table_unsigend = vars.local_values[start_lookup_col];
    let next_table_unsigend = vars.next_values[start_lookup_col];
    yield_constr.constraint_first_row(builder, cur_table_unsigend);
    let incr = builder.sub_extension(next_table_unsigend, cur_table_unsigend);
    let t = builder.mul_sub_extension(incr, incr, incr);
    yield_constr.constraint_transition(builder, t);
    let range_max = builder.constant_extension(F::Extension::from_canonical_usize((1 << 8) - 1));
    let t = builder.sub_extension(cur_table_unsigend, range_max);
    yield_constr.constraint_last_row(builder, t);

    let cur_table_sigend = vars.local_values[start_lookup_col + 1 + 2 * num_range_unsigned_cols];
    let next_table_sigend = vars.next_values[start_lookup_col + 1 + 2 * num_range_unsigned_cols];
    let t = builder.add_extension(cur_table_sigend, range_max);
    yield_constr.constraint_first_row(builder, t);
    let incr = builder.sub_extension(next_table_sigend, cur_table_sigend);
    let t = builder.mul_sub_extension(incr, incr, incr);
    yield_constr.constraint_transition(builder, t);
    let t = builder.sub_extension(cur_table_sigend, range_max);
    yield_constr.constraint_last_row(builder, t);
}

pub fn modular_permutation_pairs(
    start_lookup_col: usize,
    range_check_unsigned: Range<usize>,
    range_check_signed: Range<usize>,
) -> Vec<PermutationPair> {
    let pairs_unsigned = range_check_unsigned
        .clone()
        .enumerate()
        .map(|(i, pos)| PermutationPair::singletons(pos, start_lookup_col + 1 + 2 * i))
        .collect_vec();
    let pairs_signed = range_check_signed
        .clone()
        .enumerate()
        .map(|(i, pos)| {
            PermutationPair::singletons(
                pos,
                start_lookup_col + 1 + 2 * range_check_unsigned.len() + 1 + 2 * i,
            )
        })
        .collect_vec();
    let pairs_unsigned_table = (0..range_check_unsigned.len())
        .map(|i| PermutationPair::singletons(start_lookup_col, start_lookup_col + 2 + 2 * i))
        .collect_vec();
    let pairs_signed_table = (0..range_check_signed.len())
        .map(|i| {
            PermutationPair::singletons(
                start_lookup_col + 1 + 2 * range_check_unsigned.len(),
                start_lookup_col + 1 + 2 * range_check_unsigned.len() + 2 + 2 * i,
            )
        })
        .collect_vec();
    let mut pairs = vec![];
    pairs.extend(pairs_unsigned);
    pairs.extend(pairs_signed);
    pairs.extend(pairs_unsigned_table);
    pairs.extend(pairs_signed_table);
    pairs
}

#[cfg(test)]
mod tests {
    use core::{marker::PhantomData, ops::Range};

    use ark_bn254::Fq;
    use ark_std::UniformRand;
    use itertools::Itertools;
    use num_bigint::BigUint;
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
        util::{timing::TimingTree, transpose},
    };

    use crate::{
        config::StarkConfig,
        constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer},
        develop::constants::{LIMB_BITS, N_LIMBS},
        develop::{
            modular::{
                bn254_base_modulus_bigint, bn254_base_modulus_packfield, eval_modular_lookup,
                eval_modular_lookup_circuit,
            },
            utils::{
                columns_to_bigint, pol_mul_wide, pol_mul_wide_ext_circuit, pol_sub_assign,
                pol_sub_assign_ext_circuit,
            },
        },
        develop::{
            modular::{read_quot, write_modulus_aux, write_quot, write_u256},
            utils::fq_to_columns,
        },
        permutation::PermutationPair,
        prover::prove,
        recursive_verifier::{
            add_virtual_stark_proof_with_pis, set_stark_proof_with_pis_target,
            verify_stark_proof_circuit,
        },
        stark::Stark,
        vars::{StarkEvaluationTargets, StarkEvaluationVars},
        verifier::verify_stark_proof,
    };

    use super::{
        generate_modular_op, generate_modular_range_check, modular_constr_poly,
        modular_constr_poly_ext_circuit, modular_permutation_pairs, read_modulus_aux, read_u256,
    };

    const MAIN_COLS: usize = 14 * N_LIMBS - 3;
    const ROWS: usize = 1 << 9;

    const NUM_RANGE_CHECK_UNSIGNED: usize = 12 * N_LIMBS - 4;
    const NUM_RANGE_CHECK_SIGNED: usize = 2 * N_LIMBS;

    const RANGE_CHECK_UNSIGNED: Range<usize> = 0..NUM_RANGE_CHECK_UNSIGNED;
    const RANGE_CHECK_SIGNED: Range<usize> =
        12 * N_LIMBS - 4..12 * N_LIMBS - 4 + NUM_RANGE_CHECK_SIGNED;

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

            for _ in 0..ROWS {
                let input0_fq = Fq::rand(&mut rng);
                let input1_fq = Fq::rand(&mut rng);
                let output_fq: Fq = input0_fq * input1_fq;
                let output_expected: BigUint = output_fq.into();

                let input0_limbs: [i64; N_LIMBS] = fq_to_columns(input0_fq);
                let input1_limbs: [i64; N_LIMBS] = fq_to_columns(input1_fq);

                let input0 = input0_limbs.map(|x| F::from_canonical_u64(x as u64));
                let input1 = input1_limbs.map(|x| F::from_canonical_u64(x as u64));

                let pol_input = pol_mul_wide(input0_limbs, input1_limbs);

                let (output, quot, aux) =
                    generate_modular_op::<F>(bn254_base_modulus_bigint(), pol_input);

                let output_actual = columns_to_bigint(&output.map(|a| a.to_canonical_u64() as i64));
                assert!(output_expected == output_actual.to_biguint().unwrap());

                let mut lv = [F::ZERO; MAIN_COLS];

                let mut cur_col = 0;

                write_u256(&mut lv, &input0, &mut cur_col); // N_LIMBS
                write_u256(&mut lv, &input1, &mut cur_col); // N_LIMBS
                write_u256(&mut lv, &output, &mut cur_col); // N_LIMBS
                write_modulus_aux(&mut lv, &aux, &mut cur_col); // 9*N_LIMBS - 4
                write_quot(&mut lv, &quot, &mut cur_col); // 2*N_LIMBS
                lv[cur_col] = F::ONE;
                cur_col += 1;

                assert!(cur_col == MAIN_COLS);
                assert!(lv.iter().all(|x| x.to_canonical_u64() < (1 << LIMB_BITS)));
                rows.push(lv);
            }

            let mut trace_cols = transpose(&rows.iter().map(|v| v.to_vec()).collect_vec());
            generate_modular_range_check(RANGE_CHECK_UNSIGNED, RANGE_CHECK_SIGNED, &mut trace_cols);

            trace_cols
                .into_iter()
                .map(|column| PolynomialValues::new(column))
                .collect()
        }
    }

    impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D> for ModularStark<F, D> {
        const COLUMNS: usize =
            MAIN_COLS + 2 + 2 * NUM_RANGE_CHECK_UNSIGNED + 2 * NUM_RANGE_CHECK_SIGNED;
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

            eval_modular_lookup(
                vars,
                yield_constr,
                MAIN_COLS,
                NUM_RANGE_CHECK_UNSIGNED,
                NUM_RANGE_CHECK_SIGNED,
            );

            let mut cur_col = 0;

            let input0: [P; N_LIMBS] = read_u256(&lv, &mut cur_col);
            let input1: [P; N_LIMBS] = read_u256(&lv, &mut cur_col);
            let output = read_u256(&lv, &mut cur_col);

            let aux = read_modulus_aux(&lv, &mut cur_col);
            let quot = read_quot(&lv, &mut cur_col);

            let filter = lv[cur_col];
            cur_col += 1;
            assert!(cur_col == MAIN_COLS);

            let constr_poly = modular_constr_poly(
                yield_constr,
                filter,
                bn254_base_modulus_packfield(),
                output,
                quot,
                &aux,
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

            eval_modular_lookup_circuit(
                builder,
                vars,
                yield_constr,
                MAIN_COLS,
                NUM_RANGE_CHECK_UNSIGNED,
                NUM_RANGE_CHECK_SIGNED,
            );

            let mut cur_col = 0;

            let input0 = read_u256(&lv, &mut cur_col);
            let input1 = read_u256(&lv, &mut cur_col);
            let output = read_u256(&lv, &mut cur_col);

            let modulus: [F::Extension; N_LIMBS] = bn254_base_modulus_packfield();
            let modulus = modulus.map(|x| builder.constant_extension(x));

            let aux = read_modulus_aux(&lv, &mut cur_col);
            let quot = read_quot(&lv, &mut cur_col);

            let filter = lv[cur_col];
            cur_col += 1;
            assert!(cur_col == MAIN_COLS);

            let constr_poly = modular_constr_poly_ext_circuit(
                builder,
                yield_constr,
                filter,
                modulus,
                output,
                quot,
                &aux,
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
            modular_permutation_pairs(MAIN_COLS, RANGE_CHECK_UNSIGNED, RANGE_CHECK_SIGNED)
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

use core::fmt;
use core::marker::PhantomData;

use ark_bn254::{Fq12, Fr};
use ark_ff::Field;
use ark_std::UniformRand;
use itertools::Itertools;
use num_bigint::BigUint;
use plonky2::field::types::Field as plonky2_field;
use plonky2::iop::ext_target::ExtensionTarget;
use plonky2::{
    field::{
        extension::{Extendable, FieldExtension},
        packed::PackedField,
        polynomial::PolynomialValues,
    },
    hash::hash_types::RichField,
    plonk::circuit_builder::CircuitBuilder,
    util::transpose,
};

use crate::develop::fq12::{
    generate_fq12_modular_op, pol_mul_fq12, pol_mul_fq12_ext_circuit, read_fq12, write_fq12,
};
use crate::develop::range_check::{
    eval_u16_range_check, eval_u16_range_check_circuit, generate_u16_range_check,
};
use crate::develop::utils::{biguint_to_bits, columns_to_fq12, fq12_to_columns};
use crate::{
    constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer},
    develop::constants::N_LIMBS,
    develop::modular::write_modulus_aux,
    permutation::PermutationPair,
    stark::Stark,
    vars::{StarkEvaluationTargets, StarkEvaluationVars},
};

use crate::develop::modular::{
    bn254_base_modulus_bigint, eval_modular_op_circuit, read_modulus_aux,
};

use super::modular::{bn254_base_modulus_packfield, eval_modular_op};
use super::range_check::u16_range_check_pairs;

pub fn write_instruction<F: Copy, const N: usize, const INSTRUCTION_LEN: usize>(
    lv: &mut [F; N],
    instruction: &[F; INSTRUCTION_LEN],
    cur_col: &mut usize,
) {
    lv[*cur_col..*cur_col + INSTRUCTION_LEN].copy_from_slice(instruction);
    *cur_col += INSTRUCTION_LEN;
}

pub fn read_instruction<F: Clone + fmt::Debug, const N: usize, const INSTRUCTION_LEN: usize>(
    lv: &[F; N],
    cur_col: &mut usize,
) -> [F; INSTRUCTION_LEN] {
    let output = lv[*cur_col..*cur_col + INSTRUCTION_LEN].to_vec();
    *cur_col += INSTRUCTION_LEN;
    output.try_into().unwrap()
}

pub fn eval_bool<P: PackedField>(yield_constr: &mut ConstraintConsumer<P>, val: P) {
    yield_constr.constraint(val * val - val);
}

pub fn eval_bool_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    val: ExtensionTarget<D>,
) {
    let t = builder.mul_sub_extension(val, val, val);
    yield_constr.constraint(builder, t);
}

pub fn fq12_equal_transition<P: PackedField>(
    yield_constr: &mut ConstraintConsumer<P>,
    filter: P,
    x: &Vec<[P; N_LIMBS]>,
    y: &Vec<[P; N_LIMBS]>,
) {
    assert!(x.len() == 12 && y.len() == 12);
    (0..12).for_each(|i| {
        let x_i = x[i];
        let y_i = y[i];
        x_i.iter()
            .zip(y_i.iter())
            .for_each(|(&x, &y)| yield_constr.constraint_transition(filter * (x - y)));
    });
}

pub fn fq12_equal_transition_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    filter: ExtensionTarget<D>,
    x: &Vec<[ExtensionTarget<D>; N_LIMBS]>,
    y: &Vec<[ExtensionTarget<D>; N_LIMBS]>,
) {
    assert!(x.len() == 12 && y.len() == 12);
    (0..12).for_each(|i| {
        let x_i = x[i];
        let y_i = y[i];
        x_i.iter().zip(y_i.iter()).for_each(|(&x, &y)| {
            let diff = builder.sub_extension(x, y);
            let t = builder.mul_extension(filter, diff);
            yield_constr.constraint_transition(builder, t);
        });
    });
}

const BITS_LEN: usize = 256;

const START_RANGE_CHECK: usize = 24 * N_LIMBS;
const NUM_RANGE_CHECK: usize = 84 * N_LIMBS - 12;
const END_RANGE_CHECK: usize = START_RANGE_CHECK + NUM_RANGE_CHECK;

const IS_SQ_COL: usize = END_RANGE_CHECK + 12;
const IS_NOOP_COL: usize = IS_SQ_COL + 1;
const IS_MUL_COL: usize = IS_SQ_COL + 2;

const MAIN_COLS: usize = IS_MUL_COL + BITS_LEN;

const ROWS: usize = 1 << 16;

#[derive(Clone, Copy)]
pub struct Fq12ExpStark<F: RichField + Extendable<D>, const D: usize> {
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> Fq12ExpStark<F, D> {
    pub fn new() -> Self {
        Self {
            _phantom: PhantomData,
        }
    }

    pub fn generate_trace(&self) -> Vec<PolynomialValues<F>> {
        let mut rng = rand::thread_rng();

        let modulus = bn254_base_modulus_bigint();
        let xi = 9;

        let exp_val: Fr = Fr::rand(&mut rng);
        let exp_bits: Vec<F> = biguint_to_bits(&exp_val.into(), BITS_LEN)
            .iter()
            .map(|&b| F::from_bool(b))
            .collect_vec();
        assert!(exp_bits.len() == BITS_LEN);

        let x_input = Fq12::rand(&mut rng);
        let exp_val_biguint: BigUint = exp_val.into();
        let x_exp_expected: Fq12 = x_input.pow(&exp_val_biguint.to_u64_digits());

        let x_i64 = fq12_to_columns(x_input);
        let y_i64 = fq12_to_columns(Fq12::ONE);

        let x = x_i64
            .iter()
            .map(|coeff| coeff.map(|x| F::from_canonical_i64(x)))
            .collect_vec();
        let y = y_i64
            .iter()
            .map(|coeff| coeff.map(|x| F::from_canonical_i64(x)))
            .collect_vec();

        let mut lv = [F::ZERO; MAIN_COLS];
        let mut cur_col = 0;
        write_fq12(&mut lv, &x, &mut cur_col); //12*N_LIMBS
        write_fq12(&mut lv, &y, &mut cur_col); //12*N_LIMBS

        lv[IS_SQ_COL] = F::ZERO;
        cur_col = IS_MUL_COL;
        write_instruction::<_, MAIN_COLS, BITS_LEN>(
            &mut lv,
            &exp_bits.try_into().unwrap(),
            &mut cur_col,
        );
        lv[IS_NOOP_COL] = F::ONE - lv[IS_MUL_COL];

        let mut rows = vec![];

        for _ in 0..ROWS {
            // read x, y, and instruction
            let mut cur_col = 0;
            let x = read_fq12(&lv, &mut cur_col);
            let y = read_fq12(&lv, &mut cur_col);
            let is_sq = lv[IS_SQ_COL];
            let is_mul = lv[IS_MUL_COL];
            let is_noop = lv[IS_NOOP_COL];

            cur_col = IS_MUL_COL;
            let mul_instruction = read_instruction::<_, MAIN_COLS, BITS_LEN>(&lv, &mut cur_col);

            let x_i64 = x
                .iter()
                .map(|limb| limb.map(|x| x.to_canonical_u64() as i64))
                .collect_vec();
            let y_i64 = y
                .iter()
                .map(|limb| limb.map(|x| x.to_canonical_u64() as i64))
                .collect_vec();

            // compute input
            let input = if is_sq == F::ONE {
                assert!(is_mul == F::ZERO && is_noop == F::ZERO);
                pol_mul_fq12(x_i64.clone(), x_i64.clone(), xi)
            } else if is_mul == F::ONE {
                assert!(is_sq == F::ZERO && is_noop == F::ZERO);
                pol_mul_fq12(x_i64.clone(), y_i64.clone(), xi)
            } else {
                assert!(is_noop == F::ONE && is_sq == F::ZERO && is_mul == F::ZERO);
                vec![[0i64; 2 * N_LIMBS - 1]; 12]
            };

            // compute output
            let (output, auxs, quot_signs) = generate_fq12_modular_op::<F>(modulus.clone(), &input);
            // write output
            cur_col = 24 * N_LIMBS;
            write_fq12(&mut lv, &output, &mut cur_col);

            // write auxs
            auxs.iter().for_each(|aux| {
                write_modulus_aux(&mut lv, aux, &mut cur_col);
            });
            quot_signs.iter().for_each(|&sign| {
                lv[cur_col] = sign;
                cur_col += 1;
            });
            assert!(cur_col == IS_SQ_COL);

            // transition rule
            let mut nv = [F::ZERO; MAIN_COLS];
            cur_col = 0;

            if is_sq == F::ONE {
                write_fq12(&mut nv, &output, &mut cur_col);
                write_fq12(&mut nv, &y, &mut cur_col);
            } else if is_mul == F::ONE {
                write_fq12(&mut nv, &x, &mut cur_col);
                write_fq12(&mut nv, &output, &mut cur_col);
            } else {
                assert!(is_noop == F::ONE);
                write_fq12(&mut nv, &x, &mut cur_col);
                write_fq12(&mut nv, &y, &mut cur_col);
            }
            // transition rule for instruction
            nv[IS_SQ_COL] = F::ONE - is_sq;
            cur_col = IS_MUL_COL;
            if is_sq == F::ONE {
                // rotate instruction
                let mut rotated_instruction = mul_instruction[1..].to_vec();
                rotated_instruction.push(F::ZERO);
                write_instruction::<_, MAIN_COLS, BITS_LEN>(
                    &mut nv,
                    &rotated_instruction.try_into().unwrap(),
                    &mut cur_col,
                );
            } else {
                write_instruction::<_, MAIN_COLS, BITS_LEN>(
                    &mut nv,
                    &mul_instruction.try_into().unwrap(),
                    &mut cur_col,
                );
                // set nv[IS_MUL_COL] to 0 to ensure is_mul + is_sq + is_noop = 1
                // this cell is never used.
                nv[IS_MUL_COL] = F::ZERO;
            }

            nv[IS_NOOP_COL] = (F::ONE - nv[IS_MUL_COL]) * (F::ONE - nv[IS_SQ_COL]);

            rows.push(lv);
            lv = nv;
        }
        assert!(rows.len() == ROWS);

        let mut cur_col = 12 * N_LIMBS;
        let y = read_fq12(&lv, &mut cur_col);
        let result = columns_to_fq12(&y);
        assert!(result == x_exp_expected);

        let mut trace_cols = transpose(&rows.iter().map(|v| v.to_vec()).collect_vec());

        generate_u16_range_check(START_RANGE_CHECK..END_RANGE_CHECK, &mut trace_cols);

        let trace = trace_cols
            .into_iter()
            .map(|column| PolynomialValues::new(column))
            .collect();

        trace
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D> for Fq12ExpStark<F, D> {
    const COLUMNS: usize = MAIN_COLS + 1 + 2 * NUM_RANGE_CHECK;
    const PUBLIC_INPUTS: usize = 0;

    fn eval_packed_generic<FE, P, const D2: usize>(
        &self,
        vars: StarkEvaluationVars<FE, P, { Self::COLUMNS }, { Self::PUBLIC_INPUTS }>,
        yield_constr: &mut ConstraintConsumer<P>,
    ) where
        FE: FieldExtension<D2, BaseField = F>,
        P: PackedField<Scalar = FE>,
    {
        let xi: P = P::Scalar::from_canonical_u32(9).into();
        let modulus = bn254_base_modulus_packfield();

        eval_u16_range_check(
            vars,
            yield_constr,
            MAIN_COLS,
            START_RANGE_CHECK..END_RANGE_CHECK,
        );

        let lv = vars.local_values.clone();
        // read x, y, z, and instruction
        let mut cur_col = 0;
        let x = read_fq12(&lv, &mut cur_col);
        let y = read_fq12(&lv, &mut cur_col);
        let z = read_fq12(&lv, &mut cur_col);
        let auxs = (0..12)
            .map(|_| read_modulus_aux(&lv, &mut cur_col))
            .collect_vec();
        let quot_signs = (0..12)
            .map(|_| {
                let sign = lv[cur_col];
                cur_col += 1;
                sign
            })
            .collect_vec();
        assert!(cur_col == IS_SQ_COL);
        let is_sq = lv[IS_SQ_COL];
        let is_mul = lv[IS_MUL_COL];
        let is_noop = lv[IS_NOOP_COL];

        // validation of first row
        yield_constr.constraint_first_row(is_sq);

        // validation of instruction
        eval_bool(yield_constr, is_noop);
        yield_constr.constraint(is_sq + is_mul + is_noop - P::ONES);

        // validation of z
        let x_sq: Vec<[_; 2 * N_LIMBS - 1]> = pol_mul_fq12(x.clone(), x.clone(), xi);
        let x_mul_y: Vec<[_; 2 * N_LIMBS - 1]> = pol_mul_fq12(x.clone(), y.clone(), xi);

        (0..12).for_each(|i| {
            eval_modular_op(
                yield_constr,
                is_sq,
                modulus,
                x_sq[i],
                z[i],
                quot_signs[i],
                &auxs[i],
            );
            eval_modular_op(
                yield_constr,
                is_mul,
                modulus,
                x_mul_y[i],
                z[i],
                quot_signs[i],
                &auxs[i],
            )
        });

        // transition rule
        let nv = vars.next_values.clone();
        cur_col = 0;
        let next_x = read_fq12(&nv, &mut cur_col);
        let next_y = read_fq12(&nv, &mut cur_col);
        let next_is_sq = nv[IS_SQ_COL];

        cur_col = IS_MUL_COL;
        let next_instruction: [_; BITS_LEN] = read_instruction(&nv, &mut cur_col);

        // if is_sq == 1
        fq12_equal_transition(yield_constr, is_sq, &z, &next_x);
        fq12_equal_transition(yield_constr, is_sq, &y, &next_y);

        // if is_mul == 1
        fq12_equal_transition(yield_constr, is_mul, &x, &next_x);
        fq12_equal_transition(yield_constr, is_mul, &z, &next_y);

        // if is_noop == 1
        fq12_equal_transition(yield_constr, is_noop, &x, &next_x);
        fq12_equal_transition(yield_constr, is_noop, &y, &next_y);

        // transition rule for instruction
        cur_col = IS_MUL_COL;
        let instruction: [_; BITS_LEN] = read_instruction(&lv, &mut cur_col);
        yield_constr.constraint_transition(next_is_sq + is_sq - P::ONES);

        // if is_sq == 1, then rotate instruction
        for i in 1..BITS_LEN {
            yield_constr.constraint_transition(is_sq * (next_instruction[i - 1] - instruction[i]));
        }
        yield_constr.constraint_transition(is_sq * next_instruction[BITS_LEN - 1]);

        // if is_sq == 0, then copy instruction, except for the first which is set to 0 (this does not have to be verified)
        let not_is_sq = P::ONES - is_sq;
        for i in 1..BITS_LEN {
            yield_constr.constraint_transition(not_is_sq * (next_instruction[i] - instruction[i]));
        }
    }

    fn eval_ext_circuit(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        vars: StarkEvaluationTargets<D, { Self::COLUMNS }, { Self::PUBLIC_INPUTS }>,
        yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    ) {
        let xi = F::Extension::from_canonical_u32(9);
        let modulus = bn254_base_modulus_packfield().map(|x| builder.constant_extension(x));
        let one = builder.one_extension();

        eval_u16_range_check_circuit(
            builder,
            vars,
            yield_constr,
            MAIN_COLS,
            START_RANGE_CHECK..END_RANGE_CHECK,
        );

        let lv = vars.local_values.clone();
        // read x, y, z, and instruction
        let mut cur_col = 0;
        let x = read_fq12(&lv, &mut cur_col);
        let y = read_fq12(&lv, &mut cur_col);
        let z = read_fq12(&lv, &mut cur_col);
        let auxs = (0..12)
            .map(|_| read_modulus_aux(&lv, &mut cur_col))
            .collect_vec();
        let quot_signs = (0..12)
            .map(|_| {
                let sign = lv[cur_col];
                cur_col += 1;
                sign
            })
            .collect_vec();
        assert!(cur_col == IS_SQ_COL);
        let is_sq = lv[IS_SQ_COL];
        let is_mul = lv[IS_MUL_COL];
        let is_noop = lv[IS_NOOP_COL];

        // validation of first row
        yield_constr.constraint_first_row(builder, is_sq);

        // validation of instruction
        eval_bool_circuit(builder, yield_constr, is_noop);
        let sum = builder.add_many_extension([is_sq, is_mul, is_noop]);
        let diff = builder.sub_extension(sum, one);
        yield_constr.constraint(builder, diff);

        // validation of z
        let x_sq: Vec<[_; 2 * N_LIMBS - 1]> =
            pol_mul_fq12_ext_circuit(builder, x.clone(), x.clone(), xi);
        let x_mul_y: Vec<[_; 2 * N_LIMBS - 1]> =
            pol_mul_fq12_ext_circuit(builder, x.clone(), y.clone(), xi);

        (0..12).for_each(|i| {
            eval_modular_op_circuit(
                builder,
                yield_constr,
                is_sq,
                modulus,
                x_sq[i],
                z[i],
                quot_signs[i],
                &auxs[i],
            );
            eval_modular_op_circuit(
                builder,
                yield_constr,
                is_mul,
                modulus,
                x_mul_y[i],
                z[i],
                quot_signs[i],
                &auxs[i],
            )
        });

        // transition rule
        let nv = vars.next_values.clone();
        cur_col = 0;
        let next_x = read_fq12(&nv, &mut cur_col);
        let next_y = read_fq12(&nv, &mut cur_col);
        let next_is_sq = nv[IS_SQ_COL];

        cur_col = IS_MUL_COL;
        let next_instruction: [_; BITS_LEN] = read_instruction(&nv, &mut cur_col);

        // if is_sq == 1
        fq12_equal_transition_circuit(builder, yield_constr, is_sq, &z, &next_x);
        fq12_equal_transition_circuit(builder, yield_constr, is_sq, &y, &next_y);

        // if is_mul == 1
        fq12_equal_transition_circuit(builder, yield_constr, is_mul, &x, &next_x);
        fq12_equal_transition_circuit(builder, yield_constr, is_mul, &z, &next_y);

        // if is_noop == 1
        fq12_equal_transition_circuit(builder, yield_constr, is_noop, &x, &next_x);
        fq12_equal_transition_circuit(builder, yield_constr, is_noop, &y, &next_y);

        // transition rule for instruction
        cur_col = IS_MUL_COL;
        let instruction: [_; BITS_LEN] = read_instruction(&lv, &mut cur_col);
        let sum = builder.add_extension(next_is_sq, is_sq);
        let diff = builder.sub_extension(sum, one);
        yield_constr.constraint_transition(builder, diff);

        // if is_sq == 1, then rotate instruction
        for i in 1..BITS_LEN {
            let diff = builder.sub_extension(next_instruction[i - 1], instruction[i]);
            let t = builder.mul_extension(is_sq, diff);
            yield_constr.constraint_transition(builder, t);
        }
        let t = builder.mul_extension(is_sq, next_instruction[BITS_LEN - 1]);
        yield_constr.constraint_transition(builder, t);

        // if is_sq == 0, then copy instruction, except for the first which is set to 0 (this does not have to be verified)
        let not_is_sq = builder.sub_extension(one, is_sq);
        for i in 1..BITS_LEN {
            let diff = builder.sub_extension(next_instruction[i], instruction[i]);
            let t = builder.mul_extension(not_is_sq, diff);
            yield_constr.constraint_transition(builder, t);
        }
    }

    fn constraint_degree(&self) -> usize {
        3
    }

    fn permutation_pairs(&self) -> Vec<PermutationPair> {
        u16_range_check_pairs(MAIN_COLS, START_RANGE_CHECK..END_RANGE_CHECK)
    }
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use plonky2::{
        iop::witness::PartialWitness,
        plonk::{
            circuit_builder::CircuitBuilder,
            circuit_data::CircuitConfig,
            config::{GenericConfig, PoseidonGoldilocksConfig},
        },
        util::timing::TimingTree,
    };

    use crate::{
        config::StarkConfig,
        develop::fq12_exp::Fq12ExpStark,
        prover::prove,
        recursive_verifier::{
            add_virtual_stark_proof_with_pis, set_stark_proof_with_pis_target,
            verify_stark_proof_circuit,
        },
        verifier::verify_stark_proof,
    };

    #[test]
    fn test_fq12_exp() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type S = Fq12ExpStark<F, D>;
        let inner_config = StarkConfig::standard_fast_config();
        let stark = S::new();
        let trace = stark.generate_trace();

        println!("start stark proof generation");
        let now = Instant::now();
        let pi = vec![];
        let inner_proof = prove::<F, C, S, D>(
            stark,
            &inner_config,
            trace,
            pi.try_into().unwrap(),
            &mut TimingTree::default(),
        )
        .unwrap();
        verify_stark_proof(stark, inner_proof.clone(), &inner_config).unwrap();
        println!("end stark proof generation: {:?}", now.elapsed());

        let circuit_config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(circuit_config);
        let mut pw = PartialWitness::new();
        let degree_bits = inner_proof.proof.recover_degree_bits(&inner_config);
        let pt = add_virtual_stark_proof_with_pis(&mut builder, stark, &inner_config, degree_bits);
        set_stark_proof_with_pis_target(&mut pw, &pt, &inner_proof);
        verify_stark_proof_circuit::<F, C, S, D>(&mut builder, stark, pt, &inner_config);
        let data = builder.build::<C>();

        println!("start plonky2 proof generation");
        let now = Instant::now();
        let _proof = data.prove(pw).unwrap();
        println!("end plonky2 proof generation: {:?}", now.elapsed());
    }
}

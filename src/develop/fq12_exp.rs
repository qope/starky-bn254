use core::marker::PhantomData;

use ark_bn254::{Fq12, Fr};
use ark_ff::Field;
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
use crate::develop::instruction::{
    eval_pow_instruction, eval_pow_instruction_cirucuit, fq12_equal_first,
    fq12_equal_first_circuit, fq12_equal_last, fq12_equal_last_circuit, fq2_equal_last,
    generate_initial_pow_instruction, generate_next_pow_instruction, read_instruction,
};
use crate::develop::range_check::{
    eval_split_u16_range_check, eval_split_u16_range_check_circuit, generate_split_u16_range_check,
};
use crate::develop::utils::{
    bits_to_biguint, columns_to_fq12, fq12_to_columns, i64_to_column_positive,
};
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

use super::constants::BITS_LEN;
use super::modular::{bn254_base_modulus_packfield, eval_modular_op};
use super::range_check::split_u16_range_check_pairs;

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

const START_RANGE_CHECK: usize = 24 * N_LIMBS;
const NUM_RANGE_CHECK: usize = 84 * N_LIMBS - 12;
const END_RANGE_CHECK: usize = START_RANGE_CHECK + NUM_RANGE_CHECK;

const IS_SQ_COL: usize = END_RANGE_CHECK + 12;
const IS_NOOP_COL: usize = IS_SQ_COL + 1;
const IS_MUL_COL: usize = IS_SQ_COL + 2;

const MAIN_COLS: usize = IS_MUL_COL + BITS_LEN;

const ROWS: usize = 1 << 9;

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

    pub fn generate_trace(
        &self,
        x: Fq12,
        x_exp: Fq12,
        exp_bits: [bool; BITS_LEN],
    ) -> Vec<PolynomialValues<F>> {
        let modulus = bn254_base_modulus_bigint();
        let xi = 9;

        let exp_val = bits_to_biguint(&exp_bits);
        let exp_val: Fr = exp_val.into();
        let exp_bits = exp_bits.map(|b| F::from_bool(b));

        let x_input = x;
        let exp_val_biguint: BigUint = exp_val.into();
        let x_exp_expected: Fq12 = x_input.pow(&exp_val_biguint.to_u64_digits());
        assert!(x_exp_expected == x_exp);

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

        generate_initial_pow_instruction(
            &mut lv,
            IS_SQ_COL,
            IS_MUL_COL,
            IS_NOOP_COL,
            exp_bits.try_into().unwrap(),
        );

        let mut rows = vec![];

        for _ in 0..ROWS {
            // read x, y, and instruction
            let mut cur_col = 0;
            let x = read_fq12(&lv, &mut cur_col);
            let y = read_fq12(&lv, &mut cur_col);
            let is_sq = lv[IS_SQ_COL];
            let is_mul = lv[IS_MUL_COL];
            let is_noop = lv[IS_NOOP_COL];

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
            generate_next_pow_instruction(&lv, &mut nv, IS_SQ_COL, IS_MUL_COL, IS_NOOP_COL);
            rows.push(lv);
            lv = nv;
        }
        assert!(rows.len() == ROWS);

        let mut cur_col = 12 * N_LIMBS;
        let y = read_fq12(&lv, &mut cur_col);
        let result = columns_to_fq12(&y);
        assert!(result == x_exp_expected);

        let mut trace_cols = transpose(&rows.iter().map(|v| v.to_vec()).collect_vec());

        generate_split_u16_range_check(START_RANGE_CHECK..END_RANGE_CHECK, &mut trace_cols);

        let trace = trace_cols
            .into_iter()
            .map(|column| PolynomialValues::new(column))
            .collect();

        trace
    }

    pub fn generate_public_inputs(
        x: Fq12,
        x_exp: Fq12,
        exp_bits: [bool; BITS_LEN],
    ) -> [F; 24 * N_LIMBS + BITS_LEN] {
        let mut pi = [F::ZERO; 24 * N_LIMBS + BITS_LEN];
        let x = fq12_to_columns(x)
            .iter()
            .map(|x| i64_to_column_positive(*x))
            .collect_vec();
        let x_exp = fq12_to_columns(x_exp)
            .iter()
            .map(|x| i64_to_column_positive(*x))
            .collect_vec();
        let exp_bits = exp_bits.map(|b| F::from_bool(b));
        let mut cur_col = 0;
        write_fq12(&mut pi, &x, &mut cur_col);
        write_fq12(&mut pi, &x_exp, &mut cur_col);
        for i in 0..BITS_LEN {
            pi[cur_col] = exp_bits[i];
            cur_col += 1;
        }
        assert!(cur_col == 24 * N_LIMBS + BITS_LEN);
        pi
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D> for Fq12ExpStark<F, D> {
    const COLUMNS: usize = MAIN_COLS + 1 + 6 * NUM_RANGE_CHECK;
    const PUBLIC_INPUTS: usize = 24 * N_LIMBS + BITS_LEN;

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

        eval_split_u16_range_check(
            vars,
            yield_constr,
            MAIN_COLS,
            START_RANGE_CHECK..END_RANGE_CHECK,
        );

        let lv = vars.local_values;
        // read x, y, z, and instruction
        let mut cur_col = 0;
        let x = read_fq12(&lv, &mut cur_col);
        let y = read_fq12(&lv, &mut cur_col);
        let z = read_fq12(&lv, &mut cur_col);
        let auxs = (0..12)
            .map(|_| read_modulus_aux(lv, &mut cur_col))
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
        cur_col = IS_MUL_COL;
        let bits: [_; BITS_LEN] = read_instruction(lv, &mut cur_col);

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

        // public inputs
        let pi = vars.public_inputs;
        let pi: [P; Self::PUBLIC_INPUTS] = pi.map(|x| x.into());
        cur_col = 0;
        let pi_x = read_fq12(&pi, &mut cur_col);
        let pi_x_exp = read_fq12(&pi, &mut cur_col);
        let pi_bits: [_; BITS_LEN] = read_instruction(&pi, &mut cur_col);
        fq12_equal_first(yield_constr, &pi_x, &x);
        fq12_equal_last(yield_constr, &pi_x_exp, &y);
        for i in 0..BITS_LEN {
            yield_constr.constraint_first_row(pi_bits[i] - bits[i]);
        }

        // transition rule
        let nv = vars.next_values;
        cur_col = 0;
        let next_x = read_fq12(&nv, &mut cur_col);
        let next_y = read_fq12(&nv, &mut cur_col);

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
        eval_pow_instruction(yield_constr, lv, nv, IS_SQ_COL, IS_MUL_COL, IS_NOOP_COL);
    }

    fn eval_ext_circuit(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        vars: StarkEvaluationTargets<D, { Self::COLUMNS }, { Self::PUBLIC_INPUTS }>,
        yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    ) {
        let xi = F::Extension::from_canonical_u32(9);
        let modulus = bn254_base_modulus_packfield().map(|x| builder.constant_extension(x));

        eval_split_u16_range_check_circuit(
            builder,
            vars,
            yield_constr,
            MAIN_COLS,
            START_RANGE_CHECK..END_RANGE_CHECK,
        );

        let lv = vars.local_values;
        // read x, y, z, and instruction
        let mut cur_col = 0;
        let x = read_fq12(&lv, &mut cur_col);
        let y = read_fq12(&lv, &mut cur_col);
        let z = read_fq12(&lv, &mut cur_col);
        let auxs = (0..12)
            .map(|_| read_modulus_aux(lv, &mut cur_col))
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
        cur_col = IS_MUL_COL;
        let bits: [_; BITS_LEN] = read_instruction(lv, &mut cur_col);

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

        // public inputs
        let pi = vars.public_inputs;
        cur_col = 0;
        let pi_x = read_fq12(&pi, &mut cur_col);
        let pi_x_exp = read_fq12(&pi, &mut cur_col);
        let pi_bits: [_; BITS_LEN] = read_instruction(&pi, &mut cur_col);
        fq12_equal_first_circuit(builder, yield_constr, &pi_x, &x);
        fq12_equal_last_circuit(builder, yield_constr, &pi_x_exp, &y);
        for i in 0..BITS_LEN {
            let diff = builder.sub_extension(pi_bits[i], bits[i]);
            yield_constr.constraint_first_row(builder, diff);
        }

        // transition rule
        let nv = vars.next_values;
        cur_col = 0;
        let next_x = read_fq12(&nv, &mut cur_col);
        let next_y = read_fq12(&nv, &mut cur_col);

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
        eval_pow_instruction_cirucuit(
            builder,
            yield_constr,
            lv,
            nv,
            IS_SQ_COL,
            IS_MUL_COL,
            IS_NOOP_COL,
        );
    }

    fn constraint_degree(&self) -> usize {
        3
    }

    fn permutation_pairs(&self) -> Vec<PermutationPair> {
        split_u16_range_check_pairs(MAIN_COLS, START_RANGE_CHECK..END_RANGE_CHECK)
    }
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use ark_bn254::{Fq12, Fr};
    use ark_ff::Field;
    use ark_std::UniformRand;
    use num_bigint::BigUint;
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
        develop::{constants::BITS_LEN, fq12_exp::Fq12ExpStark, utils::biguint_to_bits},
        prover::prove,
        recursive_verifier::{
            add_virtual_stark_proof_with_pis, set_stark_proof_with_pis_target,
            verify_stark_proof_circuit,
        },
        verifier::verify_stark_proof,
    };

    #[test]
    fn test_fq12_exp() {
        let mut rng = rand::thread_rng();
        let exp_val: Fr = Fr::rand(&mut rng);
        let exp_bits: [bool; BITS_LEN] = biguint_to_bits(&exp_val.into(), BITS_LEN)
            .try_into()
            .unwrap();
        let x = Fq12::rand(&mut rng);
        let exp_val_biguint: BigUint = exp_val.into();
        let x_exp = x.pow(&exp_val_biguint.to_u64_digits());

        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type S = Fq12ExpStark<F, D>;
        let inner_config = StarkConfig::standard_fast_config();
        let stark = S::new();
        let trace = stark.generate_trace(x, x_exp, exp_bits);

        println!("start stark proof generation");
        let now = Instant::now();
        let pi = S::generate_public_inputs(x, x_exp, exp_bits);
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

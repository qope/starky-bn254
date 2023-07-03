use core::fmt;

use plonky2::{
    field::{extension::Extendable, packed::PackedField},
    hash::hash_types::RichField,
    iop::ext_target::ExtensionTarget,
    plonk::circuit_builder::CircuitBuilder,
};

use crate::constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer};

pub fn next_instruction<T>(cur_instruction: &[T], boundary: T) -> Vec<T>
where
    T: Copy,
{
    [&cur_instruction[1..], &[boundary]].concat()
}

pub fn eval_instruction<P: PackedField>(
    yield_constr: &mut ConstraintConsumer<P>,
    initial: &[P::Scalar],
    partial_lv: &[P],
    partial_nv: &[P],
    boundary: P::Scalar,
) {
    assert!(initial.len() == partial_lv.len() && partial_lv.len() == partial_nv.len());

    // inital condition
    initial
        .iter()
        .zip(partial_lv.iter())
        .for_each(|(&i, &l)| yield_constr.constraint_first_row(i - l));

    // transition condition
    for i in 1..initial.len() {
        yield_constr.constraint_transition(partial_nv[i - 1] - partial_lv[i]);
    }
    yield_constr.constraint_transition(*partial_nv.last().unwrap() - boundary);
}

pub fn eval_instruction_ext_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    initial: &[ExtensionTarget<D>],
    partial_lv: &[ExtensionTarget<D>],
    partial_nv: &[ExtensionTarget<D>],
    boundary: F::Extension,
) {
    assert!(initial.len() == partial_lv.len() && partial_lv.len() == partial_nv.len());

    let boundary = builder.constant_extension(boundary);

    // inital condition
    initial.iter().zip(partial_lv.iter()).for_each(|(&i, &l)| {
        let diff = builder.sub_extension(i, l);
        yield_constr.constraint_first_row(builder, diff);
    });

    // transition condition
    for i in 1..initial.len() {
        let diff = builder.sub_extension(partial_nv[i - 1], partial_lv[i]);
        yield_constr.constraint_transition(builder, diff);
    }

    let diff = builder.sub_extension(*partial_nv.last().unwrap(), boundary);
    yield_constr.constraint_transition(builder, diff);
}

pub fn write_instruction<F: Copy, const NUM_COL: usize, const INSTRUCTION_LEN: usize>(
    lv: &mut [F; NUM_COL],
    instruction: &[F; INSTRUCTION_LEN],
    cur_col: &mut usize,
) {
    lv[*cur_col..*cur_col + INSTRUCTION_LEN].copy_from_slice(instruction);
    *cur_col += INSTRUCTION_LEN;
}

pub fn read_instruction<F: Clone + fmt::Debug, const INSTRUCTION_LEN: usize>(
    lv: &[F],
    cur_col: &mut usize,
) -> [F; INSTRUCTION_LEN] {
    let output = lv[*cur_col..*cur_col + INSTRUCTION_LEN].to_vec();
    *cur_col += INSTRUCTION_LEN;
    output.try_into().unwrap()
}

#[cfg(test)]
mod tests {
    use core::marker::PhantomData;

    use ark_bn254::{Fq, Fr};
    use ark_ff::Field;
    use ark_std::UniformRand;
    use itertools::Itertools;
    use num::FromPrimitive;
    use num_bigint::{BigInt, BigUint};
    use plonky2::field::types::Field as plonky2_field;
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

    use crate::develop::fq_exp::eval_instruction_ext_circuit;
    use crate::{
        config::StarkConfig,
        constants::{LIMB_BITS, N_LIMBS},
        constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer},
        develop::{
            fq_exp::{eval_instruction, next_instruction, read_instruction, write_instruction},
            modular::{read_quot, write_modulus_aux, write_quot, write_u256},
        },
        lookup::{eval_lookups, eval_lookups_circuit, generate_range_checks},
        permutation::PermutationPair,
        prover::prove,
        recursive_verifier::{
            add_virtual_stark_proof_with_pis, set_stark_proof_with_pis_target,
            verify_stark_proof_circuit,
        },
        stark::Stark,
        util::{
            bigint_to_columns, biguint_to_bits, columns_to_bigint, fq_to_columns, pol_mul_wide,
            pol_mul_wide_ext_circuit, pol_sub_assign, pol_sub_assign_ext_circuit,
        },
        vars::{StarkEvaluationTargets, StarkEvaluationVars},
        verifier::verify_stark_proof,
    };

    use crate::develop::modular::{
        generate_modular_op, modular_constr_poly, modular_constr_poly_ext_circuit,
        read_modulus_aux, read_u256,
    };

    const BITS_LEN: usize = 256;
    const INSTRUCTION_LEN: usize = 2 * BITS_LEN;
    const MAIN_COLS: usize = 10 * N_LIMBS - 2 + 3 * INSTRUCTION_LEN;
    const RANGE32_COLS: usize = 7 * N_LIMBS - 2;

    #[derive(Clone, Copy)]
    pub struct FqExpStark<F: RichField + Extendable<D>, const D: usize> {
        _phantom: PhantomData<F>,
    }

    impl<F: RichField + Extendable<D>, const D: usize> FqExpStark<F, D> {
        pub fn new() -> Self {
            Self {
                _phantom: PhantomData,
            }
        }

        pub fn generate_trace(&self) -> (Vec<F>, Vec<PolynomialValues<F>>) {
            let mut pi = [F::ZERO; 3 * INSTRUCTION_LEN];
            let mut rng = rand::thread_rng();

            let neg_one: BigUint = Fq::from(-1).into();
            let modulus_biguint: BigUint = neg_one + BigUint::from_usize(1).unwrap();
            let modulus_bigint: BigInt = modulus_biguint.into();
            let modulus: [F; N_LIMBS] =
                bigint_to_columns(&modulus_bigint).map(|x| F::from_canonical_i64(x));

            let exp_val: Fr = Fr::rand(&mut rng);
            let exp_bits: [bool; BITS_LEN] = biguint_to_bits(&exp_val.into(), BITS_LEN)
                .try_into()
                .unwrap();
            let square_instruction = (0..BITS_LEN).flat_map(|_| [F::ZERO, F::ONE]).collect_vec();
            let mul_instruction = (0..BITS_LEN)
                .flat_map(|i| [F::from_bool(exp_bits[i]), F::ZERO])
                .collect_vec();
            let no_instruction = square_instruction
                .iter()
                .zip(mul_instruction.iter())
                .map(|(&is_sq, &is_mul)| (F::ONE - is_sq) * (F::ONE - is_mul))
                .collect_vec();
            let mut cur_col = 0;
            write_instruction::<_, { 3 * INSTRUCTION_LEN }, INSTRUCTION_LEN>(
                &mut pi,
                &square_instruction.clone().try_into().unwrap(),
                &mut cur_col,
            );
            write_instruction::<_, { 3 * INSTRUCTION_LEN }, INSTRUCTION_LEN>(
                &mut pi,
                &mul_instruction.clone().try_into().unwrap(),
                &mut cur_col,
            );
            write_instruction::<_, { 3 * INSTRUCTION_LEN }, INSTRUCTION_LEN>(
                &mut pi,
                &no_instruction.clone().try_into().unwrap(),
                &mut cur_col,
            );

            let x_input = Fq::rand(&mut rng);

            let exp_val_biguint: BigUint = exp_val.into();
            let x_exp_expected = x_input.pow(&exp_val_biguint.to_u64_digits());

            let mut x: [_; N_LIMBS] = fq_to_columns(x_input);
            let mut y: [_; N_LIMBS] = fq_to_columns(Fq::ONE);

            let mut rows: Vec<[F; MAIN_COLS]> = vec![];
            let mut lv = [F::ZERO; MAIN_COLS];

            let mut cur_col = 0;
            write_u256(&mut lv, &x.map(|x| F::from_canonical_i64(x)), &mut cur_col);
            write_u256(&mut lv, &y.map(|x| F::from_canonical_i64(x)), &mut cur_col);

            cur_col = 10 * N_LIMBS - 2;
            write_instruction::<_, MAIN_COLS, INSTRUCTION_LEN>(
                &mut lv,
                &square_instruction.clone().try_into().unwrap(),
                &mut cur_col,
            );
            write_instruction::<_, MAIN_COLS, INSTRUCTION_LEN>(
                &mut lv,
                &mul_instruction.clone().try_into().unwrap(),
                &mut cur_col,
            );
            write_instruction::<_, MAIN_COLS, INSTRUCTION_LEN>(
                &mut lv,
                &no_instruction.clone().try_into().unwrap(),
                &mut cur_col,
            );

            let range_max = 1 << LIMB_BITS;
            for _ in 0..range_max {
                let mut cur_col = 0;
                x = read_u256::<_, N_LIMBS>(&lv, &mut cur_col).map(|a| a.to_canonical_u64() as i64);
                y = read_u256::<_, N_LIMBS>(&lv, &mut cur_col).map(|a| a.to_canonical_u64() as i64);
                assert!(cur_col == 2 * N_LIMBS);

                // spare room for aux(5*N_LIMBS - 2) and quot(2*N_LIMBS)
                // because instructions does not have to be range checked
                cur_col = 10 * N_LIMBS - 2;
                let square_instruction = read_instruction::<_, INSTRUCTION_LEN>(&lv, &mut cur_col);
                let mul_instruction = read_instruction::<_, INSTRUCTION_LEN>(&lv, &mut cur_col);
                let no_instruction = read_instruction::<_, INSTRUCTION_LEN>(&lv, &mut cur_col);
                let is_sq = square_instruction[0] == F::ONE;
                let is_mul = mul_instruction[0] == F::ONE;
                let is_noop = no_instruction[0] == F::ONE;

                assert!(cur_col == 10 * N_LIMBS - 2 + 3 * INSTRUCTION_LEN);

                let x_sq = pol_mul_wide(x, x);
                let x_mul_y = pol_mul_wide(x, y);
                let zero = [0i64; 2 * N_LIMBS - 1];

                // dbg!(is_sq, is_mul, is_noop);
                let input = if is_sq {
                    x_sq
                } else if is_mul {
                    x_mul_y
                } else {
                    assert!(is_noop);
                    zero
                };
                let (output, quot, aux) = generate_modular_op(modulus_bigint.clone(), input);

                cur_col = 2 * N_LIMBS;
                write_modulus_aux::<_, MAIN_COLS, N_LIMBS>(&mut lv, &aux, &mut cur_col);
                write_quot(&mut lv, &quot, &mut cur_col);
                write_u256(&mut lv, &modulus, &mut cur_col);
                assert!(cur_col == 10 * N_LIMBS - 2);

                let mut nv = [F::ZERO; MAIN_COLS];
                let mut cur_col = 0;

                if is_sq {
                    write_u256(&mut nv, &output, &mut cur_col);
                    write_u256(&mut nv, &y.map(|a| F::from_canonical_i64(a)), &mut cur_col);
                } else if is_mul {
                    write_u256(&mut nv, &x.map(|a| F::from_canonical_i64(a)), &mut cur_col);
                    write_u256(&mut nv, &output, &mut cur_col);
                } else {
                    assert!(is_noop);
                    write_u256(&mut nv, &x.map(|a| F::from_canonical_i64(a)), &mut cur_col);
                    write_u256(&mut nv, &y.map(|a| F::from_canonical_i64(a)), &mut cur_col);
                }
                assert!(cur_col == 2 * N_LIMBS);

                cur_col = 10 * N_LIMBS - 2;
                let next_square_instruction = next_instruction(&square_instruction, F::ZERO);
                let next_mul_instruction = next_instruction(&mul_instruction, F::ZERO);
                let next_no_instruction = next_instruction(&no_instruction, F::ONE);
                write_instruction::<_, MAIN_COLS, INSTRUCTION_LEN>(
                    &mut nv,
                    &next_square_instruction.clone().try_into().unwrap(),
                    &mut cur_col,
                );
                write_instruction::<_, MAIN_COLS, INSTRUCTION_LEN>(
                    &mut nv,
                    &next_mul_instruction.clone().try_into().unwrap(),
                    &mut cur_col,
                );
                write_instruction::<_, MAIN_COLS, INSTRUCTION_LEN>(
                    &mut nv,
                    &next_no_instruction.clone().try_into().unwrap(),
                    &mut cur_col,
                );
                assert!(cur_col == MAIN_COLS);

                rows.push(lv);
                lv = nv;
            }

            let final_y = columns_to_bigint(&y);
            let final_fq: Fq = final_y.to_biguint().unwrap().into();
            assert!(final_fq == x_exp_expected);

            let mut trace_cols = transpose(&rows.iter().map(|v| v.to_vec()).collect_vec());
            let (table, pairs) =
                generate_range_checks(range_max, &trace_cols[0..RANGE32_COLS].to_vec());

            trace_cols.push(table);
            pairs.iter().for_each(|(c_perm, t_perm)| {
                trace_cols.push(c_perm.to_vec());
                trace_cols.push(t_perm.to_vec());
            });

            let trace = trace_cols
                .into_iter()
                .map(|column| PolynomialValues::new(column))
                .collect();

            (pi.try_into().unwrap(), trace)
        }
    }

    impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D> for FqExpStark<F, D> {
        const COLUMNS: usize = MAIN_COLS + 1 + 2 * RANGE32_COLS;
        const PUBLIC_INPUTS: usize = 3 * INSTRUCTION_LEN;

        fn eval_packed_generic<FE, P, const D2: usize>(
            &self,
            vars: StarkEvaluationVars<FE, P, { Self::COLUMNS }, { Self::PUBLIC_INPUTS }>,
            yield_constr: &mut ConstraintConsumer<P>,
        ) where
            FE: FieldExtension<D2, BaseField = F>,
            P: PackedField<Scalar = FE>,
        {
            let lv = vars.local_values.clone();
            let nv = vars.next_values.clone();
            let pi = vars.public_inputs.clone();

            for i in (MAIN_COLS + 1..MAIN_COLS + 1 + 2 * RANGE32_COLS).step_by(2) {
                eval_lookups(vars, yield_constr, i, i + 1);
            }

            let mut cur_col = 0;

            let cur_x: [_; N_LIMBS] = read_u256(&lv, &mut cur_col);
            let cur_y: [_; N_LIMBS] = read_u256(&lv, &mut cur_col);
            let aux = read_modulus_aux::<_, N_LIMBS>(&lv, &mut cur_col);
            let quot = read_quot::<_, { 2 * N_LIMBS }>(&lv, &mut cur_col);
            let modulus: [_; N_LIMBS] = read_u256(&lv, &mut cur_col);
            let cur_square_instruction = read_instruction::<_, INSTRUCTION_LEN>(&lv, &mut cur_col);
            let cur_mul_instruction = read_instruction::<_, INSTRUCTION_LEN>(&lv, &mut cur_col);
            let cur_no_instruction = read_instruction::<_, INSTRUCTION_LEN>(&lv, &mut cur_col);

            assert!(cur_col == MAIN_COLS);

            cur_col = 0;
            let next_x: [_; N_LIMBS] = read_u256(&nv, &mut cur_col);
            let next_y: [_; N_LIMBS] = read_u256(&nv, &mut cur_col);
            cur_col = 10 * N_LIMBS - 2;
            let next_square_instruction = read_instruction::<_, INSTRUCTION_LEN>(&nv, &mut cur_col);
            let next_mul_instruction = read_instruction::<_, INSTRUCTION_LEN>(&nv, &mut cur_col);
            let next_no_instruction = read_instruction::<_, INSTRUCTION_LEN>(&nv, &mut cur_col);
            assert!(cur_col == MAIN_COLS);

            // verify in the case of is_sq == one;
            let is_sq = cur_square_instruction[0];
            let x_sq = pol_mul_wide(cur_x, cur_x);
            let constr_poly = modular_constr_poly::<P>(
                yield_constr,
                is_sq,
                modulus,
                next_x,
                aux.out_aux_red,
                quot,
                aux.aux_input_lo,
                aux.aux_input_hi,
            );
            let mut constr_poly_copy = constr_poly;
            pol_sub_assign(&mut constr_poly_copy, &x_sq);
            for &c in constr_poly_copy.iter() {
                yield_constr.constraint_transition(is_sq * c);
            }

            // verify in the case of is_mul == one;
            let is_mul = cur_mul_instruction[0];
            let x_mul_y = pol_mul_wide(cur_x, cur_y);
            let constr_poly = modular_constr_poly::<P>(
                yield_constr,
                is_mul,
                modulus,
                next_y,
                aux.out_aux_red,
                quot,
                aux.aux_input_lo,
                aux.aux_input_hi,
            );
            let mut constr_poly_copy = constr_poly;
            pol_sub_assign(&mut constr_poly_copy, &x_mul_y);
            for &c in constr_poly_copy.iter() {
                yield_constr.constraint_transition(is_mul * c);
            }

            // verify in the case of is_noop
            let is_noop = cur_no_instruction[0];
            cur_x.iter().zip(next_x.iter()).for_each(|(&cx, &nx)| {
                yield_constr.constraint_transition(is_noop * (cx - nx));
            });
            cur_y.iter().zip(next_y.iter()).for_each(|(&cy, &ny)| {
                yield_constr.constraint_transition(is_noop * (cy - ny));
            });

            // verify the transition of instructions
            let mut cur_col = 0;
            let initial_square_instruction: [_; INSTRUCTION_LEN] =
                read_instruction(&pi, &mut cur_col);
            let initial_mul_instruction: [_; INSTRUCTION_LEN] = read_instruction(&pi, &mut cur_col);
            let initial_no_instruction: [_; INSTRUCTION_LEN] = read_instruction(&pi, &mut cur_col);

            eval_instruction(
                yield_constr,
                &initial_square_instruction,
                &cur_square_instruction,
                &next_square_instruction,
                P::Scalar::ZEROS,
            );
            eval_instruction(
                yield_constr,
                &initial_mul_instruction,
                &cur_mul_instruction,
                &next_mul_instruction,
                P::Scalar::ZEROS,
            );
            eval_instruction(
                yield_constr,
                &initial_no_instruction,
                &cur_no_instruction,
                &next_no_instruction,
                P::Scalar::ONE,
            );
        }

        fn eval_ext_circuit(
            &self,
            builder: &mut CircuitBuilder<F, D>,
            vars: StarkEvaluationTargets<D, { Self::COLUMNS }, { Self::PUBLIC_INPUTS }>,
            yield_constr: &mut RecursiveConstraintConsumer<F, D>,
        ) {
            let lv = vars.local_values.clone();
            let nv = vars.next_values.clone();
            let pi = vars.public_inputs.clone();

            for i in (MAIN_COLS + 1..MAIN_COLS + 1 + 2 * RANGE32_COLS).step_by(2) {
                eval_lookups_circuit(builder, vars, yield_constr, i, i + 1);
            }

            let mut cur_col = 0;

            let cur_x: [_; N_LIMBS] = read_u256(&lv, &mut cur_col);
            let cur_y: [_; N_LIMBS] = read_u256(&lv, &mut cur_col);
            let aux = read_modulus_aux::<_, N_LIMBS>(&lv, &mut cur_col);
            let quot = read_quot::<_, { 2 * N_LIMBS }>(&lv, &mut cur_col);
            let modulus: [_; N_LIMBS] = read_u256(&lv, &mut cur_col);
            let cur_square_instruction = read_instruction::<_, INSTRUCTION_LEN>(&lv, &mut cur_col);
            let cur_mul_instruction = read_instruction::<_, INSTRUCTION_LEN>(&lv, &mut cur_col);
            let cur_no_instruction = read_instruction::<_, INSTRUCTION_LEN>(&lv, &mut cur_col);

            assert!(cur_col == MAIN_COLS);

            cur_col = 0;
            let next_x: [_; N_LIMBS] = read_u256(&nv, &mut cur_col);
            let next_y: [_; N_LIMBS] = read_u256(&nv, &mut cur_col);
            cur_col = 10 * N_LIMBS - 2;
            let next_square_instruction = read_instruction::<_, INSTRUCTION_LEN>(&nv, &mut cur_col);
            let next_mul_instruction = read_instruction::<_, INSTRUCTION_LEN>(&nv, &mut cur_col);
            let next_no_instruction = read_instruction::<_, INSTRUCTION_LEN>(&nv, &mut cur_col);
            assert!(cur_col == MAIN_COLS);

            // verify in the case of is_sq == one;
            let is_sq = cur_square_instruction[0];
            let x_sq = pol_mul_wide_ext_circuit(builder, cur_x, cur_x);
            let constr_poly = modular_constr_poly_ext_circuit(
                builder,
                yield_constr,
                is_sq,
                modulus,
                next_x,
                aux.out_aux_red,
                quot,
                aux.aux_input_lo,
                aux.aux_input_hi,
            );
            let mut constr_poly_copy = constr_poly;
            pol_sub_assign_ext_circuit(builder, &mut constr_poly_copy, &x_sq);
            for &c in constr_poly_copy.iter() {
                let t = builder.mul_extension(is_sq, c);
                yield_constr.constraint_transition(builder, t);
            }

            // verify in the case of is_mul == one;
            let is_mul = cur_mul_instruction[0];
            let x_mul_y = pol_mul_wide_ext_circuit(builder, cur_x, cur_y);
            let constr_poly = modular_constr_poly_ext_circuit(
                builder,
                yield_constr,
                is_mul,
                modulus,
                next_y,
                aux.out_aux_red,
                quot,
                aux.aux_input_lo,
                aux.aux_input_hi,
            );
            let mut constr_poly_copy = constr_poly;
            pol_sub_assign_ext_circuit(builder, &mut constr_poly_copy, &x_mul_y);
            for &c in constr_poly_copy.iter() {
                let t = builder.mul_extension(is_mul, c);
                yield_constr.constraint_transition(builder, t);
            }

            // verify in the case of is_noop
            let is_noop = cur_no_instruction[0];
            cur_x.iter().zip(next_x.iter()).for_each(|(&cx, &nx)| {
                let diff = builder.sub_extension(cx, nx);
                let t = builder.mul_extension(is_noop, diff);
                yield_constr.constraint_transition(builder, t);
            });
            cur_y.iter().zip(next_y.iter()).for_each(|(&cy, &ny)| {
                let diff = builder.sub_extension(cy, ny);
                let t = builder.mul_extension(is_noop, diff);
                yield_constr.constraint_transition(builder, t);
            });

            // verify the transition of instructions
            let mut cur_col = 0;
            let initial_square_instruction: [_; INSTRUCTION_LEN] =
                read_instruction(&pi, &mut cur_col);
            let initial_mul_instruction: [_; INSTRUCTION_LEN] = read_instruction(&pi, &mut cur_col);
            let initial_no_instruction: [_; INSTRUCTION_LEN] = read_instruction(&pi, &mut cur_col);

            eval_instruction_ext_circuit(
                builder,
                yield_constr,
                &initial_square_instruction,
                &cur_square_instruction,
                &next_square_instruction,
                F::Extension::ZERO,
            );
            eval_instruction_ext_circuit(
                builder,
                yield_constr,
                &initial_mul_instruction,
                &cur_mul_instruction,
                &next_mul_instruction,
                F::Extension::ZERO,
            );
            eval_instruction_ext_circuit(
                builder,
                yield_constr,
                &initial_no_instruction,
                &cur_no_instruction,
                &next_no_instruction,
                F::Extension::ONE,
            );
        }

        fn constraint_degree(&self) -> usize {
            3
        }

        fn permutation_pairs(&self) -> Vec<PermutationPair> {
            let mut pairs = (0..RANGE32_COLS)
                .map(|i| PermutationPair::singletons(i, MAIN_COLS + 1 + 2 * i))
                .collect_vec();
            let pairs_table = (0..RANGE32_COLS)
                .map(|i| PermutationPair::singletons(MAIN_COLS, MAIN_COLS + 2 + 2 * i))
                .collect_vec();

            pairs.extend(pairs_table);

            pairs
        }
    }

    #[test]
    fn test_fq_exp() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type S = FqExpStark<F, D>;

        let inner_config = StarkConfig::standard_fast_config();

        let stark = S::new();
        let (pi, trace) = stark.generate_trace();
        let inner_proof = prove::<F, C, S, D>(
            stark,
            &inner_config,
            trace,
            pi.try_into().unwrap(),
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

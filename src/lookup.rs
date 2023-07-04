use std::cmp::Ordering;

use itertools::Itertools;
use plonky2::field::extension::Extendable;
use plonky2::field::packed::PackedField;
use plonky2::field::types::{Field, PrimeField64};
use plonky2::hash::hash_types::RichField;
use plonky2::plonk::circuit_builder::CircuitBuilder;

use crate::constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer};
use crate::vars::{StarkEvaluationTargets, StarkEvaluationVars};

pub fn eval_lookups<
    F: Field,
    P: PackedField<Scalar = F>,
    const COLS: usize,
    const PUBLIC_INPUTS: usize,
>(
    vars: StarkEvaluationVars<F, P, COLS, PUBLIC_INPUTS>,
    yield_constr: &mut ConstraintConsumer<P>,
    col_permuted_input: usize,
    col_permuted_table: usize,
) {
    let local_perm_input = vars.local_values[col_permuted_input];
    let next_perm_table = vars.next_values[col_permuted_table];
    let next_perm_input = vars.next_values[col_permuted_input];

    // A "vertical" diff between the local and next permuted inputs.
    let diff_input_prev = next_perm_input - local_perm_input;
    // A "horizontal" diff between the next permuted input and permuted table value.
    let diff_input_table = next_perm_input - next_perm_table;

    yield_constr.constraint(diff_input_prev * diff_input_table);

    // This is actually constraining the first row, as per the spec, since `diff_input_table`
    // is a diff of the next row's values. In the context of `constraint_last_row`, the next
    // row is the first row.
    yield_constr.constraint_last_row(diff_input_table);
}

pub fn eval_lookups_circuit<
    F: RichField + Extendable<D>,
    const D: usize,
    const COLS: usize,
    const PUBLIC_INPUTS: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    vars: StarkEvaluationTargets<D, COLS, PUBLIC_INPUTS>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    col_permuted_input: usize,
    col_permuted_table: usize,
) {
    let local_perm_input = vars.local_values[col_permuted_input];
    let next_perm_table = vars.next_values[col_permuted_table];
    let next_perm_input = vars.next_values[col_permuted_input];

    // A "vertical" diff between the local and next permuted inputs.
    let diff_input_prev = builder.sub_extension(next_perm_input, local_perm_input);
    // A "horizontal" diff between the next permuted input and permuted table value.
    let diff_input_table = builder.sub_extension(next_perm_input, next_perm_table);

    let diff_product = builder.mul_extension(diff_input_prev, diff_input_table);
    yield_constr.constraint(builder, diff_product);

    yield_constr.constraint_last_row(builder, diff_input_table);
}

/// Given an input column and a table column, generate the permuted input and permuted table columns
/// used in the Halo2 permutation argument.
pub fn permuted_cols<F: PrimeField64>(inputs: &[F], table: &[F]) -> (Vec<F>, Vec<F>) {
    let n = inputs.len();

    let sorted_inputs = inputs
        .iter()
        .map(|x| x.to_canonical())
        .sorted_unstable_by_key(|x| x.to_noncanonical_u64())
        .collect_vec();
    let sorted_table = table
        .iter()
        .map(|x| x.to_canonical())
        .sorted_unstable_by_key(|x| x.to_noncanonical_u64())
        .collect_vec();

    let mut unused_table_inds = Vec::with_capacity(n);
    let mut unused_table_vals = Vec::with_capacity(n);
    let mut permuted_table = vec![F::ZERO; n];
    let mut i = 0;
    let mut j = 0;
    while (j < n) && (i < n) {
        let input_val = sorted_inputs[i].to_noncanonical_u64();
        let table_val = sorted_table[j].to_noncanonical_u64();
        match input_val.cmp(&table_val) {
            Ordering::Greater => {
                unused_table_vals.push(sorted_table[j]);
                j += 1;
            }
            Ordering::Less => {
                if let Some(x) = unused_table_vals.pop() {
                    permuted_table[i] = x;
                } else {
                    unused_table_inds.push(i);
                }
                i += 1;
            }
            Ordering::Equal => {
                permuted_table[i] = sorted_table[j];
                i += 1;
                j += 1;
            }
        }
    }

    unused_table_vals.extend_from_slice(&sorted_table[j..n]);
    unused_table_inds.extend(i..n);

    for (ind, val) in unused_table_inds.into_iter().zip_eq(unused_table_vals) {
        permuted_table[ind] = val;
    }

    (sorted_inputs, permuted_table)
}


#[cfg(test)]
mod tests {
    use std::marker::PhantomData;

    use itertools::Itertools;
    use plonky2::field::extension::{Extendable, FieldExtension};
    use plonky2::field::packed::PackedField;
    use plonky2::field::polynomial::PolynomialValues;
    use plonky2::hash::hash_types::RichField;
    use plonky2::plonk::circuit_builder::CircuitBuilder;
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
    use plonky2::util::timing::TimingTree;

    use super::{eval_lookups, eval_lookups_circuit, permuted_cols};
    use crate::config::StarkConfig;
    use crate::constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer};
    use crate::prover::prove;
    use crate::stark::Stark;
    use crate::vars::{StarkEvaluationTargets, StarkEvaluationVars};
    use crate::verifier::verify_stark_proof;

    #[derive(Clone, Copy)]
    struct MyStark<F: RichField + Extendable<D>, const D: usize> {
        _phantom: PhantomData<F>,
    }

    impl<F: RichField + Extendable<D>, const D: usize> MyStark<F, D> {
        const COL_PERMUTED_INPUT: usize = 2;
        const COL_PERMUTED_TABLE: usize = 3;

        fn new() -> Self {
            Self {
                _phantom: PhantomData,
            }
        }

        fn generate_trace(&self) -> Vec<PolynomialValues<F>> {
            let inputs = vec![6, 3, 1, 1, 0, 0, 0, 0]
                .iter()
                .map(|&x| F::from_canonical_u32(x))
                .collect_vec();
            let table = vec![0, 1, 2, 3, 4, 5, 6, 7]
                .iter()
                .map(|&x| F::from_canonical_u32(x))
                .collect_vec();
            let (permuted_input, permuted_table) = permuted_cols(&inputs, &table);

            let cols = vec![inputs, table, permuted_input, permuted_table];
            cols.into_iter()
                .map(|c| PolynomialValues::new(c))
                .collect_vec()
        }
    }

    impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D> for MyStark<F, D> {
        const COLUMNS: usize = 4;
        const PUBLIC_INPUTS: usize = 0;

        fn eval_packed_generic<FE, P, const D2: usize>(
            &self,
            vars: StarkEvaluationVars<FE, P, { Self::COLUMNS }, { Self::PUBLIC_INPUTS }>,
            yield_constr: &mut ConstraintConsumer<P>,
        ) where
            FE: FieldExtension<D2, BaseField = F>,
            P: PackedField<Scalar = FE>,
        {
            eval_lookups(
                vars,
                yield_constr,
                Self::COL_PERMUTED_INPUT,
                Self::COL_PERMUTED_TABLE,
            );
        }

        fn eval_ext_circuit(
            &self,
            builder: &mut CircuitBuilder<F, D>,
            vars: StarkEvaluationTargets<D, { Self::COLUMNS }, { Self::PUBLIC_INPUTS }>,
            yield_constr: &mut RecursiveConstraintConsumer<F, D>,
        ) {
            eval_lookups_circuit(
                builder,
                vars,
                yield_constr,
                Self::COL_PERMUTED_INPUT,
                Self::COL_PERMUTED_TABLE,
            );
        }

        fn constraint_degree(&self) -> usize {
            3
        }
    }

    #[test]
    fn test_mystark() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type S = MyStark<F, D>;

        let config = StarkConfig::standard_fast_config();
        let stark = S::new();
        let trace = stark.generate_trace();
        let proof =
            prove::<F, C, S, D>(stark, &config, trace, [], &mut TimingTree::default()).unwrap();

        verify_stark_proof(stark, proof.clone(), &config).unwrap();
    }
}

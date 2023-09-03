use plonky2::field::extension::Extendable;
use plonky2::field::packed::PackedField;
use plonky2::field::types::PrimeField64;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::ext_target::ExtensionTarget;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use starky::constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer};

use crate::constants::N_LIMBS;
use crate::modular::modular::{
    bn254_base_modulus_bigint, bn254_base_modulus_packfield, eval_modular_op,
    eval_modular_op_circuit, generate_modular_op, read_modulus_aux, read_u256, write_modulus_aux,
    write_u256, ModulusAux,
};
use crate::modular::pol_utils::{pol_mul_wide, pol_mul_wide_ext_circuit};
use crate::utils::utils::positive_column_to_i64;

pub struct FqOutput<F> {
    pub output: [F; N_LIMBS],
    pub aux: ModulusAux<F>,
    pub quot_sign: F,
}

impl<F: RichField + Default> Default for FqOutput<F> {
    fn default() -> Self {
        Self {
            output: [F::ZERO; N_LIMBS],
            aux: ModulusAux::<F>::default(),
            quot_sign: F::ONE,
        }
    }
}

pub fn generate_fq_mul<F: PrimeField64>(x: [F; N_LIMBS], y: [F; N_LIMBS]) -> FqOutput<F> {
    let modulus = bn254_base_modulus_bigint();
    let x_i64 = positive_column_to_i64(x);
    let y_i64 = positive_column_to_i64(y);
    let pol_input = pol_mul_wide(x_i64, y_i64);
    let (output, quot_sign, aux) = generate_modular_op::<F>(&modulus, pol_input);
    FqOutput {
        output,
        aux,
        quot_sign,
    }
}

/// 7*N_LIMBS
/// range_check: 7*N_LIMBS - 1
pub fn write_fq_output<F: Copy>(lv: &mut [F], output: &FqOutput<F>, cur_col: &mut usize) {
    write_u256(lv, &output.output, cur_col);
    write_modulus_aux(lv, &output.aux, cur_col);
    lv[*cur_col] = output.quot_sign;
    *cur_col += 1;
}

/// 7*N_LIMBS
pub fn read_fq_output<F: Copy + core::fmt::Debug>(lv: &[F], cur_col: &mut usize) -> FqOutput<F> {
    let output = read_u256(lv, cur_col);
    let aux = read_modulus_aux(lv, cur_col);
    let quot_sign = lv[*cur_col];
    *cur_col += 1;
    FqOutput {
        output,
        aux,
        quot_sign,
    }
}

pub fn eval_fq_mul<P: PackedField>(
    yield_constr: &mut ConstraintConsumer<P>,
    filter: P,
    x: [P; N_LIMBS],
    y: [P; N_LIMBS],
    output: &FqOutput<P>,
) {
    let input = pol_mul_wide(x, y);
    let modulus = bn254_base_modulus_packfield();
    eval_modular_op(
        yield_constr,
        filter,
        modulus,
        input,
        output.output,
        output.quot_sign,
        &output.aux,
    );
}

pub fn eval_fq_mul_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    filter: ExtensionTarget<D>,
    x: [ExtensionTarget<D>; N_LIMBS],
    y: [ExtensionTarget<D>; N_LIMBS],
    output: &FqOutput<ExtensionTarget<D>>,
) {
    let input = pol_mul_wide_ext_circuit(builder, x, y);
    let modulus: [F::Extension; N_LIMBS] = bn254_base_modulus_packfield();
    let modulus = modulus.map(|x| builder.constant_extension(x));
    eval_modular_op_circuit(
        builder,
        yield_constr,
        filter,
        modulus,
        input,
        output.output,
        output.quot_sign,
        &output.aux,
    );
}

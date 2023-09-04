#![allow(non_snake_case)]
use ark_bn254::{Fq, Fq2};
use ark_ff::{Field, MontFp};
use num_bigint::BigUint;
use num_traits::One;
use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::target::BoolTarget,
    plonk::{
        circuit_builder::CircuitBuilder,
        config::{AlgebraicHasher, GenericConfig},
    },
};
use plonky2_bn254::{
    curves::g2curve_target::G2Target,
    fields::{fq2_target::Fq2Target, fq_target::FqTarget, u256_target::U256Target},
};

use crate::fields::fq::circuit::{fq_exp_circuit, FqExpInputTarget};

use super::circuit::g2_mul_by_cofactor_circuit;

pub(crate) fn batch_is_square_circuit<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    inputs: &[FqTarget<F, D>],
) -> Vec<BoolTarget>
where
    C::Hasher: AlgebraicHasher<F>,
{
    let one = FqTarget::constant(builder, Fq::one());
    let offset = one.clone();
    let exp_val_b = BigUint::from(Fq::from(-1) / Fq::from(2));
    let exp_val = U256Target::constant(builder, &exp_val_b);
    let exp_inputs = inputs
        .iter()
        .map(|x| FqExpInputTarget {
            x: x.clone(),
            offset: offset.clone(),
            exp_val: exp_val.clone(),
        })
        .collect::<Vec<_>>();
    let exp_outputs = fq_exp_circuit::<F, C, D>(builder, &exp_inputs);
    exp_outputs
        .into_iter()
        .map(|output| output.is_equal(builder, &one))
        .collect::<Vec<_>>()
}

fn or_circuit<F, const D: usize>(
    a: BoolTarget,
    b: BoolTarget,
    builder: &mut CircuitBuilder<F, D>,
) -> BoolTarget
where
    F: RichField + Extendable<D>,
{
    // a = 0, b = 0 => 0
    // a = 1, b = 0 => 1
    // a = 0, b = 1 => 1
    // a = 1, b = 1 => 1
    // or(a, b) = 1 - (1-a)*(1-b) = a+b-ab
    let a_plus_b = builder.add(a.target, b.target);
    let c = builder.arithmetic(F::NEG_ONE, F::ONE, a.target, b.target, a_plus_b);
    BoolTarget::new_unsafe(c)
}

struct IsSquareStatement<F: RichField + Extendable<D>, const D: usize> {
    x: FqTarget<F, D>,
    is_sq: BoolTarget,
}

fn map_to_g2_without_cofactor_mul_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    u: &Fq2Target<F, D>,
) -> (G2Target<F, D>, Vec<IsSquareStatement<F, D>>) {
    // constants
    let Z = Fq2::one();
    let B = Fq2::new(
        MontFp!("19485874751759354771024239261021720505790618469301721065564631296452457478373"),
        MontFp!("266929791119991161246907387137283842545076965332900288569378510910307636690"),
    );
    let g = |x: Fq2| -> Fq2 { x * x * x + B };
    let g_target = |x: &Fq2Target<F, D>, builder: &mut CircuitBuilder<F, D>| -> Fq2Target<F, D> {
        let x_cub = x.mul(builder, &x).mul(builder, &x);
        let b = Fq2Target::constant(builder, B);
        let x_cub_plus_b = x_cub.add(builder, &b);
        x_cub_plus_b
    };
    let norm = |input: &Fq2Target<F, D>, builder: &mut CircuitBuilder<F, D>| -> FqTarget<F, D> {
        let x = input.coeffs[0].clone();
        let y = input.coeffs[1].clone();
        let x_sq = x.mul(builder, &x);
        let y_sq = y.mul(builder, &y);
        x_sq.add(builder, &y_sq)
    };
    let gz = g(Z);
    let neg_two_by_z = -Z / (Fq2::from(2));
    let tv4 = (-gz * Fq2::from(3) * Z * Z).sqrt().unwrap();
    let tv6 = -Fq2::from(4) * gz / (Fq2::from(3) * Z * Z);
    // end of constants
    let Z = Fq2Target::constant(builder, Z);
    let gz = Fq2Target::constant(builder, gz);
    let tv4 = Fq2Target::constant(builder, tv4);
    let tv6 = Fq2Target::constant(builder, tv6);
    let neg_two_by_z = Fq2Target::constant(builder, neg_two_by_z);
    let one = Fq2Target::constant(builder, Fq2::one());

    let tv1 = u.mul(builder, &u).mul(builder, &gz);
    let tv2 = one.add(builder, &tv1);
    let tv1 = one.sub(builder, &tv1);
    let tv3 = tv1.mul(builder, &tv2).inv0(builder);
    let tv5 = u.mul(builder, &tv1).mul(builder, &tv3).mul(builder, &tv4);
    let x1 = neg_two_by_z.sub(builder, &tv5);
    let x2 = neg_two_by_z.add(builder, &tv5);
    let tv2tv2tv3 = tv2.mul(builder, &tv2).mul(builder, &tv3);
    let tv2tv2tv3_sq = tv2tv2tv3.mul(builder, &tv2tv2tv3);
    let tv6_tv2tv2tv3_sq = tv6.mul(builder, &tv2tv2tv3_sq);
    let x3 = Z.add(builder, &tv6_tv2tv2tv3_sq);
    let gx1 = g_target(&x1, builder);
    let gx2 = g_target(&x2, builder);

    let normed_gx1 = norm(&gx1, builder);
    let normed_gx2 = norm(&gx2, builder);
    let is_gx1_sq = builder.add_virtual_bool_target_unsafe();
    let is_gx2_sq = builder.add_virtual_bool_target_unsafe();
    let is_sq_statements = vec![
        IsSquareStatement {
            x: normed_gx1,
            is_sq: is_gx1_sq,
        },
        IsSquareStatement {
            x: normed_gx2,
            is_sq: is_gx2_sq,
        },
    ];

    let x1_or_x2 = Fq2Target::select(builder, &x1, &x2, &is_gx1_sq);
    let isgx1_or_isgx2 = or_circuit(is_gx1_sq, is_gx2_sq, builder);
    let x = Fq2Target::select(builder, &x1_or_x2, &x3, &isgx1_or_isgx2);

    let gx = g_target(&x, builder);
    let sgn_u = u.sgn0(builder);
    let y = gx.sqrt_with_sgn(builder, sgn_u);
    (G2Target::new(x, y), is_sq_statements)
}

pub fn batch_map_to_g2_circuit<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    inputs: &[Fq2Target<F, D>],
) -> Vec<G2Target<F, D>>
where
    <C as GenericConfig<D>>::Hasher: AlgebraicHasher<F>,
{
    let mut g2_before_cofactor_muls = vec![];
    let mut is_sq_statements = vec![];
    for u in inputs.iter() {
        let (g2, is_sq_statement) = map_to_g2_without_cofactor_mul_circuit(builder, u);
        g2_before_cofactor_muls.push(g2);
        is_sq_statements.extend(is_sq_statement);
    }
    let is_sq_inputs = is_sq_statements
        .iter()
        .map(|input| input.x.clone())
        .collect::<Vec<_>>();
    let is_sq_outputs = is_sq_statements
        .iter()
        .map(|input| input.is_sq)
        .collect::<Vec<_>>();

    let constr_is_sq = batch_is_square_circuit::<F, C, D>(builder, &is_sq_inputs);
    constr_is_sq
        .iter()
        .zip(is_sq_outputs.iter())
        .for_each(|(a, b)| builder.connect(a.target, b.target));

    let outputs = g2_mul_by_cofactor_circuit::<F, C, D>(builder, &g2_before_cofactor_muls);
    outputs
}

#[cfg(test)]
mod tests {
    use ark_bn254::{Fq, Fq2, G2Affine};
    use ark_ec::AffineRepr;
    use ark_ff::Field;
    use ark_std::UniformRand;
    use plonky2::{
        iop::witness::{PartialWitness, WitnessWrite},
        plonk::{
            circuit_builder::CircuitBuilder,
            circuit_data::CircuitConfig,
            config::{GenericConfig, PoseidonGoldilocksConfig},
        },
    };
    use plonky2_bn254::{
        curves::map_to_g2::map_to_g2_without_cofactor_mul,
        fields::{fq2_target::Fq2Target, fq_target::FqTarget},
    };

    use crate::curves::g2::batch_map_to_g2::{batch_is_square_circuit, batch_map_to_g2_circuit};

    #[test]
    fn test_batch_is_square_circuit() {
        let n = 1 << 7;
        let mut rng = rand::thread_rng();
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let circuit_config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(circuit_config);
        let inputs_t = (0..n)
            .map(|_| FqTarget::empty(&mut builder))
            .collect::<Vec<_>>();
        let outputs_t = batch_is_square_circuit::<F, C, D>(&mut builder, &inputs_t);

        let mut pw = PartialWitness::new();
        let inputs = (0..n).map(|_| Fq::rand(&mut rng)).collect::<Vec<_>>();
        let outputs = inputs
            .iter()
            .map(|x| x.legendre().is_qr())
            .collect::<Vec<_>>();
        inputs_t
            .iter()
            .zip(inputs.iter())
            .for_each(|(t, w)| t.set_witness(&mut pw, w));
        outputs_t
            .iter()
            .zip(outputs.iter())
            .for_each(|(t, w)| pw.set_bool_target(*t, *w));
        let data = builder.build::<C>();
        let _proof = data.prove(pw).unwrap();
    }

    #[test]
    fn test_batch_map_to_g2_circuit() {
        let n = 1 << 7;
        let mut rng = rand::thread_rng();
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let circuit_config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(circuit_config);
        let inputs_t = (0..n)
            .map(|_| Fq2Target::empty(&mut builder))
            .collect::<Vec<_>>();
        let outputs_t = batch_map_to_g2_circuit::<F, C, D>(&mut builder, &inputs_t);

        let mut pw = PartialWitness::new();
        let inputs = (0..n).map(|_| Fq2::rand(&mut rng)).collect::<Vec<_>>();
        let outputs = inputs
            .iter()
            .map(|x| G2Affine::from(map_to_g2_without_cofactor_mul(*x).mul_by_cofactor()))
            .collect::<Vec<_>>();

        inputs_t
            .iter()
            .zip(inputs.iter())
            .for_each(|(t, w)| t.set_witness(&mut pw, w));
        outputs_t
            .iter()
            .zip(outputs.iter())
            .for_each(|(t, w)| t.set_witness(&mut pw, w));
        let data = builder.build::<C>();
        let _proof = data.prove(pw).unwrap();
    }
}

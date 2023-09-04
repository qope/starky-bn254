use ark_bn254::Fq;
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
use plonky2_bn254::fields::{fq_target::FqTarget, u256_target::U256Target};

use crate::fields::fq::circuit::{fq_exp_circuit, FqExpInputTarget};

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

#[cfg(test)]
mod tests {
    use ark_bn254::Fq;
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
    use plonky2_bn254::fields::fq_target::FqTarget;

    use crate::curves::g2::batch_map_to_g2::batch_is_square_circuit;

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
}

use std::marker::PhantomData;

use crate::{
    g1_exp::{g1_exp_circuit_with_proof_target, G1ExpIONative, G1ExpStark},
    input_target::G1ExpInputTarget,
    utils::u32_digits_to_biguint,
};
use ark_bn254::{Fr, G1Affine};
use itertools::Itertools;
use num_bigint::BigUint;
use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::{
        generator::{GeneratedValues, SimpleGenerator},
        target::Target,
        witness::{PartitionWitness, Witness},
    },
    plonk::{
        circuit_builder::CircuitBuilder,
        config::{AlgebraicHasher, GenericConfig},
    },
    util::{serialization::Buffer, timing::TimingTree},
};
use plonky2_bn254::curves::g1curve_target::G1Target;
use starky::{
    proof::StarkProofWithPublicInputsTarget, prover::prove,
    recursive_verifier::set_stark_proof_with_pis_target, verifier::verify_stark_proof,
};

#[derive(Clone, Debug)]
pub struct G1ExpOutputGenerator<F: RichField + Extendable<D>, const D: usize> {
    pub input: G1ExpInputTarget<F, D>,
    pub output: G1Target<F, D>,
}

impl<F, const D: usize> SimpleGenerator<F> for G1ExpOutputGenerator<F, D>
where
    F: RichField + Extendable<D>,
{
    fn dependencies(&self) -> Vec<Target> {
        self.input.to_vec()
    }

    fn run_once(&self, pw: &PartitionWitness<F>, out_buffer: &mut GeneratedValues<F>) {
        let get_biguint = |x: &[Target]| -> BigUint {
            assert!(x.len() == 8);
            let x_value = x
                .iter()
                .map(|x| pw.get_target(*x).to_canonical_u64() as u32)
                .collect_vec();
            u32_digits_to_biguint(&x_value)
        };

        let x_x = get_biguint(&self.input.x.x.to_vec());
        let x_y = get_biguint(&self.input.x.y.to_vec());
        let offset_x = get_biguint(&self.input.offset.x.to_vec());
        let offset_y = get_biguint(&self.input.offset.y.to_vec());
        let exp_val = get_biguint(&self.input.exp_val.to_vec());
        let x = G1Affine::new(x_x.into(), x_y.into());
        let offset = G1Affine::new(offset_x.into(), offset_y.into());
        let exp_val: Fr = exp_val.into();
        let output: G1Affine = (x * exp_val + offset).into();

        self.output.set_witness(out_buffer, &output);
    }

    fn id(&self) -> String {
        "G1ExpOutputGenerator".to_string()
    }
    fn serialize(&self, _dst: &mut Vec<u8>) -> plonky2::util::serialization::IoResult<()> {
        todo!()
    }
    fn deserialize(_src: &mut Buffer) -> plonky2::util::serialization::IoResult<Self> {
        todo!()
    }
}

#[derive(Clone, Debug)]
pub struct G1ExpStarkyProofGenerator<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
> {
    pub inputs: Vec<G1ExpInputTarget<F, D>>,
    pub outputs: Vec<G1Target<F, D>>,
    pub starky_proof: StarkProofWithPublicInputsTarget<D>,
    _config: std::marker::PhantomData<C>,
}

impl<F, C, const D: usize> SimpleGenerator<F> for G1ExpStarkyProofGenerator<F, C, D>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    C::Hasher: AlgebraicHasher<F>,
{
    fn dependencies(&self) -> Vec<Target> {
        let mut targets = vec![];
        self.inputs.iter().cloned().for_each(|input| {
            targets.extend(input.to_vec());
        });
        targets
    }
    fn run_once(&self, pw: &PartitionWitness<F>, out_buffer: &mut GeneratedValues<F>) {
        let get_biguint = |x: &[Target]| -> BigUint {
            assert!(x.len() == 8);
            let x_value = x
                .iter()
                .map(|x| pw.get_target(*x).to_canonical_u64() as u32)
                .collect_vec();
            u32_digits_to_biguint(&x_value)
        };

        let ios_native = self
            .inputs
            .iter()
            .cloned()
            .map(|input| {
                let x_x = get_biguint(&input.x.x.to_vec());
                let x_y = get_biguint(&input.x.y.to_vec());
                let offset_x = get_biguint(&input.offset.x.to_vec());
                let offset_y = get_biguint(&input.offset.y.to_vec());
                let exp_val = get_biguint(&input.exp_val.to_vec());
                let x = G1Affine::new(x_x.into(), x_y.into());
                let offset = G1Affine::new(offset_x.into(), offset_y.into());
                let mut exp_val_u32 = exp_val.to_u32_digits();
                exp_val_u32.extend(vec![0; 8 - exp_val_u32.len()]);
                let exp_val: Fr = exp_val.into();
                let output: G1Affine = (x * exp_val + offset).into();
                G1ExpIONative {
                    x,
                    offset,
                    exp_val: exp_val_u32.try_into().unwrap(),
                    output,
                }
            })
            .collect_vec();

        let num_io = ios_native.len();
        let stark = G1ExpStark::<F, D>::new(num_io);
        let inner_config = stark.config();
        let trace = stark.generate_trace(&ios_native);
        let pi = stark.generate_public_inputs(&ios_native);
        let inner_proof = prove::<F, C, _, D>(
            stark,
            &inner_config,
            trace,
            pi.try_into().unwrap(),
            &mut TimingTree::default(),
        )
        .unwrap();
        verify_stark_proof(stark, inner_proof.clone(), &inner_config).unwrap();
        set_stark_proof_with_pis_target(out_buffer, &self.starky_proof, &inner_proof);
    }

    fn id(&self) -> String {
        "G1ExpStarkyProofGenerator".to_string()
    }
    fn serialize(&self, _dst: &mut Vec<u8>) -> plonky2::util::serialization::IoResult<()> {
        todo!()
    }
    fn deserialize(_src: &mut Buffer) -> plonky2::util::serialization::IoResult<Self> {
        todo!()
    }
}

pub fn g1_exp_circuit<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    inputs: &[G1ExpInputTarget<F, D>],
) -> Vec<G1Target<F, D>>
where
    C::Hasher: AlgebraicHasher<F>,
{
    assert!(inputs.len().is_power_of_two());
    assert!(inputs.len() >= 128);
    let log_num_io = inputs.len().trailing_zeros() as usize;

    let (inputs_constr, outputs, starky_proof) =
        g1_exp_circuit_with_proof_target::<F, C, D>(builder, log_num_io);

    for (input_c, input) in inputs_constr.iter().zip(inputs.iter()) {
        G1ExpInputTarget::connect(builder, input_c, input);
    }

    for (input, output) in inputs.iter().zip(outputs.iter()) {
        let output_generator = G1ExpOutputGenerator {
            input: input.to_owned(),
            output: output.to_owned(),
        };
        builder.add_simple_generator(output_generator);
    }

    let proof_generator = G1ExpStarkyProofGenerator::<F, C, D> {
        inputs: inputs.to_vec(),
        outputs: outputs.clone(),
        starky_proof,
        _config: PhantomData,
    };
    builder.add_simple_generator(proof_generator);
    outputs
}

#[cfg(test)]
mod tests {
    use ark_bn254::{Fr, G1Affine};
    use ark_std::UniformRand;
    use itertools::Itertools;
    use plonky2::{
        field::goldilocks_field::GoldilocksField,
        iop::witness::PartialWitness,
        plonk::{
            circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
            config::PoseidonGoldilocksConfig,
        },
    };
    use plonky2_bn254::{curves::g1curve_target::G1Target, fields::u256_target::U256Target};

    use crate::{
        circuits::g1_exp_circuit,
        flags::NUM_INPUT_LIMBS,
        input_target::{G1ExpInput, G1ExpInputTarget},
        utils::u32_digits_to_biguint,
    };

    #[test]
    fn test_g1_exp_circuit_with_generator() {
        let mut rng = rand::thread_rng();
        type F = GoldilocksField;
        type C = PoseidonGoldilocksConfig;
        const D: usize = 2;
        let log_num_io = 7;
        let num_io = 1 << log_num_io;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let inputs_t = (0..num_io)
            .map(|_| {
                let x = G1Target::empty(&mut builder);
                let offset = G1Target::empty(&mut builder);
                let exp_val = U256Target::empty(&mut builder);
                G1ExpInputTarget { x, offset, exp_val }
            })
            .collect_vec();

        let outputs_t = g1_exp_circuit::<F, C, D>(&mut builder, &inputs_t);

        let mut pw = PartialWitness::<F>::new();
        let mut inputs = vec![];
        let mut outputs = vec![];
        for _ in 0..num_io {
            let exp_val: [u32; NUM_INPUT_LIMBS] = rand::random();
            let exp_val_fr: Fr = u32_digits_to_biguint(&exp_val).into();
            let x = G1Affine::rand(&mut rng);
            let offset = G1Affine::rand(&mut rng);
            let output: G1Affine = (x * exp_val_fr + offset).into();
            let input = G1ExpInput {
                x,
                offset,
                exp_val: u32_digits_to_biguint(&exp_val),
            };
            inputs.push(input);
            outputs.push(output);
        }

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

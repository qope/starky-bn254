use std::marker::PhantomData;

use ark_bn254::{Fr, G1Affine};
use num_bigint::BigUint;
use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::{
        generator::{GeneratedValues, SimpleGenerator},
        target::Target,
        witness::{PartialWitness, PartitionWitness},
    },
    plonk::{
        circuit_builder::CircuitBuilder,
        config::{AlgebraicHasher, GenericConfig},
    },
    util::{serialization::Buffer, timing::TimingTree},
};
use plonky2_bn254::{
    curves::g1curve_target::G1Target,
    fields::{fq_target::FqTarget, u256_target::U256Target},
};
use starky::{
    proof::StarkProofWithPublicInputsTarget, recursive_verifier::set_stark_proof_with_pis_target,
    verifier::verify_stark_proof,
};
use starky::{
    prover::prove,
    recursive_verifier::{add_virtual_stark_proof_with_pis, verify_stark_proof_circuit},
};

use crate::{
    curves::g1::exp::{read_g1_exp_io, G1_EXP_IO_LEN},
    utils::utils::get_u256_biguint,
};

use super::exp::{G1ExpIONative, G1ExpStark};

pub const G1_EXP_INPUT_LEN: usize = 5 * 8;

#[derive(Clone, Debug)]
pub struct G1ExpInput {
    pub x: G1Affine,
    pub offset: G1Affine,
    pub exp_val: BigUint,
}

#[derive(Clone, Debug)]
pub struct G1ExpInputTarget<F: RichField + Extendable<D>, const D: usize> {
    pub x: G1Target<F, D>,
    pub offset: G1Target<F, D>,
    pub exp_val: U256Target<F, D>,
}

impl<F: RichField + Extendable<D>, const D: usize> G1ExpInputTarget<F, D> {
    pub fn connect(builder: &mut CircuitBuilder<F, D>, lhs: &Self, rhs: &Self) {
        G1Target::connect(builder, &lhs.x, &rhs.x);
        G1Target::connect(builder, &lhs.offset, &rhs.offset);
        U256Target::connect(builder, &lhs.exp_val, &rhs.exp_val);
    }

    pub fn to_vec(&self) -> Vec<Target> {
        self.x
            .to_vec()
            .iter()
            .chain(self.offset.to_vec().iter())
            .chain(self.exp_val.to_vec().iter())
            .cloned()
            .collect::<Vec<_>>()
    }
    pub fn from_vec(
        builder: &mut CircuitBuilder<F, D>,
        input: &[Target],
    ) -> G1ExpInputTarget<F, D> {
        assert!(input.len() == G1_EXP_INPUT_LEN);
        let num_limbs = 8;
        let num_g1_limbs = 2 * num_limbs;
        let mut input = input.to_vec();
        let x_raw = input.drain(0..num_g1_limbs).collect::<Vec<_>>();
        let offset_raw = input.drain(0..num_g1_limbs).collect::<Vec<_>>();
        let exp_val_raw = input.drain(0..num_limbs).collect::<Vec<_>>();
        assert_eq!(input.len(), 0);

        let x = G1Target::from_vec(builder, &x_raw);
        let offset = G1Target::from_vec(builder, &offset_raw);
        let exp_val = U256Target::from_vec(&exp_val_raw);
        G1ExpInputTarget { x, offset, exp_val }
    }

    pub fn set_witness(&self, pw: &mut PartialWitness<F>, value: &G1ExpInput) {
        self.x.set_witness(pw, &value.x);
        self.offset.set_witness(pw, &value.offset);
        self.exp_val.set_witness(pw, &value.exp_val);
    }
}

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
        let x_x = get_u256_biguint(pw, &self.input.x.x.to_vec());
        let x_y = get_u256_biguint(pw, &self.input.x.y.to_vec());
        let offset_x = get_u256_biguint(pw, &self.input.offset.x.to_vec());
        let offset_y = get_u256_biguint(pw, &self.input.offset.y.to_vec());
        let exp_val = get_u256_biguint(pw, &self.input.exp_val.to_vec());
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
        let ios_native = self
            .inputs
            .iter()
            .cloned()
            .map(|input| {
                let x_x = get_u256_biguint(pw, &input.x.x.to_vec());
                let x_y = get_u256_biguint(pw, &input.x.y.to_vec());
                let offset_x = get_u256_biguint(pw, &input.offset.x.to_vec());
                let offset_y = get_u256_biguint(pw, &input.offset.y.to_vec());
                let exp_val = get_u256_biguint(pw, &input.exp_val.to_vec());
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
            .collect::<Vec<_>>();

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

fn g1_exp_circuit_with_proof_target<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    log_num_io: usize,
) -> (
    Vec<G1ExpInputTarget<F, D>>,
    Vec<G1Target<F, D>>,
    StarkProofWithPublicInputsTarget<D>,
)
where
    <C as GenericConfig<D>>::Hasher: AlgebraicHasher<F>,
{
    assert!(log_num_io >= 7);
    let num_io = 1 << log_num_io;
    let stark = G1ExpStark::<F, D>::new(num_io);
    let inner_config = stark.config();
    let degree_bits = 9 + log_num_io;
    let starky_proof_t =
        add_virtual_stark_proof_with_pis(builder, stark, &inner_config, degree_bits);
    verify_stark_proof_circuit::<F, C, _, D>(builder, stark, &starky_proof_t, &inner_config);
    assert!(starky_proof_t.public_inputs.len() == G1_EXP_IO_LEN * num_io);
    let mut cur_col = 0;
    let mut inputs = vec![];
    let mut outputs = vec![];
    let pi = starky_proof_t.public_inputs.clone();
    for _ in 0..num_io {
        let io = read_g1_exp_io(&pi, &mut cur_col);
        let x_x = FqTarget::from_limbs(builder, &io.x[0]);
        let x_y = FqTarget::from_limbs(builder, &io.x[1]);
        let x = G1Target::new(x_x, x_y);
        let offset_x = FqTarget::from_limbs(builder, &io.offset[0]);
        let offset_y = FqTarget::from_limbs(builder, &io.offset[1]);
        let output_x = FqTarget::from_limbs(builder, &io.output[0]);
        let output_y = FqTarget::from_limbs(builder, &io.output[1]);
        let output = G1Target::new(output_x, output_y);
        let offset = G1Target::new(offset_x, offset_y);
        let exp_val = U256Target::<F, D>::from_vec(&io.exp_val);
        let input = G1ExpInputTarget { x, offset, exp_val };
        inputs.push(input);
        outputs.push(output);
    }
    (inputs, outputs, starky_proof_t)
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
    let n = inputs.len();
    let next_power_of_two = n.next_power_of_two();
    assert!(next_power_of_two >= 128);
    let mut inputs = inputs.to_vec();
    inputs.resize(next_power_of_two, inputs.last().unwrap().clone());
    let log_num_io = next_power_of_two.trailing_zeros() as usize;

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

    outputs[..n].to_vec()
}

#[cfg(test)]
mod tests {
    use ark_bn254::{Fr, G1Affine};
    use ark_ec::AffineRepr;
    use ark_std::UniformRand;
    use itertools::Itertools;
    use num_bigint::BigUint;
    use plonky2::{
        field::goldilocks_field::GoldilocksField,
        iop::witness::PartialWitness,
        plonk::{
            circuit_builder::CircuitBuilder,
            circuit_data::CircuitConfig,
            config::{GenericConfig, PoseidonGoldilocksConfig},
        },
        util::timing::TimingTree,
    };
    use plonky2_bn254::{curves::g1curve_target::G1Target, fields::u256_target::U256Target};
    use starky::{
        prover::prove, recursive_verifier::set_stark_proof_with_pis_target,
        verifier::verify_stark_proof,
    };

    use crate::{
        curves::g1::{
            circuit::{
                g1_exp_circuit, g1_exp_circuit_with_proof_target, G1ExpInput, G1ExpInputTarget,
            },
            exp::{G1ExpIONative, G1ExpStark},
        },
        utils::{flags::NUM_INPUT_LIMBS, utils::u32_digits_to_biguint},
    };

    #[test]
    fn test_g1_exp_circuit() {
        let log_num_io = 7;
        let num_io = 1 << log_num_io;
        let mut rng = rand::thread_rng();
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let circuit_config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(circuit_config);
        let (inputs_t, outputs_t, starky_proof_t) =
            g1_exp_circuit_with_proof_target::<F, C, D>(&mut builder, log_num_io);

        let stark = G1ExpStark::<F, D>::new(num_io);
        let inner_config = stark.config();

        let mut ios = vec![];
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
            let io = G1ExpIONative {
                x,
                offset,
                exp_val,
                output,
            };
            inputs.push(input);
            outputs.push(output);
            ios.push(io);
        }

        let trace = stark.generate_trace(&ios);
        let pi = stark.generate_public_inputs(&ios);
        let inner_proof = prove::<F, C, _, D>(
            stark,
            &inner_config,
            trace,
            pi.try_into().unwrap(),
            &mut TimingTree::default(),
        )
        .unwrap();
        verify_stark_proof(stark, inner_proof.clone(), &inner_config).unwrap();

        let mut pw = PartialWitness::<F>::new();
        set_stark_proof_with_pis_target(&mut pw, &starky_proof_t, &inner_proof);
        inputs_t.iter().zip(inputs.iter()).for_each(|(t, w)| {
            t.set_witness(&mut pw, w);
        });
        outputs_t.iter().zip(outputs.iter()).for_each(|(t, w)| {
            t.set_witness(&mut pw, w);
        });

        let data = builder.build::<C>();
        let _proof = data.prove(pw).unwrap();
    }

    #[test]
    fn test_g1_exp_circuit_with_generator() {
        let mut rng = rand::thread_rng();
        type F = GoldilocksField;
        type C = PoseidonGoldilocksConfig;
        const D: usize = 2;
        let num_io = 127;

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

    #[test]
    fn test_g1_msm() {
        let mut rng = rand::thread_rng();
        type F = GoldilocksField;
        type C = PoseidonGoldilocksConfig;
        const D: usize = 2;
        let log_num_io = 7;
        let num_io = 1 << log_num_io;

        let config = CircuitConfig::standard_ecc_config();
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

        let generator_t = G1Target::constant(&mut builder, G1Affine::generator());
        G1Target::connect(&mut builder, &inputs_t[0].offset, &generator_t);
        for i in 1..num_io {
            G1Target::connect(&mut builder, &inputs_t[i].offset, &outputs_t[i - 1]);
        }
        let mut pw = PartialWitness::<F>::new();
        let xs = (0..num_io).map(|_| G1Affine::rand(&mut rng)).collect_vec();
        let exp_vals: Vec<BigUint> = (0..num_io)
            .map(|_| {
                let exp_val = Fr::rand(&mut rng);
                exp_val.into()
            })
            .collect_vec();
        let expected = {
            let mut sum = G1Affine::zero();
            for i in 0..num_io {
                let exp_val_fr: Fr = exp_vals[i].clone().into();
                sum = (sum + xs[i] * exp_val_fr).into();
            }
            sum
        };
        for i in 0..num_io {
            inputs_t[i].x.set_witness(&mut pw, &xs[i]);
            inputs_t[i].exp_val.set_witness(&mut pw, &exp_vals[i]);
        }
        let neg_generator = G1Target::constant(&mut builder, -G1Affine::generator());
        let output = outputs_t.last().unwrap().add(&mut builder, &neg_generator);
        output.set_witness(&mut pw, &expected);
        let data = builder.build::<C>();
        let _proof = data.prove(pw).unwrap();
    }
}

use std::marker::PhantomData;

use ark_bn254::{Fq, Fq12};
use ark_ff::Field;
use itertools::Itertools;
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
use plonky2_bn254::fields::{
    fq12_target::Fq12Target, fq_target::FqTarget, native::MyFq12, u256_target::U256Target,
};
use starky::{
    proof::StarkProofWithPublicInputsTarget,
    prover::prove,
    recursive_verifier::{
        add_virtual_stark_proof_with_pis, set_stark_proof_with_pis_target,
        verify_stark_proof_circuit,
    },
    verifier::verify_stark_proof,
};

use crate::{
    fields::fq12::exp::{read_fq12_exp_io, FQ12_EXP_IO_LEN},
    utils::utils::{get_u256_biguint, u16_columns_to_u32_columns_base_circuit},
};

use super::exp::{Fq12ExpIONative, Fq12ExpStark};

pub const FQ12_EXP_INPUT_LEN: usize = 12 * 8 * 3 + 8;

#[derive(Clone, Debug)]
pub struct Fq12ExpInput {
    pub x: Fq12,
    pub offset: Fq12,
    pub exp_val: BigUint,
}

#[derive(Clone, Debug)]
pub struct Fq12ExpInputTarget<F: RichField + Extendable<D>, const D: usize> {
    pub x: Fq12Target<F, D>,
    pub offset: Fq12Target<F, D>,
    pub exp_val: U256Target<F, D>,
}

impl<F: RichField + Extendable<D>, const D: usize> Fq12ExpInputTarget<F, D> {
    pub fn connect(builder: &mut CircuitBuilder<F, D>, lhs: &Self, rhs: &Self) {
        Fq12Target::connect(builder, &lhs.x, &rhs.x);
        Fq12Target::connect(builder, &lhs.offset, &rhs.offset);
        U256Target::connect(builder, &lhs.exp_val, &rhs.exp_val);
    }
    pub fn to_vec(&self) -> Vec<Target> {
        self.x
            .to_vec()
            .iter()
            .chain(self.offset.to_vec().iter())
            .chain(self.exp_val.to_vec().iter())
            .cloned()
            .collect_vec()
    }
    pub fn from_vec(
        builder: &mut CircuitBuilder<F, D>,
        input: &[Target],
    ) -> Fq12ExpInputTarget<F, D> {
        assert!(input.len() == FQ12_EXP_INPUT_LEN);
        let num_limbs = 8;
        let num_fq12_limbs = 12 * num_limbs;
        let mut input = input.to_vec();
        let x_raw = input.drain(0..num_fq12_limbs).collect_vec();
        let offset_raw = input.drain(0..num_fq12_limbs).collect_vec();
        let exp_val_raw = input.drain(0..num_limbs).collect_vec();
        assert_eq!(input.len(), 0);

        let x = Fq12Target::from_vec(builder, &x_raw);
        let offset = Fq12Target::from_vec(builder, &offset_raw);
        let exp_val = U256Target::from_vec(&exp_val_raw);
        Fq12ExpInputTarget { x, offset, exp_val }
    }

    pub fn set_witness(&self, pw: &mut PartialWitness<F>, value: &Fq12ExpInput) {
        self.x.set_witness(pw, &value.x);
        self.offset.set_witness(pw, &value.offset);
        self.exp_val.set_witness(pw, &value.exp_val);
    }
}

#[derive(Clone, Debug)]
pub struct Fq12ExpOutputGenerator<F: RichField + Extendable<D>, const D: usize> {
    pub input: Fq12ExpInputTarget<F, D>,
    pub output: Fq12Target<F, D>,
}

impl<F, const D: usize> SimpleGenerator<F> for Fq12ExpOutputGenerator<F, D>
where
    F: RichField + Extendable<D>,
{
    fn dependencies(&self) -> Vec<Target> {
        self.input.to_vec()
    }

    fn run_once(&self, pw: &PartitionWitness<F>, out_buffer: &mut GeneratedValues<F>) {
        let x_coeffs: [Fq; 12] = self
            .input
            .x
            .clone()
            .coeffs
            .map(|x| get_u256_biguint(pw, &x.to_vec()).into());
        let x: Fq12 = MyFq12 { coeffs: x_coeffs }.into();
        let offset_coeffs = self
            .input
            .offset
            .clone()
            .coeffs
            .map(|x| get_u256_biguint(pw, &x.to_vec()).into());
        let offset: Fq12 = MyFq12 {
            coeffs: offset_coeffs,
        }
        .into();
        let exp_val = get_u256_biguint(pw, &self.input.exp_val.to_vec());
        let output = offset * x.pow(&exp_val.to_u64_digits());
        self.output.set_witness(out_buffer, &output);
    }

    fn id(&self) -> String {
        "Fq12ExpOutputGenerator".to_string()
    }
    fn serialize(&self, _dst: &mut Vec<u8>) -> plonky2::util::serialization::IoResult<()> {
        todo!()
    }
    fn deserialize(_src: &mut Buffer) -> plonky2::util::serialization::IoResult<Self> {
        todo!()
    }
}

#[derive(Clone, Debug)]
pub struct Fq12ExpStarkyProofGenerator<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
> {
    pub inputs: Vec<Fq12ExpInputTarget<F, D>>,
    pub outputs: Vec<Fq12Target<F, D>>,
    pub starky_proof: StarkProofWithPublicInputsTarget<D>,
    _config: std::marker::PhantomData<C>,
}

impl<F, C, const D: usize> SimpleGenerator<F> for Fq12ExpStarkyProofGenerator<F, C, D>
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
                let x_coeffs: [Fq; 12] = input
                    .x
                    .coeffs
                    .map(|x| get_u256_biguint(pw, &x.to_vec()).into());
                let x: Fq12 = MyFq12 { coeffs: x_coeffs }.into();
                let offset_coeffs = input
                    .offset
                    .coeffs
                    .map(|x| get_u256_biguint(pw, &x.to_vec()).into());
                let offset: Fq12 = MyFq12 {
                    coeffs: offset_coeffs,
                }
                .into();
                let exp_val = get_u256_biguint(pw, &input.exp_val.to_vec());
                let mut exp_val_u32 = exp_val.to_u32_digits();
                exp_val_u32.extend(vec![0; 8 - exp_val_u32.len()]);
                let output = offset * x.pow(&exp_val.to_u64_digits());
                Fq12ExpIONative {
                    x,
                    offset,
                    exp_val: exp_val_u32.try_into().unwrap(),
                    output,
                }
            })
            .collect_vec();

        let num_io = ios_native.len();
        let stark = Fq12ExpStark::<F, D>::new(num_io);
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
        "Fq12ExpStarkyProofGenerator".to_string()
    }
    fn serialize(&self, _dst: &mut Vec<u8>) -> plonky2::util::serialization::IoResult<()> {
        todo!()
    }
    fn deserialize(_src: &mut Buffer) -> plonky2::util::serialization::IoResult<Self> {
        todo!()
    }
}

fn fq12_exp_circuit_with_proof_target<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    log_num_io: usize,
) -> (
    Vec<Fq12ExpInputTarget<F, D>>,
    Vec<Fq12Target<F, D>>,
    StarkProofWithPublicInputsTarget<D>,
)
where
    <C as GenericConfig<D>>::Hasher: AlgebraicHasher<F>,
{
    let num_io = 1 << log_num_io;
    let stark = Fq12ExpStark::<F, D>::new(num_io);
    let inner_config = stark.config();
    let degree_bits = 9 + log_num_io;
    let starky_proof_t =
        add_virtual_stark_proof_with_pis(builder, stark, &inner_config, degree_bits);
    verify_stark_proof_circuit::<F, C, _, D>(builder, stark, &starky_proof_t, &inner_config);
    assert!(starky_proof_t.public_inputs.len() == FQ12_EXP_IO_LEN * num_io);
    let mut cur_col = 0;
    let mut inputs = vec![];
    let mut outputs = vec![];
    let pi = starky_proof_t.public_inputs.clone();
    for _ in 0..num_io {
        let io = read_fq12_exp_io(&pi, &mut cur_col);
        let x_coeffs =
            io.x.iter()
                .map(|limb| {
                    // range check
                    limb.iter().for_each(|l| builder.range_check(*l, 16));
                    let limb_u32 = u16_columns_to_u32_columns_base_circuit(builder, *limb);
                    FqTarget::from_limbs(builder, &limb_u32)
                })
                .collect_vec();
        let offset_coeffs = io
            .offset
            .iter()
            .map(|limb| {
                // range check
                limb.iter().for_each(|l| builder.range_check(*l, 16));
                let limb_u32 = u16_columns_to_u32_columns_base_circuit(builder, *limb);
                FqTarget::from_limbs(builder, &limb_u32)
            })
            .collect_vec();
        let output_coeffs = io
            .output
            .iter()
            .map(|limb| {
                // range check
                // limb.iter().for_each(|l| builder.range_check(*l, 16));
                let limb_u32 = u16_columns_to_u32_columns_base_circuit(builder, *limb);
                FqTarget::from_limbs(builder, &limb_u32)
            })
            .collect_vec();
        let x = Fq12Target::new(x_coeffs);
        let offset = Fq12Target::new(offset_coeffs);
        let output = Fq12Target::new(output_coeffs);
        let exp_val = U256Target::<F, D>::from_vec(&io.exp_val);
        let input = Fq12ExpInputTarget { x, offset, exp_val };
        inputs.push(input);
        outputs.push(output);
    }
    (inputs, outputs, starky_proof_t)
}

pub fn fq12_exp_circuit<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    inputs: &[Fq12ExpInputTarget<F, D>],
) -> Vec<Fq12Target<F, D>>
where
    C::Hasher: AlgebraicHasher<F>,
{
    let n = inputs.len();
    let next_power_of_two = n.next_power_of_two();
    let mut inputs = inputs.to_vec();
    inputs.resize(next_power_of_two, inputs.last().unwrap().clone());
    let log_num_io = next_power_of_two.trailing_zeros() as usize;

    let (inputs_constr, outputs, starky_proof) =
        fq12_exp_circuit_with_proof_target::<F, C, D>(builder, log_num_io);

    for (input_c, input) in inputs_constr.iter().zip(inputs.iter()) {
        Fq12ExpInputTarget::connect(builder, input_c, input);
    }

    for (input, output) in inputs.iter().zip(outputs.iter()) {
        let output_generator = Fq12ExpOutputGenerator {
            input: input.to_owned(),
            output: output.to_owned(),
        };
        builder.add_simple_generator(output_generator);
    }

    let proof_generator = Fq12ExpStarkyProofGenerator::<F, C, D> {
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
    use std::time::Instant;

    use ark_bn254::{Fq12, Fr};
    use ark_ff::Field;
    use ark_std::UniformRand;
    use itertools::Itertools;
    use num_bigint::BigUint;
    use num_traits::One;
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
    use plonky2_bn254::fields::{fq12_target::Fq12Target, u256_target::U256Target};
    use starky::{
        prover::prove, recursive_verifier::set_stark_proof_with_pis_target,
        verifier::verify_stark_proof,
    };

    use crate::{
        fields::fq12::{
            circuit::{
                fq12_exp_circuit, fq12_exp_circuit_with_proof_target, Fq12ExpInput,
                Fq12ExpInputTarget,
            },
            exp::{Fq12ExpIONative, Fq12ExpStark},
        },
        utils::{flags::NUM_INPUT_LIMBS, utils::u32_digits_to_biguint},
    };

    #[test]
    fn test_fq12_exp_circuit() {
        let log_num_io = 4;
        let num_io = 1 << log_num_io;
        let mut rng = rand::thread_rng();
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let circuit_config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(circuit_config);
        let (inputs_t, outputs_t, starky_proof_t) =
            fq12_exp_circuit_with_proof_target::<F, C, D>(&mut builder, log_num_io);

        let stark = Fq12ExpStark::<F, D>::new(num_io);
        let inner_config = stark.config();

        let mut ios = vec![];
        let mut inputs = vec![];
        let mut outputs = vec![];
        for _ in 0..num_io {
            let exp_val: [u32; NUM_INPUT_LIMBS] = rand::random();
            let exp_val_b = u32_digits_to_biguint(&exp_val);
            let x = Fq12::rand(&mut rng);
            let offset = Fq12::rand(&mut rng);
            let output: Fq12 = offset * x.pow(&exp_val_b.to_u64_digits());
            let input = Fq12ExpInput {
                x,
                offset,
                exp_val: u32_digits_to_biguint(&exp_val),
            };
            let io = Fq12ExpIONative {
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

        dbg!(builder.num_gates());
        let data = builder.build::<C>();
        dbg!(&data.common);

        let mut pw = PartialWitness::<F>::new();
        set_stark_proof_with_pis_target(&mut pw, &starky_proof_t, &inner_proof);
        inputs_t.iter().zip(inputs.iter()).for_each(|(t, w)| {
            t.set_witness(&mut pw, w);
        });
        outputs_t.iter().zip(outputs.iter()).for_each(|(t, w)| {
            t.set_witness(&mut pw, w);
        });
        let now = Instant::now();
        let _proof = data.prove(pw).unwrap();
        println!("end plonky2 proof generation: {:?}", now.elapsed());
    }

    #[test]
    fn test_fq12_msm() {
        let mut rng = rand::thread_rng();
        type F = GoldilocksField;
        type C = PoseidonGoldilocksConfig;
        const D: usize = 2;
        let log_num_io = 4;
        let num_io = 1 << log_num_io;

        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let inputs_t = (0..num_io)
            .map(|_| {
                let x = Fq12Target::empty(&mut builder);
                let offset = Fq12Target::empty(&mut builder);
                let exp_val = U256Target::empty(&mut builder);
                Fq12ExpInputTarget { x, offset, exp_val }
            })
            .collect_vec();
        let outputs_t = fq12_exp_circuit::<F, C, D>(&mut builder, &inputs_t);

        let one = Fq12Target::constant(&mut builder, Fq12::one());
        Fq12Target::connect(&mut builder, &inputs_t[0].offset, &one);
        for i in 1..num_io {
            Fq12Target::connect(&mut builder, &inputs_t[i].offset, &outputs_t[i - 1]);
        }
        let data = builder.build::<C>();

        let now = Instant::now();
        let mut pw = PartialWitness::<F>::new();
        let xs = (0..num_io).map(|_| Fq12::rand(&mut rng)).collect_vec();
        let exp_vals: Vec<BigUint> = (0..num_io)
            .map(|_| {
                let exp_val = Fr::rand(&mut rng);
                exp_val.into()
            })
            .collect_vec();
        let expected = {
            let mut total = Fq12::one();
            for i in 0..num_io {
                total = total * xs[i].pow(&exp_vals[i].to_u64_digits());
            }
            total
        };
        for i in 0..num_io {
            inputs_t[i].x.set_witness(&mut pw, &xs[i]);
            inputs_t[i].exp_val.set_witness(&mut pw, &exp_vals[i]);
        }
        let output = outputs_t.last().unwrap();
        output.set_witness(&mut pw, &expected);

        let _proof = data.prove(pw).unwrap();
        println!("Fq12 msm time: {:?}", now.elapsed());
    }
}

use std::{marker::PhantomData, str::FromStr};

use crate::{
    fq12_exp::{fq12_exp_circuit_with_proof_target, Fq12ExpIONative, Fq12ExpStark},
    fq12_exp_u64::fq12_exp_u64::{
        fq12_exp_u64_circuit_with_proof_target, Fq12ExpU64IONative, Fq12ExpU64Stark,
    },
    g1_exp::{g1_exp_circuit_with_proof_target, G1ExpIONative, G1ExpStark},
    g2_exp::{g2_exp_circuit_with_proof_target, G2ExpIONative, G2ExpStark},
    input_target::{Fq12ExpInputTarget, Fq12ExpU64InputTarget, G1ExpInputTarget, G2ExpInputTarget},
    native::MyFq12,
    utils::u32_digits_to_biguint,
};
use ark_bn254::{Fq, Fq12, Fq2, Fr, G1Affine, G2Affine};
use ark_ec::AffineRepr;
use ark_ff::Field;
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
use plonky2_bn254::{
    curves::{g1curve_target::G1Target, g2curve_target::G2Target},
    fields::{fq12_target::Fq12Target, u256_target::U256Target},
};
use starky::{
    proof::StarkProofWithPublicInputsTarget, prover::prove,
    recursive_verifier::set_stark_proof_with_pis_target, verifier::verify_stark_proof,
};

fn get_biguint<F: RichField, W: Witness<F>>(pw: &W, x: &[Target]) -> BigUint {
    assert!(x.len() == 8);
    let x_value = x
        .iter()
        .map(|x| pw.get_target(*x).to_canonical_u64() as u32)
        .collect_vec();
    u32_digits_to_biguint(&x_value)
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
        let x_x = get_biguint(pw, &self.input.x.x.to_vec());
        let x_y = get_biguint(pw, &self.input.x.y.to_vec());
        let offset_x = get_biguint(pw, &self.input.offset.x.to_vec());
        let offset_y = get_biguint(pw, &self.input.offset.y.to_vec());
        let exp_val = get_biguint(pw, &self.input.exp_val.to_vec());
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
                let x_x = get_biguint(pw, &input.x.x.to_vec());
                let x_y = get_biguint(pw, &input.x.y.to_vec());
                let offset_x = get_biguint(pw, &input.offset.x.to_vec());
                let offset_y = get_biguint(pw, &input.offset.y.to_vec());
                let exp_val = get_biguint(pw, &input.exp_val.to_vec());
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

#[derive(Clone, Debug)]
pub struct G2ExpOutputGenerator<F: RichField + Extendable<D>, const D: usize> {
    pub input: G2ExpInputTarget<F, D>,
    pub output: G2Target<F, D>,
}

impl<F, const D: usize> SimpleGenerator<F> for G2ExpOutputGenerator<F, D>
where
    F: RichField + Extendable<D>,
{
    fn dependencies(&self) -> Vec<Target> {
        self.input.to_vec()
    }

    fn run_once(&self, pw: &PartitionWitness<F>, out_buffer: &mut GeneratedValues<F>) {
        let x_x_c0 = get_biguint(pw, &self.input.x.x.coeffs[0].to_vec());
        let x_x_c1 = get_biguint(pw, &self.input.x.x.coeffs[1].to_vec());
        let x_y_c0 = get_biguint(pw, &self.input.x.y.coeffs[0].to_vec());
        let x_y_c1 = get_biguint(pw, &self.input.x.y.coeffs[1].to_vec());
        let x_x = Fq2::new(x_x_c0.into(), x_x_c1.into());
        let x_y = Fq2::new(x_y_c0.into(), x_y_c1.into());
        let x = G2Affine::new_unchecked(x_x, x_y);

        let offset_x_c0 = get_biguint(pw, &self.input.offset.x.coeffs[0].to_vec());
        let offset_x_c1 = get_biguint(pw, &self.input.offset.x.coeffs[1].to_vec());
        let offset_y_c0 = get_biguint(pw, &self.input.offset.y.coeffs[0].to_vec());
        let offset_y_c1 = get_biguint(pw, &self.input.offset.y.coeffs[1].to_vec());
        let offset_x = Fq2::new(offset_x_c0.into(), offset_x_c1.into());
        let offset_y = Fq2::new(offset_y_c0.into(), offset_y_c1.into());
        let offset = G2Affine::new(offset_x, offset_y);

        let exp_val = get_biguint(pw, &self.input.exp_val.to_vec());
        let output: G2Affine = (x.mul_bigint(&exp_val.to_u64_digits()) + offset).into();
        self.output.set_witness(out_buffer, &output);
    }

    fn id(&self) -> String {
        "G2ExpOutputGenerator".to_string()
    }
    fn serialize(&self, _dst: &mut Vec<u8>) -> plonky2::util::serialization::IoResult<()> {
        todo!()
    }
    fn deserialize(_src: &mut Buffer) -> plonky2::util::serialization::IoResult<Self> {
        todo!()
    }
}

#[derive(Clone, Debug)]
pub struct G2ExpStarkyProofGenerator<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
> {
    pub inputs: Vec<G2ExpInputTarget<F, D>>,
    pub outputs: Vec<G2Target<F, D>>,
    pub starky_proof: StarkProofWithPublicInputsTarget<D>,
    _config: std::marker::PhantomData<C>,
}

impl<F, C, const D: usize> SimpleGenerator<F> for G2ExpStarkyProofGenerator<F, C, D>
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
                let x_x_c0 = get_biguint(pw, &input.x.x.coeffs[0].to_vec());
                let x_x_c1 = get_biguint(pw, &input.x.x.coeffs[1].to_vec());
                let x_y_c0 = get_biguint(pw, &input.x.y.coeffs[0].to_vec());
                let x_y_c1 = get_biguint(pw, &input.x.y.coeffs[1].to_vec());
                let x_x = Fq2::new(x_x_c0.into(), x_x_c1.into());
                let x_y = Fq2::new(x_y_c0.into(), x_y_c1.into());
                let x = G2Affine::new_unchecked(x_x, x_y);

                let offset_x_c0 = get_biguint(pw, &input.offset.x.coeffs[0].to_vec());
                let offset_x_c1 = get_biguint(pw, &input.offset.x.coeffs[1].to_vec());
                let offset_y_c0 = get_biguint(pw, &input.offset.y.coeffs[0].to_vec());
                let offset_y_c1 = get_biguint(pw, &input.offset.y.coeffs[1].to_vec());
                let offset_x = Fq2::new(offset_x_c0.into(), offset_x_c1.into());
                let offset_y = Fq2::new(offset_y_c0.into(), offset_y_c1.into());
                let offset = G2Affine::new(offset_x, offset_y);
                let exp_val = get_biguint(pw, &input.exp_val.to_vec());
                let mut exp_val_u32 = exp_val.to_u32_digits();
                exp_val_u32.extend(vec![0; 8 - exp_val_u32.len()]);
                let output: G2Affine = (x.mul_bigint(&exp_val.to_u64_digits()) + offset).into();
                G2ExpIONative {
                    x,
                    offset,
                    exp_val: exp_val_u32.try_into().unwrap(),
                    output,
                }
            })
            .collect_vec();

        let num_io = ios_native.len();
        let stark = G2ExpStark::<F, D>::new(num_io);
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
        "G2ExpStarkyProofGenerator".to_string()
    }
    fn serialize(&self, _dst: &mut Vec<u8>) -> plonky2::util::serialization::IoResult<()> {
        todo!()
    }
    fn deserialize(_src: &mut Buffer) -> plonky2::util::serialization::IoResult<Self> {
        todo!()
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
            .map(|x| get_biguint(pw, &x.to_vec()).into());
        let x: Fq12 = MyFq12 { coeffs: x_coeffs }.into();
        let offset_coeffs = self
            .input
            .offset
            .clone()
            .coeffs
            .map(|x| get_biguint(pw, &x.to_vec()).into());
        let offset: Fq12 = MyFq12 {
            coeffs: offset_coeffs,
        }
        .into();
        let exp_val = get_biguint(pw, &self.input.exp_val.to_vec());
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
                let x_coeffs: [Fq; 12] =
                    input.x.coeffs.map(|x| get_biguint(pw, &x.to_vec()).into());
                let x: Fq12 = MyFq12 { coeffs: x_coeffs }.into();
                let offset_coeffs = input
                    .offset
                    .coeffs
                    .map(|x| get_biguint(pw, &x.to_vec()).into());
                let offset: Fq12 = MyFq12 {
                    coeffs: offset_coeffs,
                }
                .into();
                let exp_val = get_biguint(pw, &input.exp_val.to_vec());
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

#[derive(Clone, Debug)]
pub struct Fq12ExpU64OutputGenerator<F: RichField + Extendable<D>, const D: usize> {
    pub input: Fq12ExpU64InputTarget<F, D>,
    pub output: Fq12Target<F, D>,
}

impl<F, const D: usize> SimpleGenerator<F> for Fq12ExpU64OutputGenerator<F, D>
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
            .map(|x| get_biguint(pw, &x.to_vec()).into());
        let x: Fq12 = MyFq12 { coeffs: x_coeffs }.into();
        let offset_coeffs = self
            .input
            .offset
            .clone()
            .coeffs
            .map(|x| get_biguint(pw, &x.to_vec()).into());
        let offset: Fq12 = MyFq12 {
            coeffs: offset_coeffs,
        }
        .into();
        let exp_val = pw.get_target(self.input.exp_val).to_canonical_u64();
        let output = offset * x.pow(&[exp_val]);
        self.output.set_witness(out_buffer, &output);
    }

    fn id(&self) -> String {
        "Fq12ExpU64OutputGenerator".to_string()
    }
    fn serialize(&self, _dst: &mut Vec<u8>) -> plonky2::util::serialization::IoResult<()> {
        todo!()
    }
    fn deserialize(_src: &mut Buffer) -> plonky2::util::serialization::IoResult<Self> {
        todo!()
    }
}

#[derive(Clone, Debug)]
pub struct Fq12ExpU64StarkyProofGenerator<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
> {
    pub inputs: Vec<Fq12ExpU64InputTarget<F, D>>,
    pub outputs: Vec<Fq12Target<F, D>>,
    pub starky_proof: StarkProofWithPublicInputsTarget<D>,
    _config: std::marker::PhantomData<C>,
}

impl<F, C, const D: usize> SimpleGenerator<F> for Fq12ExpU64StarkyProofGenerator<F, C, D>
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
                let x_coeffs: [Fq; 12] =
                    input.x.coeffs.map(|x| get_biguint(pw, &x.to_vec()).into());
                let x: Fq12 = MyFq12 { coeffs: x_coeffs }.into();
                let offset_coeffs = input
                    .offset
                    .coeffs
                    .map(|x| get_biguint(pw, &x.to_vec()).into());
                let offset: Fq12 = MyFq12 {
                    coeffs: offset_coeffs,
                }
                .into();
                let exp_val = pw.get_target(input.exp_val).to_canonical_u64();
                let output = offset * x.pow(&[exp_val]);
                Fq12ExpU64IONative {
                    x,
                    offset,
                    exp_val,
                    output,
                }
            })
            .collect_vec();

        let num_io = ios_native.len();
        let stark = Fq12ExpU64Stark::<F, D>::new(num_io);
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
        "Fq12ExpU64StarkyProofGenerator".to_string()
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

pub fn g2_exp_circuit<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    inputs: &[G2ExpInputTarget<F, D>],
) -> Vec<G2Target<F, D>>
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
        g2_exp_circuit_with_proof_target::<F, C, D>(builder, log_num_io);

    for (input_c, input) in inputs_constr.iter().zip(inputs.iter()) {
        G2ExpInputTarget::connect(builder, input_c, input);
    }

    for (input, output) in inputs.iter().zip(outputs.iter()) {
        let output_generator = G2ExpOutputGenerator {
            input: input.to_owned(),
            output: output.to_owned(),
        };
        builder.add_simple_generator(output_generator);
    }

    let proof_generator = G2ExpStarkyProofGenerator::<F, C, D> {
        inputs: inputs.to_vec(),
        outputs: outputs.clone(),
        starky_proof,
        _config: PhantomData,
    };
    builder.add_simple_generator(proof_generator);
    outputs[..n].to_vec()
}

pub fn g2_mul_by_cofactor_circuit<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    inputs: &[G2Target<F, D>],
) -> Vec<G2Target<F, D>>
where
    <C as GenericConfig<D>>::Hasher: AlgebraicHasher<F>,
{
    let exp_val_b = BigUint::from_str(
        "21888242871839275222246405745257275088844257914179612981679871602714643921549",
    )
    .unwrap();
    let exp_val = U256Target::constant(builder, &exp_val_b);
    let g2_gen = G2Target::constant(builder, G2Affine::generator());
    let neg_g2_gen = G2Target::constant(builder, -G2Affine::generator());
    let exp_inputs = inputs
        .iter()
        .map(|x| G2ExpInputTarget {
            x: x.clone(),
            offset: g2_gen.clone(),
            exp_val: exp_val.clone(),
        })
        .collect::<Vec<_>>();
    let exp_outputs = g2_exp_circuit::<F, C, D>(builder, &exp_inputs);
    let outputs = exp_outputs
        .into_iter()
        .map(|x| x.add(builder, &neg_g2_gen))
        .collect::<Vec<_>>();
    outputs
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
    assert!(next_power_of_two >= 128);
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

pub fn fq12_exp_u64_circuit<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    inputs: &[Fq12ExpU64InputTarget<F, D>],
) -> Vec<Fq12Target<F, D>>
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
        fq12_exp_u64_circuit_with_proof_target::<F, C, D>(builder, log_num_io);

    for (input_c, input) in inputs_constr.iter().zip(inputs.iter()) {
        Fq12ExpU64InputTarget::connect(builder, input_c, input);
    }

    for (input, output) in inputs.iter().zip(outputs.iter()) {
        let output_generator = Fq12ExpU64OutputGenerator {
            input: input.to_owned(),
            output: output.to_owned(),
        };
        builder.add_simple_generator(output_generator);
    }

    let proof_generator = Fq12ExpU64StarkyProofGenerator::<F, C, D> {
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

    use ark_bn254::{Fq12, Fq2, Fr, G1Affine, G2Affine};
    use ark_ec::AffineRepr;
    use ark_ff::Field;
    use ark_std::UniformRand;
    use itertools::Itertools;
    use num_bigint::BigUint;
    use num_traits::One;
    use plonky2::{
        field::{
            goldilocks_field::GoldilocksField,
            types::{PrimeField64, Sample},
        },
        iop::witness::{PartialWitness, WitnessWrite},
        plonk::{
            circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
            config::PoseidonGoldilocksConfig,
        },
    };
    use plonky2_bn254::{
        curves::{
            g1curve_target::G1Target, g2curve_target::G2Target,
            map_to_g2::map_to_g2_without_cofactor_mul,
        },
        fields::{fq12_target::Fq12Target, u256_target::U256Target},
    };

    use crate::{
        circuits::{
            fq12_exp_circuit, fq12_exp_u64_circuit, g1_exp_circuit, g2_exp_circuit,
            g2_mul_by_cofactor_circuit,
        },
        flags::NUM_INPUT_LIMBS,
        input_target::{
            Fq12ExpInputTarget, Fq12ExpU64InputTarget, G1ExpInput, G1ExpInputTarget,
            G2ExpInputTarget,
        },
        utils::u32_digits_to_biguint,
    };

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

    #[test]
    fn test_g2_msm() {
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
                let x = G2Target::empty(&mut builder);
                let offset = G2Target::empty(&mut builder);
                let exp_val = U256Target::empty(&mut builder);
                G2ExpInputTarget { x, offset, exp_val }
            })
            .collect_vec();
        let outputs_t = g2_exp_circuit::<F, C, D>(&mut builder, &inputs_t);

        let generator_t = G2Target::constant(&mut builder, G2Affine::generator());
        G2Target::connect(&mut builder, &inputs_t[0].offset, &generator_t);
        for i in 1..num_io {
            G2Target::connect(&mut builder, &inputs_t[i].offset, &outputs_t[i - 1]);
        }
        let mut pw = PartialWitness::<F>::new();
        let xs = (0..num_io).map(|_| G2Affine::rand(&mut rng)).collect_vec();
        let exp_vals: Vec<BigUint> = (0..num_io)
            .map(|_| {
                let exp_val = Fr::rand(&mut rng);
                exp_val.into()
            })
            .collect_vec();
        let expected = {
            let mut sum = G2Affine::zero();
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
        let neg_generator = G2Target::constant(&mut builder, -G2Affine::generator());
        let output = outputs_t.last().unwrap().add(&mut builder, &neg_generator);
        output.set_witness(&mut pw, &expected);
        let data = builder.build::<C>();
        let _proof = data.prove(pw).unwrap();
    }

    #[test]
    fn test_g2_mul_by_cofactor() {
        let mut rng = rand::thread_rng();
        type F = GoldilocksField;
        type C = PoseidonGoldilocksConfig;
        const D: usize = 2;
        let num_io = 65;

        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let inputs_t = (0..num_io)
            .map(|_| G2Target::empty(&mut builder))
            .collect_vec();
        let outputs_t = g2_mul_by_cofactor_circuit::<F, C, D>(&mut builder, &inputs_t);

        let mut pw = PartialWitness::<F>::new();
        let inputs = (0..num_io)
            .map(|_| {
                let u = Fq2::rand(&mut rng);
                map_to_g2_without_cofactor_mul(u)
            })
            .collect_vec();
        let outputs = inputs.iter().map(|x| x.mul_by_cofactor()).collect_vec();
        for i in 0..num_io {
            inputs_t[i].set_witness(&mut pw, &inputs[i]);
            outputs_t[i].set_witness(&mut pw, &outputs[i]);
        }
        let data = builder.build::<C>();
        let _proof = data.prove(pw).unwrap();
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

    #[test]
    fn test_fq12_u64_msm() {
        let mut rng = rand::thread_rng();
        type F = GoldilocksField;
        type C = PoseidonGoldilocksConfig;
        const D: usize = 2;
        let log_num_io = 2;
        let num_io = 1 << log_num_io;

        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let inputs_t = (0..num_io)
            .map(|_| {
                let x = Fq12Target::empty(&mut builder);
                let offset = Fq12Target::empty(&mut builder);
                let exp_val = builder.add_virtual_target();
                Fq12ExpU64InputTarget { x, offset, exp_val }
            })
            .collect_vec();
        let outputs_t = fq12_exp_u64_circuit::<F, C, D>(&mut builder, &inputs_t);

        let one = Fq12Target::constant(&mut builder, Fq12::one());
        Fq12Target::connect(&mut builder, &inputs_t[0].offset, &one);
        for i in 1..num_io {
            Fq12Target::connect(&mut builder, &inputs_t[i].offset, &outputs_t[i - 1]);
        }
        let data = builder.build::<C>();

        let now = Instant::now();
        let mut pw = PartialWitness::<F>::new();
        let xs = (0..num_io).map(|_| Fq12::rand(&mut rng)).collect_vec();
        let exp_vals: Vec<u64> = (0..num_io)
            .map(|_| {
                let exp_val_f = F::sample(&mut rng);
                exp_val_f.to_canonical_u64()
            })
            .collect_vec();
        let expected = {
            let mut total = Fq12::one();
            for i in 0..num_io {
                total = total * xs[i].pow(&[exp_vals[i]]);
            }
            total
        };
        use plonky2::field::types::Field;
        for i in 0..num_io {
            inputs_t[i].x.set_witness(&mut pw, &xs[i]);
            pw.set_target(inputs_t[i].exp_val, F::from_canonical_u64(exp_vals[i]));
        }
        let output = outputs_t.last().unwrap();
        output.set_witness(&mut pw, &expected);
        let _proof = data.prove(pw).unwrap();
        println!("Fq12 u64 msm time: {:?}", now.elapsed());
    }
}

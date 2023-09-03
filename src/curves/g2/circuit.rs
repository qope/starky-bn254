use std::{marker::PhantomData, str::FromStr};

use crate::{
    curves::g2::exp::{read_g2_exp_io, G2ExpStark, G2_EXP_IO_LEN},
    utils::utils::get_u256_biguint,
};
use ark_bn254::{Fq2, G2Affine};
use ark_ec::AffineRepr;
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
    curves::g2curve_target::G2Target,
    fields::{fq2_target::Fq2Target, fq_target::FqTarget, u256_target::U256Target},
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

use super::exp::G2ExpIONative;

pub const G2_EXP_INPUT_LEN: usize = 13 * 8;

#[derive(Clone, Debug)]
pub struct G2ExpInput {
    pub x: G2Affine,
    pub offset: G2Affine,
    pub exp_val: BigUint,
}

#[derive(Clone, Debug)]
pub struct G2ExpInputTarget<F: RichField + Extendable<D>, const D: usize> {
    pub x: G2Target<F, D>,
    pub offset: G2Target<F, D>,
    pub exp_val: U256Target<F, D>,
}

impl<F: RichField + Extendable<D>, const D: usize> G2ExpInputTarget<F, D> {
    pub fn connect(builder: &mut CircuitBuilder<F, D>, lhs: &Self, rhs: &Self) {
        G2Target::connect(builder, &lhs.x, &rhs.x);
        G2Target::connect(builder, &lhs.offset, &rhs.offset);
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
    ) -> G2ExpInputTarget<F, D> {
        assert!(input.len() == G2_EXP_INPUT_LEN);
        let num_limbs = 8;
        let num_g2_limbs = 4 * num_limbs;
        let mut input = input.to_vec();
        let x_raw = input.drain(0..num_g2_limbs).collect::<Vec<_>>();
        let offset_raw = input.drain(0..num_g2_limbs).collect::<Vec<_>>();
        let exp_val_raw = input.drain(0..num_limbs).collect::<Vec<_>>();
        assert_eq!(input.len(), 0);

        let x = G2Target::from_vec(builder, &x_raw);
        let offset = G2Target::from_vec(builder, &offset_raw);
        let exp_val = U256Target::from_vec(&exp_val_raw);
        G2ExpInputTarget { x, offset, exp_val }
    }

    pub fn set_witness(&self, pw: &mut PartialWitness<F>, value: &G2ExpInput) {
        self.x.set_witness(pw, &value.x);
        self.offset.set_witness(pw, &value.offset);
        self.exp_val.set_witness(pw, &value.exp_val);
    }
}

fn g2_exp_circuit_with_proof_target<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    log_num_io: usize,
) -> (
    Vec<G2ExpInputTarget<F, D>>,
    Vec<G2Target<F, D>>,
    StarkProofWithPublicInputsTarget<D>,
)
where
    <C as GenericConfig<D>>::Hasher: AlgebraicHasher<F>,
{
    assert!(log_num_io >= 7);
    let num_io = 1 << log_num_io;
    let stark = G2ExpStark::<F, D>::new(num_io);
    let inner_config = stark.config();
    let degree_bits = 9 + log_num_io;
    let starky_proof_t =
        add_virtual_stark_proof_with_pis(builder, stark, &inner_config, degree_bits);
    verify_stark_proof_circuit::<F, C, _, D>(builder, stark, &starky_proof_t, &inner_config);
    assert!(starky_proof_t.public_inputs.len() == G2_EXP_IO_LEN * num_io);
    let mut cur_col = 0;
    let mut inputs = vec![];
    let mut outputs = vec![];
    let pi = starky_proof_t.public_inputs.clone();
    for _ in 0..num_io {
        let io = read_g2_exp_io(&pi, &mut cur_col);
        let x_x_c0 = FqTarget::from_limbs(builder, &io.x[0]);
        let x_x_c1 = FqTarget::from_limbs(builder, &io.x[1]);
        let x_y_c0 = FqTarget::from_limbs(builder, &io.x[2]);
        let x_y_c1 = FqTarget::from_limbs(builder, &io.x[3]);
        let x_x = Fq2Target::new(vec![x_x_c0, x_x_c1]);
        let x_y = Fq2Target::new(vec![x_y_c0, x_y_c1]);
        let x = G2Target::new(x_x, x_y);

        let offset_x_c0 = FqTarget::from_limbs(builder, &io.offset[0]);
        let offset_x_c1 = FqTarget::from_limbs(builder, &io.offset[1]);
        let offset_y_c0 = FqTarget::from_limbs(builder, &io.offset[2]);
        let offset_y_c1 = FqTarget::from_limbs(builder, &io.offset[3]);
        let offset_x = Fq2Target::new(vec![offset_x_c0, offset_x_c1]);
        let offset_y = Fq2Target::new(vec![offset_y_c0, offset_y_c1]);
        let offset = G2Target::new(offset_x, offset_y);

        let output_x_c0 = FqTarget::from_limbs(builder, &io.output[0]);
        let output_x_c1 = FqTarget::from_limbs(builder, &io.output[1]);
        let output_y_c0 = FqTarget::from_limbs(builder, &io.output[2]);
        let output_y_c1 = FqTarget::from_limbs(builder, &io.output[3]);
        let output_x = Fq2Target::new(vec![output_x_c0, output_x_c1]);
        let output_y = Fq2Target::new(vec![output_y_c0, output_y_c1]);
        let output = G2Target::new(output_x, output_y);
        let exp_val = U256Target::<F, D>::from_vec(&io.exp_val);
        let input = G2ExpInputTarget { x, offset, exp_val };
        inputs.push(input);
        outputs.push(output);
    }
    (inputs, outputs, starky_proof_t)
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
        let x_x_c0 = get_u256_biguint(pw, &self.input.x.x.coeffs[0].to_vec());
        let x_x_c1 = get_u256_biguint(pw, &self.input.x.x.coeffs[1].to_vec());
        let x_y_c0 = get_u256_biguint(pw, &self.input.x.y.coeffs[0].to_vec());
        let x_y_c1 = get_u256_biguint(pw, &self.input.x.y.coeffs[1].to_vec());
        let x_x = Fq2::new(x_x_c0.into(), x_x_c1.into());
        let x_y = Fq2::new(x_y_c0.into(), x_y_c1.into());
        let x = G2Affine::new_unchecked(x_x, x_y);

        let offset_x_c0 = get_u256_biguint(pw, &self.input.offset.x.coeffs[0].to_vec());
        let offset_x_c1 = get_u256_biguint(pw, &self.input.offset.x.coeffs[1].to_vec());
        let offset_y_c0 = get_u256_biguint(pw, &self.input.offset.y.coeffs[0].to_vec());
        let offset_y_c1 = get_u256_biguint(pw, &self.input.offset.y.coeffs[1].to_vec());
        let offset_x = Fq2::new(offset_x_c0.into(), offset_x_c1.into());
        let offset_y = Fq2::new(offset_y_c0.into(), offset_y_c1.into());
        let offset = G2Affine::new(offset_x, offset_y);

        let exp_val = get_u256_biguint(pw, &self.input.exp_val.to_vec());
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
                let x_x_c0 = get_u256_biguint(pw, &input.x.x.coeffs[0].to_vec());
                let x_x_c1 = get_u256_biguint(pw, &input.x.x.coeffs[1].to_vec());
                let x_y_c0 = get_u256_biguint(pw, &input.x.y.coeffs[0].to_vec());
                let x_y_c1 = get_u256_biguint(pw, &input.x.y.coeffs[1].to_vec());
                let x_x = Fq2::new(x_x_c0.into(), x_x_c1.into());
                let x_y = Fq2::new(x_y_c0.into(), x_y_c1.into());
                let x = G2Affine::new_unchecked(x_x, x_y);

                let offset_x_c0 = get_u256_biguint(pw, &input.offset.x.coeffs[0].to_vec());
                let offset_x_c1 = get_u256_biguint(pw, &input.offset.x.coeffs[1].to_vec());
                let offset_y_c0 = get_u256_biguint(pw, &input.offset.y.coeffs[0].to_vec());
                let offset_y_c1 = get_u256_biguint(pw, &input.offset.y.coeffs[1].to_vec());
                let offset_x = Fq2::new(offset_x_c0.into(), offset_x_c1.into());
                let offset_y = Fq2::new(offset_y_c0.into(), offset_y_c1.into());
                let offset = G2Affine::new(offset_x, offset_y);
                let exp_val = get_u256_biguint(pw, &input.exp_val.to_vec());
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
            .collect::<Vec<_>>();

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

#[cfg(test)]
mod tests {
    use crate::curves::g2::circuit::{
        g2_exp_circuit, g2_mul_by_cofactor_circuit, G2ExpInputTarget,
    };
    use ark_bn254::{Fq2, Fr, G2Affine};
    use ark_ec::AffineRepr;
    use ark_std::UniformRand;
    use itertools::Itertools;
    use num_bigint::BigUint;
    use plonky2::{
        field::goldilocks_field::GoldilocksField,
        iop::witness::PartialWitness,
        plonk::{
            circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
            config::PoseidonGoldilocksConfig,
        },
    };
    use plonky2_bn254::{
        curves::{g2curve_target::G2Target, map_to_g2::map_to_g2_without_cofactor_mul},
        fields::u256_target::U256Target,
    };
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
}

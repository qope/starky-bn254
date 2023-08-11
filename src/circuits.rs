use crate::{
    flags::NUM_INPUT_LIMBS,
    g1_exp::{g1_exp_circuit_with_proof_target, G1ExpIO, G1ExpIONative, G1ExpStark},
    g2_exp::{g2_exp_circuit_with_proof_target, G2ExpIO, G2ExpIONative, G2ExpStark},
    utils::u32_digits_to_biguint,
};
use ark_bn254::{Fq2, Fr, G1Affine, G2Affine};
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
    util::timing::TimingTree,
};
use starky::{
    proof::StarkProofWithPublicInputsTarget, prover::prove,
    recursive_verifier::set_stark_proof_with_pis_target, verifier::verify_stark_proof,
};

#[derive(Clone, Debug)]
pub struct G1ExpStarkyProofGenerator<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
> {
    pub ios: Vec<G1ExpIO<Target>>,
    pub starky_proof: StarkProofWithPublicInputsTarget<D>,
    _config: std::marker::PhantomData<C>,
}

impl<F: RichField + Extendable<D>, C: GenericConfig<D, F = F>, const D: usize>
    G1ExpStarkyProofGenerator<F, C, D>
{
    pub fn new(builder: &mut CircuitBuilder<F, D>, log_num_io: usize) -> Self
    where
        C::Hasher: AlgebraicHasher<F>,
    {
        let (ios, starky_proof) = g1_exp_circuit_with_proof_target::<F, C, D>(builder, log_num_io);
        Self {
            ios,
            starky_proof,
            _config: std::marker::PhantomData,
        }
    }
}

impl<F, C, const D: usize> SimpleGenerator<F> for G1ExpStarkyProofGenerator<F, C, D>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    C::Hasher: AlgebraicHasher<F>,
{
    fn dependencies(&self) -> Vec<Target> {
        let mut dep_vec = vec![];
        // x, offset, exp_val
        self.ios.iter().cloned().for_each(|io| {
            dep_vec.extend(io.x[0]);
            dep_vec.extend(io.x[1]);
            dep_vec.extend(io.offset[0]);
            dep_vec.extend(io.offset[1]);
            dep_vec.extend(io.exp_val);
        });
        dep_vec
    }
    fn run_once(&self, pw: &PartitionWitness<F>, out_buffer: &mut GeneratedValues<F>) {
        let get_biguint = |x: [Target; NUM_INPUT_LIMBS]| -> BigUint {
            let x_value = x
                .iter()
                .map(|x| pw.get_target(*x).to_canonical_u64() as u32)
                .collect_vec();
            u32_digits_to_biguint(&x_value)
        };

        let get_u32 = |x: [Target; NUM_INPUT_LIMBS]| -> [u32; NUM_INPUT_LIMBS] {
            let x_value = x
                .iter()
                .map(|x| pw.get_target(*x).to_canonical_u64() as u32)
                .collect_vec();
            x_value.try_into().unwrap()
        };

        let ios_native = self
            .ios
            .iter()
            .cloned()
            .map(|io| {
                let x_x = get_biguint(io.x[0]);
                let x_y = get_biguint(io.x[1]);
                let offset_x = get_biguint(io.offset[0]);
                let offset_y = get_biguint(io.offset[1]);
                let exp_val = get_biguint(io.exp_val);
                let x = G1Affine::new(x_x.into(), x_y.into());
                let offset = G1Affine::new(offset_x.into(), offset_y.into());
                let exp_val_u32 = get_u32(io.exp_val);
                let exp_val: Fr = exp_val.into();
                let output: G1Affine = (x * exp_val + offset).into();
                G1ExpIONative {
                    x,
                    offset,
                    exp_val: exp_val_u32,
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
        self.ios
            .iter()
            .zip(ios_native.iter())
            .for_each(|(io, native)| {
                io.set_witness(out_buffer, native);
            });
    }
}

pub fn g1_exp_circuit<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    log_num_io: usize,
) -> Vec<G1ExpIO<Target>>
where
    C::Hasher: AlgebraicHasher<F>,
{
    let generator = G1ExpStarkyProofGenerator::<F, C, D>::new(builder, log_num_io);
    let ios = generator.ios.clone();
    builder.add_simple_generator(generator);
    ios
}

#[derive(Clone, Debug)]
pub struct G2ExpStarkyProofGenerator<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
> {
    pub ios: Vec<G2ExpIO<Target>>,
    pub starky_proof: StarkProofWithPublicInputsTarget<D>,
    _config: std::marker::PhantomData<C>,
}

impl<F: RichField + Extendable<D>, C: GenericConfig<D, F = F>, const D: usize>
    G2ExpStarkyProofGenerator<F, C, D>
{
    pub fn new(builder: &mut CircuitBuilder<F, D>, log_num_io: usize) -> Self
    where
        C::Hasher: AlgebraicHasher<F>,
    {
        let (ios, starky_proof) = g2_exp_circuit_with_proof_target::<F, C, D>(builder, log_num_io);
        Self {
            ios,
            starky_proof,
            _config: std::marker::PhantomData,
        }
    }
}

impl<F, C, const D: usize> SimpleGenerator<F> for G2ExpStarkyProofGenerator<F, C, D>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    C::Hasher: AlgebraicHasher<F>,
{
    fn dependencies(&self) -> Vec<Target> {
        let mut dep_vec = vec![];
        // x, offset, exp_val
        self.ios.iter().cloned().for_each(|io| {
            dep_vec.extend(io.x[0]);
            dep_vec.extend(io.x[1]);
            dep_vec.extend(io.x[2]);
            dep_vec.extend(io.x[3]);
            dep_vec.extend(io.offset[0]);
            dep_vec.extend(io.offset[1]);
            dep_vec.extend(io.offset[2]);
            dep_vec.extend(io.offset[3]);
            dep_vec.extend(io.exp_val);
        });
        dep_vec
    }
    fn run_once(&self, pw: &PartitionWitness<F>, out_buffer: &mut GeneratedValues<F>) {
        let get_biguint = |x: [Target; NUM_INPUT_LIMBS]| -> BigUint {
            let x_value = x
                .iter()
                .map(|x| pw.get_target(*x).to_canonical_u64() as u32)
                .collect_vec();
            u32_digits_to_biguint(&x_value)
        };

        let get_u32 = |x: [Target; NUM_INPUT_LIMBS]| -> [u32; NUM_INPUT_LIMBS] {
            let x_value = x
                .iter()
                .map(|x| pw.get_target(*x).to_canonical_u64() as u32)
                .collect_vec();
            x_value.try_into().unwrap()
        };

        let ios_native = self
            .ios
            .iter()
            .cloned()
            .map(|io| {
                let x_x_c0 = get_biguint(io.x[0]);
                let x_x_c1 = get_biguint(io.x[1]);
                let x_y_c0 = get_biguint(io.x[2]);
                let x_y_c1 = get_biguint(io.x[3]);
                let offset_x_c0 = get_biguint(io.offset[0]);
                let offset_x_c1 = get_biguint(io.offset[1]);
                let offset_y_c0 = get_biguint(io.offset[2]);
                let offset_y_c1 = get_biguint(io.offset[3]);
                let exp_val = get_biguint(io.exp_val);
                let x_x = Fq2::new(x_x_c0.into(), x_x_c1.into());
                let x_y = Fq2::new(x_y_c0.into(), x_y_c1.into());
                let x = G2Affine::new(x_x, x_y);
                let offset_x = Fq2::new(offset_x_c0.into(), offset_x_c1.into());
                let offset_y = Fq2::new(offset_y_c0.into(), offset_y_c1.into());
                let offset = G2Affine::new(offset_x, offset_y);
                let exp_val_u32 = get_u32(io.exp_val);
                let exp_val: Fr = exp_val.into();
                let output: G2Affine = (x * exp_val + offset).into();
                G2ExpIONative {
                    x,
                    offset,
                    exp_val: exp_val_u32,
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

        self.ios
            .iter()
            .zip(ios_native.iter())
            .for_each(|(io, native)| {
                io.set_witness(out_buffer, native);
            });
    }
}

pub fn g2_exp_circuit<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    log_num_io: usize,
) -> Vec<G2ExpIO<Target>>
where
    C::Hasher: AlgebraicHasher<F>,
{
    let generator = G2ExpStarkyProofGenerator::<F, C, D>::new(builder, log_num_io);
    let ios = generator.ios.clone();
    builder.add_simple_generator(generator);
    ios
}
#[cfg(test)]
mod tests {
    use ark_bn254::{Fr, G1Affine, G2Affine};
    use ark_ec::AffineRepr;
    use ark_std::UniformRand;
    use itertools::Itertools;
    use plonky2::{
        field::{goldilocks_field::GoldilocksField, types::Field},
        iop::{generator, witness::PartialWitness},
        plonk::{
            circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
            config::PoseidonGoldilocksConfig,
        },
    };

    use crate::{
        circuits::{g1_exp_circuit, g2_exp_circuit},
        flags::NUM_INPUT_LIMBS,
        g1_exp::G1ExpIONative,
        g2_exp::G2ExpIONative,
        utils::{fq_to_u32_columns, u32_digits_to_biguint},
    };

    #[test]
    fn test_g1_exp_circuit() {
        let mut rng = rand::thread_rng();
        type F = GoldilocksField;
        type C = PoseidonGoldilocksConfig;
        const D: usize = 2;
        let log_num_io = 7;
        let num_io = 1 << log_num_io;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let ios = g1_exp_circuit::<F, C, D>(&mut builder, log_num_io);

        let mut pw = PartialWitness::<F>::new();
        let inputs = (0..num_io)
            .map(|_| {
                let exp_val: [u32; NUM_INPUT_LIMBS] = rand::random();
                let exp_val_fr: Fr = u32_digits_to_biguint(&exp_val).into();
                let x = G1Affine::rand(&mut rng);
                let offset = G1Affine::rand(&mut rng);
                let output: G1Affine = (x * exp_val_fr + offset).into();
                G1ExpIONative {
                    x,
                    offset,
                    exp_val,
                    output,
                }
            })
            .collect_vec();

        ios.iter()
            .zip(inputs.iter())
            .for_each(|(io, input)| io.set_witness(&mut pw, input));
        let data = builder.build::<C>();
        let _proof = data.prove(pw).unwrap();
    }

    #[test]
    fn test_g1_msm_circuit() {
        let mut rng = rand::thread_rng();
        type F = GoldilocksField;
        type C = PoseidonGoldilocksConfig;
        const D: usize = 2;
        let log_num_io = 7;
        let num_io = 1 << log_num_io;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let ios = g1_exp_circuit::<F, C, D>(&mut builder, log_num_io);

        let mut pw = PartialWitness::<F>::new();

        let exp_vals: Vec<[u32; NUM_INPUT_LIMBS]> = (0..num_io).map(|_| rand::random()).collect();
        let basis = (0..num_io).map(|_| G1Affine::rand(&mut rng)).collect_vec();
        let expected = {
            let mut expected = G1Affine::generator();
            for (exp_val, &basis) in exp_vals.iter().zip(basis.iter()) {
                let exp_val_fr: Fr = u32_digits_to_biguint(exp_val).into();
                expected = (expected + basis * exp_val_fr).into();
            }
            expected
        };
        let generator = G1Affine::generator();
        let generator_limbs_x: [F; 8] = fq_to_u32_columns(generator.x);
        let generator_x_t = generator_limbs_x
            .iter()
            .map(|x| builder.constant(*x))
            .collect_vec();
        let generator_limbs_y: [F; 8] = fq_to_u32_columns(generator.y);
        let generator_y_t = generator_limbs_y
            .iter()
            .map(|x| builder.constant(*x))
            .collect_vec();
        // let basis_limbs: Vec<_> = basis.iter().map(|x| fq_to_u32_columns(x.x)).collect();
        // let mut offset =

        let inputs = (0..num_io)
            .map(|_| {
                let exp_val: [u32; NUM_INPUT_LIMBS] = rand::random();
                let exp_val_fr: Fr = u32_digits_to_biguint(&exp_val).into();
                let x = G1Affine::rand(&mut rng);
                let offset = G1Affine::rand(&mut rng);
                let output: G1Affine = (x * exp_val_fr + offset).into();
                G1ExpIONative {
                    x,
                    offset,
                    exp_val,
                    output,
                }
            })
            .collect_vec();

        ios.iter()
            .zip(inputs.iter())
            .for_each(|(io, input)| io.set_witness(&mut pw, input));
        let data = builder.build::<C>();
        let _proof = data.prove(pw).unwrap();
    }

    #[test]
    fn test_g2_exp_circuit() {
        let mut rng = rand::thread_rng();
        type F = GoldilocksField;
        type C = PoseidonGoldilocksConfig;
        const D: usize = 2;
        let log_num_io = 7;
        let num_io = 1 << log_num_io;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let ios = g2_exp_circuit::<F, C, D>(&mut builder, log_num_io);

        let mut pw = PartialWitness::<F>::new();
        let inputs = (0..num_io)
            .map(|_| {
                let exp_val: [u32; NUM_INPUT_LIMBS] = rand::random();
                let exp_val_fr: Fr = u32_digits_to_biguint(&exp_val).into();
                let x = G2Affine::rand(&mut rng);
                let offset = G2Affine::rand(&mut rng);
                let output: G2Affine = (x * exp_val_fr + offset).into();
                G2ExpIONative {
                    x,
                    offset,
                    exp_val,
                    output,
                }
            })
            .collect_vec();

        ios.iter()
            .zip(inputs.iter())
            .for_each(|(io, input)| io.set_witness(&mut pw, input));
        let data = builder.build::<C>();
        let _proof = data.prove(pw).unwrap();
    }
}

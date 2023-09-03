use std::marker::PhantomData;

use ark_bn254::Fq;
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
use plonky2_bn254::fields::{fq_target::FqTarget, u256_target::U256Target};
use starky::{
    proof::StarkProofWithPublicInputsTarget,
    prover::prove,
    recursive_verifier::{
        add_virtual_stark_proof_with_pis, set_stark_proof_with_pis_target,
        verify_stark_proof_circuit,
    },
    verifier::verify_stark_proof,
};

use crate::fields::fq::exp::{read_fq_exp_io, FqExpStark, FQ_EXP_IO_LEN};
use crate::{fields::fq::exp::FqExpIONative, utils::utils::get_u256_biguint};
pub const FQ_EXP_INPUT_LEN: usize = 3 * 8;

#[derive(Clone, Debug)]
pub struct FqExpInput {
    pub x: Fq,
    pub offset: Fq,
    pub exp_val: BigUint,
}

#[derive(Clone, Debug)]
pub struct FqExpInputTarget<F: RichField + Extendable<D>, const D: usize> {
    pub x: FqTarget<F, D>,
    pub offset: FqTarget<F, D>,
    pub exp_val: U256Target<F, D>,
}

impl<F: RichField + Extendable<D>, const D: usize> FqExpInputTarget<F, D> {
    pub fn connect(builder: &mut CircuitBuilder<F, D>, lhs: &Self, rhs: &Self) {
        FqTarget::connect(builder, &lhs.x, &rhs.x);
        FqTarget::connect(builder, &lhs.offset, &rhs.offset);
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
    pub fn from_vec(builder: &mut CircuitBuilder<F, D>, input: &[Target]) -> Self {
        assert!(input.len() == FQ_EXP_INPUT_LEN);
        let num_limbs = 8;
        let mut input = input.to_vec();
        let x_raw = input.drain(0..num_limbs).collect_vec();
        let offset_raw = input.drain(0..num_limbs).collect_vec();
        let exp_val_raw = input.drain(0..num_limbs).collect_vec();
        assert_eq!(input.len(), 0);

        let x = FqTarget::from_vec(builder, &x_raw);
        let offset = FqTarget::from_vec(builder, &offset_raw);
        let exp_val = U256Target::from_vec(&exp_val_raw);
        Self { x, offset, exp_val }
    }

    pub fn set_witness(&self, pw: &mut PartialWitness<F>, value: &FqExpInput) {
        self.x.set_witness(pw, &value.x);
        self.offset.set_witness(pw, &value.offset);
        self.exp_val.set_witness(pw, &value.exp_val);
    }
}

fn fq_exp_circuit_with_proof_target<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    log_num_io: usize,
) -> (
    Vec<FqExpInputTarget<F, D>>,
    Vec<FqTarget<F, D>>,
    StarkProofWithPublicInputsTarget<D>,
)
where
    <C as GenericConfig<D>>::Hasher: AlgebraicHasher<F>,
{
    assert!(log_num_io >= 7);
    let num_io = 1 << log_num_io;
    let stark = FqExpStark::<F, D>::new(num_io);
    let inner_config = stark.config();
    let degree_bits = 9 + log_num_io;
    let starky_proof_t =
        add_virtual_stark_proof_with_pis(builder, stark, &inner_config, degree_bits);
    verify_stark_proof_circuit::<F, C, _, D>(builder, stark, &starky_proof_t, &inner_config);
    assert!(starky_proof_t.public_inputs.len() == FQ_EXP_IO_LEN * num_io);
    let mut cur_col = 0;
    let mut inputs = vec![];
    let mut outputs = vec![];
    let pi = starky_proof_t.public_inputs.clone();
    for _ in 0..num_io {
        let io = read_fq_exp_io(&pi, &mut cur_col);
        let x = FqTarget::from_limbs(builder, &io.x);
        let offset = FqTarget::from_limbs(builder, &io.offset);
        let output = FqTarget::from_limbs(builder, &io.output);
        let exp_val = U256Target::<F, D>::from_vec(&io.exp_val);
        let input = FqExpInputTarget { x, offset, exp_val };
        inputs.push(input);
        outputs.push(output);
    }
    (inputs, outputs, starky_proof_t)
}

#[derive(Clone, Debug)]
pub struct FqExpOutputGenerator<F: RichField + Extendable<D>, const D: usize> {
    pub input: FqExpInputTarget<F, D>,
    pub output: FqTarget<F, D>,
}

impl<F, const D: usize> SimpleGenerator<F> for FqExpOutputGenerator<F, D>
where
    F: RichField + Extendable<D>,
{
    fn dependencies(&self) -> Vec<Target> {
        self.input.to_vec()
    }

    fn run_once(&self, pw: &PartitionWitness<F>, out_buffer: &mut GeneratedValues<F>) {
        let x = get_u256_biguint(pw, &self.input.x.to_vec());
        let offset = get_u256_biguint(pw, &self.input.offset.to_vec());
        let exp_val = get_u256_biguint(pw, &self.input.exp_val.to_vec());
        let x = Fq::from(x);
        let offset = Fq::from(offset);
        use ark_ff::Field;
        let output = x.pow(&exp_val.to_u64_digits()) * offset;
        self.output.set_witness(out_buffer, &output);
    }

    fn id(&self) -> String {
        "FqExpOutputGenerator".to_string()
    }
    fn serialize(&self, _dst: &mut Vec<u8>) -> plonky2::util::serialization::IoResult<()> {
        todo!()
    }
    fn deserialize(_src: &mut Buffer) -> plonky2::util::serialization::IoResult<Self> {
        todo!()
    }
}

#[derive(Clone, Debug)]
pub struct FqExpStarkyProofGenerator<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
> {
    pub inputs: Vec<FqExpInputTarget<F, D>>,
    pub outputs: Vec<FqTarget<F, D>>,
    pub starky_proof: StarkProofWithPublicInputsTarget<D>,
    _config: std::marker::PhantomData<C>,
}

impl<F, C, const D: usize> SimpleGenerator<F> for FqExpStarkyProofGenerator<F, C, D>
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
                let x = get_u256_biguint(pw, &input.x.to_vec());
                let offset = get_u256_biguint(pw, &input.offset.to_vec());
                let exp_val = get_u256_biguint(pw, &input.exp_val.to_vec());
                let x = Fq::from(x);
                let offset = Fq::from(offset);
                use ark_ff::Field;
                let output = x.pow(&exp_val.to_u64_digits()) * offset;
                let mut exp_val_u32 = exp_val.to_u32_digits();
                exp_val_u32.extend(vec![0; 8 - exp_val_u32.len()]);
                FqExpIONative {
                    x,
                    offset,
                    exp_val: exp_val_u32.try_into().unwrap(),
                    output,
                }
            })
            .collect_vec();

        let num_io = ios_native.len();
        let stark = FqExpStark::<F, D>::new(num_io);
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
        "FqExpStarkyProofGenerator".to_string()
    }
    fn serialize(&self, _dst: &mut Vec<u8>) -> plonky2::util::serialization::IoResult<()> {
        todo!()
    }
    fn deserialize(_src: &mut Buffer) -> plonky2::util::serialization::IoResult<Self> {
        todo!()
    }
}

pub fn fq_exp_circuit<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    inputs: &[FqExpInputTarget<F, D>],
) -> Vec<FqTarget<F, D>>
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
        fq_exp_circuit_with_proof_target::<F, C, D>(builder, log_num_io);

    for (input_c, input) in inputs_constr.iter().zip(inputs.iter()) {
        FqExpInputTarget::connect(builder, input_c, input);
    }

    for (input, output) in inputs.iter().zip(outputs.iter()) {
        let output_generator = FqExpOutputGenerator {
            input: input.to_owned(),
            output: output.to_owned(),
        };
        builder.add_simple_generator(output_generator);
    }

    let proof_generator = FqExpStarkyProofGenerator::<F, C, D> {
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

    use ark_bn254::Fq;

    use ark_ff::Field;
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
    use plonky2_bn254::fields::{fq_target::FqTarget, u256_target::U256Target};

    use crate::{
        fields::fq::circuit::{fq_exp_circuit, FqExpInput, FqExpInputTarget},
        utils::{flags::NUM_INPUT_LIMBS, utils::u32_digits_to_biguint},
    };

    #[test]
    fn test_fq_exp_circuit_with_generator() {
        let mut rng = rand::thread_rng();
        type F = GoldilocksField;
        type C = PoseidonGoldilocksConfig;
        const D: usize = 2;
        let num_io = 127;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let inputs_t = (0..num_io)
            .map(|_| {
                let x = FqTarget::empty(&mut builder);
                let offset = FqTarget::empty(&mut builder);
                let exp_val = U256Target::empty(&mut builder);
                FqExpInputTarget { x, offset, exp_val }
            })
            .collect_vec();

        let outputs_t = fq_exp_circuit::<F, C, D>(&mut builder, &inputs_t);

        let mut pw = PartialWitness::<F>::new();
        let mut inputs = vec![];
        let mut outputs = vec![];
        for _ in 0..num_io {
            let exp_val: [u32; NUM_INPUT_LIMBS] = rand::random();
            let exp_val_b = u32_digits_to_biguint(&exp_val);
            let x = Fq::rand(&mut rng);
            let offset = Fq::rand(&mut rng);
            let output = x.pow(&exp_val_b.to_u64_digits()) * offset;
            let input = FqExpInput {
                x,
                offset,
                exp_val: exp_val_b,
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

use ark_bn254::G1Affine;
use itertools::Itertools;
use num_bigint::BigUint;
use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::{target::Target, witness::PartialWitness},
    plonk::circuit_builder::CircuitBuilder,
};
use plonky2_bn254::{curves::g1curve_target::G1Target, fields::u256_target::U256Target};

pub const G1_EXP_INPUT_LEN: usize = 5 * 8;
// pub const G2_EXP_STATEMENT_LEN: usize = 13 * 8;
// pub const FQ12_EXP_STATEMENT_LEN: usize = 12 * 8 * 3 + 8;

pub struct G1ExpInput {
    pub x: G1Affine,
    pub offset: G1Affine,
    pub exp_val: BigUint,
}

pub struct G1ExpInputTarget<F: RichField + Extendable<D>, const D: usize> {
    pub x: G1Target<F, D>,
    pub offset: G1Target<F, D>,
    pub exp_val: U256Target<F, D>,
}

// pub struct G2ExpStatement<F: RichField + Extendable<D>, const D: usize> {
//     pub x: G2Target<F, D>,
//     pub offset: G2Target<F, D>,
//     pub exp_val: U256Target<F, D>,
//     pub output: G2Target<F, D>,
// }

// pub struct Fq12ExpStatement<F: RichField + Extendable<D>, const D: usize> {
//     pub x: Fq12Target<F, D>,
//     pub offset: Fq12Target<F, D>,
//     pub exp_val: U256Target<F, D>,
//     pub output: Fq12Target<F, D>,
// }

impl<F: RichField + Extendable<D>, const D: usize> G1ExpInputTarget<F, D> {
    pub fn connect(builder: &mut CircuitBuilder<F, D>, lhs: &Self, rhs: &Self) {
        G1Target::connect(builder, &lhs.x, &rhs.x);
        G1Target::connect(builder, &lhs.offset, &rhs.offset);
        U256Target::connect(builder, &lhs.exp_val, &rhs.exp_val);
    }
}

// impl<F: RichField + Extendable<D>, const D: usize> G2ExpStatement<F, D> {
//     pub fn connect(builder: &mut CircuitBuilder<F, D>, lhs: &Self, rhs: &Self) {
//         G2Target::connect(builder, &lhs.x, &rhs.x);
//         G2Target::connect(builder, &lhs.offset, &rhs.offset);
//         U256Target::connect(builder, &lhs.exp_val, &rhs.exp_val);
//         G2Target::connect(builder, &lhs.output, &rhs.output);
//     }
// }

// impl<F: RichField + Extendable<D>, const D: usize> Fq12ExpStatement<F, D> {
//     pub fn connect(builder: &mut CircuitBuilder<F, D>, lhs: &Self, rhs: &Self) {
//         Fq12Target::connect(builder, &lhs.x, &rhs.x);
//         Fq12Target::connect(builder, &lhs.offset, &rhs.offset);
//         U256Target::connect(builder, &lhs.exp_val, &rhs.exp_val);
//         Fq12Target::connect(builder, &lhs.output, &rhs.output);
//     }
// }

impl<F: RichField + Extendable<D>, const D: usize> G1ExpInputTarget<F, D> {
    // 7*8
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
    ) -> G1ExpInputTarget<F, D> {
        assert!(input.len() == G1_EXP_INPUT_LEN);
        let num_limbs = 8;
        let num_g1_limbs = 2 * num_limbs;
        let mut input = input.to_vec();
        let x_raw = input.drain(0..num_g1_limbs).collect_vec();
        let offset_raw = input.drain(0..num_g1_limbs).collect_vec();
        let exp_val_raw = input.drain(0..num_limbs).collect_vec();
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

// impl<F: RichField + Extendable<D>, const D: usize> G2ExpStatement<F, D> {
//     //13*8=104
//     pub fn to_vec(&self) -> Vec<Target> {
//         self.x
//             .to_vec()
//             .iter()
//             .chain(self.offset.to_vec().iter())
//             .chain(self.exp_val.to_vec().iter())
//             .chain(self.output.to_vec().iter())
//             .cloned()
//             .collect_vec()
//     }
//     pub fn from_vec(builder: &mut CircuitBuilder<F, D>, input: &[Target]) -> G2ExpStatement<F, D> {
//         assert!(input.len() == G2_EXP_STATEMENT_LEN);
//         let num_limbs = 8;
//         let num_g2_limbs = 4 * num_limbs;
//         let mut input = input.to_vec();
//         let x_raw = input.drain(0..num_g2_limbs).collect_vec();
//         let offset_raw = input.drain(0..num_g2_limbs).collect_vec();
//         let exp_val_raw = input.drain(0..num_limbs).collect_vec();
//         let output_raw = input.drain(0..num_g2_limbs).collect_vec();
//         assert_eq!(input.len(), 0);

//         let x = G2Target::from_vec(builder, &x_raw);
//         let offset = G2Target::from_vec(builder, &offset_raw);
//         let exp_val = U256Target::from_vec(&exp_val_raw);
//         let output = G2Target::from_vec(builder, &output_raw);
//         G2ExpStatement {
//             x,
//             offset,
//             exp_val,
//             output,
//         }
//     }
//     pub fn set_witness(&self, pw: &mut PartialWitness<F>, value: &G2ExpWitness) {
//         self.x.set_witness(pw, &value.x);
//         self.offset.set_witness(pw, &value.offset);
//         self.exp_val.set_witness(pw, &value.exp_val);
//         self.output.set_witness(pw, &value.output);
//     }
// }

// impl<F: RichField + Extendable<D>, const D: usize> Fq12ExpStatement<F, D> {
//     //12*8*3+8=296
//     pub fn to_vec(&self) -> Vec<Target> {
//         self.x
//             .to_vec()
//             .iter()
//             .chain(self.offset.to_vec().iter())
//             .chain(self.exp_val.to_vec().iter())
//             .chain(self.output.to_vec().iter())
//             .cloned()
//             .collect_vec()
//     }
//     pub fn from_vec(
//         builder: &mut CircuitBuilder<F, D>,
//         input: &[Target],
//     ) -> Fq12ExpStatement<F, D> {
//         assert!(input.len() == FQ12_EXP_STATEMENT_LEN);
//         let num_limbs = 8;
//         let num_fq12_limbs = 12 * num_limbs;
//         let mut input = input.to_vec();
//         let x_raw = input.drain(0..num_fq12_limbs).collect_vec();
//         let offset_raw = input.drain(0..num_fq12_limbs).collect_vec();
//         let exp_val_raw = input.drain(0..num_limbs).collect_vec();
//         let output_raw = input.drain(0..num_fq12_limbs).collect_vec();
//         assert_eq!(input.len(), 0);

//         let x = Fq12Target::from_vec(builder, &x_raw);
//         let offset = Fq12Target::from_vec(builder, &offset_raw);
//         let exp_val = U256Target::from_vec(&exp_val_raw);
//         let output = Fq12Target::from_vec(builder, &output_raw);
//         Fq12ExpStatement {
//             x,
//             offset,
//             exp_val,
//             output,
//         }
//     }
//     pub fn set_witness(&self, pw: &mut PartialWitness<F>, value: &Fq12ExpWitness) {
//         self.x.set_witness(pw, &value.x);
//         self.offset.set_witness(pw, &value.offset);
//         self.exp_val.set_witness(pw, &value.exp_val);
//         self.output.set_witness(pw, &value.output);
//     }
// }

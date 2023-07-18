// generate flags
// in the case of val0 = 1101, val1 = 1011, val2=0
// r | a | b | b'| bit | val0 | val1
// -------------------------------
// 0 | 0 | 1 | 1 | 1  | 101       <- public input (1 + 2*101 = val0, val1)
// 0 | 1 | 0 | 0 | ?  | 101       <- split
// 0 | 0 | 1 | 1 | 1  | 01
// 0 | 1 | 0 | 0 | ?  | 01        <- split
// 0 | 0 | 1 | 0 | 0  | 1
// 0 | 1 | 0 | 0 | ?  | 1         <- split
// 1 | 0 | 1 | 1 | 1  | 0         <- rotate (r=8-2)
// 0 | 1 | 0 | 0 | ?  | val1      <- split (<- output)
// 0 | 0 | 1 | 1 | 1  | 011
// 0 | 1 | 0 | 0 | ?  | 011       <- split
// 0 | 0 | 1 | 0 | 0  | 11
// 0 | 1 | 0 | 0 | ?  | 11        <- split
// 0 | 0 | 1 | 1 | 1  | 1
// 0 | 1 | 0 | 0 | ?  | 1         <- split
// 1 | 0 | 1 | 1 | 1  | 0         <- rotate (r=16-2)
// 0 | 1 | 0 | 0 | ?  | 0         <- public output

// overall, we need 2*bits_len rows.
// split vals at r = 2*i + 1, and rotate at r = 2*limb_bits*(i+1) - 2
// we need 8 limbs cols

// normal colsとwitness colsがある。
// normal colsは遷移的に生成するのが良く、witness colsは最後にまとめて生成するのが良い

use plonky2::hash::hash_types::RichField;

const NUM_INPUT_LIMBS: usize = 8;
const INPUT_LIMB_BITS: usize = 32;

// generate flags for the first row
// 5 + NUM_INPUT_LIMBS cols are generated
pub fn generate_flags_first_row<F: RichField>(
    lv: &mut [F],
    start_flag_col: usize,
    limbs: [u32; NUM_INPUT_LIMBS],
) {
    let is_rotate_col = start_flag_col;
    let a_col = start_flag_col + 1;
    let b_col = start_flag_col + 2;
    let filtered_bit_col = start_flag_col + 3;
    let bit_col = start_flag_col + 4;
    let start_limbs = start_flag_col + 5;
    let end_limbs = start_limbs + NUM_INPUT_LIMBS;

    let first_limb = limbs[0];
    let first_bit = first_limb % 2;
    let rest = (first_limb - first_bit) / 2;
    let mut new_limbs = limbs;
    new_limbs[0] = rest;

    lv[is_rotate_col] = F::ZERO;
    lv[a_col] = F::ZERO;
    lv[b_col] = F::ONE;
    lv[filtered_bit_col] = F::from_canonical_u32(first_bit);
    lv[bit_col] = F::from_canonical_u32(first_bit);
    for (i, col) in (start_limbs..end_limbs).enumerate() {
        lv[col] = F::from_canonical_u32(new_limbs[i]);
    }
}

pub fn generate_flags_next_row<F: RichField>(
    lv: &[F],
    nv: &mut [F],
    cur_row: usize,
    start_flag_col: usize,
) {
    let is_rotate_col = start_flag_col;
    let a_col = start_flag_col + 1;
    let b_col = start_flag_col + 2;
    let filtered_bit_col = start_flag_col + 3;
    let bit_col = start_flag_col + 4;
    let start_limbs = start_flag_col + 5;
    let end_limbs = start_limbs + NUM_INPUT_LIMBS;

    nv[a_col] = F::ONE - lv[a_col];
    nv[b_col] = F::ONE - lv[b_col];

    if cur_row % (2 * INPUT_LIMB_BITS) == 2 * INPUT_LIMB_BITS - 3 {
        nv[is_rotate_col] = F::ONE; // is_rotate_col is one at r = 2*INPUT_LIMB_BITS*(i+1) - 2
    } else {
        nv[is_rotate_col] = F::ZERO;
    }

    if lv[a_col] == F::ONE {
        // split
        let first_limb = lv[start_limbs].to_canonical_u64();
        let next_bit = first_limb % 2;
        let next_first_limb = (first_limb - next_bit) / 2;
        nv[bit_col] = F::from_canonical_u64(next_bit);
        nv[start_limbs] = F::from_canonical_u64(next_first_limb);
    } else {
        // no split
        nv[bit_col] = lv[bit_col];
        nv[start_limbs] = lv[start_limbs];
    }

    if lv[is_rotate_col] == F::ONE {
        // rotate
        for col in start_limbs + 1..end_limbs {
            nv[col - 1] = lv[col];
        }
        nv[end_limbs - 1] = F::ZERO;
    } else {
        // no rotate
        for col in start_limbs + 1..end_limbs {
            nv[col] = lv[col]; // copy limbs except for the first limb
        }
    }
    nv[filtered_bit_col] = nv[bit_col] * nv[b_col];
}

#[cfg(test)]
mod tests {
    use bitvec::prelude::*;
    use itertools::Itertools;
    use plonky2::field::{
        goldilocks_field::GoldilocksField,
        types::{Field, PrimeField64},
    };

    use crate::flags::{INPUT_LIMB_BITS, NUM_INPUT_LIMBS};

    use super::{generate_flags_first_row, generate_flags_next_row};

    type F = GoldilocksField;

    #[test]
    fn test_flag() {
        let input_limbs: [u32; NUM_INPUT_LIMBS] = rand::random();
        let mut lv = vec![F::ZERO; 5 + NUM_INPUT_LIMBS];

        let num_rows = 2 * INPUT_LIMB_BITS * NUM_INPUT_LIMBS;
        let start_flag_col = 0;
        generate_flags_first_row(&mut lv, 0, input_limbs);
        let mut rows = vec![lv.clone()];

        for i in 0..num_rows - 1 {
            let mut nv = vec![F::ZERO; 5 + NUM_INPUT_LIMBS];
            generate_flags_next_row(&lv, &mut nv, i, start_flag_col);
            rows.push(nv.clone());
            lv = nv;
        }
        assert!(rows.len() == num_rows);
        let filtered_bit_col = start_flag_col + 4;
        let mut filtered_bits = vec![];
        for cur_row in (0..num_rows).step_by(2) {
            filtered_bits.push(rows[cur_row][filtered_bit_col]);
        }
        let filtered_bits = filtered_bits
            .into_iter()
            .map(|x| x.to_canonical_u64() == 1u64)
            .collect_vec();
        let mut bits = vec![];
        for limb in input_limbs {
            let limb_bits = limb.view_bits::<Lsb0>().iter().map(|b| *b).collect_vec();
            bits.extend(limb_bits);
        }

        assert!(bits == filtered_bits);

        // dbg!(&rows[num_rows - 2]);
    }
}

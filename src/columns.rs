//! Arithmetic unit

pub const LIMB_BITS: usize = 16;
const EVM_REGISTER_BITS: usize = 256;

/// Return the number of LIMB_BITS limbs that are in an EVM
/// register-sized number, panicking if LIMB_BITS doesn't divide in
/// the EVM register size.
const fn n_limbs() -> usize {
    if EVM_REGISTER_BITS % LIMB_BITS != 0 {
        panic!("limb size must divide EVM register size");
    }
    let n = EVM_REGISTER_BITS / LIMB_BITS;
    if n % 2 == 1 {
        panic!("number of limbs must be even");
    }
    n
}

/// Number of LIMB_BITS limbs that are in on EVM register-sized number.
pub const N_LIMBS: usize = n_limbs(); // 16

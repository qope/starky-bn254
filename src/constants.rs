pub const LIMB_BITS: usize = 16;
pub const N_LIMBS: usize = 16;

pub struct ExpU64StarkConstants {
    pub num_columns: usize,
    pub num_public_inputs: usize,
    pub num_main_cols: usize,
    pub num_io: usize,
    pub start_flags_col: usize,
    pub start_periodic_pulse_col: usize,
    pub start_io_pulses_col: usize,
    pub start_lookups_col: usize,
    pub start_range_check_col: usize,
    pub end_range_check_col: usize,
    pub num_range_check_cols: usize,
}

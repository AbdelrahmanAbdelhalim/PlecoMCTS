
static POPCNT8: &'static [u8] = &[
    0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4,
    1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5,
    1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5,
    2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6,
    1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5,
    2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6,
    2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6,
    3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7,
    1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5,
    2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6,
    2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6,
    3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7,
    2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6,
    3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7,
    3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7,
    4, 5, 5, 6, 5, 6, 6, 7, 5, 6, 6, 7, 6, 7, 7, 8
];

// Returns count of bits
pub fn popcount64(x: u64) -> u8 {
    let x = x as usize;
    if x == 0 { return 0 }
    if x & (x - 1) == 0 { return 1 }
    POPCNT8[x >> 56] +
        POPCNT8[(x >> 48) & 0xFF] +
        POPCNT8[(x >> 40) & 0xFF] +
        POPCNT8[(x >> 32) & 0xFF] +
        POPCNT8[(x >> 24) & 0xFF] +
        POPCNT8[(x >> 16) & 0xFF] +
        POPCNT8[(x >> 8) & 0xFF] +
        POPCNT8[x & 0xFF]
}

// Returns index of the LSB
pub fn bit_scan_forward(bits: u64) -> u8 {
    popcount64((bits & (!bits + 1)) - 1)
}

// Returns the LSB
pub fn lsb(bits: u64) -> u64 {
    1 << (popcount64((bits & (!bits + 1)) - 1) as u64)
}

pub fn msb(bits: u64) -> u64 {
    unimplemented!();
}

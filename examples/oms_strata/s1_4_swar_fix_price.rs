#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

#[inline(always)]
fn is_ascii_digit_byte(b: u8) -> bool {
    b >= b'0' && b <= b'9'
}

/// S1.4 Reference 8-byte ASCII digit validator (pure, total, zero memory).
/// Returns `1` iff every one of the 8 bytes in `word` is in `0x30..=0x39` (`'0'..='9'`).
#[unsafe(no_mangle)]
pub extern "C" fn is_8_ascii_digits_ref(word: i64) -> i32 {
    let u = word as u64;
    let b0 = (u & 0xFF) as u8;
    let b1 = ((u >> 8) & 0xFF) as u8;
    let b2 = ((u >> 16) & 0xFF) as u8;
    let b3 = ((u >> 24) & 0xFF) as u8;
    let b4 = ((u >> 32) & 0xFF) as u8;
    let b5 = ((u >> 40) & 0xFF) as u8;
    let b6 = ((u >> 48) & 0xFF) as u8;
    let b7 = ((u >> 56) & 0xFF) as u8;
    if is_ascii_digit_byte(b0)
        && is_ascii_digit_byte(b1)
        && is_ascii_digit_byte(b2)
        && is_ascii_digit_byte(b3)
        && is_ascii_digit_byte(b4)
        && is_ascii_digit_byte(b5)
        && is_ascii_digit_byte(b6)
        && is_ascii_digit_byte(b7)
    {
        1
    } else {
        0
    }
}

/// S1.4 Branchless SWAR 8-byte ASCII digit validator (Lemire / simdjson formula):
/// - High nibble of every byte must equal `0x3` (`0x30..=0x3F`).
/// - Because high nibbles are `0x3`, adding `0x06` per byte stays within `0x36..=0x45`
///   with ZERO inter-byte carry bleed, and its high nibble remains `0x3` iff low nibble <= 9.
#[unsafe(no_mangle)]
pub extern "C" fn is_8_ascii_digits_swar(word: i64) -> i32 {
    let u = word as u64;
    let hi_nibbles = u & 0xF0F0_F0F0_F0F0_F0F0;
    let shifted_plus6 = (u.wrapping_add(0x0606_0606_0606_0606) & 0xF0F0_F0F0_F0F0_F0F0) >> 4;
    if (hi_nibbles | shifted_plus6) == 0x3333_3333_3333_3333 {
        1
    } else {
        0
    }
}

/// Relational equivalence contract for 8-byte ASCII digit validators:
/// Proves exact equivalence `ret == is_8_ascii_digits_ref(word)` over all 2^64 inputs.
#[unsafe(no_mangle)]
pub extern "C" fn ens_swar_eq(word: i64, ret: i32) -> i32 {
    if ret != 0 && ret != 1 {
        return 0;
    }
    if ret == is_8_ascii_digits_ref(word) {
        1
    } else {
        0
    }
}

/// Buggy mutant for `is_8_ascii_digits_swar`:
/// Classic inter-byte borrow/carry-bleed bug: subtracts `0x30` per byte and adds `0x06`
/// without masking out the high nibbles between operations.
/// Counterexample: `word = 0x3030_3030_3030_312F` (`"/1000000"`, containing `'/' = 0x2F`):
///   `word - 0x3030... = 0x0000_0000_0000_00FF` (borrow bleeds from byte 1 into byte 0)
///   `+ 0x0606...      = 0x0606_0606_0606_0705` (carry bleeds back into byte 1!)
///   `& 0xF0F0...      = 0` -> falsely accepts non-digit FIX price payload!
#[unsafe(no_mangle)]
pub extern "C" fn is_8_ascii_digits_swar_buggy_carry(word: i64) -> i32 {
    let u = word as u64;
    let v = u.wrapping_sub(0x3030_3030_3030_3030);
    if (v.wrapping_add(0x0606_0606_0606_0606) & 0xF0F0_F0F0_F0F0_F0F0) == 0 {
        1
    } else {
        0
    }
}

/// S1.4 Reference 4-byte little-endian ASCII digit parser (`"1234"` -> `0x3433_3231` -> `1234`).
/// Returns `-1` if any byte is not in `'0'..='9'`, otherwise returns the exact decimal integer `0..=9999`.
#[unsafe(no_mangle)]
pub extern "C" fn parse_4_ascii_digits_ref(word: i32) -> i32 {
    let u = word as u32;
    let b0 = (u & 0xFF) as u8;
    let b1 = ((u >> 8) & 0xFF) as u8;
    let b2 = ((u >> 16) & 0xFF) as u8;
    let b3 = ((u >> 24) & 0xFF) as u8;
    if !is_ascii_digit_byte(b0)
        || !is_ascii_digit_byte(b1)
        || !is_ascii_digit_byte(b2)
        || !is_ascii_digit_byte(b3)
    {
        return -1;
    }
    let d0 = (b0 - b'0') as i32;
    let d1 = (b1 - b'0') as i32;
    let d2 = (b2 - b'0') as i32;
    let d3 = (b3 - b'0') as i32;
    d0 * 1000 + d1 * 100 + d2 * 10 + d3
}

/// S1.4 Branchless SWAR 4-byte ASCII digit validator + multiply-accumulate parser.
/// Validates all 4 bytes via carry-free SWAR and combines digits in two stages:
///   pair stage: `10 * d0 + d1`, `10 * d2 + d3`
///   quad stage: `100 * (10 * d0 + d1) + (10 * d2 + d3)`.
#[unsafe(no_mangle)]
pub extern "C" fn parse_4_ascii_digits_swar(word: i32) -> i32 {
    let u = word as u32;
    let hi_nibbles = u & 0xF0F0_F0F0;
    let shifted_plus6 = (u.wrapping_add(0x0606_0606) & 0xF0F0_F0F0) >> 4;
    if (hi_nibbles | shifted_plus6) != 0x3333_3333 {
        return -1;
    }
    let digits = u & 0x0F0F_0F0F;
    let pairs = ((digits & 0x00FF_00FF).wrapping_mul(10))
        .wrapping_add((digits >> 8) & 0x00FF_00FF);
    let total = ((pairs & 0x0000_FFFF).wrapping_mul(100)).wrapping_add(pairs >> 16);
    total as i32
}

/// Relational equivalence contract for 4-byte ASCII digit parsers:
/// Proves exact equivalence `ret == parse_4_ascii_digits_ref(word)` over all 2^32 inputs.
#[unsafe(no_mangle)]
pub extern "C" fn ens_parse4_eq(word: i32, ret: i32) -> i32 {
    if ret == parse_4_ascii_digits_ref(word) {
        1
    } else {
        0
    }
}

#![forbid(unsafe_code)]

//! 30-reference + 30-mutant `no_std` Rust -> `wasm32-unknown-unknown` systems corpus.

use crate::{BenchError, CorpusCase};
use serde::{Deserialize, Serialize};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CorpusManifestEntry {
    pub id: &'static str,
    pub category: &'static str,
    pub bug_kind: &'static str,
    pub ref_wasm_bytes: usize,
    pub mut_wasm_bytes: usize,
}

struct EmbeddedPair {
    id: &'static str,
    category: &'static str,
    bug_kind: &'static str,
    reference_wasm: &'static [u8],
    mutant_wasm: &'static [u8],
}

macro_rules! pair {
    ($id:literal, $cat:literal, $bug:literal) => {
        EmbeddedPair {
            id: $id,
            category: $cat,
            bug_kind: $bug,
            reference_wasm: include_bytes!(concat!(env!("OUT_DIR"), "/wasm/", $id, "_ref.wasm")),
            mutant_wasm: include_bytes!(concat!(env!("OUT_DIR"), "/wasm/", $id, "_mut.wasm")),
        }
    };
}

const CORPUS_PAIRS: &[EmbeddedPair] = &[
    // 1. Fixed-capacity ring buffers (5 pairs)
    pair!(
        "ring_wrap_mask",
        "ring_buffer",
        "stale power-of-2 wrap mask (& 7 instead of & 15)"
    ),
    pair!(
        "ring_len_underflow",
        "ring_buffer",
        "unmasked tail-head wrap-around underflow"
    ),
    pair!(
        "ring_peek_bounds",
        "ring_buffer",
        "off-by-one peek bounds (off > len instead of off >= len)"
    ),
    pair!(
        "ring_wrap_write",
        "ring_buffer",
        "omitted wrapped second segment at end of ring buffer"
    ),
    pair!(
        "ring_saturating_drain",
        "ring_buffer",
        "unclamped drain count causing len underflow and stale reads"
    ),
    // 2. Binary TLV / varint packet parsers (5 pairs)
    pair!(
        "varint_u32_decode",
        "tlv_varint",
        "missing 5th-byte u32 overflow and continuation check"
    ),
    pair!(
        "varint_u32_encode",
        "tlv_varint",
        "signed arithmetic right-shift instead of unsigned u32 shift"
    ),
    pair!(
        "tlv_header_bounds",
        "tlv_varint",
        "signed 32-bit bounds addition wraps on negative/large lengths"
    ),
    pair!(
        "tlv_tag_scan",
        "tlv_varint",
        "advances TLV cursor by 1 + len instead of 2 + len"
    ),
    pair!(
        "tlv_checksum",
        "tlv_varint",
        "off-by-one checksum loop bound drops final byte"
    ),
    // 3. SipHash / CRC32C / ChaCha20 blocks (5 pairs)
    pair!(
        "siphash_round",
        "crypto_hash",
        "wrong SipRound rotation constant (rotl 20 instead of 21)"
    ),
    pair!(
        "siphash_2_4_u64",
        "crypto_hash",
        "omits v2 ^= 0xff finalization domain separation"
    ),
    pair!(
        "crc32c_byte_step",
        "crypto_hash",
        "wrong CRC32 polynomial (IEEE 0xEDB88320 vs Castagnoli 0x82F63B78)"
    ),
    pair!(
        "crc32c_buf_fold",
        "crypto_hash",
        "omits final bitwise inversion (!crc)"
    ),
    pair!(
        "chacha20_quarter_round",
        "crypto_hash",
        "wrong rotation direction (rotr 7 instead of rotl 7)"
    ),
    // 4. Bump / slab allocators (5 pairs)
    pair!(
        "bump_alloc_overflow",
        "allocator",
        "checks arena capacity before rounding cursor up for alignment"
    ),
    pair!(
        "bump_reset",
        "allocator",
        "resets watermark without zero-clearing dirty arena bytes"
    ),
    pair!(
        "slab_bitmask_alloc",
        "allocator",
        "clears lowest free bit before reading trailing_zeros index"
    ),
    pair!(
        "slab_free_bounds",
        "allocator",
        "omits 8-byte pointer alignment validation in free"
    ),
    pair!(
        "slab_slot_copy",
        "allocator",
        "forward memcpy clobbers overlapping destination slice"
    ),
    // 5. Token-bucket rate limiters (5 pairs)
    pair!(
        "bucket_refill_overflow",
        "rate_limiter",
        "32-bit wrapping multiply overflow on elapsed * rate refill"
    ),
    pair!(
        "bucket_consume_underflow",
        "rate_limiter",
        "signed subtraction check wraps on large token deficit"
    ),
    pair!(
        "bucket_burst_clamp",
        "rate_limiter",
        "off-by-one burst clamp (>= cap returns cap - 1)"
    ),
    pair!(
        "bucket_wait_time_div0",
        "rate_limiter",
        "floor division instead of ceil and masks zero-rate error"
    ),
    pair!(
        "bucket_multi_tier",
        "rate_limiter",
        "non-atomic tier-1 deduction before tier-2 check"
    ),
    // 6. Endianness cursors & bitfield codecs (5 pairs)
    pair!(
        "cursor_u16_be_read",
        "endian_codec",
        "little-endian byte decode instead of big-endian"
    ),
    pair!(
        "cursor_u32_be_bounds",
        "endian_codec",
        "off-by-one remaining byte check (p + 3 > len vs p + 4 > len)"
    ),
    pair!(
        "cursor_u64_le_write",
        "endian_codec",
        "truncates unaligned cursor offset via alignment mask"
    ),
    pair!(
        "cursor_checked_advance",
        "endian_codec",
        "unchecked wrapping_add bypasses upper limit check"
    ),
    pair!(
        "bitfield_pack_unpack",
        "endian_codec",
        "missing bitfield mask bleeds upper bits into adjacent fields"
    ),
];

/// Returns all 30 reference+mutant pairs in deterministic manifest order.
pub fn corpus_cases() -> Vec<CorpusCase> {
    CORPUS_PAIRS
        .iter()
        .map(|p| CorpusCase {
            id: p.id.to_owned(),
            category: p.category.to_owned(),
            reference_wasm: p.reference_wasm.to_vec(),
            mutant_wasm: p.mutant_wasm.to_vec(),
            bug_kind: p.bug_kind.to_owned(),
        })
        .collect()
}

/// Returns lightweight manifest metadata (including compiled `.wasm` sizes in `OUT_DIR`).
pub fn corpus_manifest() -> Vec<CorpusManifestEntry> {
    CORPUS_PAIRS
        .iter()
        .map(|p| CorpusManifestEntry {
            id: p.id,
            category: p.category,
            bug_kind: p.bug_kind,
            ref_wasm_bytes: p.reference_wasm.len(),
            mut_wasm_bytes: p.mutant_wasm.len(),
        })
        .collect()
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WasmBinarySummary {
    pub total_bytes: usize,
    pub section_ids: Vec<u8>,
    pub has_import: bool,
    pub has_table: bool,
    pub has_element: bool,
    pub has_start: bool,
    pub has_memory: bool,
    pub code_bodies: u32,
    pub func_exports: Vec<(String, u32)>,
    pub memory_exports: Vec<(String, u32)>,
}

fn read_leb_u32(bytes: &[u8], pos: &mut usize) -> Result<u32, BenchError> {
    let mut result = 0u32;
    let mut shift = 0u32;
    for _ in 0..5 {
        let b = *bytes
            .get(*pos)
            .ok_or_else(|| BenchError::InvalidWasm("unexpected EOF in LEB128".into()))?;
        *pos += 1;
        if shift == 28 && (b & 0xF0) != 0 {
            return Err(BenchError::InvalidWasm("u32 LEB128 overflow".into()));
        }
        result |= u32::from(b & 0x7F) << shift;
        if (b & 0x80) == 0 {
            return Ok(result);
        }
        shift += 7;
    }
    Err(BenchError::InvalidWasm("overlong u32 LEB128".into()))
}

/// Validates a compiled `.wasm` binary header, sections, exports, and code count.
pub fn inspect_wasm_binary(bytes: &[u8]) -> Result<WasmBinarySummary, BenchError> {
    if bytes.len() < 8 {
        return Err(BenchError::InvalidWasm("binary shorter than 8 bytes".into()));
    }
    if !bytes.starts_with(b"\0asm") {
        return Err(BenchError::InvalidWasm("missing \\0asm magic header".into()));
    }
    if bytes[4..8] != [1, 0, 0, 0] {
        return Err(BenchError::InvalidWasm("unsupported Wasm version".into()));
    }

    let mut summary = WasmBinarySummary {
        total_bytes: bytes.len(),
        section_ids: Vec::new(),
        has_import: false,
        has_table: false,
        has_element: false,
        has_start: false,
        has_memory: false,
        code_bodies: 0,
        func_exports: Vec::new(),
        memory_exports: Vec::new(),
    };

    let mut pos = 8usize;
    while pos < bytes.len() {
        let sec_id = bytes[pos];
        pos += 1;
        let sec_len = read_leb_u32(bytes, &mut pos)? as usize;
        let end = pos
            .checked_add(sec_len)
            .ok_or_else(|| BenchError::InvalidWasm("section length overflow".into()))?;
        if end > bytes.len() {
            return Err(BenchError::InvalidWasm("truncated Wasm section".into()));
        }
        let sec = &bytes[pos..end];
        pos = end;

        summary.section_ids.push(sec_id);
        match sec_id {
            2 => summary.has_import = true,
            4 => summary.has_table = true,
            5 => summary.has_memory = true,
            7 => {
                let mut sp = 0usize;
                let count = read_leb_u32(sec, &mut sp)?;
                for _ in 0..count {
                    let name_len = read_leb_u32(sec, &mut sp)? as usize;
                    let name_end = sp
                        .checked_add(name_len)
                        .ok_or_else(|| BenchError::InvalidWasm("export name overflow".into()))?;
                    let name_bytes = sec
                        .get(sp..name_end)
                        .ok_or_else(|| BenchError::InvalidWasm("truncated export name".into()))?;
                    let name = core::str::from_utf8(name_bytes)
                        .map_err(|_| BenchError::InvalidWasm("non-UTF8 export name".into()))?
                        .to_owned();
                    sp = name_end;
                    let kind = *sec
                        .get(sp)
                        .ok_or_else(|| BenchError::InvalidWasm("missing export kind".into()))?;
                    sp += 1;
                    let idx = read_leb_u32(sec, &mut sp)?;
                    match kind {
                        0 => summary.func_exports.push((name, idx)),
                        2 => summary.memory_exports.push((name, idx)),
                        _ => {}
                    }
                }
            }
            8 => summary.has_start = true,
            9 => summary.has_element = true,
            10 => {
                let mut sp = 0usize;
                summary.code_bodies = read_leb_u32(sec, &mut sp)?;
            }
            _ => {}
        }
    }

    Ok(summary)
}

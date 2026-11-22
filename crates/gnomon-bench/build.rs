#![forbid(unsafe_code)]

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::SystemTime;

const CORPUS_IDS: &[&str] = &[
    // 1. Fixed-capacity ring buffers
    "ring_wrap_mask",
    "ring_len_underflow",
    "ring_peek_bounds",
    "ring_wrap_write",
    "ring_saturating_drain",
    // 2. Binary TLV / varint packet parsers
    "varint_u32_decode",
    "varint_u32_encode",
    "tlv_header_bounds",
    "tlv_tag_scan",
    "tlv_checksum",
    // 3. SipHash / CRC32C / ChaCha20 blocks
    "siphash_round",
    "siphash_2_4_u64",
    "crc32c_byte_step",
    "crc32c_buf_fold",
    "chacha20_quarter_round",
    // 4. Bump / slab allocators
    "bump_alloc_overflow",
    "bump_reset",
    "slab_bitmask_alloc",
    "slab_free_bounds",
    "slab_slot_copy",
    // 5. Token-bucket rate limiters
    "bucket_refill_overflow",
    "bucket_consume_underflow",
    "bucket_burst_clamp",
    "bucket_wait_time_div0",
    "bucket_multi_tier",
    // 6. Endianness cursors & bitfield codecs
    "cursor_u16_be_read",
    "cursor_u32_be_bounds",
    "cursor_u64_le_write",
    "cursor_checked_advance",
    "bitfield_pack_unpack",
];

fn needs_rebuild(src: &Path, dst: &Path, build_rs_mtime: Option<SystemTime>) -> bool {
    let Ok(dst_meta) = fs::metadata(dst) else {
        return true;
    };
    let Ok(dst_mtime) = dst_meta.modified() else {
        return true;
    };
    let Ok(src_meta) = fs::metadata(src) else {
        return true;
    };
    let Ok(src_mtime) = src_meta.modified() else {
        return true;
    };
    if src_mtime > dst_mtime {
        return true;
    }
    if let Some(brs) = build_rs_mtime
        && brs > dst_mtime
    {
        return true;
    }
    false
}

struct CompileJob {
    crate_name: String,
    src_path: PathBuf,
    out_path: PathBuf,
}

fn compile_wasm(rustc: &std::ffi::OsStr, job: &CompileJob) -> Result<(), String> {
    let output = Command::new(rustc)
        .arg("--edition")
        .arg("2024")
        .arg("--target")
        .arg("wasm32-unknown-unknown")
        .arg("--crate-type")
        .arg("cdylib")
        .arg("-C")
        .arg("opt-level=2")
        .arg("-C")
        .arg("target-feature=-simd128,-reference-types")
        .arg("--crate-name")
        .arg(&job.crate_name)
        .arg("-o")
        .arg(&job.out_path)
        .arg(&job.src_path)
        .output()
        .map_err(|e| format!("failed to spawn rustc for {}: {e}", job.src_path.display()))?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let stdout = String::from_utf8_lossy(&output.stdout);
        return Err(format!(
            "rustc failed for {} (status {}):\n{}\n{}",
            job.src_path.display(),
            output.status,
            stdout,
            stderr
        ));
    }
    Ok(())
}

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=corpus");

    let manifest_dir = PathBuf::from(env::var_os("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR"));
    let out_dir = PathBuf::from(env::var_os("OUT_DIR").expect("OUT_DIR"));
    let wasm_out_dir = out_dir.join("wasm");
    fs::create_dir_all(&wasm_out_dir).expect("create OUT_DIR/wasm");

    let corpus_dir = manifest_dir.join("corpus");
    let build_rs_mtime = fs::metadata(manifest_dir.join("build.rs"))
        .and_then(|m| m.modified())
        .ok();
    let rustc = env::var_os("RUSTC").unwrap_or_else(|| "rustc".into());

    let mut jobs = Vec::with_capacity(CORPUS_IDS.len() * 2);
    for &id in CORPUS_IDS {
        for suffix in ["ref", "mut"] {
            let file_stem = format!("{id}_{suffix}");
            let src_path = corpus_dir.join(format!("{file_stem}.rs"));
            println!("cargo:rerun-if-changed={}", src_path.display());
            if !src_path.exists() {
                panic!("missing corpus source file: {}", src_path.display());
            }
            let out_path = wasm_out_dir.join(format!("{file_stem}.wasm"));
            if needs_rebuild(&src_path, &out_path, build_rs_mtime) {
                jobs.push(CompileJob {
                    crate_name: format!("gnomon_corpus_{file_stem}"),
                    src_path,
                    out_path,
                });
            }
        }
    }

    if jobs.is_empty() {
        return;
    }

    let workers = std::thread::available_parallelism()
        .map(|n| n.get().min(8))
        .unwrap_or(4);

    let next_idx = std::sync::atomic::AtomicUsize::new(0);
    let results: std::sync::Mutex<Vec<Result<(), String>>> = std::sync::Mutex::new(Vec::new());

    std::thread::scope(|s| {
        for _ in 0..workers.min(jobs.len()) {
            s.spawn(|| {
                loop {
                    let idx = next_idx.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    if idx >= jobs.len() {
                        break;
                    }
                    let res = compile_wasm(&rustc, &jobs[idx]);
                    results.lock().expect("lock").push(res);
                }
            });
        }
    });

    for res in results.into_inner().expect("unlock") {
        if let Err(err) = res {
            panic!("{err}");
        }
    }
}

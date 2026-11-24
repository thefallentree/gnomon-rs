//! Lossless `.ir` JSON wire format and `-t wasm|ir|rust|auto` input loader (files & stdin).

use std::io::Read;
use std::path::Path;

use base64::Engine as _;
use gnomon_kernel::{
    BinOp, CallTarget, EffectOp, FuncDef, FuncId, GlobalDef, GlobalId, HostCallId, HostContract,
    LaneKind, Law, LawKind, LawList, MemId, MemWidth, MemoryDef, Module, OffsetRange, Op, Region,
    RegionBuilder, RegionNode, RegionRef, SliceBound, Span, Stmt, Stratum, StratumId, StratumOp,
    StratumRegistry, TrapCode, UnOp, Val, ValId, ValType,
};
use gnomon_wasm::lift_wasm;
use serde::{Deserialize, Serialize};

use crate::GnomonError;
use crate::rust_bridge::{
    bind_stratum_imports, compile_rust_to_wasm_with_registry, looks_like_rust_source,
    module_has_stratum_imports,
};

/// Explicit input format selected via CLI `-t` / `--type` or MCP tool parameter.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, schemars::JsonSchema)]
#[serde(rename_all = "lowercase")]
pub enum InputType {
    Auto,
    Wasm,
    Ir,
    Rust,
}

/// Decoded payload from either a `.wasm` binary or `.ir` JSON document.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LoadedArtifact {
    Module(Module),
    Region {
        params: Vec<(ValId, ValType)>,
        results: Vec<ValType>,
        region: Region,
    },
}

/// Unpacked `(optional_module, params, results, region)` tuple extracted from a `LoadedArtifact`.
pub type ExtractedRegion = (Option<Module>, Vec<(ValId, ValType)>, Vec<ValType>, Region);

impl LoadedArtifact {
    /// Extracts a `Region` directly, or the entry function body (func 0 / named export)
    /// when loaded from a `Module`.
    pub fn into_region(self, entry: Option<&str>) -> Result<ExtractedRegion, GnomonError> {
        match self {
            LoadedArtifact::Region { params, results, region } => Ok((None, params, results, region)),
            LoadedArtifact::Module(m) => {
                let func = find_entry_func(&m, entry)?;
                let params = func.params.clone();
                let results = func.results.clone();
                let body = func.body.clone();
                Ok((Some(m), params, results, body))
            }
        }
    }
}

pub fn find_entry_func<'a>(m: &'a Module, entry: Option<&str>) -> Result<&'a FuncDef, GnomonError> {
    if let Some(name) = entry {
        m.funcs
            .iter()
            .find(|f| f.name == name || f.export_name.as_deref() == Some(name))
            .ok_or_else(|| GnomonError::InvalidInput(format!("entry function '{name}' not found")))
    } else {
        m.funcs
            .first()
            .ok_or_else(|| GnomonError::InvalidInput("module has no functions".into()))
    }
}

/// Reads raw bytes from a file path, or from stdin when `path` is `None` or `Some("-")`.
pub fn read_input_bytes(path: Option<&str>) -> Result<(Vec<u8>, Option<&str>), GnomonError> {
    match path {
        None | Some("-") => {
            let mut buf = Vec::new();
            std::io::stdin()
                .read_to_end(&mut buf)
                .map_err(|e| GnomonError::Io(format!("failed reading stdin: {e}")))?;
            Ok((buf, None))
        }
        Some(p) => {
            let bytes = std::fs::read(p)
                .map_err(|e| GnomonError::Io(format!("failed reading '{p}': {e}")))?;
            Ok((bytes, Some(p)))
        }
    }
}

/// Detects whether raw bytes are `.wasm`, `.rs`, or `.ir` JSON using `-t` + path extension + content heuristics.
pub fn resolve_input_type(kind: InputType, path: Option<&str>, bytes: &[u8]) -> InputType {
    match kind {
        InputType::Wasm => InputType::Wasm,
        InputType::Ir => InputType::Ir,
        InputType::Rust => InputType::Rust,
        InputType::Auto => {
            if bytes.starts_with(b"\0asm") {
                return InputType::Wasm;
            }
            if let Some(p) = path {
                let ext = Path::new(p)
                    .extension()
                    .and_then(|s| s.to_str())
                    .map(|s| s.to_ascii_lowercase());
                match ext.as_deref() {
                    Some("wasm") => return InputType::Wasm,
                    Some("rs") => return InputType::Rust,
                    Some("ir") | Some("json") => return InputType::Ir,
                    _ => {}
                }
            }
            if let Ok(s) = std::str::from_utf8(bytes) {
                let trimmed = s.trim_start();
                if trimmed.starts_with("base64:") || trimmed.starts_with("hex:") {
                    return InputType::Wasm;
                }
                if looks_like_rust_source(trimmed) {
                    return InputType::Rust;
                }
            }
            InputType::Ir
        }
    }
}

fn maybe_bind_artifact(
    artifact: LoadedArtifact,
    registry: Option<&StratumRegistry>,
) -> Result<LoadedArtifact, GnomonError> {
    match (artifact, registry) {
        (LoadedArtifact::Module(m), Some(reg)) if module_has_stratum_imports(&m) => {
            Ok(LoadedArtifact::Module(bind_stratum_imports(m, reg)?))
        }
        (art, _) => Ok(art),
    }
}

/// Loads raw bytes (from file or stdin) as `.wasm`, `.rs`, or `.ir` JSON according to `kind`.
pub fn load_artifact_bytes(
    bytes: &[u8],
    kind: InputType,
    path: Option<&str>,
) -> Result<(InputType, LoadedArtifact), GnomonError> {
    load_artifact_bytes_with_registry(bytes, kind, path, None)
}

/// Loads raw bytes as `.wasm`, `.rs`, or `.ir` JSON, synthesizing `strata.rs` for inline Rust
/// and automatically binding `"stratum"` Wasm imports when `registry` is provided.
pub fn load_artifact_bytes_with_registry(
    bytes: &[u8],
    kind: InputType,
    path: Option<&str>,
    registry: Option<&StratumRegistry>,
) -> Result<(InputType, LoadedArtifact), GnomonError> {
    let resolved = resolve_input_type(kind, path, bytes);
    match resolved {
        InputType::Wasm => {
            let wasm_bytes = decode_maybe_encoded_wasm(bytes)?;
            let module = lift_wasm(&wasm_bytes)
                .map_err(|e| GnomonError::Wasm(e.to_string()))?;
            let art = maybe_bind_artifact(LoadedArtifact::Module(module), registry)?;
            Ok((InputType::Wasm, art))
        }
        InputType::Rust => {
            let src = std::str::from_utf8(bytes)
                .map_err(|e| GnomonError::InvalidInput(format!("invalid UTF-8 in .rs input: {e}")))?;
            let wasm_bytes =
                compile_rust_to_wasm_with_registry(src, path.map(Path::new), registry)?;
            let module = lift_wasm(&wasm_bytes)
                .map_err(|e| GnomonError::Wasm(e.to_string()))?;
            let art = maybe_bind_artifact(LoadedArtifact::Module(module), registry)?;
            Ok((InputType::Rust, art))
        }
        InputType::Ir | InputType::Auto => {
            let text = std::str::from_utf8(bytes)
                .map_err(|e| GnomonError::InvalidInput(format!("invalid UTF-8 in .ir input: {e}")))?;
            let doc: IrDocument = serde_json::from_str(text)
                .map_err(|e| GnomonError::InvalidInput(format!("invalid .ir JSON: {e}")))?;
            let art = maybe_bind_artifact(doc.into_loaded()?, registry)?;
            Ok((InputType::Ir, art))
        }
    }
}

/// Loads a string payload (used by MCP JSON tools): accepts `.ir` JSON, strict `#![no_std]` Rust
/// source, `base64:` / raw base64 `.wasm`, `hex:` `.wasm`, or a local file path when `file_path`
/// is passed.
pub fn load_artifact_from_mcp_arg(
    content: Option<&str>,
    file_path: Option<&str>,
    kind: InputType,
) -> Result<(InputType, LoadedArtifact), GnomonError> {
    load_artifact_from_mcp_arg_with_registry(content, file_path, kind, None)
}

/// Registry-aware MCP artifact loader that synthesizes `strata.rs` for inline Rust snippets
/// and automatically binds `"stratum"` Wasm imports when `registry` is provided.
pub fn load_artifact_from_mcp_arg_with_registry(
    content: Option<&str>,
    file_path: Option<&str>,
    kind: InputType,
    registry: Option<&StratumRegistry>,
) -> Result<(InputType, LoadedArtifact), GnomonError> {
    if let Some(p) = file_path {
        let bytes = std::fs::read(p)
            .map_err(|e| GnomonError::Io(format!("failed reading '{p}': {e}")))?;
        return load_artifact_bytes_with_registry(&bytes, kind, Some(p), registry);
    }
    let raw = content
        .ok_or_else(|| GnomonError::InvalidInput("either content or path must be provided".into()))?;
    let trimmed = raw.trim();
    match kind {
        InputType::Wasm => {
            let wasm_bytes = decode_wasm_string(trimmed)?;
            let module = lift_wasm(&wasm_bytes).map_err(|e| GnomonError::Wasm(e.to_string()))?;
            let art = maybe_bind_artifact(LoadedArtifact::Module(module), registry)?;
            Ok((InputType::Wasm, art))
        }
        InputType::Rust => {
            let wasm_bytes = compile_rust_to_wasm_with_registry(raw, None, registry)?;
            let module = lift_wasm(&wasm_bytes).map_err(|e| GnomonError::Wasm(e.to_string()))?;
            let art = maybe_bind_artifact(LoadedArtifact::Module(module), registry)?;
            Ok((InputType::Rust, art))
        }
        InputType::Ir => {
            let doc: IrDocument = serde_json::from_str(trimmed)
                .map_err(|e| GnomonError::InvalidInput(format!("invalid .ir JSON: {e}")))?;
            let art = maybe_bind_artifact(doc.into_loaded()?, registry)?;
            Ok((InputType::Ir, art))
        }
        InputType::Auto => {
            if trimmed.starts_with('{') {
                let doc: IrDocument = serde_json::from_str(trimmed)
                    .map_err(|e| GnomonError::InvalidInput(format!("invalid .ir JSON: {e}")))?;
                let art = maybe_bind_artifact(doc.into_loaded()?, registry)?;
                Ok((InputType::Ir, art))
            } else if looks_like_rust_source(trimmed) {
                let wasm_bytes = compile_rust_to_wasm_with_registry(raw, None, registry)?;
                let module =
                    lift_wasm(&wasm_bytes).map_err(|e| GnomonError::Wasm(e.to_string()))?;
                let art = maybe_bind_artifact(LoadedArtifact::Module(module), registry)?;
                Ok((InputType::Rust, art))
            } else {
                let wasm_bytes = decode_wasm_string(trimmed)?;
                let module =
                    lift_wasm(&wasm_bytes).map_err(|e| GnomonError::Wasm(e.to_string()))?;
                let art = maybe_bind_artifact(LoadedArtifact::Module(module), registry)?;
                Ok((InputType::Wasm, art))
            }
        }
    }
}

fn decode_maybe_encoded_wasm(bytes: &[u8]) -> Result<Vec<u8>, GnomonError> {
    if bytes.starts_with(b"\0asm") {
        return Ok(bytes.to_vec());
    }
    if let Ok(s) = std::str::from_utf8(bytes) {
        let trimmed = s.trim();
        if let Ok(decoded) = decode_wasm_string(trimmed)
            && decoded.starts_with(b"\0asm")
        {
            return Ok(decoded);
        }
    }
    Ok(bytes.to_vec())
}

fn decode_wasm_string(s: &str) -> Result<Vec<u8>, GnomonError> {
    if let Some(hex_body) = s.strip_prefix("hex:") {
        return decode_hex(hex_body.trim());
    }
    let b64_body = s.strip_prefix("base64:").unwrap_or(s).trim();
    if let Ok(decoded) = base64::engine::general_purpose::STANDARD.decode(b64_body)
        && decoded.starts_with(b"\0asm")
    {
        return Ok(decoded);
    }
    if let Ok(decoded) = decode_hex(s)
        && decoded.starts_with(b"\0asm")
    {
        return Ok(decoded);
    }
    base64::engine::general_purpose::STANDARD
        .decode(b64_body)
        .map_err(|e| GnomonError::InvalidInput(format!("expected .wasm base64 or hex bytes: {e}")))
}

fn decode_hex(s: &str) -> Result<Vec<u8>, GnomonError> {
    let clean: String = s.chars().filter(|c| !c.is_whitespace()).collect();
    if !clean.len().is_multiple_of(2) {
        return Err(GnomonError::InvalidInput("odd-length hex string".into()));
    }
    let mut out = Vec::with_capacity(clean.len() / 2);
    let bytes = clean.as_bytes();
    let (chunks, _) = bytes.as_chunks::<2>();
    for pair in chunks {
        let hex_pair = std::str::from_utf8(pair)
            .map_err(|e| GnomonError::InvalidInput(format!("invalid hex utf8: {e}")))?;
        let b = u8::from_str_radix(hex_pair, 16)
            .map_err(|e| GnomonError::InvalidInput(format!("invalid hex byte '{hex_pair}': {e}")))?;
        out.push(b);
    }
    Ok(out)
}

// ===========================================================================
// Serde Wire DTOs for Lossless `.ir` JSON Format
// ===========================================================================

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum IrDocument {
    Module(IrModule),
    Region {
        #[serde(default)]
        params: Vec<IrTypedVar>,
        #[serde(default)]
        results: Vec<IrValType>,
        region: IrRegion,
    },
}

impl IrDocument {
    pub fn from_module(m: &Module) -> Self {
        IrDocument::Module(IrModule::from_kernel(m))
    }

    pub fn from_region(
        params: &[(ValId, ValType)],
        results: &[ValType],
        region: &Region,
    ) -> Self {
        IrDocument::Region {
            params: params
                .iter()
                .map(|&(id, ty)| IrTypedVar { id: id.0, ty: ty.into() })
                .collect(),
            results: results.iter().copied().map(Into::into).collect(),
            region: IrRegion::from_kernel(region),
        }
    }

    pub fn into_loaded(self) -> Result<LoadedArtifact, GnomonError> {
        match self {
            IrDocument::Module(m) => Ok(LoadedArtifact::Module(m.into_kernel()?)),
            IrDocument::Region { params, results, region } => Ok(LoadedArtifact::Region {
                params: params.into_iter().map(|v| (ValId(v.id), v.ty.into())).collect(),
                results: results.into_iter().map(Into::into).collect(),
                region: region.into_kernel()?,
            }),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, schemars::JsonSchema)]
#[serde(rename_all = "lowercase")]
pub enum IrValType {
    I32,
    I64,
    F32,
    F64,
    V128,
}

impl From<ValType> for IrValType {
    fn from(v: ValType) -> Self {
        match v {
            ValType::I32 => IrValType::I32,
            ValType::I64 => IrValType::I64,
            ValType::F32 => IrValType::F32,
            ValType::F64 => IrValType::F64,
            ValType::V128 => IrValType::V128,
        }
    }
}

impl From<IrValType> for ValType {
    fn from(v: IrValType) -> Self {
        match v {
            IrValType::I32 => ValType::I32,
            IrValType::I64 => ValType::I64,
            IrValType::F32 => ValType::F32,
            IrValType::F64 => ValType::F64,
            IrValType::V128 => ValType::V128,
        }
    }
}

/// Lossless JSON value DTO: two's-complement `i32`/`i64`, raw IEEE-754 bit patterns
/// `u32`/`u64` for `f32`/`f64`, and little-endian `[lo, hi]` (`[u64; 2]`) for `v128`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, schemars::JsonSchema)]
#[serde(tag = "ty", content = "val", rename_all = "lowercase")]
pub enum IrVal {
    I32(i32),
    I64(i64),
    F32(u32),
    F64(u64),
    V128([u64; 2]),
}

impl From<Val> for IrVal {
    fn from(v: Val) -> Self {
        match v {
            Val::I32(x) => IrVal::I32(x),
            Val::I64(x) => IrVal::I64(x),
            Val::F32(bits) => IrVal::F32(bits),
            Val::F64(bits) => IrVal::F64(bits),
            Val::V128(bits) => IrVal::V128([bits as u64, (bits >> 64) as u64]),
        }
    }
}

impl From<IrVal> for Val {
    fn from(v: IrVal) -> Self {
        match v {
            IrVal::I32(x) => Val::I32(x),
            IrVal::I64(x) => Val::I64(x),
            IrVal::F32(bits) => Val::F32(bits),
            IrVal::F64(bits) => Val::F64(bits),
            IrVal::V128([lo, hi]) => Val::V128((lo as u128) | ((hi as u128) << 64)),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, schemars::JsonSchema)]
pub struct IrTypedVar {
    pub id: u32,
    pub ty: IrValType,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IrModule {
    #[serde(default)]
    pub memories: Vec<IrMemoryDef>,
    #[serde(default)]
    pub globals: Vec<IrGlobalDef>,
    #[serde(default)]
    pub funcs: Vec<IrFuncDef>,
    #[serde(default)]
    pub host_contracts: Vec<IrHostContract>,
    #[serde(default)]
    pub memory_exports: Vec<(String, u16)>,
    #[serde(default)]
    pub global_exports: Vec<(String, u32)>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IrMemoryDef {
    pub id: u16,
    pub min_pages: u32,
    pub max_pages: Option<u32>,
    #[serde(default)]
    pub init_data: Vec<(u32, Vec<u8>)>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IrGlobalDef {
    pub id: u32,
    pub ty: IrValType,
    pub mutable: bool,
    pub init: IrVal,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IrFuncDef {
    pub id: u32,
    pub name: String,
    #[serde(default)]
    pub export_name: Option<String>,
    #[serde(default)]
    pub params: Vec<IrTypedVar>,
    #[serde(default)]
    pub results: Vec<IrValType>,
    pub body: IrRegion,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IrHostContract {
    pub id: u32,
    pub module_name: String,
    pub field_name: String,
    #[serde(default)]
    pub params: Vec<IrTypedVar>,
    #[serde(default)]
    pub results: Vec<IrTypedVar>,
    pub precondition: IrRegion,
    pub postcondition: IrRegion,
    #[serde(default)]
    pub read_footprints: Vec<(u16, IrOffsetRange)>,
    #[serde(default)]
    pub write_footprints: Vec<(u16, IrOffsetRange)>,
    #[serde(default)]
    pub sim_body: Option<IrRegion>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IrOffsetRange {
    pub base: IrSliceBound,
    pub len: IrSliceBound,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", content = "val", rename_all = "snake_case")]
pub enum IrSliceBound {
    Const(u32),
    Arg(u32),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "node", rename_all = "snake_case")]
pub enum IrRegion {
    Block {
        #[serde(default)]
        stmts: Vec<IrStmt>,
    },
    IfElse {
        cond: u32,
        then_region: Box<IrRegion>,
        else_region: Box<IrRegion>,
        #[serde(default)]
        results: Vec<IrValType>,
    },
    BoundedLoop {
        max_iters: u32,
        #[serde(default)]
        init_vars: Vec<u32>,
        #[serde(default)]
        state_vars: Vec<IrTypedVar>,
        body: Box<IrRegion>,
    },
    InvariantLoop {
        #[serde(default)]
        init_vars: Vec<u32>,
        #[serde(default)]
        state_vars: Vec<IrTypedVar>,
        cond: Box<IrRegion>,
        invariant_pred: Box<IrRegion>,
        fuel_measure: Box<IrRegion>,
        body: Box<IrRegion>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "stmt", rename_all = "snake_case")]
pub enum IrStmt {
    Let {
        dst: u32,
        ty: IrValType,
        op: IrOp,
    },
    Effect {
        effect: IrEffectOp,
    },
    Region {
        #[serde(default)]
        results: Vec<IrTypedVar>,
        region: IrRegion,
    },
    Call {
        #[serde(default)]
        results: Vec<IrTypedVar>,
        target: IrCallTarget,
        #[serde(default)]
        args: Vec<u32>,
    },
    Yield {
        #[serde(default)]
        vals: Vec<u32>,
    },
    Break {
        depth: u32,
        #[serde(default)]
        cond: Option<u32>,
        #[serde(default)]
        values: Vec<u32>,
    },
    Continue {
        depth: u32,
        #[serde(default)]
        cond: Option<u32>,
        #[serde(default)]
        values: Vec<u32>,
    },
    Return {
        #[serde(default)]
        vals: Vec<u32>,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", content = "id", rename_all = "snake_case")]
pub enum IrCallTarget {
    Func(u32),
    Host(u32),
    Stratum(u32),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "op", rename_all = "snake_case")]
pub enum IrOp {
    ConstI32 { val: i32 },
    ConstI64 { val: i64 },
    ConstF32 { bits: u32 },
    ConstF64 { bits: u64 },
    ConstV128 { bits: [u64; 2] },
    Copy { src: u32 },
    Un { unop: IrUnOp, arg: u32 },
    Bin { binop: IrBinOp, lhs: u32, rhs: u32 },
    Select { cond: u32, true_val: u32, false_val: u32 },
    Load {
        mem: u16,
        addr: u32,
        offset: u32,
        width: IrMemWidth,
        signed: bool,
        result_ty: IrValType,
    },
    GlobalGet { id: u32 },
    MemorySize { mem: u16 },
    MemoryGrow { mem: u16, delta: u32 },
    SimdExtractLane { kind: IrLaneKind, lane: u8, vec: u32 },
    SimdReplaceLane { kind: IrLaneKind, lane: u8, vec: u32, val: u32 },
    SimdBitselect { a: u32, b: u32, mask: u32 },
    SimdShuffle { lhs: u32, rhs: u32, lanes: [u8; 16] },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "op", rename_all = "snake_case")]
pub enum IrEffectOp {
    Store { mem: u16, addr: u32, offset: u32, width: IrMemWidth, val: u32 },
    MemoryCopy { dst_mem: u16, src_mem: u16, dst: u32, src: u32, len: u32 },
    MemoryFill { mem: u16, dst: u32, val: u32, len: u32 },
    GlobalSet { id: u32, val: u32 },
    Trap { code: IrTrapCode },
    Nop,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum IrMemWidth {
    B1,
    B2,
    B4,
    B8,
    B16,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, schemars::JsonSchema)]
#[serde(rename_all = "snake_case")]
pub enum IrTrapCode {
    DivByZero,
    IntOverflow,
    OutOfBoundsMem,
    OutOfFuel,
    HostContractViolation,
    Unreachable,
}

macro_rules! mirror_ir_enum {
    ($ir_ty:ident <-> $kernel_ty:ident { $($variant:ident),+ $(,)? }) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
        #[serde(rename_all = "snake_case")]
        pub enum $ir_ty {
            $($variant,)+
        }

        impl From<$kernel_ty> for $ir_ty {
            fn from(v: $kernel_ty) -> Self {
                match v {
                    $($kernel_ty::$variant => $ir_ty::$variant,)+
                }
            }
        }

        impl From<$ir_ty> for $kernel_ty {
            fn from(v: $ir_ty) -> Self {
                match v {
                    $($ir_ty::$variant => $kernel_ty::$variant,)+
                }
            }
        }
    };
}

mirror_ir_enum!(IrLaneKind <-> LaneKind {
    I8x16S,
    I8x16U,
    I16x8S,
    I16x8U,
    I32x4,
    I64x2,
    F32x4,
    F64x2,
});

mirror_ir_enum!(IrUnOp <-> UnOp {
    // Integer unary (0..=15)
    I32Eqz,
    I64Eqz,
    I32Clz,
    I32Ctz,
    I32Popcnt,
    I64Clz,
    I64Ctz,
    I64Popcnt,
    I32WrapI64,
    I64ExtendI32S,
    I64ExtendI32U,
    I32Extend8S,
    I32Extend16S,
    I64Extend8S,
    I64Extend16S,
    I64Extend32S,
    // Scalar FP unary (16..=29)
    F32Abs,
    F32Neg,
    F32Ceil,
    F32Floor,
    F32Trunc,
    F32Nearest,
    F32Sqrt,
    F64Abs,
    F64Neg,
    F64Ceil,
    F64Floor,
    F64Trunc,
    F64Nearest,
    F64Sqrt,
    // Trapping float-to-int truncations (30..=37)
    I32TruncF32S,
    I32TruncF32U,
    I32TruncF64S,
    I32TruncF64U,
    I64TruncF32S,
    I64TruncF32U,
    I64TruncF64S,
    I64TruncF64U,
    // Saturating float-to-int truncations (38..=45)
    I32TruncSatF32S,
    I32TruncSatF32U,
    I32TruncSatF64S,
    I32TruncSatF64U,
    I64TruncSatF32S,
    I64TruncSatF32U,
    I64TruncSatF64S,
    I64TruncSatF64U,
    // Int-to-float conversions (46..=53)
    F32ConvertI32S,
    F32ConvertI32U,
    F32ConvertI64S,
    F32ConvertI64U,
    F64ConvertI32S,
    F64ConvertI32U,
    F64ConvertI64S,
    F64ConvertI64U,
    // Demote / Promote / Reinterpret (54..=59)
    F32DemoteF64,
    F64PromoteF32,
    I32ReinterpretF32,
    I64ReinterpretF64,
    F32ReinterpretI32,
    F64ReinterpretI64,
    // v128 unary / splat / bitmask / lane-convert (60..=99)
    V128Not,
    V128AnyTrue,
    I8x16Splat,
    I16x8Splat,
    I32x4Splat,
    I64x2Splat,
    F32x4Splat,
    F64x2Splat,
    I8x16Bitmask,
    I16x8Bitmask,
    I32x4Bitmask,
    I64x2Bitmask,
    I32x4AllTrue,
    I64x2AllTrue,
    I32x4Abs,
    I32x4Neg,
    I64x2Abs,
    I64x2Neg,
    F32x4Abs,
    F32x4Neg,
    F32x4Sqrt,
    F32x4Ceil,
    F32x4Floor,
    F32x4Trunc,
    F32x4Nearest,
    F64x2Abs,
    F64x2Neg,
    F64x2Sqrt,
    F64x2Ceil,
    F64x2Floor,
    F64x2Trunc,
    F64x2Nearest,
    I32x4TruncSatF32x4S,
    I32x4TruncSatF32x4U,
    F32x4ConvertI32x4S,
    F32x4ConvertI32x4U,
    I64x2ExtendLowI32x4S,
    I64x2ExtendLowI32x4U,
    I64x2ExtendHighI32x4S,
    I64x2ExtendHighI32x4U,
});

mirror_ir_enum!(IrBinOp <-> BinOp {
    // Integer binary (0..=49)
    I32Eq,
    I32Ne,
    I32LtS,
    I32LtU,
    I32GtS,
    I32GtU,
    I32LeS,
    I32LeU,
    I32GeS,
    I32GeU,
    I64Eq,
    I64Ne,
    I64LtS,
    I64LtU,
    I64GtS,
    I64GtU,
    I64LeS,
    I64LeU,
    I64GeS,
    I64GeU,
    I32Add,
    I32Sub,
    I32Mul,
    I32DivS,
    I32DivU,
    I32RemS,
    I32RemU,
    I64Add,
    I64Sub,
    I64Mul,
    I64DivS,
    I64DivU,
    I64RemS,
    I64RemU,
    I32And,
    I32Or,
    I32Xor,
    I32Shl,
    I32ShrS,
    I32ShrU,
    I32Rotl,
    I32Rotr,
    I64And,
    I64Or,
    I64Xor,
    I64Shl,
    I64ShrS,
    I64ShrU,
    I64Rotl,
    I64Rotr,
    // Scalar FP binary (50..=75)
    F32Add,
    F32Sub,
    F32Mul,
    F32Div,
    F32Min,
    F32Max,
    F32Copysign,
    F32Eq,
    F32Ne,
    F32Lt,
    F32Gt,
    F32Le,
    F32Ge,
    F64Add,
    F64Sub,
    F64Mul,
    F64Div,
    F64Min,
    F64Max,
    F64Copysign,
    F64Eq,
    F64Ne,
    F64Lt,
    F64Gt,
    F64Le,
    F64Ge,
    // v128 bitwise & swizzle (76..=80)
    V128And,
    V128AndNot,
    V128Or,
    V128Xor,
    I8x16Swizzle,
    // i32x4 lane binary (81..=100)
    I32x4Add,
    I32x4Sub,
    I32x4Mul,
    I32x4MinS,
    I32x4MinU,
    I32x4MaxS,
    I32x4MaxU,
    I32x4Eq,
    I32x4Ne,
    I32x4LtS,
    I32x4LtU,
    I32x4GtS,
    I32x4GtU,
    I32x4LeS,
    I32x4LeU,
    I32x4GeS,
    I32x4GeU,
    I32x4Shl,
    I32x4ShrS,
    I32x4ShrU,
    // i64x2 lane binary (101..=112)
    I64x2Add,
    I64x2Sub,
    I64x2Mul,
    I64x2Eq,
    I64x2Ne,
    I64x2LtS,
    I64x2GtS,
    I64x2LeS,
    I64x2GeS,
    I64x2Shl,
    I64x2ShrS,
    I64x2ShrU,
    // f32x4 lane binary (113..=126)
    F32x4Add,
    F32x4Sub,
    F32x4Mul,
    F32x4Div,
    F32x4Min,
    F32x4Max,
    F32x4PMin,
    F32x4PMax,
    F32x4Eq,
    F32x4Ne,
    F32x4Lt,
    F32x4Gt,
    F32x4Le,
    F32x4Ge,
    // f64x2 lane binary (127..=140)
    F64x2Add,
    F64x2Sub,
    F64x2Mul,
    F64x2Div,
    F64x2Min,
    F64x2Max,
    F64x2PMin,
    F64x2PMax,
    F64x2Eq,
    F64x2Ne,
    F64x2Lt,
    F64x2Gt,
    F64x2Le,
    F64x2Ge,
});

// ===========================================================================
// Persistent Stratum / Law DTOs (for `--state` JSON persistence)
// ===========================================================================

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IrStratumOp {
    pub id: u32,
    pub name: String,
    pub layer: u16,
    pub params: Vec<IrTypedVar>,
    pub results: Vec<IrValType>,
    pub body: IrRegion,
    pub docstring: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum IrLawKind {
    Algebraic,
    MemoryFrame { untouched_mem: u16 },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IrLaw {
    pub name: String,
    pub kind: IrLawKind,
    pub params: Vec<IrTypedVar>,
    pub precondition: IrRegion,
    pub lhs: IrRegion,
    pub rhs: IrRegion,
    pub proof_digest: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IrStratum {
    pub op: IrStratumOp,
    pub laws: Vec<IrLaw>,
}

impl IrStratumOp {
    pub fn from_kernel(op: &StratumOp) -> Self {
        Self {
            id: op.id.0,
            name: op.name.clone(),
            layer: op.layer,
            params: op
                .params
                .iter()
                .map(|&(id, ty)| IrTypedVar { id: id.0, ty: ty.into() })
                .collect(),
            results: op.results.iter().copied().map(Into::into).collect(),
            body: IrRegion::from_kernel(&op.body),
            docstring: op.docstring.clone(),
        }
    }

    pub fn into_kernel(self) -> Result<StratumOp, GnomonError> {
        Ok(StratumOp {
            id: StratumId(self.id),
            name: self.name,
            layer: self.layer,
            params: self.params.into_iter().map(|v| (ValId(v.id), v.ty.into())).collect(),
            results: self.results.into_iter().map(Into::into).collect(),
            body: self.body.into_kernel()?,
            docstring: self.docstring,
        })
    }
}

impl IrLaw {
    pub fn from_kernel(law: &Law) -> Self {
        Self {
            name: law.name.clone(),
            kind: match law.kind {
                LawKind::Algebraic => IrLawKind::Algebraic,
                LawKind::MemoryFrame { untouched_mem } => {
                    IrLawKind::MemoryFrame { untouched_mem: untouched_mem.0 }
                }
            },
            params: law
                .params
                .iter()
                .map(|&(id, ty)| IrTypedVar { id: id.0, ty: ty.into() })
                .collect(),
            precondition: IrRegion::from_kernel(&law.precondition),
            lhs: IrRegion::from_kernel(&law.lhs),
            rhs: IrRegion::from_kernel(&law.rhs),
            proof_digest: law.proof_digest,
        }
    }

    pub fn into_kernel(self) -> Result<Law, GnomonError> {
        Ok(Law {
            name: self.name,
            kind: match self.kind {
                IrLawKind::Algebraic => LawKind::Algebraic,
                IrLawKind::MemoryFrame { untouched_mem } => {
                    LawKind::MemoryFrame { untouched_mem: MemId(untouched_mem) }
                }
            },
            params: self.params.into_iter().map(|v| (ValId(v.id), v.ty.into())).collect(),
            precondition: self.precondition.into_kernel()?,
            lhs: self.lhs.into_kernel()?,
            rhs: self.rhs.into_kernel()?,
            proof_digest: self.proof_digest,
        })
    }
}

impl IrStratum {
    pub fn from_kernel(st: &Stratum) -> Self {
        Self {
            op: IrStratumOp::from_kernel(&st.op),
            laws: st.laws.iter().map(IrLaw::from_kernel).collect(),
        }
    }

    pub fn into_kernel(self) -> Result<Stratum, GnomonError> {
        let laws: Vec<Law> = self
            .laws
            .into_iter()
            .map(IrLaw::into_kernel)
            .collect::<Result<_, _>>()?;
        Ok(Stratum { op: self.op.into_kernel()?, laws: LawList::from_vec(laws) })
    }
}

// ===========================================================================
// Conversions between GnomonIR and IrModule / IrRegion
// ===========================================================================

impl IrModule {
    pub fn from_kernel(m: &Module) -> Self {
        Self {
            memories: m
                .memories
                .iter()
                .map(|mem| IrMemoryDef {
                    id: mem.id.0,
                    min_pages: mem.min_pages,
                    max_pages: mem.max_pages,
                    init_data: mem.init_data.clone(),
                })
                .collect(),
            globals: m
                .globals
                .iter()
                .map(|g| IrGlobalDef {
                    id: g.id.0,
                    ty: g.ty.into(),
                    mutable: g.mutable,
                    init: g.init.into(),
                })
                .collect(),
            funcs: m
                .funcs
                .iter()
                .map(|f| IrFuncDef {
                    id: f.id.0,
                    name: f.name.clone(),
                    export_name: f.export_name.clone(),
                    params: f
                        .params
                        .iter()
                        .map(|&(id, ty)| IrTypedVar { id: id.0, ty: ty.into() })
                        .collect(),
                    results: f.results.iter().copied().map(Into::into).collect(),
                    body: IrRegion::from_kernel(&f.body),
                })
                .collect(),
            host_contracts: m
                .host_contracts
                .iter()
                .map(|h| IrHostContract {
                    id: h.id.0,
                    module_name: h.module_name.clone(),
                    field_name: h.field_name.clone(),
                    params: h
                        .params
                        .iter()
                        .map(|&(id, ty)| IrTypedVar { id: id.0, ty: ty.into() })
                        .collect(),
                    results: h
                        .results
                        .iter()
                        .map(|&(id, ty)| IrTypedVar { id: id.0, ty: ty.into() })
                        .collect(),
                    precondition: IrRegion::from_kernel(&h.precondition),
                    postcondition: IrRegion::from_kernel(&h.postcondition),
                    read_footprints: h
                        .read_footprints
                        .iter()
                        .map(|&(m, r)| (m.0, r.into()))
                        .collect(),
                    write_footprints: h
                        .write_footprints
                        .iter()
                        .map(|&(m, r)| (m.0, r.into()))
                        .collect(),
                    sim_body: h.sim_body.as_ref().map(IrRegion::from_kernel),
                })
                .collect(),
            memory_exports: m.memory_exports.iter().map(|(n, id)| (n.clone(), id.0)).collect(),
            global_exports: m.global_exports.iter().map(|(n, id)| (n.clone(), id.0)).collect(),
        }
    }

    pub fn into_kernel(self) -> Result<Module, GnomonError> {
        Ok(Module {
            memories: self
                .memories
                .into_iter()
                .map(|m| MemoryDef {
                    id: MemId(m.id),
                    min_pages: m.min_pages,
                    max_pages: m.max_pages,
                    init_data: m.init_data,
                })
                .collect(),
            globals: self
                .globals
                .into_iter()
                .map(|g| GlobalDef {
                    id: GlobalId(g.id),
                    ty: g.ty.into(),
                    mutable: g.mutable,
                    init: g.init.into(),
                })
                .collect(),
            funcs: self
                .funcs
                .into_iter()
                .map(|f| {
                    Ok(FuncDef {
                        id: FuncId(f.id),
                        name: f.name,
                        export_name: f.export_name,
                        params: f
                            .params
                            .into_iter()
                            .map(|v| (ValId(v.id), v.ty.into()))
                            .collect(),
                        results: f.results.into_iter().map(Into::into).collect(),
                        body: f.body.into_kernel()?,
                    })
                })
                .collect::<Result<_, GnomonError>>()?,
            host_contracts: self
                .host_contracts
                .into_iter()
                .map(|h| {
                    Ok(HostContract {
                        id: HostCallId(h.id),
                        module_name: h.module_name,
                        field_name: h.field_name,
                        params: h
                            .params
                            .into_iter()
                            .map(|v| (ValId(v.id), v.ty.into()))
                            .collect(),
                        results: h
                            .results
                            .into_iter()
                            .map(|v| (ValId(v.id), v.ty.into()))
                            .collect(),
                        precondition: h.precondition.into_kernel()?,
                        postcondition: h.postcondition.into_kernel()?,
                        read_footprints: h
                            .read_footprints
                            .into_iter()
                            .map(|(m, r)| (MemId(m), r.into()))
                            .collect(),
                        write_footprints: h
                            .write_footprints
                            .into_iter()
                            .map(|(m, r)| (MemId(m), r.into()))
                            .collect(),
                        sim_body: h.sim_body.map(IrRegion::into_kernel).transpose()?,
                    })
                })
                .collect::<Result<_, GnomonError>>()?,
            memory_exports: self
                .memory_exports
                .into_iter()
                .map(|(n, id)| (n, MemId(id)))
                .collect(),
            global_exports: self
                .global_exports
                .into_iter()
                .map(|(n, id)| (n, GlobalId(id)))
                .collect(),
        })
    }
}

impl IrRegion {
    pub fn from_kernel(region: &Region) -> Self {
        Self::from_ref(region.as_ref())
    }

    fn from_ref(r: RegionRef<'_>) -> Self {
        match r.node {
            RegionNode::Block(span) => {
                let mut stmts = Vec::with_capacity(span.len as usize);
                for i in 0..span.len {
                    if let Some(stmt) = r.region.try_stmt(span, i) {
                        stmts.push(stmt_from_kernel(r, stmt));
                    }
                }
                IrRegion::Block { stmts }
            }
            RegionNode::IfElse { cond, then_region, else_region, results } => IrRegion::IfElse {
                cond: cond.0,
                then_region: Box::new(Self::from_ref(r.child_or_empty(then_region))),
                else_region: Box::new(Self::from_ref(r.child_or_empty(else_region))),
                results: r.tys(results).map(Into::into).collect(),
            },
            RegionNode::BoundedLoop { max_iters, init_vars, state_vars, body } => {
                IrRegion::BoundedLoop {
                    max_iters,
                    init_vars: r.vals(init_vars).map(|v| v.0).collect(),
                    state_vars: r
                        .vars(state_vars)
                        .map(|(id, ty)| IrTypedVar { id: id.0, ty: ty.into() })
                        .collect(),
                    body: Box::new(Self::from_ref(r.child_or_empty(body))),
                }
            }
            RegionNode::InvariantLoop {
                init_vars,
                state_vars,
                cond,
                invariant_pred,
                fuel_measure,
                body,
            } => IrRegion::InvariantLoop {
                init_vars: r.vals(init_vars).map(|v| v.0).collect(),
                state_vars: r
                    .vars(state_vars)
                    .map(|(id, ty)| IrTypedVar { id: id.0, ty: ty.into() })
                    .collect(),
                cond: Box::new(Self::from_ref(r.child_or_empty(cond))),
                invariant_pred: Box::new(Self::from_ref(r.child_or_empty(invariant_pred))),
                fuel_measure: Box::new(Self::from_ref(r.child_or_empty(fuel_measure))),
                body: Box::new(Self::from_ref(r.child_or_empty(body))),
            },
        }
    }

    pub fn into_kernel(self) -> Result<Region, GnomonError> {
        match self {
            IrRegion::Block { stmts } => {
                let mut builder = RegionBuilder::new();
                for s in stmts {
                    push_ir_stmt(&mut builder, s)?;
                }
                Ok(builder.finish())
            }
            IrRegion::IfElse { cond, then_region, else_region, results } => {
                let t = then_region.into_kernel()?;
                let e = else_region.into_kernel()?;
                let res: Vec<ValType> = results.into_iter().map(Into::into).collect();
                Ok(Region::if_else(ValId(cond), &t, &e, &res))
            }
            IrRegion::BoundedLoop { max_iters, init_vars, state_vars, body } => {
                let inits: Vec<ValId> = init_vars.into_iter().map(ValId).collect();
                let states: Vec<(ValId, ValType)> =
                    state_vars.into_iter().map(|v| (ValId(v.id), v.ty.into())).collect();
                let b = body.into_kernel()?;
                Ok(Region::bounded_loop(max_iters, &inits, &states, &b))
            }
            IrRegion::InvariantLoop {
                init_vars,
                state_vars,
                cond,
                invariant_pred,
                fuel_measure,
                body,
            } => {
                let inits: Vec<ValId> = init_vars.into_iter().map(ValId).collect();
                let states: Vec<(ValId, ValType)> =
                    state_vars.into_iter().map(|v| (ValId(v.id), v.ty.into())).collect();
                let c = cond.into_kernel()?;
                let inv = invariant_pred.into_kernel()?;
                let f = fuel_measure.into_kernel()?;
                let b = body.into_kernel()?;
                Ok(Region::invariant_loop(&inits, &states, &c, &inv, &f, &b))
            }
        }
    }
}

fn stmt_from_kernel(r: RegionRef<'_>, stmt: Stmt) -> IrStmt {
    match stmt {
        Stmt::Let { dst, ty, op } => IrStmt::Let { dst: dst.0, ty: ty.into(), op: op.into() },
        Stmt::Effect(eff) => IrStmt::Effect { effect: eff.into() },
        Stmt::Region { results, region } => IrStmt::Region {
            results: r
                .vars(results)
                .map(|(id, ty)| IrTypedVar { id: id.0, ty: ty.into() })
                .collect(),
            region: IrRegion::from_ref(r.child_or_empty(region)),
        },
        Stmt::Call { results, target, args } => IrStmt::Call {
            results: r
                .vars(results)
                .map(|(id, ty)| IrTypedVar { id: id.0, ty: ty.into() })
                .collect(),
            target: match target {
                CallTarget::Func(f) => IrCallTarget::Func(f.0),
                CallTarget::Host(h) => IrCallTarget::Host(h.0),
                CallTarget::Stratum(s) => IrCallTarget::Stratum(s.0),
            },
            args: r.vals(args).map(|v| v.0).collect(),
        },
        Stmt::Yield(span) => IrStmt::Yield { vals: r.vals(span).map(|v| v.0).collect() },
        Stmt::Break { depth, cond, values } => IrStmt::Break {
            depth,
            cond: cond.map(|v| v.0),
            values: r.vals(values).map(|v| v.0).collect(),
        },
        Stmt::Continue { depth, cond, values } => IrStmt::Continue {
            depth,
            cond: cond.map(|v| v.0),
            values: r.vals(values).map(|v| v.0).collect(),
        },
        Stmt::Return(span) => IrStmt::Return { vals: r.vals(span).map(|v| v.0).collect() },
    }
}

fn push_ir_stmt(b: &mut RegionBuilder, stmt: IrStmt) -> Result<(), GnomonError> {
    match stmt {
        IrStmt::Let { dst, ty, op } => b.push_let(ValId(dst), ty.into(), op.into()),
        IrStmt::Effect { effect } => b.push_effect(effect.into()),
        IrStmt::Region { results, region } => {
            let res: Vec<(ValId, ValType)> =
                results.into_iter().map(|v| (ValId(v.id), v.ty.into())).collect();
            let sub = region.into_kernel()?;
            b.push_subregion(&res, &sub);
        }
        IrStmt::Call { results, target, args } => {
            let res: Vec<(ValId, ValType)> =
                results.into_iter().map(|v| (ValId(v.id), v.ty.into())).collect();
            let tgt = match target {
                IrCallTarget::Func(f) => CallTarget::Func(FuncId(f)),
                IrCallTarget::Host(h) => CallTarget::Host(HostCallId(h)),
                IrCallTarget::Stratum(s) => CallTarget::Stratum(StratumId(s)),
            };
            let arg_ids: Vec<ValId> = args.into_iter().map(ValId).collect();
            b.push_call(&res, tgt, &arg_ids);
        }
        IrStmt::Yield { vals } => {
            let ids: Vec<ValId> = vals.into_iter().map(ValId).collect();
            b.push_yield(&ids);
        }
        IrStmt::Break { depth, cond, values } => {
            let ids: Vec<ValId> = values.into_iter().map(ValId).collect();
            b.push_break(depth, cond.map(ValId), &ids);
        }
        IrStmt::Continue { depth, cond, values } => {
            let ids: Vec<ValId> = values.into_iter().map(ValId).collect();
            b.push_continue(depth, cond.map(ValId), &ids);
        }
        IrStmt::Return { vals } => {
            let ids: Vec<ValId> = vals.into_iter().map(ValId).collect();
            b.push_return(&ids);
        }
    }
    Ok(())
}

impl From<OffsetRange> for IrOffsetRange {
    fn from(r: OffsetRange) -> Self {
        Self { base: r.base.into(), len: r.len.into() }
    }
}

impl From<IrOffsetRange> for OffsetRange {
    fn from(r: IrOffsetRange) -> Self {
        Self { base: r.base.into(), len: r.len.into() }
    }
}

impl From<SliceBound> for IrSliceBound {
    fn from(b: SliceBound) -> Self {
        match b {
            SliceBound::Const(c) => IrSliceBound::Const(c),
            SliceBound::Arg(v) => IrSliceBound::Arg(v),
        }
    }
}

impl From<IrSliceBound> for SliceBound {
    fn from(b: IrSliceBound) -> Self {
        match b {
            IrSliceBound::Const(c) => SliceBound::Const(c),
            IrSliceBound::Arg(v) => SliceBound::Arg(v),
        }
    }
}

impl From<MemWidth> for IrMemWidth {
    fn from(w: MemWidth) -> Self {
        match w {
            MemWidth::B1 => IrMemWidth::B1,
            MemWidth::B2 => IrMemWidth::B2,
            MemWidth::B4 => IrMemWidth::B4,
            MemWidth::B8 => IrMemWidth::B8,
            MemWidth::B16 => IrMemWidth::B16,
        }
    }
}

impl From<IrMemWidth> for MemWidth {
    fn from(w: IrMemWidth) -> Self {
        match w {
            IrMemWidth::B1 => MemWidth::B1,
            IrMemWidth::B2 => MemWidth::B2,
            IrMemWidth::B4 => MemWidth::B4,
            IrMemWidth::B8 => MemWidth::B8,
            IrMemWidth::B16 => MemWidth::B16,
        }
    }
}

impl From<TrapCode> for IrTrapCode {
    fn from(t: TrapCode) -> Self {
        match t {
            TrapCode::DivByZero => IrTrapCode::DivByZero,
            TrapCode::IntOverflow => IrTrapCode::IntOverflow,
            TrapCode::OutOfBoundsMem => IrTrapCode::OutOfBoundsMem,
            TrapCode::OutOfFuel => IrTrapCode::OutOfFuel,
            TrapCode::HostContractViolation => IrTrapCode::HostContractViolation,
            TrapCode::Unreachable => IrTrapCode::Unreachable,
        }
    }
}

impl From<IrTrapCode> for TrapCode {
    fn from(t: IrTrapCode) -> Self {
        match t {
            IrTrapCode::DivByZero => TrapCode::DivByZero,
            IrTrapCode::IntOverflow => TrapCode::IntOverflow,
            IrTrapCode::OutOfBoundsMem => TrapCode::OutOfBoundsMem,
            IrTrapCode::OutOfFuel => TrapCode::OutOfFuel,
            IrTrapCode::HostContractViolation => TrapCode::HostContractViolation,
            IrTrapCode::Unreachable => TrapCode::Unreachable,
        }
    }
}

impl From<Op> for IrOp {
    fn from(op: Op) -> Self {
        match op {
            Op::ConstI32(val) => IrOp::ConstI32 { val },
            Op::ConstI64(val) => IrOp::ConstI64 { val },
            Op::ConstF32(bits) => IrOp::ConstF32 { bits },
            Op::ConstF64(bits) => IrOp::ConstF64 { bits },
            Op::ConstV128(bits) => IrOp::ConstV128 { bits: [bits as u64, (bits >> 64) as u64] },
            Op::Copy(src) => IrOp::Copy { src: src.0 },
            Op::Un(unop, arg) => IrOp::Un { unop: unop.into(), arg: arg.0 },
            Op::Bin(binop, lhs, rhs) => IrOp::Bin { binop: binop.into(), lhs: lhs.0, rhs: rhs.0 },
            Op::Select { cond, true_val, false_val } => IrOp::Select {
                cond: cond.0,
                true_val: true_val.0,
                false_val: false_val.0,
            },
            Op::Load { mem, addr, offset, width, signed, result_ty } => IrOp::Load {
                mem: mem.0,
                addr: addr.0,
                offset,
                width: width.into(),
                signed,
                result_ty: result_ty.into(),
            },
            Op::GlobalGet(id) => IrOp::GlobalGet { id: id.0 },
            Op::MemorySize(mem) => IrOp::MemorySize { mem: mem.0 },
            Op::MemoryGrow { mem, delta } => IrOp::MemoryGrow { mem: mem.0, delta: delta.0 },
            Op::SimdExtractLane { kind, lane, vec } => IrOp::SimdExtractLane {
                kind: kind.into(),
                lane,
                vec: vec.0,
            },
            Op::SimdReplaceLane { kind, lane, vec, val } => IrOp::SimdReplaceLane {
                kind: kind.into(),
                lane,
                vec: vec.0,
                val: val.0,
            },
            Op::SimdBitselect { a, b, mask } => IrOp::SimdBitselect {
                a: a.0,
                b: b.0,
                mask: mask.0,
            },
            Op::SimdShuffle { lhs, rhs, lanes } => IrOp::SimdShuffle {
                lhs: lhs.0,
                rhs: rhs.0,
                lanes,
            },
        }
    }
}

impl From<IrOp> for Op {
    fn from(op: IrOp) -> Self {
        match op {
            IrOp::ConstI32 { val } => Op::ConstI32(val),
            IrOp::ConstI64 { val } => Op::ConstI64(val),
            IrOp::ConstF32 { bits } => Op::ConstF32(bits),
            IrOp::ConstF64 { bits } => Op::ConstF64(bits),
            IrOp::ConstV128 { bits: [lo, hi] } => {
                Op::ConstV128((lo as u128) | ((hi as u128) << 64))
            }
            IrOp::Copy { src } => Op::Copy(ValId(src)),
            IrOp::Un { unop, arg } => Op::Un(unop.into(), ValId(arg)),
            IrOp::Bin { binop, lhs, rhs } => Op::Bin(binop.into(), ValId(lhs), ValId(rhs)),
            IrOp::Select { cond, true_val, false_val } => Op::Select {
                cond: ValId(cond),
                true_val: ValId(true_val),
                false_val: ValId(false_val),
            },
            IrOp::Load { mem, addr, offset, width, signed, result_ty } => Op::Load {
                mem: MemId(mem),
                addr: ValId(addr),
                offset,
                width: width.into(),
                signed,
                result_ty: result_ty.into(),
            },
            IrOp::GlobalGet { id } => Op::GlobalGet(GlobalId(id)),
            IrOp::MemorySize { mem } => Op::MemorySize(MemId(mem)),
            IrOp::MemoryGrow { mem, delta } => {
                Op::MemoryGrow { mem: MemId(mem), delta: ValId(delta) }
            }
            IrOp::SimdExtractLane { kind, lane, vec } => Op::SimdExtractLane {
                kind: kind.into(),
                lane,
                vec: ValId(vec),
            },
            IrOp::SimdReplaceLane { kind, lane, vec, val } => Op::SimdReplaceLane {
                kind: kind.into(),
                lane,
                vec: ValId(vec),
                val: ValId(val),
            },
            IrOp::SimdBitselect { a, b, mask } => Op::SimdBitselect {
                a: ValId(a),
                b: ValId(b),
                mask: ValId(mask),
            },
            IrOp::SimdShuffle { lhs, rhs, lanes } => Op::SimdShuffle {
                lhs: ValId(lhs),
                rhs: ValId(rhs),
                lanes,
            },
        }
    }
}

impl From<EffectOp> for IrEffectOp {
    fn from(eff: EffectOp) -> Self {
        match eff {
            EffectOp::Store { mem, addr, offset, width, val } => IrEffectOp::Store {
                mem: mem.0,
                addr: addr.0,
                offset,
                width: width.into(),
                val: val.0,
            },
            EffectOp::MemoryCopy { dst_mem, src_mem, dst, src, len } => IrEffectOp::MemoryCopy {
                dst_mem: dst_mem.0,
                src_mem: src_mem.0,
                dst: dst.0,
                src: src.0,
                len: len.0,
            },
            EffectOp::MemoryFill { mem, dst, val, len } => IrEffectOp::MemoryFill {
                mem: mem.0,
                dst: dst.0,
                val: val.0,
                len: len.0,
            },
            EffectOp::GlobalSet { id, val } => IrEffectOp::GlobalSet { id: id.0, val: val.0 },
            EffectOp::Trap(code) => IrEffectOp::Trap { code: code.into() },
            EffectOp::Nop => IrEffectOp::Nop,
        }
    }
}

impl From<IrEffectOp> for EffectOp {
    fn from(eff: IrEffectOp) -> Self {
        match eff {
            IrEffectOp::Store { mem, addr, offset, width, val } => EffectOp::Store {
                mem: MemId(mem),
                addr: ValId(addr),
                offset,
                width: width.into(),
                val: ValId(val),
            },
            IrEffectOp::MemoryCopy { dst_mem, src_mem, dst, src, len } => EffectOp::MemoryCopy {
                dst_mem: MemId(dst_mem),
                src_mem: MemId(src_mem),
                dst: ValId(dst),
                src: ValId(src),
                len: ValId(len),
            },
            IrEffectOp::MemoryFill { mem, dst, val, len } => EffectOp::MemoryFill {
                mem: MemId(mem),
                dst: ValId(dst),
                val: ValId(val),
                len: ValId(len),
            },
            IrEffectOp::GlobalSet { id, val } => {
                EffectOp::GlobalSet { id: GlobalId(id), val: ValId(val) }
            }
            IrEffectOp::Trap { code } => EffectOp::Trap(code.into()),
            IrEffectOp::Nop => EffectOp::Nop,
        }
    }
}

#[allow(dead_code)]
fn _assert_span(_: Span) {}

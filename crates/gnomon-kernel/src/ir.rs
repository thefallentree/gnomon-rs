//! Core `GnomonIR` Region-SSA data model.

use alloc::{boxed::Box, string::String, vec::Vec};

/// Primitive WebAssembly scalar value types supported in `GnomonIR`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum ValType { I32, I64 }

/// Runtime scalar value with exact two's-complement bit width.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Val { I32(i32), I64(i64) }

impl Val {
    pub fn val_type(self) -> ValType { match self { Self::I32(_) => ValType::I32, Self::I64(_) => ValType::I64 } }
    pub fn default_for(ty: ValType) -> Self { match ty { ValType::I32 => Self::I32(0), ValType::I64 => Self::I64(0) } }
    pub fn as_i32(self) -> Option<i32> { match self { Self::I32(v) => Some(v), Self::I64(_) => None } }
    pub fn as_i64(self) -> Option<i64> { match self { Self::I64(v) => Some(v), Self::I32(_) => None } }
    pub fn as_u32(self) -> Option<u32> { self.as_i32().map(|v| v as u32) }
    pub fn as_u64(self) -> Option<u64> { self.as_i64().map(|v| v as u64) }
}

/// Deterministic WebAssembly and Gnomon execution trap codes.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum TrapCode { DivByZero, IntOverflow, OutOfBoundsMem, OutOfFuel, HostContractViolation, Unreachable }

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)] pub struct MemId(pub u16);
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)] pub struct ValId(pub u32);
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)] pub struct GlobalId(pub u32);
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)] pub struct FuncId(pub u32);
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)] pub struct HostCallId(pub u32);
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)] pub struct StratumId(pub u32);

/// Byte width for memory load and store operations.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum MemWidth { B1 = 1, B2 = 2, B4 = 4, B8 = 8 }
impl MemWidth { pub const fn bytes(self) -> u64 { self as u64 } }

/// Deterministic unary WebAssembly operations.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum UnOp {
    I32Eqz, I64Eqz, I32Clz, I32Ctz, I32Popcnt, I64Clz, I64Ctz, I64Popcnt,
    I32WrapI64, I64ExtendI32S, I64ExtendI32U, I32Extend8S, I32Extend16S, I64Extend8S, I64Extend16S, I64Extend32S,
}

impl UnOp {
    pub fn input_ty(self) -> ValType {
        match self {
            Self::I64Eqz | Self::I64Clz | Self::I64Ctz | Self::I64Popcnt | Self::I32WrapI64
            | Self::I64Extend8S | Self::I64Extend16S | Self::I64Extend32S => ValType::I64,
            _ => ValType::I32,
        }
    }
    pub fn output_ty(self) -> ValType {
        match self {
            Self::I64Clz | Self::I64Ctz | Self::I64Popcnt | Self::I64ExtendI32S | Self::I64ExtendI32U
            | Self::I64Extend8S | Self::I64Extend16S | Self::I64Extend32S => ValType::I64,
            _ => ValType::I32,
        }
    }
}

/// Deterministic binary WebAssembly operations.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum BinOp {
    I32Eq, I32Ne, I32LtS, I32LtU, I32GtS, I32GtU, I32LeS, I32LeU, I32GeS, I32GeU,
    I64Eq, I64Ne, I64LtS, I64LtU, I64GtS, I64GtU, I64LeS, I64LeU, I64GeS, I64GeU,
    I32Add, I32Sub, I32Mul, I32DivS, I32DivU, I32RemS, I32RemU,
    I64Add, I64Sub, I64Mul, I64DivS, I64DivU, I64RemS, I64RemU,
    I32And, I32Or, I32Xor, I32Shl, I32ShrS, I32ShrU, I32Rotl, I32Rotr,
    I64And, I64Or, I64Xor, I64Shl, I64ShrS, I64ShrU, I64Rotl, I64Rotr,
}

impl BinOp {
    pub fn operand_ty(self) -> ValType { if (self as u8) >= (Self::I64Eq as u8) && (self as u8) <= (Self::I64GeU as u8) || (self as u8) >= (Self::I64Add as u8) && (self as u8) <= (Self::I64RemU as u8) || (self as u8) >= (Self::I64And as u8) { ValType::I64 } else { ValType::I32 } }
    pub fn output_ty(self) -> ValType { if (self as u8) >= (Self::I64Add as u8) && (self as u8) <= (Self::I64RemU as u8) || (self as u8) >= (Self::I64And as u8) { ValType::I64 } else { ValType::I32 } }
}

/// Value-producing primitive expression in `GnomonIR`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Op {
    ConstI32(i32), ConstI64(i64), Copy(ValId),
    Select { cond: ValId, true_val: ValId, false_val: ValId },
    GlobalGet(GlobalId), Un(UnOp, ValId), Bin(BinOp, ValId, ValId),
    Load { mem: MemId, addr: ValId, offset: u32, width: MemWidth, signed: bool, result_ty: ValType },
    MemorySize(MemId), MemoryGrow { mem: MemId, delta: ValId },
}

/// Side-effecting statement primitive in `GnomonIR`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EffectOp {
    Store { mem: MemId, addr: ValId, offset: u32, width: MemWidth, val: ValId },
    MemoryCopy { dst_mem: MemId, src_mem: MemId, dst: ValId, src: ValId, len: ValId },
    MemoryFill { mem: MemId, dst: ValId, val: ValId, len: ValId },
    GlobalSet { id: GlobalId, val: ValId }, Trap(TrapCode), Nop,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CallTarget { Func(FuncId), Host(HostCallId), Stratum(StratumId) }

/// Single SSA statement inside a `Region::Block`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Stmt {
    Let { dst: ValId, ty: ValType, op: Op }, Effect(EffectOp),
    Region { results: Vec<(ValId, ValType)>, region: Region },
    Call { results: Vec<(ValId, ValType)>, target: CallTarget, args: Vec<ValId> },
    Yield(Vec<ValId>), Break { depth: u32, cond: Option<ValId>, values: Vec<ValId> },
    Continue { depth: u32, cond: Option<ValId>, values: Vec<ValId> }, Return(Vec<ValId>),
}

/// Structured hierarchical Region-SSA node.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Region {
    Block(Vec<Stmt>),
    IfElse { cond: ValId, then_region: Box<Region>, else_region: Box<Region>, results: Vec<ValType> },
    BoundedLoop { max_iters: u32, init_vars: Vec<ValId>, state_vars: Vec<(ValId, ValType)>, body: Box<Region> },
    InvariantLoop {
        init_vars: Vec<ValId>, state_vars: Vec<(ValId, ValType)>,
        cond: Box<Region>, invariant_pred: Box<Region>, fuel_measure: Box<Region>, body: Box<Region>,
    },
}

impl Drop for Region {
    fn drop(&mut self) {
        if let Self::Block(stmts) = self
            && !stmts.is_empty()
            && stmts.len() <= 8
        {
            let _ = stmts.pop();
            let _ = stmts.pop();
            let _ = stmts.pop();
            let _ = stmts.pop();
            let _ = stmts.pop();
            let _ = stmts.pop();
            let _ = stmts.pop();
            let _ = stmts.pop();
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)] pub enum SliceBound { Const(u32), Arg(u32) }
#[derive(Clone, Copy, Debug, PartialEq, Eq)] pub struct OffsetRange { pub base: SliceBound, pub len: SliceBound }

/// Explicit specification and memory-footprint contract for an external host call.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HostContract {
    pub id: HostCallId, pub module_name: String, pub field_name: String,
    pub params: Vec<(ValId, ValType)>, pub results: Vec<(ValId, ValType)>, pub precondition: Region,
    pub read_footprints: Vec<(MemId, OffsetRange)>, pub write_footprints: Vec<(MemId, OffsetRange)>,
    pub postcondition: Region, pub sim_body: Option<Region>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MemoryDef { pub id: MemId, pub min_pages: u32, pub max_pages: Option<u32>, pub init_data: Vec<(u32, Vec<u8>)> }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GlobalDef { pub id: GlobalId, pub ty: ValType, pub mutable: bool, pub init: Val }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FuncDef {
    pub id: FuncId, pub name: String, pub export_name: Option<String>,
    pub params: Vec<(ValId, ValType)>, pub results: Vec<ValType>, pub body: Region,
}

/// Complete verified Wasm-derived module representation.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Module {
    pub memories: Vec<MemoryDef>, pub globals: Vec<GlobalDef>,
    pub host_contracts: Vec<HostContract>, pub funcs: Vec<FuncDef>,
    pub memory_exports: Vec<(String, MemId)>, pub global_exports: Vec<(String, GlobalId)>,
}

impl Module {
    pub fn func(&self, id: FuncId) -> Option<&FuncDef> { self.funcs.iter().find(|f| f.id == id) }
    pub fn host_contract(&self, id: HostCallId) -> Option<&HostContract> { self.host_contracts.iter().find(|h| h.id == id) }
    pub fn global(&self, id: GlobalId) -> Option<&GlobalDef> { self.globals.iter().find(|g| g.id == id) }
}

/// Inline-first LIFO stack (`6` inline slots) spilling to `Vec<T>` at deeper nesting.
pub(crate) struct Stack2<T> {
    s0: Option<T>,
    s1: Option<T>,
    s2: Option<T>,
    s3: Option<T>,
    s4: Option<T>,
    s5: Option<T>,
    spill: Vec<T>,
}

impl<T> Stack2<T> {
    pub(crate) fn new() -> Self {
        Self { s0: None, s1: None, s2: None, s3: None, s4: None, s5: None, spill: Vec::new() }
    }
    pub(crate) fn with_first(v: T) -> Self {
        Self { s0: Some(v), s1: None, s2: None, s3: None, s4: None, s5: None, spill: Vec::new() }
    }
    pub(crate) fn push(&mut self, v: T) {
        if !self.spill.is_empty() {
            self.spill.push(v);
        } else if self.s0.is_none() {
            self.s0 = Some(v);
        } else if self.s1.is_none() {
            self.s1 = Some(v);
        } else if self.s2.is_none() {
            self.s2 = Some(v);
        } else if self.s3.is_none() {
            self.s3 = Some(v);
        } else if self.s4.is_none() {
            self.s4 = Some(v);
        } else if self.s5.is_none() {
            self.s5 = Some(v);
        } else {
            self.spill.push(v);
        }
    }
    pub(crate) fn pop(&mut self) -> Option<T> {
        if !self.spill.is_empty() {
            self.spill.pop()
        } else if self.s5.is_some() {
            self.s5.take()
        } else if self.s4.is_some() {
            self.s4.take()
        } else if self.s3.is_some() {
            self.s3.take()
        } else if self.s2.is_some() {
            self.s2.take()
        } else if self.s1.is_some() {
            self.s1.take()
        } else {
            self.s0.take()
        }
    }
}

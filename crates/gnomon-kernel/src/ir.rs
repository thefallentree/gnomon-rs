//! Core `GnomonIR` flat arena-backed Region-SSA data model.
//!
//! All sub-regions, statements, and operand/type slices within a `Region` are stored
//! in a single contiguous pool of `Copy` (`!needs_drop`) `IrSlot` items indexed by
//! `RegionNodeId` and `Span`. This eliminates recursive pointer ownership (`Box<Region>`)
//! and recursive drop glue while preserving structured hierarchical Region-SSA semantics.

use alloc::{string::String, vec::Vec};

/// Primitive WebAssembly scalar value types supported in `GnomonIR`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum ValType {
    I32,
    I64,
}

impl ValType {
    pub(crate) const fn to_u8(self) -> u8 {
        match self {
            Self::I32 => 0,
            Self::I64 => 1,
        }
    }

    pub(crate) const fn from_u8(v: u8) -> Option<Self> {
        match v {
            0 => Some(Self::I32),
            1 => Some(Self::I64),
            _ => None,
        }
    }
}

/// Runtime scalar value with exact two's-complement bit width.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Val {
    I32(i32),
    I64(i64),
}

impl Val {
    pub fn val_type(self) -> ValType {
        match self {
            Self::I32(_) => ValType::I32,
            Self::I64(_) => ValType::I64,
        }
    }
    pub fn default_for(ty: ValType) -> Self {
        match ty {
            ValType::I32 => Self::I32(0),
            ValType::I64 => Self::I64(0),
        }
    }
    pub fn as_i32(self) -> Option<i32> {
        match self {
            Self::I32(v) => Some(v),
            Self::I64(_) => None,
        }
    }
    pub fn as_i64(self) -> Option<i64> {
        match self {
            Self::I64(v) => Some(v),
            Self::I32(_) => None,
        }
    }
    pub fn as_u32(self) -> Option<u32> {
        self.as_i32().map(|v| v as u32)
    }
    pub fn as_u64(self) -> Option<u64> {
        self.as_i64().map(|v| v as u64)
    }
}

/// Deterministic WebAssembly and Gnomon execution trap codes.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum TrapCode {
    DivByZero,
    IntOverflow,
    OutOfBoundsMem,
    OutOfFuel,
    HostContractViolation,
    Unreachable,
}

impl TrapCode {
    pub(crate) const fn to_u8(self) -> u8 {
        match self {
            Self::DivByZero => 0,
            Self::IntOverflow => 1,
            Self::OutOfBoundsMem => 2,
            Self::OutOfFuel => 3,
            Self::HostContractViolation => 4,
            Self::Unreachable => 5,
        }
    }

    pub(crate) const fn from_u8(v: u8) -> Option<Self> {
        match v {
            0 => Some(Self::DivByZero),
            1 => Some(Self::IntOverflow),
            2 => Some(Self::OutOfBoundsMem),
            3 => Some(Self::OutOfFuel),
            4 => Some(Self::HostContractViolation),
            5 => Some(Self::Unreachable),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct MemId(pub u16);
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct ValId(pub u32);
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct GlobalId(pub u32);
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct FuncId(pub u32);
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct HostCallId(pub u32);
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct StratumId(pub u32);

/// Index of a `RegionNode` slot inside a `Region`'s flat pool.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct RegionNodeId(pub u32);

/// Contiguous slice range `[start .. start + len]` within a `Region`'s flat pool.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Default)]
pub struct Span {
    pub start: u32,
    pub len: u32,
}

impl Span {
    pub const EMPTY: Self = Self { start: 0, len: 0 };
    pub const fn is_empty(self) -> bool {
        self.len == 0
    }
    pub const fn len_usize(self) -> usize {
        self.len as usize
    }
    pub(crate) const fn shift(self, offset: u32) -> Self {
        if self.len == 0 {
            Self::EMPTY
        } else {
            Self { start: self.start + offset, len: self.len }
        }
    }
}

/// Byte width for memory load and store operations.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum MemWidth {
    B1 = 1,
    B2 = 2,
    B4 = 4,
    B8 = 8,
}

impl MemWidth {
    pub const fn bytes(self) -> u64 {
        self as u64
    }

    pub(crate) const fn to_u8(self) -> u8 {
        self as u8
    }

    pub(crate) const fn from_u8(v: u8) -> Option<Self> {
        match v {
            1 => Some(Self::B1),
            2 => Some(Self::B2),
            4 => Some(Self::B4),
            8 => Some(Self::B8),
            _ => None,
        }
    }
}

/// Deterministic unary WebAssembly operations.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum UnOp {
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
}

impl UnOp {
    pub(crate) const fn to_u8(self) -> u8 {
        self as u8
    }

    pub(crate) const fn from_u8(v: u8) -> Option<Self> {
        match v {
            0 => Some(Self::I32Eqz),
            1 => Some(Self::I64Eqz),
            2 => Some(Self::I32Clz),
            3 => Some(Self::I32Ctz),
            4 => Some(Self::I32Popcnt),
            5 => Some(Self::I64Clz),
            6 => Some(Self::I64Ctz),
            7 => Some(Self::I64Popcnt),
            8 => Some(Self::I32WrapI64),
            9 => Some(Self::I64ExtendI32S),
            10 => Some(Self::I64ExtendI32U),
            11 => Some(Self::I32Extend8S),
            12 => Some(Self::I32Extend16S),
            13 => Some(Self::I64Extend8S),
            14 => Some(Self::I64Extend16S),
            15 => Some(Self::I64Extend32S),
            _ => None,
        }
    }

    pub fn input_ty(self) -> ValType {
        match self {
            Self::I64Eqz
            | Self::I64Clz
            | Self::I64Ctz
            | Self::I64Popcnt
            | Self::I32WrapI64
            | Self::I64Extend8S
            | Self::I64Extend16S
            | Self::I64Extend32S => ValType::I64,
            _ => ValType::I32,
        }
    }
    pub fn output_ty(self) -> ValType {
        match self {
            Self::I64Clz
            | Self::I64Ctz
            | Self::I64Popcnt
            | Self::I64ExtendI32S
            | Self::I64ExtendI32U
            | Self::I64Extend8S
            | Self::I64Extend16S
            | Self::I64Extend32S => ValType::I64,
            _ => ValType::I32,
        }
    }
}

/// Deterministic binary WebAssembly operations.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum BinOp {
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
}

impl BinOp {
    pub(crate) const fn to_u8(self) -> u8 {
        self as u8
    }

    pub(crate) const fn from_u8(v: u8) -> Option<Self> {
        match v {
            0 => Some(Self::I32Eq),
            1 => Some(Self::I32Ne),
            2 => Some(Self::I32LtS),
            3 => Some(Self::I32LtU),
            4 => Some(Self::I32GtS),
            5 => Some(Self::I32GtU),
            6 => Some(Self::I32LeS),
            7 => Some(Self::I32LeU),
            8 => Some(Self::I32GeS),
            9 => Some(Self::I32GeU),
            10 => Some(Self::I64Eq),
            11 => Some(Self::I64Ne),
            12 => Some(Self::I64LtS),
            13 => Some(Self::I64LtU),
            14 => Some(Self::I64GtS),
            15 => Some(Self::I64GtU),
            16 => Some(Self::I64LeS),
            17 => Some(Self::I64LeU),
            18 => Some(Self::I64GeS),
            19 => Some(Self::I64GeU),
            20 => Some(Self::I32Add),
            21 => Some(Self::I32Sub),
            22 => Some(Self::I32Mul),
            23 => Some(Self::I32DivS),
            24 => Some(Self::I32DivU),
            25 => Some(Self::I32RemS),
            26 => Some(Self::I32RemU),
            27 => Some(Self::I64Add),
            28 => Some(Self::I64Sub),
            29 => Some(Self::I64Mul),
            30 => Some(Self::I64DivS),
            31 => Some(Self::I64DivU),
            32 => Some(Self::I64RemS),
            33 => Some(Self::I64RemU),
            34 => Some(Self::I32And),
            35 => Some(Self::I32Or),
            36 => Some(Self::I32Xor),
            37 => Some(Self::I32Shl),
            38 => Some(Self::I32ShrS),
            39 => Some(Self::I32ShrU),
            40 => Some(Self::I32Rotl),
            41 => Some(Self::I32Rotr),
            42 => Some(Self::I64And),
            43 => Some(Self::I64Or),
            44 => Some(Self::I64Xor),
            45 => Some(Self::I64Shl),
            46 => Some(Self::I64ShrS),
            47 => Some(Self::I64ShrU),
            48 => Some(Self::I64Rotl),
            49 => Some(Self::I64Rotr),
            _ => None,
        }
    }

    pub fn operand_ty(self) -> ValType {
        let x = self as u8;
        if (Self::I64Eq as u8..=Self::I64GeU as u8).contains(&x)
            || (Self::I64Add as u8..=Self::I64RemU as u8).contains(&x)
            || x >= Self::I64And as u8
        {
            ValType::I64
        } else {
            ValType::I32
        }
    }
    pub fn output_ty(self) -> ValType {
        let x = self as u8;
        if (Self::I64Add as u8..=Self::I64RemU as u8).contains(&x) || x >= Self::I64And as u8 {
            ValType::I64
        } else {
            ValType::I32
        }
    }
}

/// Value-producing primitive expression in `GnomonIR`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Op {
    ConstI32(i32),
    ConstI64(i64),
    Copy(ValId),
    Select { cond: ValId, true_val: ValId, false_val: ValId },
    GlobalGet(GlobalId),
    Un(UnOp, ValId),
    Bin(BinOp, ValId, ValId),
    Load { mem: MemId, addr: ValId, offset: u32, width: MemWidth, signed: bool, result_ty: ValType },
    MemorySize(MemId),
    MemoryGrow { mem: MemId, delta: ValId },
}

/// Side-effecting statement primitive in `GnomonIR`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EffectOp {
    Store { mem: MemId, addr: ValId, offset: u32, width: MemWidth, val: ValId },
    MemoryCopy { dst_mem: MemId, src_mem: MemId, dst: ValId, src: ValId, len: ValId },
    MemoryFill { mem: MemId, dst: ValId, val: ValId, len: ValId },
    GlobalSet { id: GlobalId, val: ValId },
    Trap(TrapCode),
    Nop,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CallTarget {
    Func(FuncId),
    Host(HostCallId),
    Stratum(StratumId),
}

/// Single `Copy` SSA statement inside a `RegionNode::Block`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Stmt {
    Let { dst: ValId, ty: ValType, op: Op },
    Effect(EffectOp),
    Region { results: Span, region: RegionNodeId },
    Call { results: Span, target: CallTarget, args: Span },
    Yield(Span),
    Break { depth: u32, cond: Option<ValId>, values: Span },
    Continue { depth: u32, cond: Option<ValId>, values: Span },
    Return(Span),
}

/// Structured hierarchical `Copy` Region-SSA node.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RegionNode {
    Block(Span),
    IfElse {
        cond: ValId,
        then_region: RegionNodeId,
        else_region: RegionNodeId,
        results: Span,
    },
    BoundedLoop {
        max_iters: u32,
        init_vars: Span,
        state_vars: Span,
        body: RegionNodeId,
    },
    InvariantLoop {
        init_vars: Span,
        state_vars: Span,
        cond: RegionNodeId,
        invariant_pred: RegionNodeId,
        fuel_measure: RegionNodeId,
        body: RegionNodeId,
    },
}

impl RegionNode {
    pub(crate) const fn shift(self, offset: u32) -> Self {
        match self {
            Self::Block(s) => Self::Block(s.shift(offset)),
            Self::IfElse { cond, then_region, else_region, results } => Self::IfElse {
                cond,
                then_region: RegionNodeId(then_region.0 + offset),
                else_region: RegionNodeId(else_region.0 + offset),
                results: results.shift(offset),
            },
            Self::BoundedLoop { max_iters, init_vars, state_vars, body } => Self::BoundedLoop {
                max_iters,
                init_vars: init_vars.shift(offset),
                state_vars: state_vars.shift(offset),
                body: RegionNodeId(body.0 + offset),
            },
            Self::InvariantLoop {
                init_vars,
                state_vars,
                cond,
                invariant_pred,
                fuel_measure,
                body,
            } => Self::InvariantLoop {
                init_vars: init_vars.shift(offset),
                state_vars: state_vars.shift(offset),
                cond: RegionNodeId(cond.0 + offset),
                invariant_pred: RegionNodeId(invariant_pred.0 + offset),
                fuel_measure: RegionNodeId(fuel_measure.0 + offset),
                body: RegionNodeId(body.0 + offset),
            },
        }
    }
}

pub(crate) const TAG_VAL: u8 = 0;
pub(crate) const TAG_VAR: u8 = 1;
pub(crate) const TAG_TY: u8 = 2;
pub(crate) const TAG_NODE_BLOCK: u8 = 3;
pub(crate) const TAG_NODE_IF: u8 = 4;
pub(crate) const TAG_NODE_BLOOP: u8 = 5;
pub(crate) const TAG_NODE_ILOOP: u8 = 6;
pub(crate) const TAG_STMT_LET: u8 = 7;
pub(crate) const TAG_STMT_EFFECT: u8 = 8;
pub(crate) const TAG_STMT_REGION: u8 = 9;
pub(crate) const TAG_STMT_CALL: u8 = 10;
pub(crate) const TAG_STMT_YIELD: u8 = 11;
pub(crate) const TAG_STMT_BREAK: u8 = 12;
pub(crate) const TAG_STMT_CONTINUE: u8 = 13;
pub(crate) const TAG_STMT_RETURN: u8 = 14;

pub(crate) const OP_CONST_I32: u8 = 0;
pub(crate) const OP_CONST_I64: u8 = 1;
pub(crate) const OP_COPY: u8 = 2;
pub(crate) const OP_SELECT: u8 = 3;
pub(crate) const OP_GLOBAL_GET: u8 = 4;
pub(crate) const OP_UN: u8 = 5;
pub(crate) const OP_BIN: u8 = 6;
pub(crate) const OP_LOAD: u8 = 7;
pub(crate) const OP_MEM_SIZE: u8 = 8;
pub(crate) const OP_MEM_GROW: u8 = 9;

pub(crate) const EFF_STORE: u8 = 0;
pub(crate) const EFF_MEM_COPY: u8 = 1;
pub(crate) const EFF_MEM_FILL: u8 = 2;
pub(crate) const EFF_GLOBAL_SET: u8 = 3;
pub(crate) const EFF_TRAP: u8 = 4;
pub(crate) const EFF_NOP: u8 = 5;

pub(crate) const CALL_FUNC: u8 = 0;
pub(crate) const CALL_HOST: u8 = 1;
pub(crate) const CALL_STRATUM: u8 = 2;

#[inline]
const fn shift_pair(start: u32, len: u32, offset: u32) -> (u32, u32) {
    if len == 0 { (0, 0) } else { (start + offset, len) }
}

/// Flat zero-union, zero-padding arena element (`36` bytes, `Copy`, `!needs_drop`)
/// stored inside `Region::pool`. Encoding items as scalar fields instead of nested
/// tagged unions eliminates enum-union padding nondets during bounded model checking.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IrSlot {
    pub tag: u8,
    pub sub: u8,
    pub aux: u16,
    pub w0: u32,
    pub w1: u32,
    pub w2: u32,
    pub w3: u32,
    pub w4: u32,
    pub w5: u32,
    pub w6: u32,
    pub w7: u32,
}

impl IrSlot {
    pub const ZERO: Self = Self {
        tag: TAG_VAL,
        sub: 0,
        aux: 0,
        w0: 0,
        w1: 0,
        w2: 0,
        w3: 0,
        w4: 0,
        w5: 0,
        w6: 0,
        w7: 0,
    };

    #[inline]
    const fn base(tag: u8, sub: u8, aux: u16) -> Self {
        Self { tag, sub, aux, w0: 0, w1: 0, w2: 0, w3: 0, w4: 0, w5: 0, w6: 0, w7: 0 }
    }

    pub const fn val(v: ValId) -> Self {
        let mut s = Self::base(TAG_VAL, 0, 0);
        s.w0 = v.0;
        s
    }

    pub const fn var(v: ValId, ty: ValType) -> Self {
        let mut s = Self::base(TAG_VAR, 0, ty.to_u8() as u16);
        s.w0 = v.0;
        s
    }

    pub const fn ty(t: ValType) -> Self {
        Self::base(TAG_TY, 0, t.to_u8() as u16)
    }

    pub const fn from_node(node: RegionNode) -> Self {
        match node {
            RegionNode::Block(span) => {
                let mut s = Self::base(TAG_NODE_BLOCK, 0, 0);
                s.w0 = span.start;
                s.w1 = span.len;
                s
            }
            RegionNode::IfElse { cond, then_region, else_region, results } => {
                let mut s = Self::base(TAG_NODE_IF, 0, 0);
                s.w0 = cond.0;
                s.w1 = then_region.0;
                s.w2 = else_region.0;
                s.w3 = results.start;
                s.w4 = results.len;
                s
            }
            RegionNode::BoundedLoop { max_iters, init_vars, state_vars, body } => {
                let mut s = Self::base(TAG_NODE_BLOOP, 0, 0);
                s.w0 = max_iters;
                s.w1 = init_vars.start;
                s.w2 = init_vars.len;
                s.w3 = state_vars.start;
                s.w4 = state_vars.len;
                s.w5 = body.0;
                s
            }
            RegionNode::InvariantLoop {
                init_vars,
                state_vars,
                cond,
                invariant_pred,
                fuel_measure,
                body,
            } => Self {
                tag: TAG_NODE_ILOOP,
                sub: 0,
                aux: 0,
                w0: init_vars.start,
                w1: init_vars.len,
                w2: state_vars.start,
                w3: state_vars.len,
                w4: cond.0,
                w5: invariant_pred.0,
                w6: fuel_measure.0,
                w7: body.0,
            },
        }
    }

    pub const fn let_op(dst: ValId, ty: ValType, op: Op) -> Self {
        let ty_bit = ty.to_u8() as u16;
        match op {
            Op::ConstI32(x) => {
                let mut s = Self::base(TAG_STMT_LET, OP_CONST_I32, ty_bit);
                s.w0 = dst.0;
                s.w1 = x as u32;
                s
            }
            Op::ConstI64(x) => {
                let mut s = Self::base(TAG_STMT_LET, OP_CONST_I64, ty_bit);
                s.w0 = dst.0;
                s.w1 = x as u32;
                s.w2 = ((x as u64) >> 32) as u32;
                s
            }
            Op::Copy(v) => {
                let mut s = Self::base(TAG_STMT_LET, OP_COPY, ty_bit);
                s.w0 = dst.0;
                s.w1 = v.0;
                s
            }
            Op::Select { cond, true_val, false_val } => {
                let mut s = Self::base(TAG_STMT_LET, OP_SELECT, ty_bit);
                s.w0 = dst.0;
                s.w1 = cond.0;
                s.w2 = true_val.0;
                s.w3 = false_val.0;
                s
            }
            Op::GlobalGet(id) => {
                let mut s = Self::base(TAG_STMT_LET, OP_GLOBAL_GET, ty_bit);
                s.w0 = dst.0;
                s.w1 = id.0;
                s
            }
            Op::Un(u, v) => {
                let mut s =
                    Self::base(TAG_STMT_LET, OP_UN, ty_bit | ((u.to_u8() as u16) << 1));
                s.w0 = dst.0;
                s.w1 = v.0;
                s
            }
            Op::Bin(b, l, r) => {
                let mut s =
                    Self::base(TAG_STMT_LET, OP_BIN, ty_bit | ((b.to_u8() as u16) << 1));
                s.w0 = dst.0;
                s.w1 = l.0;
                s.w2 = r.0;
                s
            }
            Op::Load { mem, addr, offset, width, signed, result_ty } => {
                let aux = ty_bit
                    | ((width.to_u8() as u16) << 1)
                    | ((signed as u16) << 5)
                    | ((result_ty.to_u8() as u16) << 6);
                let mut s = Self::base(TAG_STMT_LET, OP_LOAD, aux);
                s.w0 = dst.0;
                s.w1 = mem.0 as u32;
                s.w2 = addr.0;
                s.w3 = offset;
                s
            }
            Op::MemorySize(mem) => {
                let mut s = Self::base(TAG_STMT_LET, OP_MEM_SIZE, ty_bit);
                s.w0 = dst.0;
                s.w1 = mem.0 as u32;
                s
            }
            Op::MemoryGrow { mem, delta } => {
                let mut s = Self::base(TAG_STMT_LET, OP_MEM_GROW, ty_bit);
                s.w0 = dst.0;
                s.w1 = mem.0 as u32;
                s.w2 = delta.0;
                s
            }
        }
    }

    pub const fn effect(eff: EffectOp) -> Self {
        match eff {
            EffectOp::Store { mem, addr, offset, width, val } => {
                let mut s = Self::base(TAG_STMT_EFFECT, EFF_STORE, width.to_u8() as u16);
                s.w0 = mem.0 as u32;
                s.w1 = addr.0;
                s.w2 = offset;
                s.w3 = val.0;
                s
            }
            EffectOp::MemoryCopy { dst_mem, src_mem, dst, src, len } => {
                let mut s = Self::base(TAG_STMT_EFFECT, EFF_MEM_COPY, 0);
                s.w0 = dst_mem.0 as u32;
                s.w1 = src_mem.0 as u32;
                s.w2 = dst.0;
                s.w3 = src.0;
                s.w4 = len.0;
                s
            }
            EffectOp::MemoryFill { mem, dst, val, len } => {
                let mut s = Self::base(TAG_STMT_EFFECT, EFF_MEM_FILL, 0);
                s.w0 = mem.0 as u32;
                s.w1 = dst.0;
                s.w2 = val.0;
                s.w3 = len.0;
                s
            }
            EffectOp::GlobalSet { id, val } => {
                let mut s = Self::base(TAG_STMT_EFFECT, EFF_GLOBAL_SET, 0);
                s.w0 = id.0;
                s.w1 = val.0;
                s
            }
            EffectOp::Trap(code) => Self::base(TAG_STMT_EFFECT, EFF_TRAP, code.to_u8() as u16),
            EffectOp::Nop => Self::base(TAG_STMT_EFFECT, EFF_NOP, 0),
        }
    }

    pub const fn region_stmt(results: Span, region: RegionNodeId) -> Self {
        let mut s = Self::base(TAG_STMT_REGION, 0, 0);
        s.w0 = results.start;
        s.w1 = results.len;
        s.w2 = region.0;
        s
    }

    pub const fn call(results: Span, target: CallTarget, args: Span) -> Self {
        let mut s = Self::base(TAG_STMT_CALL, 0, 0);
        match target {
            CallTarget::Func(f) => {
                s.sub = CALL_FUNC;
                s.w2 = f.0;
            }
            CallTarget::Host(h) => {
                s.sub = CALL_HOST;
                s.w2 = h.0;
            }
            CallTarget::Stratum(sid) => {
                s.sub = CALL_STRATUM;
                s.w2 = sid.0;
            }
        }
        s.w0 = results.start;
        s.w1 = results.len;
        s.w3 = args.start;
        s.w4 = args.len;
        s
    }

    pub const fn yield_span(vs: Span) -> Self {
        let mut s = Self::base(TAG_STMT_YIELD, 0, 0);
        s.w0 = vs.start;
        s.w1 = vs.len;
        s
    }

    pub const fn return_span(vs: Span) -> Self {
        let mut s = Self::base(TAG_STMT_RETURN, 0, 0);
        s.w0 = vs.start;
        s.w1 = vs.len;
        s
    }

    const fn flow_stmt(tag: u8, depth: u32, cond: Option<ValId>, values: Span) -> Self {
        let mut s = Self::base(tag, 0, 0);
        if let Some(v) = cond {
            s.sub = 1;
            s.w1 = v.0;
        }
        s.w0 = depth;
        s.w2 = values.start;
        s.w3 = values.len;
        s
    }

    pub const fn break_stmt(depth: u32, cond: Option<ValId>, values: Span) -> Self {
        Self::flow_stmt(TAG_STMT_BREAK, depth, cond, values)
    }

    pub const fn continue_stmt(depth: u32, cond: Option<ValId>, values: Span) -> Self {
        Self::flow_stmt(TAG_STMT_CONTINUE, depth, cond, values)
    }

    pub const fn from_stmt(stmt: Stmt) -> Self {
        match stmt {
            Stmt::Let { dst, ty, op } => Self::let_op(dst, ty, op),
            Stmt::Effect(eff) => Self::effect(eff),
            Stmt::Region { results, region } => Self::region_stmt(results, region),
            Stmt::Call { results, target, args } => Self::call(results, target, args),
            Stmt::Yield(vs) => Self::yield_span(vs),
            Stmt::Break { depth, cond, values } => Self::break_stmt(depth, cond, values),
            Stmt::Continue { depth, cond, values } => Self::continue_stmt(depth, cond, values),
            Stmt::Return(vs) => Self::return_span(vs),
        }
    }

    #[inline]
    pub const fn is_stmt(self) -> bool {
        self.tag >= TAG_STMT_LET && self.tag <= TAG_STMT_RETURN
    }

    #[inline]
    pub const fn is_node(self) -> bool {
        self.tag >= TAG_NODE_BLOCK && self.tag <= TAG_NODE_ILOOP
    }

    pub const fn to_val(self) -> Option<ValId> {
        if self.tag == TAG_VAL { Some(ValId(self.w0)) } else { None }
    }

    pub const fn to_var(self) -> Option<(ValId, ValType)> {
        if self.tag == TAG_VAR {
            let Some(ty) = ValType::from_u8(self.aux as u8) else { return None };
            Some((ValId(self.w0), ty))
        } else {
            None
        }
    }

    pub const fn to_ty(self) -> Option<ValType> {
        if self.tag == TAG_TY { ValType::from_u8(self.aux as u8) } else { None }
    }

    pub const fn to_node(self) -> Option<RegionNode> {
        match self.tag {
            TAG_NODE_BLOCK => Some(RegionNode::Block(Span { start: self.w0, len: self.w1 })),
            TAG_NODE_IF => Some(RegionNode::IfElse {
                cond: ValId(self.w0),
                then_region: RegionNodeId(self.w1),
                else_region: RegionNodeId(self.w2),
                results: Span { start: self.w3, len: self.w4 },
            }),
            TAG_NODE_BLOOP => Some(RegionNode::BoundedLoop {
                max_iters: self.w0,
                init_vars: Span { start: self.w1, len: self.w2 },
                state_vars: Span { start: self.w3, len: self.w4 },
                body: RegionNodeId(self.w5),
            }),
            TAG_NODE_ILOOP => Some(RegionNode::InvariantLoop {
                init_vars: Span { start: self.w0, len: self.w1 },
                state_vars: Span { start: self.w2, len: self.w3 },
                cond: RegionNodeId(self.w4),
                invariant_pred: RegionNodeId(self.w5),
                fuel_measure: RegionNodeId(self.w6),
                body: RegionNodeId(self.w7),
            }),
            _ => None,
        }
    }

    pub const fn to_let_op(self) -> Option<(ValId, ValType, Op)> {
        if self.tag != TAG_STMT_LET {
            return None;
        }
        let Some(ty) = ValType::from_u8((self.aux & 1) as u8) else { return None };
        let dst = ValId(self.w0);
        let op = match self.sub {
            OP_CONST_I32 => Op::ConstI32(self.w1 as i32),
            OP_CONST_I64 => Op::ConstI64((((self.w2 as u64) << 32) | (self.w1 as u64)) as i64),
            OP_COPY => Op::Copy(ValId(self.w1)),
            OP_SELECT => Op::Select {
                cond: ValId(self.w1),
                true_val: ValId(self.w2),
                false_val: ValId(self.w3),
            },
            OP_GLOBAL_GET => Op::GlobalGet(GlobalId(self.w1)),
            OP_UN => {
                let Some(u) = UnOp::from_u8((self.aux >> 1) as u8) else { return None };
                Op::Un(u, ValId(self.w1))
            }
            OP_BIN => {
                let Some(b) = BinOp::from_u8((self.aux >> 1) as u8) else { return None };
                Op::Bin(b, ValId(self.w1), ValId(self.w2))
            }
            OP_LOAD => {
                let Some(width) = MemWidth::from_u8(((self.aux >> 1) & 0xF) as u8) else {
                    return None;
                };
                let signed = ((self.aux >> 5) & 1) != 0;
                let Some(result_ty) = ValType::from_u8(((self.aux >> 6) & 1) as u8) else {
                    return None;
                };
                Op::Load {
                    mem: MemId(self.w1 as u16),
                    addr: ValId(self.w2),
                    offset: self.w3,
                    width,
                    signed,
                    result_ty,
                }
            }
            OP_MEM_SIZE => Op::MemorySize(MemId(self.w1 as u16)),
            OP_MEM_GROW => Op::MemoryGrow { mem: MemId(self.w1 as u16), delta: ValId(self.w2) },
            _ => return None,
        };
        Some((dst, ty, op))
    }

    pub const fn to_effect(self) -> Option<EffectOp> {
        if self.tag != TAG_STMT_EFFECT {
            return None;
        }
        match self.sub {
            EFF_STORE => {
                let Some(width) = MemWidth::from_u8(self.aux as u8) else { return None };
                Some(EffectOp::Store {
                    mem: MemId(self.w0 as u16),
                    addr: ValId(self.w1),
                    offset: self.w2,
                    width,
                    val: ValId(self.w3),
                })
            }
            EFF_MEM_COPY => Some(EffectOp::MemoryCopy {
                dst_mem: MemId(self.w0 as u16),
                src_mem: MemId(self.w1 as u16),
                dst: ValId(self.w2),
                src: ValId(self.w3),
                len: ValId(self.w4),
            }),
            EFF_MEM_FILL => Some(EffectOp::MemoryFill {
                mem: MemId(self.w0 as u16),
                dst: ValId(self.w1),
                val: ValId(self.w2),
                len: ValId(self.w3),
            }),
            EFF_GLOBAL_SET => Some(EffectOp::GlobalSet { id: GlobalId(self.w0), val: ValId(self.w1) }),
            EFF_TRAP => {
                let Some(code) = TrapCode::from_u8(self.aux as u8) else { return None };
                Some(EffectOp::Trap(code))
            }
            EFF_NOP => Some(EffectOp::Nop),
            _ => None,
        }
    }

    pub const fn to_stmt(self) -> Option<Stmt> {
        match self.tag {
            TAG_STMT_LET => {
                let Some((dst, ty, op)) = self.to_let_op() else { return None };
                Some(Stmt::Let { dst, ty, op })
            }
            TAG_STMT_EFFECT => {
                let Some(eff) = self.to_effect() else { return None };
                Some(Stmt::Effect(eff))
            }
            TAG_STMT_REGION => Some(Stmt::Region {
                results: Span { start: self.w0, len: self.w1 },
                region: RegionNodeId(self.w2),
            }),
            TAG_STMT_CALL => {
                let target = match self.sub {
                    CALL_FUNC => CallTarget::Func(FuncId(self.w2)),
                    CALL_HOST => CallTarget::Host(HostCallId(self.w2)),
                    CALL_STRATUM => CallTarget::Stratum(StratumId(self.w2)),
                    _ => return None,
                };
                Some(Stmt::Call {
                    results: Span { start: self.w0, len: self.w1 },
                    target,
                    args: Span { start: self.w3, len: self.w4 },
                })
            }
            TAG_STMT_YIELD => Some(Stmt::Yield(Span { start: self.w0, len: self.w1 })),
            TAG_STMT_BREAK => Some(Stmt::Break {
                depth: self.w0,
                cond: if self.sub != 0 { Some(ValId(self.w1)) } else { None },
                values: Span { start: self.w2, len: self.w3 },
            }),
            TAG_STMT_CONTINUE => Some(Stmt::Continue {
                depth: self.w0,
                cond: if self.sub != 0 { Some(ValId(self.w1)) } else { None },
                values: Span { start: self.w2, len: self.w3 },
            }),
            TAG_STMT_RETURN => Some(Stmt::Return(Span { start: self.w0, len: self.w1 })),
            _ => None,
        }
    }

    pub(crate) const fn shift(self, offset: u32) -> Self {
        let mut s = self;
        match s.tag {
            TAG_NODE_BLOCK | TAG_STMT_YIELD | TAG_STMT_RETURN => {
                (s.w0, s.w1) = shift_pair(s.w0, s.w1, offset);
            }
            TAG_NODE_IF => {
                s.w1 += offset;
                s.w2 += offset;
                (s.w3, s.w4) = shift_pair(s.w3, s.w4, offset);
            }
            TAG_NODE_BLOOP => {
                (s.w1, s.w2) = shift_pair(s.w1, s.w2, offset);
                (s.w3, s.w4) = shift_pair(s.w3, s.w4, offset);
                s.w5 += offset;
            }
            TAG_NODE_ILOOP => {
                (s.w0, s.w1) = shift_pair(s.w0, s.w1, offset);
                (s.w2, s.w3) = shift_pair(s.w2, s.w3, offset);
                s.w4 += offset;
                s.w5 += offset;
                s.w6 += offset;
                s.w7 += offset;
            }
            TAG_STMT_REGION => {
                (s.w0, s.w1) = shift_pair(s.w0, s.w1, offset);
                s.w2 += offset;
            }
            TAG_STMT_CALL => {
                (s.w0, s.w1) = shift_pair(s.w0, s.w1, offset);
                (s.w3, s.w4) = shift_pair(s.w3, s.w4, offset);
            }
            TAG_STMT_BREAK | TAG_STMT_CONTINUE => {
                (s.w2, s.w3) = shift_pair(s.w2, s.w3, offset);
            }
            _ => {}
        }
        s
    }
}

/// Inline capacity of `SlotPool` before spilling to heap `Vec<IrSlot>`.
pub const SLOT_POOL_INLINE: usize = 10;

/// Small-vector arena storage for `IrSlot`s: stores up to 10 flat 36-byte
/// slots inline with zero heap allocation, spilling seamlessly to `Vec<IrSlot>`
/// on the 11th+ slot.
#[derive(Debug)]
pub struct SlotPool {
    inline: [IrSlot; SLOT_POOL_INLINE],
    inline_len: usize,
    spill: Vec<IrSlot>,
}

impl SlotPool {
    pub const fn new() -> Self {
        Self { inline: [IrSlot::ZERO; SLOT_POOL_INLINE], inline_len: 0, spill: Vec::new() }
    }

    pub fn with_capacity(cap: usize) -> Self {
        if cap <= SLOT_POOL_INLINE {
            Self::new()
        } else {
            Self {
                inline: [IrSlot::ZERO; SLOT_POOL_INLINE],
                inline_len: 0,
                spill: Vec::with_capacity(cap),
            }
        }
    }

    pub const fn from_single(slot: IrSlot) -> Self {
        let mut inline = [IrSlot::ZERO; SLOT_POOL_INLINE];
        inline[0] = slot;
        Self { inline, inline_len: 1, spill: Vec::new() }
    }

    pub fn from_vec(v: Vec<IrSlot>) -> Self {
        if v.len() <= SLOT_POOL_INLINE {
            let mut p = Self::new();
            let mut i = 0;
            while i < v.len() {
                p.inline[i] = v[i];
                i += 1;
            }
            p.inline_len = v.len();
            p
        } else {
            Self { inline: [IrSlot::ZERO; SLOT_POOL_INLINE], inline_len: 0, spill: v }
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        if self.spill.is_empty() { self.inline_len } else { self.spill.len() }
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.inline_len == 0 && self.spill.is_empty()
    }

    #[inline]
    pub fn as_slice(&self) -> &[IrSlot] {
        if self.spill.is_empty() { &self.inline[..self.inline_len] } else { &self.spill }
    }

    #[cold]
    #[inline(never)]
    fn push_spill(&mut self, slot: IrSlot) {
        if self.spill.is_empty() {
            self.spill.reserve(self.inline_len + 1);
            let mut i = 0;
            while i < self.inline_len {
                self.spill.push(self.inline[i]);
                i += 1;
            }
            self.inline_len = 0;
        }
        self.spill.push(slot);
    }

    #[inline]
    pub fn push(&mut self, slot: IrSlot) {
        if self.spill.is_empty() && self.inline_len < SLOT_POOL_INLINE {
            self.inline[self.inline_len] = slot;
            self.inline_len += 1;
        } else {
            self.push_spill(slot);
        }
    }

    #[cold]
    #[inline(never)]
    fn reserve_spill(&mut self, additional: usize) {
        if self.spill.is_empty() {
            self.spill.reserve(self.inline_len + additional);
            let mut i = 0;
            while i < self.inline_len {
                self.spill.push(self.inline[i]);
                i += 1;
            }
            self.inline_len = 0;
        } else {
            self.spill.reserve(additional);
        }
    }

    pub fn reserve(&mut self, additional: usize) {
        if self.spill.is_empty() && self.inline_len.saturating_add(additional) <= SLOT_POOL_INLINE {
            return;
        }
        self.reserve_spill(additional);
    }

    #[cold]
    #[inline(never)]
    fn extend_spill(&mut self, slice: &[IrSlot]) {
        if self.spill.is_empty() {
            self.spill.reserve(self.inline_len + slice.len());
            let mut i = 0;
            while i < self.inline_len {
                self.spill.push(self.inline[i]);
                i += 1;
            }
            self.inline_len = 0;
        }
        self.spill.extend_from_slice(slice);
    }

    pub fn extend_from_slice(&mut self, slice: &[IrSlot]) {
        if self.spill.is_empty() && self.inline_len.saturating_add(slice.len()) <= SLOT_POOL_INLINE
        {
            let mut i = 0;
            while i < slice.len() {
                self.inline[self.inline_len] = slice[i];
                self.inline_len += 1;
                i += 1;
            }
        } else {
            self.extend_spill(slice);
        }
    }

    pub fn clear(&mut self) {
        self.inline_len = 0;
        self.spill.clear();
    }

    #[cold]
    #[inline(never)]
    fn clone_spill(&self) -> Self {
        Self { inline: [IrSlot::ZERO; SLOT_POOL_INLINE], inline_len: 0, spill: self.spill.clone() }
    }
}

impl Default for SlotPool {
    fn default() -> Self {
        Self::new()
    }
}

impl Clone for SlotPool {
    fn clone(&self) -> Self {
        if self.spill.is_empty() {
            Self { inline: self.inline, inline_len: self.inline_len, spill: Vec::new() }
        } else {
            self.clone_spill()
        }
    }
}

impl PartialEq for SlotPool {
    fn eq(&self, other: &Self) -> bool {
        if self.spill.is_empty() && other.spill.is_empty() {
            if self.inline_len != other.inline_len {
                return false;
            }
            let mut i = 0;
            while i < self.inline_len && i < other.inline_len {
                if self.inline[i] != other.inline[i] {
                    return false;
                }
                i += 1;
            }
            true
        } else {
            self.as_slice() == other.as_slice()
        }
    }
}

impl Eq for SlotPool {}

impl core::ops::Deref for SlotPool {
    type Target = [IrSlot];
    #[inline]
    fn deref(&self) -> &[IrSlot] {
        self.as_slice()
    }
}

/// Flat arena-backed structured Region-SSA program fragment.
#[derive(Clone, Debug)]
pub struct Region {
    pub root: RegionNode,
    pub pool: SlotPool,
}

impl Default for Region {
    fn default() -> Self {
        Self::empty()
    }
}

impl Region {
    pub const fn empty() -> Self {
        Self { root: RegionNode::Block(Span::EMPTY), pool: SlotPool::new() }
    }

    pub fn builder() -> RegionBuilder {
        RegionBuilder::new()
    }

    pub fn build(f: impl FnOnce(&mut RegionBuilder)) -> Self {
        let mut b = RegionBuilder::new();
        f(&mut b);
        b.finish()
    }

    pub fn is_empty_block(&self) -> bool {
        matches!(self.root, RegionNode::Block(s) if s.is_empty())
    }

    pub fn as_ref(&self) -> RegionRef<'_> {
        RegionRef { region: self, node: self.root }
    }

    /// Creates a 1-statement `Block([stmt])` region.
    pub fn single_stmt(stmt: Stmt) -> Self {
        Self::single_slot(IrSlot::from_stmt(stmt))
    }

    /// Creates a 1-statement `Block([slot])` region directly from an encoded `IrSlot`.
    pub fn single_slot(slot: IrSlot) -> Self {
        Self { root: RegionNode::Block(Span { start: 0, len: 1 }), pool: SlotPool::from_single(slot) }
    }

    /// Creates a 1-statement `Call` block without reallocation.
    pub fn call_stmt(results: &[(ValId, ValType)], target: CallTarget, args: &[ValId]) -> Self {
        if results.is_empty() && args.is_empty() {
            return Self::single_slot(IrSlot::call(Span::EMPTY, target, Span::EMPTY));
        }
        let total = results.len() + args.len() + 1;
        let mut pool = SlotPool::with_capacity(total);
        let res_span = if results.is_empty() {
            Span::EMPTY
        } else {
            let s = pool.len() as u32;
            let mut i = 0;
            while i < results.len() {
                pool.push(IrSlot::var(results[i].0, results[i].1));
                i += 1;
            }
            Span { start: s, len: results.len() as u32 }
        };
        let arg_span = if args.is_empty() {
            Span::EMPTY
        } else {
            let s = pool.len() as u32;
            let mut i = 0;
            while i < args.len() {
                pool.push(IrSlot::val(args[i]));
                i += 1;
            }
            Span { start: s, len: args.len() as u32 }
        };
        let pos = pool.len() as u32;
        pool.push(IrSlot::call(res_span, target, arg_span));
        Self { root: RegionNode::Block(Span { start: pos, len: 1 }), pool }
    }

    /// Creates a `Block([Yield(vals)])` region without reallocation.
    pub fn yield_vals(vals: &[ValId]) -> Self {
        let mut pool = SlotPool::with_capacity(vals.len() + 1);
        let mut i = 0;
        while i < vals.len() {
            pool.push(IrSlot::val(vals[i]));
            i += 1;
        }
        let vs = if vals.is_empty() { Span::EMPTY } else { Span { start: 0, len: vals.len() as u32 } };
        pool.push(IrSlot::yield_span(vs));
        Self { root: RegionNode::Block(Span { start: vals.len() as u32, len: 1 }), pool }
    }

    pub fn if_else(
        cond: ValId,
        then_region: &Region,
        else_region: &Region,
        results: &[ValType],
    ) -> Self {
        let t_len = if then_region.is_empty_block() { 0 } else { then_region.pool.len() };
        let e_len = if else_region.is_empty_block() { 0 } else { else_region.pool.len() };
        let total = t_len + 1 + e_len + 1 + results.len();
        let mut pool = SlotPool::with_capacity(total);

        let then_node = if t_len == 0 {
            RegionNode::Block(Span::EMPTY)
        } else {
            let off = pool.len() as u32;
            let mut i = 0;
            while i < t_len {
                pool.push(then_region.pool[i].shift(off));
                i += 1;
            }
            then_region.root.shift(off)
        };
        let then_id = RegionNodeId(pool.len() as u32);
        pool.push(IrSlot::from_node(then_node));

        let else_node = if e_len == 0 {
            RegionNode::Block(Span::EMPTY)
        } else {
            let off = pool.len() as u32;
            let mut i = 0;
            while i < e_len {
                pool.push(else_region.pool[i].shift(off));
                i += 1;
            }
            else_region.root.shift(off)
        };
        let else_id = RegionNodeId(pool.len() as u32);
        pool.push(IrSlot::from_node(else_node));

        let res_span = if results.is_empty() {
            Span::EMPTY
        } else {
            let start = pool.len() as u32;
            let mut i = 0;
            while i < results.len() {
                pool.push(IrSlot::ty(results[i]));
                i += 1;
            }
            Span { start, len: results.len() as u32 }
        };

        Self {
            root: RegionNode::IfElse {
                cond,
                then_region: then_id,
                else_region: else_id,
                results: res_span,
            },
            pool,
        }
    }

    pub fn bounded_loop(
        max_iters: u32,
        init_vars: &[ValId],
        state_vars: &[(ValId, ValType)],
        body: &Region,
    ) -> Self {
        let b_len = if body.is_empty_block() { 0 } else { body.pool.len() };
        let total = init_vars.len() + state_vars.len() + b_len + 1;
        let mut pool = SlotPool::with_capacity(total);

        let inits = if init_vars.is_empty() {
            Span::EMPTY
        } else {
            let start = pool.len() as u32;
            let mut i = 0;
            while i < init_vars.len() {
                pool.push(IrSlot::val(init_vars[i]));
                i += 1;
            }
            Span { start, len: init_vars.len() as u32 }
        };
        let states = if state_vars.is_empty() {
            Span::EMPTY
        } else {
            let start = pool.len() as u32;
            let mut i = 0;
            while i < state_vars.len() {
                pool.push(IrSlot::var(state_vars[i].0, state_vars[i].1));
                i += 1;
            }
            Span { start, len: state_vars.len() as u32 }
        };
        let body_node = if b_len == 0 {
            RegionNode::Block(Span::EMPTY)
        } else {
            let off = pool.len() as u32;
            let mut i = 0;
            while i < b_len {
                pool.push(body.pool[i].shift(off));
                i += 1;
            }
            body.root.shift(off)
        };
        let body_id = RegionNodeId(pool.len() as u32);
        pool.push(IrSlot::from_node(body_node));

        Self {
            root: RegionNode::BoundedLoop {
                max_iters,
                init_vars: inits,
                state_vars: states,
                body: body_id,
            },
            pool,
        }
    }

    pub fn invariant_loop(
        init_vars: &[ValId],
        state_vars: &[(ValId, ValType)],
        cond: &Region,
        invariant_pred: &Region,
        fuel_measure: &Region,
        body: &Region,
    ) -> Self {
        let subs = [cond, invariant_pred, fuel_measure, body];
        let sub_lens = [
            if cond.is_empty_block() { 0 } else { cond.pool.len() },
            if invariant_pred.is_empty_block() { 0 } else { invariant_pred.pool.len() },
            if fuel_measure.is_empty_block() { 0 } else { fuel_measure.pool.len() },
            if body.is_empty_block() { 0 } else { body.pool.len() },
        ];
        let total = init_vars.len()
            + state_vars.len()
            + sub_lens[0]
            + sub_lens[1]
            + sub_lens[2]
            + sub_lens[3]
            + 4;
        let mut pool = SlotPool::with_capacity(total);

        let inits = if init_vars.is_empty() {
            Span::EMPTY
        } else {
            let start = pool.len() as u32;
            let mut i = 0;
            while i < init_vars.len() {
                pool.push(IrSlot::val(init_vars[i]));
                i += 1;
            }
            Span { start, len: init_vars.len() as u32 }
        };
        let states = if state_vars.is_empty() {
            Span::EMPTY
        } else {
            let start = pool.len() as u32;
            let mut i = 0;
            while i < state_vars.len() {
                pool.push(IrSlot::var(state_vars[i].0, state_vars[i].1));
                i += 1;
            }
            Span { start, len: state_vars.len() as u32 }
        };

        let mut push_sub = |sub: &Region, slen: usize| -> RegionNodeId {
            let node = if slen == 0 {
                RegionNode::Block(Span::EMPTY)
            } else {
                let off = pool.len() as u32;
                let mut i = 0;
                while i < slen {
                    pool.push(sub.pool[i].shift(off));
                    i += 1;
                }
                sub.root.shift(off)
            };
            let id = RegionNodeId(pool.len() as u32);
            pool.push(IrSlot::from_node(node));
            id
        };
        let cond_id = push_sub(subs[0], sub_lens[0]);
        let inv_id = push_sub(subs[1], sub_lens[1]);
        let fuel_id = push_sub(subs[2], sub_lens[2]);
        let body_id = push_sub(subs[3], sub_lens[3]);

        Self {
            root: RegionNode::InvariantLoop {
                init_vars: inits,
                state_vars: states,
                cond: cond_id,
                invariant_pred: inv_id,
                fuel_measure: fuel_id,
                body: body_id,
            },
            pool,
        }
    }

    pub fn try_node(&self, id: RegionNodeId) -> Option<RegionNode> {
        self.pool.get(id.0 as usize)?.to_node()
    }

    pub fn try_node_below(&self, id: RegionNodeId, limit: usize) -> Option<RegionNode> {
        let idx = id.0 as usize;
        if idx >= limit || idx >= self.pool.len() {
            return None;
        }
        self.pool[idx].to_node()
    }

    pub fn try_stmt_slot(&self, span: Span, idx: u32) -> Option<IrSlot> {
        if idx >= span.len {
            return None;
        }
        let slot = *self.pool.get(span.start.checked_add(idx)? as usize)?;
        if slot.is_stmt() { Some(slot) } else { None }
    }

    pub fn try_stmt(&self, span: Span, idx: u32) -> Option<Stmt> {
        self.try_stmt_slot(span, idx)?.to_stmt()
    }

    pub fn try_val(&self, span: Span, idx: u32) -> Option<ValId> {
        if idx >= span.len {
            return None;
        }
        self.pool.get(span.start.checked_add(idx)? as usize)?.to_val()
    }

    pub fn try_var(&self, span: Span, idx: u32) -> Option<(ValId, ValType)> {
        if idx >= span.len {
            return None;
        }
        self.pool.get(span.start.checked_add(idx)? as usize)?.to_var()
    }

    pub fn try_ty(&self, span: Span, idx: u32) -> Option<ValType> {
        if idx >= span.len {
            return None;
        }
        self.pool.get(span.start.checked_add(idx)? as usize)?.to_ty()
    }

    fn slice(&self, span: Span) -> &[IrSlot] {
        if span.len == 0 {
            return &[];
        }
        let s = span.start as usize;
        let e = s.saturating_add(span.len as usize);
        if e <= self.pool.len() { &self.pool[s..e] } else { &[] }
    }

    pub fn stmts(&self, span: Span) -> StmtIter<'_> {
        StmtIter(self.slice(span).iter())
    }
    pub fn vals(&self, span: Span) -> ValIter<'_> {
        ValIter(self.slice(span).iter())
    }
    pub fn vars(&self, span: Span) -> VarIter<'_> {
        VarIter(self.slice(span).iter())
    }
    pub fn tys(&self, span: Span) -> TyIter<'_> {
        TyIter(self.slice(span).iter())
    }

    pub fn vals_vec(&self, span: Span) -> Vec<ValId> {
        self.vals(span).collect()
    }
    pub fn vars_vec(&self, span: Span) -> Vec<(ValId, ValType)> {
        self.vars(span).collect()
    }
    pub fn tys_vec(&self, span: Span) -> Vec<ValType> {
        self.tys(span).collect()
    }
}

macro_rules! impl_elem_iter {
    ($name:ident, $item:ty, $dec:ident) => {
        #[derive(Clone)]
        pub struct $name<'a>(core::slice::Iter<'a, IrSlot>);
        impl<'a> Iterator for $name<'a> {
            type Item = $item;
            fn next(&mut self) -> Option<Self::Item> {
                self.0.next()?.$dec()
            }
            fn size_hint(&self) -> (usize, Option<usize>) {
                self.0.size_hint()
            }
        }
        impl<'a> DoubleEndedIterator for $name<'a> {
            fn next_back(&mut self) -> Option<Self::Item> {
                self.0.next_back()?.$dec()
            }
        }
        impl<'a> ExactSizeIterator for $name<'a> {}
    };
}

impl_elem_iter!(StmtIter, Stmt, to_stmt);
impl_elem_iter!(ValIter, ValId, to_val);
impl_elem_iter!(VarIter, (ValId, ValType), to_var);
impl_elem_iter!(TyIter, ValType, to_ty);

/// Zero-copy view of a `RegionNode` within its owning `Region`.
#[derive(Clone, Copy, Debug)]
pub struct RegionRef<'a> {
    pub region: &'a Region,
    pub node: RegionNode,
}

impl<'a> RegionRef<'a> {
    pub fn is_empty_block(self) -> bool {
        matches!(self.node, RegionNode::Block(s) if s.is_empty())
    }
    pub fn child(self, id: RegionNodeId) -> Option<Self> {
        Some(Self { region: self.region, node: self.region.try_node(id)? })
    }
    pub fn child_or_empty(self, id: RegionNodeId) -> Self {
        self.child(id).unwrap_or(Self { region: self.region, node: RegionNode::Block(Span::EMPTY) })
    }
    pub fn stmts(self, span: Span) -> StmtIter<'a> {
        self.region.stmts(span)
    }
    pub fn vals(self, span: Span) -> ValIter<'a> {
        self.region.vals(span)
    }
    pub fn vars(self, span: Span) -> VarIter<'a> {
        self.region.vars(span)
    }
    pub fn tys(self, span: Span) -> TyIter<'a> {
        self.region.tys(span)
    }
    pub fn to_owned_region(self) -> Region {
        if self.is_empty_block() {
            Region::empty()
        } else {
            Region { root: self.node, pool: self.region.pool.clone() }
        }
    }
}

impl PartialEq for Region {
    fn eq(&self, other: &Self) -> bool {
        if self.root == other.root && self.pool == other.pool {
            return true;
        }
        Self::eq_nodes(self, self.root, self.pool.len(), other, other.root, other.pool.len(), 0)
    }
}

impl Region {
    fn eq_nodes(
        a: &Self,
        na: RegionNode,
        lim_a: usize,
        b: &Self,
        nb: RegionNode,
        lim_b: usize,
        depth: usize,
    ) -> bool {
        if depth >= 64 {
            return false;
        }
        let eq_vals = |sa: Span, sb: Span| {
            if sa.len != sb.len {
                return false;
            }
            let mut k = 0;
            while k < sa.len && k < sb.len {
                if a.try_val(sa, k) != b.try_val(sb, k) {
                    return false;
                }
                k += 1;
            }
            true
        };
        let eq_vars = |sa: Span, sb: Span| {
            if sa.len != sb.len {
                return false;
            }
            let mut k = 0;
            while k < sa.len && k < sb.len {
                if a.try_var(sa, k) != b.try_var(sb, k) {
                    return false;
                }
                k += 1;
            }
            true
        };
        let eq_tys = |sa: Span, sb: Span| {
            if sa.len != sb.len {
                return false;
            }
            let mut k = 0;
            while k < sa.len && k < sb.len {
                if a.try_ty(sa, k) != b.try_ty(sb, k) {
                    return false;
                }
                k += 1;
            }
            true
        };
        match (na, nb) {
            (RegionNode::Block(sa), RegionNode::Block(sb)) => {
                if sa.len != sb.len {
                    return false;
                }
                let mut i = 0;
                while i < sa.len && i < sb.len {
                    let (Some(s1), Some(s2)) = (a.try_stmt_slot(sa, i), b.try_stmt_slot(sb, i))
                    else {
                        return false;
                    };
                    if s1.tag != s2.tag {
                        return false;
                    }
                    if (s1.tag == TAG_STMT_LET && s2.tag == TAG_STMT_LET)
                        || (s1.tag == TAG_STMT_EFFECT && s2.tag == TAG_STMT_EFFECT)
                    {
                        if s1 != s2 {
                            return false;
                        }
                    } else if s1.tag == TAG_STMT_REGION && s2.tag == TAG_STMT_REGION {
                        let r1 = Span { start: s1.w0, len: s1.w1 };
                        let r2 = Span { start: s2.w0, len: s2.w1 };
                        if !eq_vars(r1, r2) {
                            return false;
                        }
                        let sub1 = RegionNodeId(s1.w2);
                        let sub2 = RegionNodeId(s2.w2);
                        let (Some(ca), Some(cb)) =
                            (a.try_node_below(sub1, lim_a), b.try_node_below(sub2, lim_b))
                        else {
                            return false;
                        };
                        if !Self::eq_nodes(
                            a,
                            ca,
                            sub1.0 as usize,
                            b,
                            cb,
                            sub2.0 as usize,
                            depth + 1,
                        ) {
                            return false;
                        }
                    } else if s1.tag == TAG_STMT_CALL && s2.tag == TAG_STMT_CALL {
                        let r1 = Span { start: s1.w0, len: s1.w1 };
                        let r2 = Span { start: s2.w0, len: s2.w1 };
                        let x1 = Span { start: s1.w3, len: s1.w4 };
                        let x2 = Span { start: s2.w3, len: s2.w4 };
                        if s1.sub != s2.sub
                            || s1.w2 != s2.w2
                            || !eq_vars(r1, r2)
                            || !eq_vals(x1, x2)
                        {
                            return false;
                        }
                    } else if (s1.tag == TAG_STMT_YIELD && s2.tag == TAG_STMT_YIELD)
                        || (s1.tag == TAG_STMT_RETURN && s2.tag == TAG_STMT_RETURN)
                    {
                        let v1 = Span { start: s1.w0, len: s1.w1 };
                        let v2 = Span { start: s2.w0, len: s2.w1 };
                        if !eq_vals(v1, v2) {
                            return false;
                        }
                    } else if (s1.tag == TAG_STMT_BREAK && s2.tag == TAG_STMT_BREAK)
                        || (s1.tag == TAG_STMT_CONTINUE && s2.tag == TAG_STMT_CONTINUE)
                    {
                        let v1 = Span { start: s1.w2, len: s1.w3 };
                        let v2 = Span { start: s2.w2, len: s2.w3 };
                        if s1.sub != s2.sub
                            || s1.w0 != s2.w0
                            || s1.w1 != s2.w1
                            || !eq_vals(v1, v2)
                        {
                            return false;
                        }
                    } else {
                        return false;
                    }
                    i += 1;
                }
                true
            }
            (
                RegionNode::IfElse { cond: c1, then_region: t1, else_region: e1, results: r1 },
                RegionNode::IfElse { cond: c2, then_region: t2, else_region: e2, results: r2 },
            ) if c1 == c2 && eq_tys(r1, r2) => {
                let (Some(ta), Some(tb), Some(ea), Some(eb)) = (
                    a.try_node_below(t1, lim_a),
                    b.try_node_below(t2, lim_b),
                    a.try_node_below(e1, lim_a),
                    b.try_node_below(e2, lim_b),
                ) else {
                    return false;
                };
                Self::eq_nodes(a, ta, t1.0 as usize, b, tb, t2.0 as usize, depth + 1)
                    && Self::eq_nodes(a, ea, e1.0 as usize, b, eb, e2.0 as usize, depth + 1)
            }
            (
                RegionNode::BoundedLoop { max_iters: m1, init_vars: i1, state_vars: s1, body: b1 },
                RegionNode::BoundedLoop { max_iters: m2, init_vars: i2, state_vars: s2, body: b2 },
            ) if m1 == m2 && eq_vals(i1, i2) && eq_vars(s1, s2) => {
                let (Some(ba), Some(bb)) =
                    (a.try_node_below(b1, lim_a), b.try_node_below(b2, lim_b))
                else {
                    return false;
                };
                Self::eq_nodes(a, ba, b1.0 as usize, b, bb, b2.0 as usize, depth + 1)
            }
            (
                RegionNode::InvariantLoop {
                    init_vars: i1,
                    state_vars: s1,
                    cond: c1,
                    invariant_pred: p1,
                    fuel_measure: f1,
                    body: b1,
                },
                RegionNode::InvariantLoop {
                    init_vars: i2,
                    state_vars: s2,
                    cond: c2,
                    invariant_pred: p2,
                    fuel_measure: f2,
                    body: b2,
                },
            ) if eq_vals(i1, i2) && eq_vars(s1, s2) => {
                let (Some(ca), Some(cb), Some(pa), Some(pb), Some(fa), Some(fb), Some(ba), Some(bb)) =
                    (
                        a.try_node_below(c1, lim_a),
                        b.try_node_below(c2, lim_b),
                        a.try_node_below(p1, lim_a),
                        b.try_node_below(p2, lim_b),
                        a.try_node_below(f1, lim_a),
                        b.try_node_below(f2, lim_b),
                        a.try_node_below(b1, lim_a),
                        b.try_node_below(b2, lim_b),
                    )
                else {
                    return false;
                };
                Self::eq_nodes(a, ca, c1.0 as usize, b, cb, c2.0 as usize, depth + 1)
                    && Self::eq_nodes(a, pa, p1.0 as usize, b, pb, p2.0 as usize, depth + 1)
                    && Self::eq_nodes(a, fa, f1.0 as usize, b, fb, f2.0 as usize, depth + 1)
                    && Self::eq_nodes(a, ba, b1.0 as usize, b, bb, b2.0 as usize, depth + 1)
            }
            _ => false,
        }
    }
}

impl Eq for Region {}

/// Ergonomic builder for constructing flat arena-backed `Region` graphs.
#[derive(Clone, Debug, Default)]
pub struct RegionBuilder {
    pub pool: SlotPool,
    pub stmts: SlotPool,
}

impl RegionBuilder {
    pub const fn new() -> Self {
        Self { pool: SlotPool::new(), stmts: SlotPool::new() }
    }

    pub fn with_capacity(pool_cap: usize) -> Self {
        Self { pool: SlotPool::with_capacity(pool_cap), stmts: SlotPool::new() }
    }

    pub fn alloc_vals(&mut self, vals: &[ValId]) -> Span {
        if vals.is_empty() {
            return Span::EMPTY;
        }
        let start = self.pool.len() as u32;
        for &v in vals {
            self.pool.push(IrSlot::val(v));
        }
        Span { start, len: vals.len() as u32 }
    }

    pub fn alloc_vars(&mut self, vars: &[(ValId, ValType)]) -> Span {
        if vars.is_empty() {
            return Span::EMPTY;
        }
        let start = self.pool.len() as u32;
        for &(id, ty) in vars {
            self.pool.push(IrSlot::var(id, ty));
        }
        Span { start, len: vars.len() as u32 }
    }

    pub fn alloc_tys(&mut self, tys: &[ValType]) -> Span {
        if tys.is_empty() {
            return Span::EMPTY;
        }
        let start = self.pool.len() as u32;
        for &t in tys {
            self.pool.push(IrSlot::ty(t));
        }
        Span { start, len: tys.len() as u32 }
    }

    pub fn alloc_stmts(&mut self, stmts: &[Stmt]) -> Span {
        if stmts.is_empty() {
            return Span::EMPTY;
        }
        let start = self.pool.len() as u32;
        for &s in stmts {
            self.pool.push(IrSlot::from_stmt(s));
        }
        Span { start, len: stmts.len() as u32 }
    }

    pub fn alloc_node(&mut self, node: RegionNode) -> RegionNodeId {
        let id = RegionNodeId(self.pool.len() as u32);
        self.pool.push(IrSlot::from_node(node));
        id
    }

    pub fn alloc_block(&mut self, stmts: &[Stmt]) -> RegionNodeId {
        let span = self.alloc_stmts(stmts);
        self.alloc_node(RegionNode::Block(span))
    }

    pub fn embed_region(&mut self, sub: &Region) -> RegionNode {
        if sub.is_empty_block() {
            return RegionNode::Block(Span::EMPTY);
        }
        let offset = self.pool.len() as u32;
        self.pool.reserve(sub.pool.len());
        for &elem in sub.pool.as_slice() {
            self.pool.push(elem.shift(offset));
        }
        sub.root.shift(offset)
    }

    pub fn embed_region_id(&mut self, sub: &Region) -> RegionNodeId {
        let node = self.embed_region(sub);
        self.alloc_node(node)
    }

    pub fn push_let(&mut self, dst: ValId, ty: ValType, op: Op) {
        self.stmts.push(IrSlot::let_op(dst, ty, op));
    }

    pub fn push_effect(&mut self, eff: EffectOp) {
        self.stmts.push(IrSlot::effect(eff));
    }

    pub fn push_subregion(&mut self, results: &[(ValId, ValType)], sub: &Region) {
        let res = self.alloc_vars(results);
        let region = self.embed_region_id(sub);
        self.stmts.push(IrSlot::region_stmt(res, region));
    }

    pub fn push_subregion_id(&mut self, results: &[(ValId, ValType)], region: RegionNodeId) {
        let res = self.alloc_vars(results);
        self.stmts.push(IrSlot::region_stmt(res, region));
    }

    pub fn push_call(&mut self, results: &[(ValId, ValType)], target: CallTarget, args: &[ValId]) {
        let res = self.alloc_vars(results);
        let arg_span = self.alloc_vals(args);
        self.stmts.push(IrSlot::call(res, target, arg_span));
    }

    pub fn push_yield(&mut self, vals: &[ValId]) {
        let vs = self.alloc_vals(vals);
        self.stmts.push(IrSlot::yield_span(vs));
    }

    pub fn push_break(&mut self, depth: u32, cond: Option<ValId>, values: &[ValId]) {
        let vs = self.alloc_vals(values);
        self.stmts.push(IrSlot::break_stmt(depth, cond, vs));
    }

    pub fn push_continue(&mut self, depth: u32, cond: Option<ValId>, values: &[ValId]) {
        let vs = self.alloc_vals(values);
        self.stmts.push(IrSlot::continue_stmt(depth, cond, vs));
    }

    pub fn push_return(&mut self, vals: &[ValId]) {
        let vs = self.alloc_vals(vals);
        self.stmts.push(IrSlot::return_span(vs));
    }

    /// Flushes accumulated `self.stmts` into a child `RegionNodeId` inside the same pool.
    pub fn finish_subblock(&mut self) -> RegionNodeId {
        if self.stmts.is_empty() {
            return self.alloc_node(RegionNode::Block(Span::EMPTY));
        }
        let start = self.pool.len() as u32;
        let len = self.stmts.len() as u32;
        self.pool.extend_from_slice(&self.stmts);
        self.stmts.clear();
        self.alloc_node(RegionNode::Block(Span { start, len }))
    }

    pub fn finish_node(self, root: RegionNode) -> Region {
        Region { root, pool: self.pool }
    }

    pub fn finish(self) -> Region {
        if self.stmts.is_empty() && self.pool.is_empty() {
            return Region::empty();
        }
        if self.stmts.is_empty() {
            return Region { root: RegionNode::Block(Span::EMPTY), pool: self.pool };
        }
        let p_len = self.pool.len() as u32;
        let s_len = self.stmts.len() as u32;
        let mut pool = self.pool;
        if pool.is_empty() {
            pool = self.stmts;
        } else {
            pool.extend_from_slice(&self.stmts);
        }
        Region { root: RegionNode::Block(Span { start: p_len, len: s_len }), pool }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SliceBound {
    Const(u32),
    Arg(u32),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OffsetRange {
    pub base: SliceBound,
    pub len: SliceBound,
}

/// Explicit specification and memory-footprint contract for an external host call.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HostContract {
    pub id: HostCallId,
    pub module_name: String,
    pub field_name: String,
    pub params: Vec<(ValId, ValType)>,
    pub results: Vec<(ValId, ValType)>,
    pub precondition: Region,
    pub read_footprints: Vec<(MemId, OffsetRange)>,
    pub write_footprints: Vec<(MemId, OffsetRange)>,
    pub postcondition: Region,
    pub sim_body: Option<Region>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MemoryDef {
    pub id: MemId,
    pub min_pages: u32,
    pub max_pages: Option<u32>,
    pub init_data: Vec<(u32, Vec<u8>)>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GlobalDef {
    pub id: GlobalId,
    pub ty: ValType,
    pub mutable: bool,
    pub init: Val,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FuncDef {
    pub id: FuncId,
    pub name: String,
    pub export_name: Option<String>,
    pub params: Vec<(ValId, ValType)>,
    pub results: Vec<ValType>,
    pub body: Region,
}

/// Complete verified Wasm-derived module representation.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Module {
    pub memories: Vec<MemoryDef>,
    pub globals: Vec<GlobalDef>,
    pub host_contracts: Vec<HostContract>,
    pub funcs: Vec<FuncDef>,
    pub memory_exports: Vec<(String, MemId)>,
    pub global_exports: Vec<(String, GlobalId)>,
}

impl Module {
    pub fn func(&self, id: FuncId) -> Option<&FuncDef> {
        self.funcs.iter().find(|f| f.id == id)
    }
    pub fn host_contract(&self, id: HostCallId) -> Option<&HostContract> {
        self.host_contracts.iter().find(|h| h.id == id)
    }
    pub fn global(&self, id: GlobalId) -> Option<&GlobalDef> {
        self.globals.iter().find(|g| g.id == id)
    }
}

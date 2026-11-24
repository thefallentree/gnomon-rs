//! Stratum admission checker and iterative Layer-0 DAG lowering gate.

use alloc::{string::String, vec::Vec};
use crate::ir::*;
use crate::vc::{max_val_id_in_region, remap_region_vals, validate_read_only_with_registry};

const MAX_CHECK_DEPTH: usize = 64;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LawKind {
    Algebraic,
    MemoryFrame { untouched_mem: MemId },
}

/// Machine-proved rewrite or memory-frame law bundled with a promoted `Stratum`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Law {
    pub name: String,
    pub kind: LawKind,
    pub params: Vec<(ValId, ValType)>,
    pub precondition: Region,
    pub lhs: Region,
    pub rhs: Region,
    pub proof_digest: [u8; 32],
}

impl Law {
    const fn empty_placeholder() -> Self {
        Self {
            name: String::new(),
            kind: LawKind::Algebraic,
            params: Vec::new(),
            precondition: Region::empty(),
            lhs: Region::empty(),
            rhs: Region::empty(),
            proof_digest: [0u8; 32],
        }
    }

    /// Returns `true` if this law carries an explicit precondition guard.
    pub fn has_precondition(&self) -> bool {
        !self.precondition.pool.is_empty() || !self.precondition.is_empty_block()
    }
}

/// Compact list of proved `Law`s storing the primary law inline (zero heap
/// allocation for the common 1-law `Stratum`) with `Vec<Law>` overflow.
#[derive(Clone, Debug)]
pub struct LawList {
    has_first: bool,
    first: Law,
    rest: Vec<Law>,
}

impl LawList {
    pub const fn empty() -> Self {
        Self { has_first: false, first: Law::empty_placeholder(), rest: Vec::new() }
    }

    pub fn single(law: Law) -> Self {
        Self { has_first: true, first: law, rest: Vec::new() }
    }

    pub fn from_vec(mut laws: Vec<Law>) -> Self {
        if laws.is_empty() {
            Self::empty()
        } else {
            let first = laws.remove(0);
            Self { has_first: true, first, rest: laws }
        }
    }

    pub fn push(&mut self, law: Law) {
        if !self.has_first {
            self.first = law;
            self.has_first = true;
        } else {
            self.rest.push(law);
        }
    }

    pub fn is_empty(&self) -> bool {
        !self.has_first
    }

    pub fn len(&self) -> usize {
        if self.has_first { 1 + self.rest.len() } else { 0 }
    }

    pub fn first(&self) -> Option<&Law> {
        if self.has_first { Some(&self.first) } else { None }
    }

    pub fn rest(&self) -> &[Law] {
        &self.rest
    }

    pub fn iter(&self) -> impl Iterator<Item = &Law> {
        self.first().into_iter().chain(self.rest.iter())
    }
}

impl Default for LawList {
    fn default() -> Self {
        Self::empty()
    }
}

impl PartialEq for LawList {
    fn eq(&self, other: &Self) -> bool {
        if self.has_first != other.has_first {
            return false;
        }
        if !self.has_first {
            return true;
        }
        self.first == other.first && self.rest == other.rest
    }
}

impl Eq for LawList {}

impl From<Law> for LawList {
    fn from(law: Law) -> Self {
        Self::single(law)
    }
}

impl From<Vec<Law>> for LawList {
    fn from(laws: Vec<Law>) -> Self {
        Self::from_vec(laws)
    }
}

/// Named typed operation defined acyclically over Layer `0 .. layer - 1`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StratumOp {
    pub id: StratumId,
    pub name: String,
    pub layer: u16,
    pub params: Vec<(ValId, ValType)>,
    pub results: Vec<ValType>,
    pub body: Region,
    pub docstring: String,
}

impl StratumOp {
    const fn empty_placeholder() -> Self {
        Self {
            id: StratumId(0),
            name: String::new(),
            layer: 0,
            params: Vec::new(),
            results: Vec::new(),
            body: Region::empty(),
            docstring: String::new(),
        }
    }
}

/// Paired sub-abstraction: acyclic Layer-`k` op + proved shortcut/frame law(s).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stratum {
    pub op: StratumOp,
    pub laws: LawList,
}

impl Stratum {
    const fn empty_placeholder() -> Self {
        Self { op: StratumOp::empty_placeholder(), laws: LawList::empty() }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum RegistryError {
    InvalidLayerZero,
    DuplicateName,
    DuplicateId,
    UnknownStratum(StratumId),
    NonAcyclicLayer { caller_layer: u16, callee: StratumId, callee_layer: u16 },
    MissingProvedLaw,
    EmptyProofDigest,
    TypeMismatch,
    UndefinedVal(ValId),
}

fn check_law_digest(d: &[u8; 32]) -> Result<(), RegistryError> {
    let [
        b0, b1, b2, b3, b4, b5, b6, b7,
        b8, b9, b10, b11, b12, b13, b14, b15,
        b16, b17, b18, b19, b20, b21, b22, b23,
        b24, b25, b26, b27, b28, b29, b30, b31,
    ] = *d;
    let nz = (b0 | b1 | b2 | b3 | b4 | b5 | b6 | b7)
        | (b8 | b9 | b10 | b11 | b12 | b13 | b14 | b15)
        | (b16 | b17 | b18 | b19 | b20 | b21 | b22 | b23)
        | (b24 | b25 | b26 | b27 | b28 | b29 | b30 | b31);
    if nz == 0 { Err(RegistryError::EmptyProofDigest) } else { Ok(()) }
}

const TENV_INLINE: usize = 16;
const TENV_UNDEF: u8 = 0;
const TENV_I32: u8 = 1;
const TENV_I64: u8 = 2;
const TENV_F32: u8 = 3;
const TENV_F64: u8 = 4;
const TENV_V128: u8 = 5;

struct TypeEnv {
    slot_tag: [u8; TENV_INLINE],
    trail_meta: [u8; TENV_INLINE],
    inline_len: usize,
    total_len: usize,
    spill: Vec<(ValId, ValType)>,
}

impl TypeEnv {
    fn new(params: &[(ValId, ValType)]) -> Self {
        let mut env = Self {
            slot_tag: [TENV_UNDEF; TENV_INLINE],
            trail_meta: [0; TENV_INLINE],
            inline_len: 0,
            total_len: 0,
            spill: Vec::new(),
        };
        let mut i = 0;
        while i < params.len() {
            env.push(params[i].0, params[i].1);
            i += 1;
        }
        env
    }

    fn len(&self) -> usize {
        self.total_len
    }

    #[cold]
    #[inline(never)]
    fn truncate_spill(&mut self, saved: usize) {
        self.spill.truncate(saved.saturating_sub(self.inline_len));
    }

    fn truncate(&mut self, saved: usize) {
        if !self.spill.is_empty() {
            self.truncate_spill(saved);
        }
        while self.inline_len > saved {
            self.inline_len -= 1;
            let meta = self.trail_meta[self.inline_len];
            self.slot_tag[(meta >> 4) as usize] = meta & 0x0f;
        }
        self.total_len = saved;
    }

    #[cold]
    #[inline(never)]
    fn push_spill(&mut self, id: ValId, ty: ValType) {
        self.spill.push((id, ty));
    }

    fn push(&mut self, id: ValId, ty: ValType) {
        let idx = id.0 as usize;
        if self.spill.is_empty() && self.inline_len < TENV_INLINE && idx < TENV_INLINE {
            let tag = match ty {
                ValType::I32 => TENV_I32,
                ValType::I64 => TENV_I64,
                ValType::F32 => TENV_F32,
                ValType::F64 => TENV_F64,
                ValType::V128 => TENV_V128,
            };
            self.trail_meta[self.inline_len] = ((idx as u8) << 4) | self.slot_tag[idx];
            self.slot_tag[idx] = tag;
            self.inline_len += 1;
        } else {
            self.push_spill(id, ty);
        }
        self.total_len += 1;
    }

    fn extend_vars(&mut self, reg: &Region, span: Span) -> Result<(), RegistryError> {
        let mut i = 0;
        while i < span.len {
            let (id, ty) = reg.try_var(span, i).ok_or(RegistryError::TypeMismatch)?;
            self.push(id, ty);
            i += 1;
        }
        Ok(())
    }

    #[cold]
    #[inline(never)]
    fn lookup_spill(&self, id: ValId) -> Option<ValType> {
        let mut s = self.spill.len();
        while s > 0 {
            s -= 1;
            if self.spill[s].0 == id {
                return Some(self.spill[s].1);
            }
        }
        None
    }

    fn lookup(&self, id: ValId) -> Result<ValType, RegistryError> {
        if !self.spill.is_empty()
            && let Some(ty) = self.lookup_spill(id)
        {
            return Ok(ty);
        }
        let idx = id.0 as usize;
        if idx < TENV_INLINE {
            match self.slot_tag[idx] {
                TENV_I32 => return Ok(ValType::I32),
                TENV_I64 => return Ok(ValType::I64),
                TENV_F32 => return Ok(ValType::F32),
                TENV_F64 => return Ok(ValType::F64),
                TENV_V128 => return Ok(ValType::V128),
                _ => {}
            }
        }
        Err(RegistryError::UndefinedVal(id))
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum SmallTys {
    Inline([ValType; 4], u8),
    Pool(u32),
}

impl SmallTys {
    const EMPTY: Self = Self::Inline([ValType::I32; 4], 0);
}

#[derive(Default)]
struct TyPool(Vec<Vec<ValType>>);

impl TyPool {
    fn intern_with<F>(&mut self, len: u32, mut get: F) -> Result<SmallTys, RegistryError>
    where
        F: FnMut(u32) -> Result<ValType, RegistryError>,
    {
        if len <= 4 {
            let mut a = [ValType::I32; 4];
            let mut i = 0;
            while i < len {
                a[i as usize] = get(i)?;
                i += 1;
            }
            Ok(SmallTys::Inline(a, len as u8))
        } else {
            let mut v = Vec::with_capacity(len as usize);
            let mut i = 0;
            while i < len {
                v.push(get(i)?);
                i += 1;
            }
            let id = self.0.len() as u32;
            self.0.push(v);
            Ok(SmallTys::Pool(id))
        }
    }

    fn intern_vals(&mut self, reg: &Region, vs: Span, env: &TypeEnv) -> Result<SmallTys, RegistryError> {
        self.intern_with(vs.len, |i| {
            env.lookup(reg.try_val(vs, i).ok_or(RegistryError::TypeMismatch)?)
        })
    }

    fn intern_tys_span(&mut self, reg: &Region, span: Span) -> Result<SmallTys, RegistryError> {
        self.intern_with(span.len, |i| reg.try_ty(span, i).ok_or(RegistryError::TypeMismatch))
    }

    fn intern_vars_span(&mut self, reg: &Region, span: Span) -> Result<SmallTys, RegistryError> {
        self.intern_with(span.len, |i| {
            Ok(reg.try_var(span, i).ok_or(RegistryError::TypeMismatch)?.1)
        })
    }

    fn len(&self, st: SmallTys) -> usize {
        match st {
            SmallTys::Inline(_, n) => n as usize,
            SmallTys::Pool(id) => self.0[id as usize].len(),
        }
    }

    fn get(&self, st: SmallTys, idx: usize) -> ValType {
        match st {
            SmallTys::Inline(a, _) => a[idx],
            SmallTys::Pool(id) => self.0[id as usize][idx],
        }
    }

    fn eq_tys(&self, a: SmallTys, b: SmallTys) -> bool {
        if self.len(a) != self.len(b) {
            return false;
        }
        let mut i = 0;
        while i < self.len(a) {
            if self.get(a, i) != self.get(b, i) {
                return false;
            }
            i += 1;
        }
        true
    }

    fn eq_slice(&self, st: SmallTys, expected: &[ValType]) -> bool {
        if self.len(st) != expected.len() {
            return false;
        }
        let mut i = 0;
        while i < expected.len() {
            if self.get(st, i) != expected[i] {
                return false;
            }
            i += 1;
        }
        true
    }

    fn eq_tys_span(&self, st: SmallTys, reg: &Region, span: Span) -> bool {
        if self.len(st) != span.len_usize() {
            return false;
        }
        let mut i = 0;
        while i < span.len {
            if reg.try_ty(span, i) != Some(self.get(st, i as usize)) {
                return false;
            }
            i += 1;
        }
        true
    }

    fn eq_vars_span(&self, st: SmallTys, reg: &Region, span: Span) -> bool {
        if self.len(st) != span.len_usize() {
            return false;
        }
        let mut i = 0;
        while i < span.len {
            if reg.try_var(span, i).map(|p| p.1) != Some(self.get(st, i as usize)) {
                return false;
            }
            i += 1;
        }
        true
    }
}

/// Small-vector storage for promoted Strata: stores up to 2 Strata inline
/// (zero heap allocation / contiguous `&[Stratum]`), spilling to `Vec<Stratum>`
/// seamlessly on the 3rd+ promoted Stratum.
/// Invariant: `occupied[1] => occupied[0]`; when `!spill.is_empty()`, `occupied == [false, false]`.
#[derive(Clone, Debug)]
struct StratumStore {
    inline: [Stratum; 2],
    occupied: [bool; 2],
    spill: Vec<Stratum>,
}

impl StratumStore {
    const fn new() -> Self {
        Self {
            inline: [Stratum::empty_placeholder(), Stratum::empty_placeholder()],
            occupied: [false, false],
            spill: Vec::new(),
        }
    }

    fn as_slice(&self) -> &[Stratum] {
        if self.spill.is_empty() {
            let len = (self.occupied[0] as usize) + (self.occupied[1] as usize);
            &self.inline[..len]
        } else {
            &self.spill
        }
    }

    #[cold]
    #[inline(never)]
    fn get_by_id_spill(&self, id: StratumId) -> Option<&Stratum> {
        let mut i = 0;
        while i < self.spill.len() {
            if self.spill[i].op.id == id {
                return Some(&self.spill[i]);
            }
            i += 1;
        }
        None
    }

    fn get_by_id(&self, id: StratumId) -> Option<&Stratum> {
        if self.spill.is_empty() {
            if self.occupied[0] && self.inline[0].op.id == id {
                return Some(&self.inline[0]);
            }
            if self.occupied[1] && self.inline[1].op.id == id {
                return Some(&self.inline[1]);
            }
            None
        } else {
            self.get_by_id_spill(id)
        }
    }

    #[cold]
    #[inline(never)]
    fn has_name_spill(&self, name: &str) -> bool {
        let mut i = 0;
        while i < self.spill.len() {
            if self.spill[i].op.name == name {
                return true;
            }
            i += 1;
        }
        false
    }

    fn has_name(&self, name: &str) -> bool {
        if self.spill.is_empty() {
            (self.occupied[0] && self.inline[0].op.name == name)
                || (self.occupied[1] && self.inline[1].op.name == name)
        } else {
            self.has_name_spill(name)
        }
    }

    #[cold]
    #[inline(never)]
    fn push_spill(&mut self, stratum: Stratum) {
        if self.spill.is_empty() {
            self.spill.reserve(3);
            if self.occupied[0] {
                let s0 = core::mem::replace(&mut self.inline[0], Stratum::empty_placeholder());
                self.spill.push(s0);
                self.occupied[0] = false;
            }
            if self.occupied[1] {
                let s1 = core::mem::replace(&mut self.inline[1], Stratum::empty_placeholder());
                self.spill.push(s1);
                self.occupied[1] = false;
            }
        }
        self.spill.push(stratum);
    }

    fn push(&mut self, stratum: Stratum) {
        if !self.spill.is_empty() {
            self.push_spill(stratum);
        } else if !self.occupied[0] {
            self.inline[0] = stratum;
            self.occupied[0] = true;
        } else if !self.occupied[1] {
            self.inline[1] = stratum;
            self.occupied[1] = true;
        } else {
            self.push_spill(stratum);
        }
    }
}

impl Default for StratumStore {
    fn default() -> Self {
        Self::new()
    }
}

/// Small-vector storage for unpromoted candidate ops: stores up to 2 ops inline,
/// spilling cleanly to `Vec<StratumOp>` on the 3rd+ simultaneous candidate.
/// Invariant: `occupied[1] => occupied[0]`; when `!spill.is_empty()`, `occupied == [false, false]`.
#[derive(Clone, Debug)]
struct CandidateStore {
    inline: [StratumOp; 2],
    occupied: [bool; 2],
    spill: Vec<StratumOp>,
}

impl CandidateStore {
    const fn new() -> Self {
        Self {
            inline: [StratumOp::empty_placeholder(), StratumOp::empty_placeholder()],
            occupied: [false, false],
            spill: Vec::new(),
        }
    }

    fn as_slice(&self) -> &[StratumOp] {
        if self.spill.is_empty() {
            let len = (self.occupied[0] as usize) + (self.occupied[1] as usize);
            &self.inline[..len]
        } else {
            &self.spill
        }
    }

    #[cold]
    #[inline(never)]
    fn get_by_id_spill(&self, id: StratumId) -> Option<&StratumOp> {
        let mut i = 0;
        while i < self.spill.len() {
            if self.spill[i].id == id {
                return Some(&self.spill[i]);
            }
            i += 1;
        }
        None
    }

    fn get_by_id(&self, id: StratumId) -> Option<&StratumOp> {
        if self.spill.is_empty() {
            if self.occupied[0] && self.inline[0].id == id {
                return Some(&self.inline[0]);
            }
            if self.occupied[1] && self.inline[1].id == id {
                return Some(&self.inline[1]);
            }
            None
        } else {
            self.get_by_id_spill(id)
        }
    }

    #[cold]
    #[inline(never)]
    fn has_conflicting_name_spill(&self, name: &str, promoted_only: bool, op_id: StratumId) -> bool {
        let mut i = 0;
        while i < self.spill.len() {
            if (!promoted_only || self.spill[i].id != op_id) && self.spill[i].name == name {
                return true;
            }
            i += 1;
        }
        false
    }

    fn has_conflicting_name(&self, name: &str, promoted_only: bool, op_id: StratumId) -> bool {
        if self.spill.is_empty() {
            (self.occupied[0]
                && (!promoted_only || self.inline[0].id != op_id)
                && self.inline[0].name == name)
                || (self.occupied[1]
                    && (!promoted_only || self.inline[1].id != op_id)
                    && self.inline[1].name == name)
        } else {
            self.has_conflicting_name_spill(name, promoted_only, op_id)
        }
    }

    #[cold]
    #[inline(never)]
    fn push_spill(&mut self, op: StratumOp) {
        if self.spill.is_empty() {
            self.spill.reserve(3);
            if self.occupied[0] {
                let s0 = core::mem::replace(&mut self.inline[0], StratumOp::empty_placeholder());
                self.spill.push(s0);
                self.occupied[0] = false;
            }
            if self.occupied[1] {
                let s1 = core::mem::replace(&mut self.inline[1], StratumOp::empty_placeholder());
                self.spill.push(s1);
                self.occupied[1] = false;
            }
        }
        self.spill.push(op);
    }

    fn push(&mut self, op: StratumOp) {
        if !self.spill.is_empty() {
            self.push_spill(op);
        } else if !self.occupied[0] {
            self.inline[0] = op;
            self.occupied[0] = true;
        } else if !self.occupied[1] {
            self.inline[1] = op;
            self.occupied[1] = true;
        } else {
            self.push_spill(op);
        }
    }

    #[cold]
    #[inline(never)]
    fn remove_spill(&mut self, id: StratumId) {
        let mut i = 0;
        while i < self.spill.len() {
            if self.spill[i].id == id {
                self.spill.remove(i);
                break;
            }
            i += 1;
        }
    }

    fn remove_by_id(&mut self, id: StratumId) {
        if !self.spill.is_empty() {
            self.remove_spill(id);
            return;
        }
        if self.occupied[0] && self.inline[0].id == id {
            if self.occupied[1] {
                self.inline[0] =
                    core::mem::replace(&mut self.inline[1], StratumOp::empty_placeholder());
                self.occupied[1] = false;
            } else {
                self.inline[0] = StratumOp::empty_placeholder();
                self.occupied[0] = false;
            }
        } else if self.occupied[1] && self.inline[1].id == id {
            self.inline[1] = StratumOp::empty_placeholder();
            self.occupied[1] = false;
        }
    }
}

impl Default for CandidateStore {
    fn default() -> Self {
        Self::new()
    }
}

/// Small-vector storage for read-only `StratumId`s: stores up to 4 IDs inline,
/// spilling cleanly to `Vec<StratumId>` on the 5th+ entry.
/// Invariant: `occupied[k + 1] => occupied[k]`; when `!spill.is_empty()`, `occupied == [false; 4]`.
#[derive(Clone, Debug)]
struct ReadOnlyIdStore {
    inline: [StratumId; 4],
    occupied: [bool; 4],
    spill: Vec<StratumId>,
}

impl ReadOnlyIdStore {
    const fn new() -> Self {
        Self { inline: [StratumId(0); 4], occupied: [false; 4], spill: Vec::new() }
    }

    #[cold]
    #[inline(never)]
    fn contains_spill(&self, id: StratumId) -> bool {
        let mut i = 0;
        while i < self.spill.len() {
            if self.spill[i] == id {
                return true;
            }
            i += 1;
        }
        false
    }

    fn contains(&self, id: StratumId) -> bool {
        if self.spill.is_empty() {
            (self.occupied[0] && self.inline[0] == id)
                || (self.occupied[1] && self.inline[1] == id)
                || (self.occupied[2] && self.inline[2] == id)
                || (self.occupied[3] && self.inline[3] == id)
        } else {
            self.contains_spill(id)
        }
    }

    #[cold]
    #[inline(never)]
    fn push_spill(&mut self, id: StratumId) {
        if self.spill.is_empty() {
            self.spill.reserve(5);
            let mut i = 0;
            while i < 4 {
                if self.occupied[i] {
                    self.spill.push(self.inline[i]);
                    self.inline[i] = StratumId(0);
                    self.occupied[i] = false;
                }
                i += 1;
            }
        }
        self.spill.push(id);
    }

    fn push(&mut self, id: StratumId) {
        if !self.spill.is_empty() {
            self.push_spill(id);
        } else if !self.occupied[0] {
            self.inline[0] = id;
            self.occupied[0] = true;
        } else if !self.occupied[1] {
            self.inline[1] = id;
            self.occupied[1] = true;
        } else if !self.occupied[2] {
            self.inline[2] = id;
            self.occupied[2] = true;
        } else if !self.occupied[3] {
            self.inline[3] = id;
            self.occupied[3] = true;
        } else {
            self.push_spill(id);
        }
    }

    #[cold]
    #[inline(never)]
    fn remove_spill(&mut self, id: StratumId) {
        let mut i = 0;
        while i < self.spill.len() {
            if self.spill[i] == id {
                self.spill.remove(i);
                break;
            }
            i += 1;
        }
    }

    fn remove_by_id(&mut self, id: StratumId) {
        if !self.spill.is_empty() {
            self.remove_spill(id);
            return;
        }
        if self.occupied[0] && self.inline[0] == id {
            if self.occupied[1] {
                self.inline[0] = self.inline[1];
                if self.occupied[2] {
                    self.inline[1] = self.inline[2];
                    if self.occupied[3] {
                        self.inline[2] = self.inline[3];
                        self.inline[3] = StratumId(0);
                        self.occupied[3] = false;
                    } else {
                        self.inline[2] = StratumId(0);
                        self.occupied[2] = false;
                    }
                } else {
                    self.inline[1] = StratumId(0);
                    self.occupied[1] = false;
                }
            } else {
                self.inline[0] = StratumId(0);
                self.occupied[0] = false;
            }
        } else if self.occupied[1] && self.inline[1] == id {
            if self.occupied[2] {
                self.inline[1] = self.inline[2];
                if self.occupied[3] {
                    self.inline[2] = self.inline[3];
                    self.inline[3] = StratumId(0);
                    self.occupied[3] = false;
                } else {
                    self.inline[2] = StratumId(0);
                    self.occupied[2] = false;
                }
            } else {
                self.inline[1] = StratumId(0);
                self.occupied[1] = false;
            }
        } else if self.occupied[2] && self.inline[2] == id {
            if self.occupied[3] {
                self.inline[2] = self.inline[3];
                self.inline[3] = StratumId(0);
                self.occupied[3] = false;
            } else {
                self.inline[2] = StratumId(0);
                self.occupied[2] = false;
            }
        } else if self.occupied[3] && self.inline[3] == id {
            self.inline[3] = StratumId(0);
            self.occupied[3] = false;
        }
    }
}

impl Default for ReadOnlyIdStore {
    fn default() -> Self {
        Self::new()
    }
}

/// TCB registry gating all candidate and promoted Strata.
#[derive(Clone, Debug, Default)]
pub struct StratumRegistry {
    candidates: CandidateStore,
    promoted: StratumStore,
    read_only_ids: ReadOnlyIdStore,
}

#[derive(Clone, Copy)]
enum CheckTask {
    Eval {
        node: RegionNode,
        limit: usize,
        depth: usize,
    },
    StepBlock {
        span: Span,
        idx: u32,
        limit: usize,
        saved_env: usize,
        yielded: Option<SmallTys>,
        depth: usize,
    },
    AfterSubStmt {
        results: Span,
    },
    AfterIfElse {
        results: Span,
    },
    AfterBoundedLoop {
        saved_env: usize,
    },
    AfterInvariantLoop {
        state_vars: Span,
        saved_env: usize,
    },
}

const MAX_INLINE_CHECK_STACK: usize = 8;
const MAX_CHECK_STACK: usize = MAX_CHECK_DEPTH * 5;

struct CheckStacks {
    inline_tasks: [CheckTask; MAX_INLINE_CHECK_STACK],
    inline_task_len: usize,
    spill_tasks: Vec<CheckTask>,
    inline_tys: [SmallTys; MAX_INLINE_CHECK_STACK],
    inline_ty_len: usize,
    spill_tys: Vec<SmallTys>,
}

fn push_inline_or_spill<T: Copy>(
    inline: &mut [T; MAX_INLINE_CHECK_STACK],
    inline_len: &mut usize,
    spill: &mut Vec<T>,
    item: T,
) -> Result<(), RegistryError> {
    if *inline_len + spill.len() >= MAX_CHECK_STACK {
        return Err(RegistryError::TypeMismatch);
    }
    if *inline_len < MAX_INLINE_CHECK_STACK {
        inline[*inline_len] = item;
        *inline_len += 1;
    } else {
        spill.push(item);
    }
    Ok(())
}

impl CheckStacks {
    fn new() -> Self {
        let dummy_task = CheckTask::AfterIfElse { results: Span::EMPTY };
        Self {
            inline_tasks: [dummy_task; MAX_INLINE_CHECK_STACK],
            inline_task_len: 0,
            spill_tasks: Vec::new(),
            inline_tys: [SmallTys::EMPTY; MAX_INLINE_CHECK_STACK],
            inline_ty_len: 0,
            spill_tys: Vec::new(),
        }
    }

    fn has_tasks(&self) -> bool {
        self.inline_task_len > 0 || !self.spill_tasks.is_empty()
    }

    fn push_task(&mut self, task: CheckTask) -> Result<(), RegistryError> {
        push_inline_or_spill(
            &mut self.inline_tasks,
            &mut self.inline_task_len,
            &mut self.spill_tasks,
            task,
        )
    }

    fn pop_task(&mut self) -> CheckTask {
        if !self.spill_tasks.is_empty() {
            self.spill_tasks
                .pop()
                .unwrap_or(CheckTask::AfterIfElse { results: Span::EMPTY })
        } else {
            self.inline_task_len -= 1;
            self.inline_tasks[self.inline_task_len]
        }
    }

    fn push_ty(&mut self, ty: SmallTys) -> Result<(), RegistryError> {
        push_inline_or_spill(
            &mut self.inline_tys,
            &mut self.inline_ty_len,
            &mut self.spill_tys,
            ty,
        )
    }

    fn pop_ty(&mut self) -> Result<SmallTys, RegistryError> {
        if !self.spill_tys.is_empty() {
            self.spill_tys.pop().ok_or(RegistryError::TypeMismatch)
        } else if self.inline_ty_len > 0 {
            self.inline_ty_len -= 1;
            Ok(self.inline_tys[self.inline_ty_len])
        } else {
            Err(RegistryError::TypeMismatch)
        }
    }
}

struct CheckCtx<'a> {
    region: &'a Region,
    caller_layer: u16,
    promoted_only: bool,
    self_op: Option<&'a StratumOp>,
}

impl StratumRegistry {
    pub const fn new() -> Self {
        Self {
            candidates: CandidateStore::new(),
            promoted: StratumStore::new(),
            read_only_ids: ReadOnlyIdStore::new(),
        }
    }

    pub fn promoted(&self) -> &[Stratum] {
        self.promoted.as_slice()
    }

    pub fn candidates(&self) -> &[StratumOp] {
        self.candidates.as_slice()
    }

    pub fn get_stratum(&self, id: StratumId) -> Option<&Stratum> {
        self.promoted.get_by_id(id)
    }

    pub fn get_op(&self, id: StratumId) -> Option<&StratumOp> {
        if let Some(s) = self.promoted.get_by_id(id) {
            return Some(&s.op);
        }
        self.candidates.get_by_id(id)
    }

    pub fn is_stratum_read_only(&self, id: StratumId) -> bool {
        self.read_only_ids.contains(id)
    }

    /// Registers an unpromoted candidate op after validating layer `>= 1`, acyclicity, and SSA types.
    pub fn register_candidate_op(&mut self, op: StratumOp) -> Result<StratumId, RegistryError> {
        if op.layer == 0 {
            return Err(RegistryError::InvalidLayerZero);
        }
        self.validate_op(&op, false)?;
        let id = op.id;
        if validate_read_only_with_registry(&op.body, self) && !self.is_stratum_read_only(id) {
            self.read_only_ids.push(id);
        }
        self.candidates.push(op);
        Ok(id)
    }

    fn validate_law(
        &self,
        op: &StratumOp,
        law: &Law,
        tp: &mut TyPool,
    ) -> Result<(), RegistryError> {
        check_law_digest(&law.proof_digest)?;
        if law.precondition.pool.is_empty() {
            if !law.precondition.is_empty_block() {
                return Err(RegistryError::TypeMismatch);
            }
        } else {
            if !validate_read_only_with_registry(&law.precondition, self) {
                return Err(RegistryError::TypeMismatch);
            }
            let pre_tys =
                self.check_region(&law.precondition, &law.params, u16::MAX, true, Some(op), tp)?;
            if !tp.eq_slice(pre_tys, &[ValType::I32]) {
                return Err(RegistryError::TypeMismatch);
            }
        }
        let lhs_tys = self.check_region(&law.lhs, &law.params, u16::MAX, true, Some(op), tp)?;
        let rhs_tys = self.check_region(&law.rhs, &law.params, u16::MAX, true, Some(op), tp)?;
        if !tp.eq_tys(lhs_tys, rhs_tys) {
            return Err(RegistryError::TypeMismatch);
        }
        Ok(())
    }

    /// Admits a verified `Stratum` (acyclic op over already-promoted callees + >= 1 non-empty proved law).
    pub fn promote_stratum(&mut self, stratum: Stratum) -> Result<StratumId, RegistryError> {
        if !stratum.laws.has_first {
            return Err(RegistryError::MissingProvedLaw);
        }
        if stratum.op.layer == 0 {
            return Err(RegistryError::InvalidLayerZero);
        }
        self.validate_op(&stratum.op, true)?;
        let mut tp = TyPool::default();
        self.validate_law(&stratum.op, &stratum.laws.first, &mut tp)?;
        let mut l_idx = 0;
        while l_idx < stratum.laws.rest.len() {
            self.validate_law(&stratum.op, &stratum.laws.rest[l_idx], &mut tp)?;
            l_idx += 1;
        }

        let id = stratum.op.id;
        self.candidates.remove_by_id(id);
        self.read_only_ids.remove_by_id(id);
        if validate_read_only_with_registry(&stratum.op.body, self) {
            self.read_only_ids.push(id);
        }
        self.promoted.push(stratum);
        Ok(id)
    }

    fn validate_op(&self, op: &StratumOp, promoted_only: bool) -> Result<(), RegistryError> {
        if self.get_stratum(op.id).is_some() || (!promoted_only && self.get_op(op.id).is_some()) {
            return Err(RegistryError::DuplicateId);
        }
        if self.promoted.has_name(&op.name)
            || self.candidates.has_conflicting_name(&op.name, promoted_only, op.id)
        {
            return Err(RegistryError::DuplicateName);
        }
        let mut tp = TyPool::default();
        let body_tys = self.check_region(&op.body, &op.params, op.layer, promoted_only, None, &mut tp)?;
        if !tp.eq_slice(body_tys, &op.results) {
            return Err(RegistryError::TypeMismatch);
        }
        Ok(())
    }

    fn resolve_callee<'a>(
        &'a self,
        sid: StratumId,
        promoted_only: bool,
        self_op: Option<&'a StratumOp>,
    ) -> Result<&'a StratumOp, RegistryError> {
        if let Some(op) = self_op
            && op.id == sid
        {
            return Ok(op);
        }
        if promoted_only {
            self.get_stratum(sid).map(|s| &s.op).ok_or(RegistryError::UnknownStratum(sid))
        } else {
            self.get_op(sid).ok_or(RegistryError::UnknownStratum(sid))
        }
    }

    fn expect_ty(id: ValId, ty: ValType, env: &TypeEnv) -> Result<(), RegistryError> {
        if env.lookup(id)? == ty { Ok(()) } else { Err(RegistryError::TypeMismatch) }
    }

    fn check_op(op: &Op, declared_ty: ValType, env: &TypeEnv) -> Result<ValType, RegistryError> {
        match op {
            Op::ConstI32(_) | Op::MemorySize(_) => Ok(ValType::I32),
            Op::ConstI64(_) => Ok(ValType::I64),
            Op::ConstF32(_) => Ok(ValType::F32),
            Op::ConstF64(_) => Ok(ValType::F64),
            Op::ConstV128(_) => Ok(ValType::V128),
            Op::Copy(v) => env.lookup(*v),
            Op::Select { cond, true_val, false_val } => {
                Self::expect_ty(*cond, ValType::I32, env)?;
                let t = env.lookup(*true_val)?;
                Self::expect_ty(*false_val, t, env)?;
                Ok(t)
            }
            Op::GlobalGet(_) => Ok(declared_ty),
            Op::Un(u, v) => {
                Self::expect_ty(*v, u.input_ty(), env)?;
                Ok(u.output_ty())
            }
            Op::Bin(b, l, r) => {
                Self::expect_ty(*l, b.lhs_ty(), env)?;
                Self::expect_ty(*r, b.rhs_ty(), env)?;
                Ok(b.output_ty())
            }
            Op::Load { addr, width, result_ty, .. } => {
                Self::expect_ty(*addr, ValType::I32, env)?;
                let ok = matches!(
                    (*result_ty, *width),
                    (ValType::I32, MemWidth::B1 | MemWidth::B2 | MemWidth::B4)
                        | (ValType::I64, MemWidth::B1 | MemWidth::B2 | MemWidth::B4 | MemWidth::B8)
                        | (ValType::F32, MemWidth::B4)
                        | (ValType::F64, MemWidth::B8)
                        | (ValType::V128, MemWidth::B16)
                );
                if !ok {
                    return Err(RegistryError::TypeMismatch);
                }
                Ok(*result_ty)
            }
            Op::MemoryGrow { delta, .. } => {
                Self::expect_ty(*delta, ValType::I32, env)?;
                Ok(ValType::I32)
            }
            Op::SimdExtractLane { kind, lane, vec } => {
                if *lane >= kind.num_lanes() {
                    return Err(RegistryError::TypeMismatch);
                }
                Self::expect_ty(*vec, ValType::V128, env)?;
                Ok(kind.scalar_ty())
            }
            Op::SimdReplaceLane { kind, lane, vec, val } => {
                if *lane >= kind.num_lanes() {
                    return Err(RegistryError::TypeMismatch);
                }
                Self::expect_ty(*vec, ValType::V128, env)?;
                Self::expect_ty(*val, kind.scalar_ty(), env)?;
                Ok(ValType::V128)
            }
            Op::SimdBitselect { a, b, mask } => {
                Self::expect_ty(*a, ValType::V128, env)?;
                Self::expect_ty(*b, ValType::V128, env)?;
                Self::expect_ty(*mask, ValType::V128, env)?;
                Ok(ValType::V128)
            }
            Op::SimdShuffle { lhs, rhs, lanes } => {
                let mut i = 0;
                while i < 16 {
                    if lanes[i] >= 32 {
                        return Err(RegistryError::TypeMismatch);
                    }
                    i += 1;
                }
                Self::expect_ty(*lhs, ValType::V128, env)?;
                Self::expect_ty(*rhs, ValType::V128, env)?;
                Ok(ValType::V128)
            }
        }
    }

    fn check_effect(eff: &EffectOp, env: &TypeEnv) -> Result<(), RegistryError> {
        match eff {
            EffectOp::Store { addr, val, width, .. } => {
                Self::expect_ty(*addr, ValType::I32, env)?;
                let vty = env.lookup(*val)?;
                let ok = matches!(
                    (vty, *width),
                    (ValType::I32, MemWidth::B1 | MemWidth::B2 | MemWidth::B4)
                        | (ValType::I64, MemWidth::B1 | MemWidth::B2 | MemWidth::B4 | MemWidth::B8)
                        | (ValType::F32, MemWidth::B4)
                        | (ValType::F64, MemWidth::B8)
                        | (ValType::V128, MemWidth::B16)
                );
                if !ok {
                    return Err(RegistryError::TypeMismatch);
                }
            }
            EffectOp::MemoryCopy { dst, src, len, .. }
            | EffectOp::MemoryFill { dst, val: src, len, .. } => {
                Self::expect_ty(*dst, ValType::I32, env)?;
                Self::expect_ty(*src, ValType::I32, env)?;
                Self::expect_ty(*len, ValType::I32, env)?;
            }
            EffectOp::GlobalSet { val, .. } => {
                env.lookup(*val)?;
            }
            EffectOp::Trap(_) | EffectOp::Nop => {}
        }
        Ok(())
    }

    fn check_vals_defined(reg: &Region, vs: Span, env: &TypeEnv) -> Result<(), RegistryError> {
        let mut i = 0;
        while i < vs.len {
            let v = reg.try_val(vs, i).ok_or(RegistryError::TypeMismatch)?;
            env.lookup(v)?;
            i += 1;
        }
        Ok(())
    }

    fn record_exit_tys(
        tp: &mut TyPool,
        reg: &Region,
        yielded: &mut Option<SmallTys>,
        vs: Span,
        env: &TypeEnv,
    ) -> Result<(), RegistryError> {
        let cur = tp.intern_vals(reg, vs, env)?;
        match *yielded {
            None => *yielded = Some(cur),
            Some(prev) if tp.eq_tys(prev, cur) => {}
            Some(_) => return Err(RegistryError::TypeMismatch),
        }
        Ok(())
    }

    fn check_loop_inits(
        region: &Region,
        init_vars: Span,
        state_vars: Span,
        env: &TypeEnv,
    ) -> Result<(), RegistryError> {
        if init_vars.len != state_vars.len {
            return Err(RegistryError::TypeMismatch);
        }
        let mut i = 0;
        while i < init_vars.len {
            let iv = region.try_val(init_vars, i).ok_or(RegistryError::TypeMismatch)?;
            let (_, sv_ty) = region.try_var(state_vars, i).ok_or(RegistryError::TypeMismatch)?;
            Self::expect_ty(iv, sv_ty, env)?;
            i += 1;
        }
        Ok(())
    }

    fn check_simple_slot(
        &self,
        ctx: &CheckCtx<'_>,
        slot: IrSlot,
        env: &mut TypeEnv,
        tp: &mut TyPool,
        yielded: &mut Option<SmallTys>,
    ) -> Result<(), RegistryError> {
        match slot.tag {
            TAG_STMT_LET => {
                let (dst, ty, op) = slot
                    .to_let_op_with_pool(ctx.region.pool.as_slice())
                    .ok_or(RegistryError::TypeMismatch)?;
                if Self::check_op(&op, ty, env)? != ty {
                    return Err(RegistryError::TypeMismatch);
                }
                env.push(dst, ty);
            }
            TAG_STMT_EFFECT => {
                let eff = slot.to_effect().ok_or(RegistryError::TypeMismatch)?;
                Self::check_effect(&eff, env)?;
            }
            TAG_STMT_CALL => {
                let results = Span { start: slot.w0, len: slot.w1 };
                let args = Span { start: slot.w3, len: slot.w4 };
                if slot.sub == CALL_STRATUM {
                    let sid = StratumId(slot.w2);
                    let callee = self.resolve_callee(sid, ctx.promoted_only, ctx.self_op)?;
                    if callee.layer >= ctx.caller_layer {
                        return Err(RegistryError::NonAcyclicLayer {
                            caller_layer: ctx.caller_layer,
                            callee: sid,
                            callee_layer: callee.layer,
                        });
                    }
                    if args.len_usize() != callee.params.len()
                        || results.len_usize() != callee.results.len()
                    {
                        return Err(RegistryError::TypeMismatch);
                    }
                    let mut j = 0;
                    while j < args.len {
                        let aid = ctx.region.try_val(args, j).ok_or(RegistryError::TypeMismatch)?;
                        Self::expect_ty(aid, callee.params[j as usize].1, env)?;
                        j += 1;
                    }
                    let mut k = 0;
                    while k < results.len {
                        let (rid, rty) =
                            ctx.region.try_var(results, k).ok_or(RegistryError::TypeMismatch)?;
                        if rty != callee.results[k as usize] {
                            return Err(RegistryError::TypeMismatch);
                        }
                        env.push(rid, rty);
                        k += 1;
                    }
                } else if slot.sub == CALL_FUNC || slot.sub == CALL_HOST {
                    Self::check_vals_defined(ctx.region, args, env)?;
                    env.extend_vars(ctx.region, results)?;
                } else {
                    return Err(RegistryError::TypeMismatch);
                }
            }
            TAG_STMT_YIELD | TAG_STMT_RETURN => {
                let vs = Span { start: slot.w0, len: slot.w1 };
                Self::record_exit_tys(tp, ctx.region, yielded, vs, env)?;
            }
            TAG_STMT_BREAK | TAG_STMT_CONTINUE => {
                if slot.sub != 0 {
                    Self::expect_ty(ValId(slot.w1), ValType::I32, env)?;
                }
                let values = Span { start: slot.w2, len: slot.w3 };
                if slot.tag == TAG_STMT_BREAK && slot.w0 == 0 {
                    Self::record_exit_tys(tp, ctx.region, yielded, values, env)?;
                } else {
                    Self::check_vals_defined(ctx.region, values, env)?;
                }
            }
            _ => return Err(RegistryError::TypeMismatch),
        }
        Ok(())
    }

    #[inline(never)]
    fn check_region_nested(
        &self,
        ctx: &CheckCtx<'_>,
        env: &mut TypeEnv,
        first_task: CheckTask,
        tp: &mut TyPool,
    ) -> Result<SmallTys, RegistryError> {
        let region = ctx.region;
        let mut st = CheckStacks::new();
        st.push_task(first_task)?;

        while st.has_tasks() {
            match st.pop_task() {
                CheckTask::Eval { node, limit, depth } => {
                    if depth >= MAX_CHECK_DEPTH {
                        return Err(RegistryError::TypeMismatch);
                    }
                    match node {
                        RegionNode::Block(span) if span.is_empty() => {
                            st.push_ty(SmallTys::EMPTY)?;
                        }
                        RegionNode::Block(span) => {
                            st.push_task(CheckTask::StepBlock {
                                span,
                                idx: 0,
                                limit,
                                saved_env: env.len(),
                                yielded: None,
                                depth,
                            })?;
                        }
                        RegionNode::IfElse { cond, then_region, else_region, results } => {
                            Self::expect_ty(cond, ValType::I32, env)?;
                            let then_n = region
                                .try_node_below(then_region, limit)
                                .ok_or(RegistryError::TypeMismatch)?;
                            let else_n = region
                                .try_node_below(else_region, limit)
                                .ok_or(RegistryError::TypeMismatch)?;
                            st.push_task(CheckTask::AfterIfElse { results })?;
                            st.push_task(CheckTask::Eval {
                                node: else_n,
                                limit: else_region.0 as usize,
                                depth: depth + 1,
                            })?;
                            st.push_task(CheckTask::Eval {
                                node: then_n,
                                limit: then_region.0 as usize,
                                depth: depth + 1,
                            })?;
                        }
                        RegionNode::BoundedLoop { init_vars, state_vars, body, .. } => {
                            Self::check_loop_inits(region, init_vars, state_vars, env)?;
                            let saved_env = env.len();
                            env.extend_vars(region, state_vars)?;
                            let body_n = region
                                .try_node_below(body, limit)
                                .ok_or(RegistryError::TypeMismatch)?;
                            st.push_task(CheckTask::AfterBoundedLoop { saved_env })?;
                            st.push_task(CheckTask::Eval {
                                node: body_n,
                                limit: body.0 as usize,
                                depth: depth + 1,
                            })?;
                        }
                        RegionNode::InvariantLoop {
                            init_vars,
                            state_vars,
                            cond,
                            invariant_pred,
                            fuel_measure,
                            body,
                        } => {
                            Self::check_loop_inits(region, init_vars, state_vars, env)?;
                            let saved_env = env.len();
                            env.extend_vars(region, state_vars)?;
                            let (Some(c), Some(inv), Some(f), Some(b)) = (
                                region.try_node_below(cond, limit),
                                region.try_node_below(invariant_pred, limit),
                                region.try_node_below(fuel_measure, limit),
                                region.try_node_below(body, limit),
                            ) else {
                                return Err(RegistryError::TypeMismatch);
                            };
                            st.push_task(CheckTask::AfterInvariantLoop { state_vars, saved_env })?;
                            st.push_task(CheckTask::Eval {
                                node: b,
                                limit: body.0 as usize,
                                depth: depth + 1,
                            })?;
                            st.push_task(CheckTask::Eval {
                                node: f,
                                limit: fuel_measure.0 as usize,
                                depth: depth + 1,
                            })?;
                            st.push_task(CheckTask::Eval {
                                node: inv,
                                limit: invariant_pred.0 as usize,
                                depth: depth + 1,
                            })?;
                            st.push_task(CheckTask::Eval {
                                node: c,
                                limit: cond.0 as usize,
                                depth: depth + 1,
                            })?;
                        }
                    }
                }
                CheckTask::StepBlock { span, idx, limit, saved_env, mut yielded, depth } => {
                    if idx >= span.len {
                        env.truncate(saved_env);
                        st.push_ty(yielded.unwrap_or(SmallTys::EMPTY))?;
                        continue;
                    }
                    let Some(pos) = span.start.checked_add(idx) else {
                        return Err(RegistryError::TypeMismatch);
                    };
                    let pos = pos as usize;
                    if pos >= region.pool.len() {
                        return Err(RegistryError::TypeMismatch);
                    }
                    let slot = region.pool[pos];
                    if !slot.is_stmt() {
                        return Err(RegistryError::TypeMismatch);
                    }
                    if slot.tag == TAG_STMT_REGION {
                        let results = Span { start: slot.w0, len: slot.w1 };
                        let sub_id = RegionNodeId(slot.w2);
                        let sub_n = region
                            .try_node_below(sub_id, limit)
                            .ok_or(RegistryError::TypeMismatch)?;
                        st.push_task(CheckTask::StepBlock {
                            span,
                            idx: idx + 1,
                            limit,
                            saved_env,
                            yielded,
                            depth,
                        })?;
                        st.push_task(CheckTask::AfterSubStmt { results })?;
                        st.push_task(CheckTask::Eval {
                            node: sub_n,
                            limit: sub_id.0 as usize,
                            depth: depth + 1,
                        })?;
                        continue;
                    }
                    self.check_simple_slot(ctx, slot, env, tp, &mut yielded)?;
                    if idx + 1 < span.len {
                        st.push_task(CheckTask::StepBlock {
                            span,
                            idx: idx + 1,
                            limit,
                            saved_env,
                            yielded,
                            depth,
                        })?;
                    } else {
                        env.truncate(saved_env);
                        st.push_ty(yielded.unwrap_or(SmallTys::EMPTY))?;
                    }
                }
                CheckTask::AfterSubStmt { results } => {
                    let sub_tys = st.pop_ty()?;
                    if !tp.eq_vars_span(sub_tys, region, results) {
                        return Err(RegistryError::TypeMismatch);
                    }
                    env.extend_vars(region, results)?;
                }
                CheckTask::AfterIfElse { results } => {
                    let else_tys = st.pop_ty()?;
                    let then_tys = st.pop_ty()?;
                    if !tp.eq_tys_span(then_tys, region, results)
                        || !tp.eq_tys_span(else_tys, region, results)
                    {
                        return Err(RegistryError::TypeMismatch);
                    }
                    st.push_ty(tp.intern_tys_span(region, results)?)?;
                }
                CheckTask::AfterBoundedLoop { saved_env } => {
                    env.truncate(saved_env);
                }
                CheckTask::AfterInvariantLoop { state_vars, saved_env } => {
                    let _body_tys = st.pop_ty()?;
                    let fuel_tys = st.pop_ty()?;
                    let inv_tys = st.pop_ty()?;
                    let cond_tys = st.pop_ty()?;
                    env.truncate(saved_env);
                    if !tp.eq_slice(cond_tys, &[ValType::I32])
                        || !tp.eq_slice(inv_tys, &[ValType::I32])
                        || !tp.eq_slice(fuel_tys, &[ValType::I64])
                    {
                        return Err(RegistryError::TypeMismatch);
                    }
                    st.push_ty(tp.intern_vars_span(region, state_vars)?)?;
                }
            }
        }
        st.pop_ty()
    }

    fn check_region(
        &self,
        region: &Region,
        params: &[(ValId, ValType)],
        caller_layer: u16,
        promoted_only: bool,
        self_op: Option<&StratumOp>,
        tp: &mut TyPool,
    ) -> Result<SmallTys, RegistryError> {
        if region.pool.is_empty() {
            return if region.is_empty_block() {
                Ok(SmallTys::EMPTY)
            } else {
                Err(RegistryError::TypeMismatch)
            };
        }
        if region.is_empty_block() {
            return Ok(SmallTys::EMPTY);
        }
        let ctx = CheckCtx { region, caller_layer, promoted_only, self_op };
        let mut env = TypeEnv::new(params);
        if let RegionNode::Block(span) = region.root {
            let saved_env = env.len();
            let mut yielded = None;
            let mut idx = 0;
            while idx < span.len {
                let Some(pos) = span.start.checked_add(idx) else {
                    return Err(RegistryError::TypeMismatch);
                };
                let pos = pos as usize;
                if pos >= region.pool.len() {
                    return Err(RegistryError::TypeMismatch);
                }
                let slot = region.pool[pos];
                if !slot.is_stmt() {
                    return Err(RegistryError::TypeMismatch);
                }
                if slot.tag == TAG_STMT_REGION {
                    return self.check_region_nested(
                        &ctx,
                        &mut env,
                        CheckTask::StepBlock {
                            span,
                            idx,
                            limit: region.pool.len(),
                            saved_env,
                            yielded,
                            depth: 0,
                        },
                        tp,
                    );
                }
                self.check_simple_slot(&ctx, slot, &mut env, tp, &mut yielded)?;
                idx += 1;
            }
            return Ok(yielded.unwrap_or(SmallTys::EMPTY));
        }
        self.check_region_nested(
            &ctx,
            &mut env,
            CheckTask::Eval { node: region.root, limit: region.pool.len(), depth: 0 },
            tp,
        )
    }

    /// Expands all `CallTarget::Stratum` calls into Layer-0 primitives across DAG layers.
    pub fn lower_region_to_layer0(
        &self,
        region: &Region,
        next_val: &mut u32,
    ) -> Result<Region, RegistryError> {
        *next_val = (*next_val).max(max_val_id_in_region(region));
        let mut cur = region.clone();
        let mut pass = 0usize;
        loop {
            if pass >= MAX_CHECK_DEPTH {
                return Err(RegistryError::TypeMismatch);
            }
            let (next_reg, changed) = self.expand_stratum_calls_once(&cur, next_val)?;
            if !changed {
                return Ok(next_reg);
            }
            cur = next_reg;
            pass += 1;
        }
    }

    fn expand_stratum_calls_once(
        &self,
        src: &Region,
        next_val: &mut u32,
    ) -> Result<(Region, bool), RegistryError> {
        if src.is_empty_block() {
            return Ok((Region::empty(), false));
        }
        let mut out = RegionBuilder::with_capacity(src.pool.len());
        let mut changed = false;
        let root_out =
            self.lower_node(src, src.root, src.pool.len(), next_val, &mut out, &mut changed, 0)?;
        Ok((out.finish_node(root_out), changed))
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_node(
        &self,
        src: &Region,
        node: RegionNode,
        limit: usize,
        next_val: &mut u32,
        out: &mut RegionBuilder,
        changed: &mut bool,
        depth: usize,
    ) -> Result<RegionNode, RegistryError> {
        if depth >= MAX_CHECK_DEPTH {
            return Err(RegistryError::TypeMismatch);
        }
        let copy_vals = |span: Span, b: &mut RegionBuilder| -> Result<Span, RegistryError> {
            if span.is_empty() {
                return Ok(Span::EMPTY);
            }
            let start = b.pool.len() as u32;
            for i in 0..span.len {
                b.pool.push(IrSlot::val(src.try_val(span, i).ok_or(RegistryError::TypeMismatch)?));
            }
            Ok(Span { start, len: span.len })
        };
        let copy_vars = |span: Span, b: &mut RegionBuilder| -> Result<Span, RegistryError> {
            if span.is_empty() {
                return Ok(Span::EMPTY);
            }
            let start = b.pool.len() as u32;
            for i in 0..span.len {
                let (id, ty) = src.try_var(span, i).ok_or(RegistryError::TypeMismatch)?;
                b.pool.push(IrSlot::var(id, ty));
            }
            Ok(Span { start, len: span.len })
        };
        let copy_tys = |span: Span, b: &mut RegionBuilder| -> Result<Span, RegistryError> {
            if span.is_empty() {
                return Ok(Span::EMPTY);
            }
            let start = b.pool.len() as u32;
            for i in 0..span.len {
                b.pool.push(IrSlot::ty(src.try_ty(span, i).ok_or(RegistryError::TypeMismatch)?));
            }
            Ok(Span { start, len: span.len })
        };

        match node {
            RegionNode::Block(span) if span.is_empty() => Ok(RegionNode::Block(Span::EMPTY)),
            RegionNode::Block(span) => {
                let mut stmts = Vec::with_capacity(span.len_usize());
                for i in 0..span.len {
                    let stmt = src.try_stmt(span, i).ok_or(RegistryError::TypeMismatch)?;
                    match stmt {
                        Stmt::Call { results, target: CallTarget::Stratum(sid), args } => {
                            let op = self.get_op(sid).ok_or(RegistryError::UnknownStratum(sid))?;
                            if args.len_usize() != op.params.len() {
                                return Err(RegistryError::TypeMismatch);
                            }
                            let mut map = Vec::with_capacity(op.params.len());
                            for j in 0..args.len {
                                let aid =
                                    src.try_val(args, j).ok_or(RegistryError::TypeMismatch)?;
                                map.push((op.params[j as usize].0, aid));
                            }
                            let remapped = remap_region_vals(&op.body, &map, next_val);
                            let new_res = copy_vars(results, out)?;
                            let sub_id = out.embed_region_id(&remapped);
                            stmts.push(Stmt::Region { results: new_res, region: sub_id });
                            *changed = true;
                        }
                        Stmt::Region { results, region: sub_id } => {
                            let sub = src
                                .try_node_below(sub_id, limit)
                                .ok_or(RegistryError::TypeMismatch)?;
                            let new_res = copy_vars(results, out)?;
                            let sub_n = self.lower_node(
                                src,
                                sub,
                                sub_id.0 as usize,
                                next_val,
                                out,
                                changed,
                                depth + 1,
                            )?;
                            let new_sub_id = out.alloc_node(sub_n);
                            stmts.push(Stmt::Region { results: new_res, region: new_sub_id });
                        }
                        Stmt::Call { results, target, args } => {
                            let r = copy_vars(results, out)?;
                            let a = copy_vals(args, out)?;
                            stmts.push(Stmt::Call { results: r, target, args: a });
                        }
                        Stmt::Yield(vs) => stmts.push(Stmt::Yield(copy_vals(vs, out)?)),
                        Stmt::Return(vs) => stmts.push(Stmt::Return(copy_vals(vs, out)?)),
                        Stmt::Break { depth: br_d, cond, values } => stmts.push(Stmt::Break {
                            depth: br_d,
                            cond,
                            values: copy_vals(values, out)?,
                        }),
                        Stmt::Continue { depth: ct_d, cond, values } => {
                            stmts.push(Stmt::Continue {
                                depth: ct_d,
                                cond,
                                values: copy_vals(values, out)?,
                            });
                        }
                        other => stmts.push(other),
                    }
                }
                Ok(RegionNode::Block(out.alloc_stmts(&stmts)))
            }
            RegionNode::IfElse { cond, then_region, else_region, results } => {
                let res = copy_tys(results, out)?;
                let t = src
                    .try_node_below(then_region, limit)
                    .ok_or(RegistryError::TypeMismatch)?;
                let e = src
                    .try_node_below(else_region, limit)
                    .ok_or(RegistryError::TypeMismatch)?;
                let t_n = self.lower_node(
                    src,
                    t,
                    then_region.0 as usize,
                    next_val,
                    out,
                    changed,
                    depth + 1,
                )?;
                let e_n = self.lower_node(
                    src,
                    e,
                    else_region.0 as usize,
                    next_val,
                    out,
                    changed,
                    depth + 1,
                )?;
                let t_id = out.alloc_node(t_n);
                let e_id = out.alloc_node(e_n);
                Ok(RegionNode::IfElse { cond, then_region: t_id, else_region: e_id, results: res })
            }
            RegionNode::BoundedLoop { max_iters, init_vars, state_vars, body } => {
                let iv = copy_vals(init_vars, out)?;
                let sv = copy_vars(state_vars, out)?;
                let b = src.try_node_below(body, limit).ok_or(RegistryError::TypeMismatch)?;
                let b_n =
                    self.lower_node(src, b, body.0 as usize, next_val, out, changed, depth + 1)?;
                let b_id = out.alloc_node(b_n);
                Ok(RegionNode::BoundedLoop { max_iters, init_vars: iv, state_vars: sv, body: b_id })
            }
            RegionNode::InvariantLoop {
                init_vars,
                state_vars,
                cond,
                invariant_pred,
                fuel_measure,
                body,
            } => {
                let iv = copy_vals(init_vars, out)?;
                let sv = copy_vars(state_vars, out)?;
                let (Some(c), Some(inv), Some(f), Some(b)) = (
                    src.try_node_below(cond, limit),
                    src.try_node_below(invariant_pred, limit),
                    src.try_node_below(fuel_measure, limit),
                    src.try_node_below(body, limit),
                ) else {
                    return Err(RegistryError::TypeMismatch);
                };
                let c_n =
                    self.lower_node(src, c, cond.0 as usize, next_val, out, changed, depth + 1)?;
                let inv_n = self.lower_node(
                    src,
                    inv,
                    invariant_pred.0 as usize,
                    next_val,
                    out,
                    changed,
                    depth + 1,
                )?;
                let f_n = self.lower_node(
                    src,
                    f,
                    fuel_measure.0 as usize,
                    next_val,
                    out,
                    changed,
                    depth + 1,
                )?;
                let b_n =
                    self.lower_node(src, b, body.0 as usize, next_val, out, changed, depth + 1)?;
                let c_id = out.alloc_node(c_n);
                let inv_id = out.alloc_node(inv_n);
                let f_id = out.alloc_node(f_n);
                let b_id = out.alloc_node(b_n);
                Ok(RegionNode::InvariantLoop {
                    init_vars: iv,
                    state_vars: sv,
                    cond: c_id,
                    invariant_pred: inv_id,
                    fuel_measure: f_id,
                    body: b_id,
                })
            }
        }
    }
}

//! Deterministic loop Verification Condition (VC) splitter and iterative region analyzers.

use alloc::{boxed::Box, vec, vec::Vec};
use crate::eval::{HeapState, eval_region_first};
use crate::ir::*;
use crate::registry::StratumRegistry;

const MAX_VC_DEPTH: usize = 64;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum VcKind {
    Init,
    Preservation,
    Exit,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum VcError {
    NotAnInvariantLoop,
    ImpureSpecificationRegion,
    ArityMismatch,
    UnstructuredControlFlow,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum VcEvalResult {
    Holds,
    Vacuous,
    Violated(Option<TrapCode>),
}

/// Small-vector storage for `VcObligation` assumption regions: stores up to 2
/// regions inline (covering `Init`, `Preservation`, and `Exit` VCs with zero
/// heap allocation), spilling seamlessly to `Vec<Region>` on the 3rd+ entry.
#[derive(Debug)]
pub struct RegionList {
    inline: [Region; 2],
    inline_len: usize,
    spill: Vec<Region>,
}

impl RegionList {
    pub const fn empty() -> Self {
        Self { inline: [Region::empty(), Region::empty()], inline_len: 0, spill: Vec::new() }
    }

    pub const fn single(r: Region) -> Self {
        Self { inline: [r, Region::empty()], inline_len: 1, spill: Vec::new() }
    }

    pub const fn pair(a: Region, b: Region) -> Self {
        Self { inline: [a, b], inline_len: 2, spill: Vec::new() }
    }

    pub fn from_vec(mut v: Vec<Region>) -> Self {
        match v.len() {
            0 => Self::empty(),
            1 => Self::single(v.pop().unwrap_or_else(Region::empty)),
            2 => {
                let b = v.pop().unwrap_or_else(Region::empty);
                let a = v.pop().unwrap_or_else(Region::empty);
                Self::pair(a, b)
            }
            _ => Self { inline: [Region::empty(), Region::empty()], inline_len: 0, spill: v },
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
    pub fn as_slice(&self) -> &[Region] {
        if self.spill.is_empty() { &self.inline[..self.inline_len] } else { &self.spill }
    }

    #[inline]
    pub fn iter(&self) -> core::slice::Iter<'_, Region> {
        self.as_slice().iter()
    }

    #[inline]
    pub fn get(&self, idx: usize) -> Option<&Region> {
        if self.spill.is_empty() {
            if idx < self.inline_len { Some(&self.inline[idx]) } else { None }
        } else {
            self.spill.get(idx)
        }
    }
}

impl Default for RegionList {
    fn default() -> Self {
        Self::empty()
    }
}

impl Clone for RegionList {
    fn clone(&self) -> Self {
        if self.spill.is_empty() {
            Self { inline: self.inline.clone(), inline_len: self.inline_len, spill: Vec::new() }
        } else {
            Self {
                inline: [Region::empty(), Region::empty()],
                inline_len: 0,
                spill: self.spill.clone(),
            }
        }
    }
}

impl PartialEq for RegionList {
    fn eq(&self, other: &Self) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl Eq for RegionList {}

impl From<Vec<Region>> for RegionList {
    fn from(v: Vec<Region>) -> Self {
        Self::from_vec(v)
    }
}

impl core::ops::Deref for RegionList {
    type Target = [Region];
    #[inline]
    fn deref(&self) -> &[Region] {
        self.as_slice()
    }
}

impl<'a> IntoIterator for &'a RegionList {
    type Item = &'a Region;
    type IntoIter = core::slice::Iter<'a, Region>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.as_slice().iter()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VcObligation {
    pub kind: VcKind,
    pub params: Vec<(ValId, ValType)>,
    pub assumptions: RegionList,
    pub goal: Region,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoopVcs {
    pub init: VcObligation,
    pub preservation: VcObligation,
    pub exit: VcObligation,
}

/// Ensures a predicate/measure/spec region performs no heap, global, or unverified call mutations.
pub fn validate_read_only(region: &Region) -> bool {
    validate_ro_upto(region, region.root, region.pool.len(), None)
}

/// Ensures `region` performs no heap or global mutations, verifying any `CallTarget::Stratum`
/// callees via `registry`'s inductively verified read-only metadata.
pub fn validate_read_only_with_registry(region: &Region, registry: &StratumRegistry) -> bool {
    validate_ro_upto(region, region.root, region.pool.len(), Some(registry))
}

#[derive(Clone, Copy)]
struct RoSlot {
    ro: bool,
    stmt_cnt: u32,
    bad_cnt: u32,
}

impl RoSlot {
    const ZERO: Self = Self { ro: false, stmt_cnt: 0, bad_cnt: 0 };
}

fn check_slot_ro(
    slot: IrSlot,
    idx: usize,
    registry: Option<&StratumRegistry>,
    slots: &[RoSlot],
) -> bool {
    match slot.tag {
        TAG_STMT_LET => slot.sub != OP_MEM_GROW,
        TAG_STMT_EFFECT => slot.sub == EFF_TRAP || slot.sub == EFF_NOP,
        TAG_STMT_REGION => {
            let s_idx = slot.w2 as usize;
            s_idx < idx && slots[s_idx].ro
        }
        TAG_STMT_CALL => {
            slot.sub == CALL_STRATUM
                && registry.is_some_and(|reg| reg.is_stratum_read_only(StratumId(slot.w2)))
        }
        TAG_STMT_YIELD | TAG_STMT_BREAK | TAG_STMT_CONTINUE | TAG_STMT_RETURN => true,
        _ => false,
    }
}

fn check_node_slot_ro_o1(slot: IrSlot, limit: usize, slots: &[RoSlot]) -> bool {
    match slot.tag {
        TAG_NODE_BLOCK => {
            if slot.w1 == 0 {
                return true;
            }
            let s = slot.w0 as usize;
            let e = s.saturating_add(slot.w1 as usize);
            e <= limit
                && (slots[e].stmt_cnt - slots[s].stmt_cnt == slot.w1)
                && (slots[e].bad_cnt == slots[s].bad_cnt)
        }
        TAG_NODE_IF => {
            let (t, e) = (slot.w1 as usize, slot.w2 as usize);
            t < limit && e < limit && slots[t].ro && slots[e].ro
        }
        TAG_NODE_BLOOP => {
            let b = slot.w5 as usize;
            b < limit && slots[b].ro
        }
        TAG_NODE_ILOOP => {
            let (c, i, f, b) =
                (slot.w4 as usize, slot.w5 as usize, slot.w6 as usize, slot.w7 as usize);
            c < limit
                && i < limit
                && f < limit
                && b < limit
                && slots[c].ro
                && slots[i].ro
                && slots[f].ro
                && slots[b].ro
        }
        _ => false,
    }
}

fn run_ro_pass(
    region: &Region,
    root_slot: IrSlot,
    lim: usize,
    registry: Option<&StratumRegistry>,
    slots: &mut [RoSlot],
) -> bool {
    let mut s_cnt = 0u32;
    let mut b_cnt = 0u32;
    let mut idx = 0;
    while idx < lim {
        let slot = region.pool[idx];
        if slot.is_stmt() {
            s_cnt += 1;
            if !check_slot_ro(slot, idx, registry, slots) {
                b_cnt += 1;
            }
        } else if slot.is_node() {
            slots[idx].ro = check_node_slot_ro_o1(slot, idx, slots);
        }
        slots[idx + 1].stmt_cnt = s_cnt;
        slots[idx + 1].bad_cnt = b_cnt;
        idx += 1;
    }
    check_node_slot_ro_o1(root_slot, lim, slots)
}

#[cold]
#[inline(never)]
fn validate_ro_upto_heap(
    region: &Region,
    root_slot: IrSlot,
    lim: usize,
    registry: Option<&StratumRegistry>,
) -> bool {
    let mut slots = vec![RoSlot::ZERO; lim + 1];
    run_ro_pass(region, root_slot, lim, registry, &mut slots)
}

fn validate_ro_slot_upto(
    region: &Region,
    root_slot: IrSlot,
    limit: usize,
    registry: Option<&StratumRegistry>,
) -> bool {
    if root_slot.tag == TAG_NODE_BLOCK && root_slot.w1 == 0 {
        return true;
    }
    let lim = limit.min(region.pool.len());
    if lim == 0 {
        return false;
    }
    if lim <= 32 {
        let mut inline = [RoSlot::ZERO; 33];
        run_ro_pass(region, root_slot, lim, registry, &mut inline[..=lim])
    } else {
        validate_ro_upto_heap(region, root_slot, lim, registry)
    }
}

pub(crate) fn validate_ro_upto(
    region: &Region,
    node: RegionNode,
    limit: usize,
    registry: Option<&StratumRegistry>,
) -> bool {
    validate_ro_slot_upto(region, IrSlot::from_node(node), limit, registry)
}

fn bump_id(v: ValId, m: &mut u32) {
    *m = (*m).max(v.0.saturating_add(1));
}

fn bump_typed(vs: &[(ValId, ValType)], m: &mut u32) {
    let mut i = 0;
    while i < vs.len() {
        bump_id(vs[i].0, m);
        i += 1;
    }
}

pub(crate) fn max_val_id_in_region(region: &Region) -> u32 {
    let mut max = 0u32;
    if let RegionNode::IfElse { cond, .. } = region.root {
        bump_id(cond, &mut max);
    }
    let mut i = 0;
    while i < region.pool.len() {
        let slot = region.pool[i];
        match slot.tag {
            TAG_NODE_IF | TAG_VAL | TAG_VAR => bump_id(ValId(slot.w0), &mut max),
            TAG_STMT_LET => {
                bump_id(ValId(slot.w0), &mut max);
                match slot.sub {
                    OP_COPY | OP_UN => bump_id(ValId(slot.w1), &mut max),
                    OP_SELECT => {
                        bump_id(ValId(slot.w1), &mut max);
                        bump_id(ValId(slot.w2), &mut max);
                        bump_id(ValId(slot.w3), &mut max);
                    }
                    OP_BIN => {
                        bump_id(ValId(slot.w1), &mut max);
                        bump_id(ValId(slot.w2), &mut max);
                    }
                    OP_LOAD | OP_MEM_GROW => bump_id(ValId(slot.w2), &mut max),
                    _ => {}
                }
            }
            TAG_STMT_EFFECT => match slot.sub {
                EFF_STORE => {
                    bump_id(ValId(slot.w1), &mut max);
                    bump_id(ValId(slot.w3), &mut max);
                }
                EFF_MEM_COPY => {
                    bump_id(ValId(slot.w2), &mut max);
                    bump_id(ValId(slot.w3), &mut max);
                    bump_id(ValId(slot.w4), &mut max);
                }
                EFF_MEM_FILL => {
                    bump_id(ValId(slot.w1), &mut max);
                    bump_id(ValId(slot.w2), &mut max);
                    bump_id(ValId(slot.w3), &mut max);
                }
                EFF_GLOBAL_SET => bump_id(ValId(slot.w1), &mut max),
                _ => {}
            },
            TAG_STMT_BREAK | TAG_STMT_CONTINUE if slot.sub != 0 => {
                bump_id(ValId(slot.w1), &mut max);
            }
            _ => {}
        }
        i += 1;
    }
    max
}

#[derive(Clone, Copy)]
struct FlowMask {
    bad: bool,
    br: u64,
    ct: u64,
}

impl FlowMask {
    const ZERO: Self = Self { bad: false, br: 0, ct: 0 };
    const BAD: Self = Self { bad: true, br: 0, ct: 0 };
}

#[derive(Clone, Copy)]
struct FlowSlot {
    norm: FlowMask,
    body: FlowMask,
    stmt_br: u64,
    stmt_ct: u64,
    stmt_cnt: u32,
    bad_cnt: u32,
    br_ct_cnt: u32,
}

impl FlowSlot {
    const ZERO: Self = Self {
        norm: FlowMask::BAD,
        body: FlowMask::BAD,
        stmt_br: 0,
        stmt_ct: 0,
        stmt_cnt: 0,
        bad_cnt: 0,
        br_ct_cnt: 0,
    };
}

#[cold]
#[inline(never)]
fn scan_block_br_ct(s: usize, e: usize, slots: &[FlowSlot]) -> (u64, u64) {
    let mut br = 0u64;
    let mut ct = 0u64;
    let mut k = s;
    while k < e {
        br |= slots[k].stmt_br;
        ct |= slots[k].stmt_ct;
        k += 1;
    }
    (br, ct)
}

fn compute_flow_o1(root_slot: IrSlot, limit: usize, slots: &[FlowSlot]) -> (FlowMask, FlowMask) {
    match root_slot.tag {
        TAG_NODE_BLOCK => {
            if root_slot.w1 == 0 {
                return (FlowMask::ZERO, FlowMask::ZERO);
            }
            let s = root_slot.w0 as usize;
            let e = s.saturating_add(root_slot.w1 as usize);
            if e > limit || (slots[e].stmt_cnt - slots[s].stmt_cnt != root_slot.w1) {
                return (FlowMask::BAD, FlowMask::BAD);
            }
            let bad = slots[e].bad_cnt != slots[s].bad_cnt;
            let (br, ct) = if slots[e].br_ct_cnt == slots[s].br_ct_cnt {
                (0u64, 0u64)
            } else {
                scan_block_br_ct(s, e, slots)
            };
            let as_body = FlowMask { bad, br, ct };
            let as_norm = FlowMask { bad: bad || ((ct & 1) != 0), br: br >> 1, ct: ct >> 1 };
            (as_norm, as_body)
        }
        TAG_NODE_IF => {
            let (t_i, e_i) = (root_slot.w1 as usize, root_slot.w2 as usize);
            if t_i >= limit || e_i >= limit {
                return (FlowMask::BAD, FlowMask::BAD);
            }
            let (t, e) = (slots[t_i].norm, slots[e_i].norm);
            let m = FlowMask { bad: t.bad || e.bad, br: t.br | e.br, ct: t.ct | e.ct };
            (m, m)
        }
        TAG_NODE_BLOOP => {
            let b_i = root_slot.w5 as usize;
            if b_i >= limit {
                return (FlowMask::BAD, FlowMask::BAD);
            }
            let b = slots[b_i].body;
            let m = FlowMask { bad: b.bad, br: b.br >> 1, ct: b.ct >> 1 };
            (m, m)
        }
        TAG_NODE_ILOOP => {
            let (c_i, inv_i, f_i, b_i) = (
                root_slot.w4 as usize,
                root_slot.w5 as usize,
                root_slot.w6 as usize,
                root_slot.w7 as usize,
            );
            if c_i >= limit || inv_i >= limit || f_i >= limit || b_i >= limit {
                return (FlowMask::BAD, FlowMask::BAD);
            }
            let (c, inv, f, b) =
                (slots[c_i].norm, slots[inv_i].norm, slots[f_i].norm, slots[b_i].body);
            let spec_bad = c.bad
                || c.br != 0
                || c.ct != 0
                || inv.bad
                || inv.br != 0
                || inv.ct != 0
                || f.bad
                || f.br != 0
                || f.ct != 0;
            let m = FlowMask { bad: spec_bad || b.bad, br: b.br >> 1, ct: b.ct >> 1 };
            (m, m)
        }
        _ => (FlowMask::BAD, FlowMask::BAD),
    }
}

fn run_flow_pass(
    region: &Region,
    root_slot: IrSlot,
    lim: usize,
    slots: &mut [FlowSlot],
) -> (FlowMask, FlowMask) {
    let mut s_cnt = 0u32;
    let mut b_cnt = 0u32;
    let mut bc_cnt = 0u32;
    let mut idx = 0;
    while idx < lim {
        let slot = region.pool[idx];
        if slot.is_stmt() {
            s_cnt += 1;
            let mut s_bad = false;
            let mut s_br = 0u64;
            let mut s_ct = 0u64;
            match slot.tag {
                TAG_STMT_RETURN => s_bad = true,
                TAG_STMT_BREAK => {
                    if slot.w0 >= 64 {
                        s_bad = true;
                    } else {
                        s_br = 1u64 << slot.w0;
                    }
                }
                TAG_STMT_CONTINUE => {
                    if slot.w0 >= 64 {
                        s_bad = true;
                    } else {
                        s_ct = 1u64 << slot.w0;
                    }
                }
                TAG_STMT_REGION => {
                    let sub_i = slot.w2 as usize;
                    if sub_i < idx {
                        let sub = slots[sub_i].norm;
                        s_bad = sub.bad;
                        s_br = sub.br;
                        s_ct = sub.ct;
                    } else {
                        s_bad = true;
                    }
                }
                _ => {}
            }
            slots[idx].stmt_br = s_br;
            slots[idx].stmt_ct = s_ct;
            if s_bad {
                b_cnt += 1;
            }
            if s_br != 0 || s_ct != 0 {
                bc_cnt += 1;
            }
        } else if slot.is_node() {
            let (a, b) = compute_flow_o1(slot, idx, slots);
            slots[idx].norm = a;
            slots[idx].body = b;
        }
        slots[idx + 1].stmt_cnt = s_cnt;
        slots[idx + 1].bad_cnt = b_cnt;
        slots[idx + 1].br_ct_cnt = bc_cnt;
        idx += 1;
    }
    compute_flow_o1(root_slot, lim, slots)
}

#[cold]
#[inline(never)]
fn has_escaping_flow_heap(region: &Region, root_slot: IrSlot, lim: usize) -> (FlowMask, FlowMask) {
    let mut slots = vec![FlowSlot::ZERO; lim + 1];
    run_flow_pass(region, root_slot, lim, &mut slots)
}

fn has_escaping_flow_slot_upto(
    region: &Region,
    root_slot: IrSlot,
    limit: usize,
    as_loop_body_root: bool,
) -> bool {
    if root_slot.tag == TAG_NODE_BLOCK && root_slot.w1 == 0 {
        return false;
    }
    let lim = limit.min(region.pool.len());
    let (norm, body) = if lim == 0 {
        compute_flow_o1(root_slot, 0, &[FlowSlot::ZERO])
    } else if lim <= 16 {
        let mut inline = [FlowSlot::ZERO; 17];
        run_flow_pass(region, root_slot, lim, &mut inline[..=lim])
    } else {
        has_escaping_flow_heap(region, root_slot, lim)
    };
    if as_loop_body_root {
        body.bad || body.br != 0 || (body.ct & !1u64) != 0
    } else {
        norm.bad || norm.br != 0 || norm.ct != 0
    }
}

fn has_escaping_flow_upto(
    region: &Region,
    node: RegionNode,
    limit: usize,
    as_loop_body_root: bool,
) -> bool {
    has_escaping_flow_slot_upto(region, IrSlot::from_node(node), limit, as_loop_body_root)
}

enum ScopeBuf {
    Inline([(ValId, ValId); 8]),
    Heap(Box<[(ValId, ValId)]>),
}

struct Scope {
    buf: ScopeBuf,
    len: usize,
}

impl Scope {
    fn with_max_cap(initial: &[(ValId, ValId)], extra_cap: usize) -> Self {
        let cap = initial.len().saturating_add(extra_cap);
        let mut s = if cap <= 8 {
            Self { buf: ScopeBuf::Inline([(ValId(0), ValId(0)); 8]), len: 0 }
        } else {
            Self { buf: ScopeBuf::Heap(vec![(ValId(0), ValId(0)); cap].into_boxed_slice()), len: 0 }
        };
        let mut i = 0;
        while i < initial.len() {
            s.push(initial[i].0, initial[i].1);
            i += 1;
        }
        s
    }

    fn len(&self) -> usize {
        self.len
    }

    fn truncate(&mut self, saved: usize) {
        self.len = saved;
    }

    fn push(&mut self, old: ValId, mapped: ValId) {
        match &mut self.buf {
            ScopeBuf::Inline(a) => {
                if self.len < a.len() {
                    a[self.len] = (old, mapped);
                    self.len += 1;
                }
            }
            ScopeBuf::Heap(h) => {
                if self.len < h.len() {
                    h[self.len] = (old, mapped);
                    self.len += 1;
                }
            }
        }
    }

    fn lookup(&self, id: ValId) -> ValId {
        let slice: &[(ValId, ValId)] = match &self.buf {
            ScopeBuf::Inline(a) => &a[..self.len],
            ScopeBuf::Heap(h) => &h[..self.len],
        };
        let mut i = slice.len();
        while i > 0 {
            i -= 1;
            if slice[i].0 == id {
                return slice[i].1;
            }
        }
        id
    }

    fn fresh(&mut self, old: ValId, next: &mut u32) -> ValId {
        let f = ValId(*next);
        *next = next.saturating_add(1);
        self.push(old, f);
        f
    }
}

#[allow(clippy::large_enum_variant)]
enum PoolStorage {
    Inline([IrSlot; 16]),
    Heap(Vec<IrSlot>),
}

struct ExactPool {
    buf: PoolStorage,
    len: usize,
}

impl ExactPool {
    fn new(cap: usize) -> Self {
        if cap <= 16 {
            Self { buf: PoolStorage::Inline([IrSlot::ZERO; 16]), len: 0 }
        } else {
            Self { buf: PoolStorage::Heap(Vec::with_capacity(cap)), len: 0 }
        }
    }
    fn push(&mut self, e: IrSlot) {
        match &mut self.buf {
            PoolStorage::Inline(a) => {
                if self.len < a.len() {
                    a[self.len] = e;
                    self.len += 1;
                }
            }
            PoolStorage::Heap(h) => {
                h.push(e);
                self.len = h.len();
            }
        }
    }
    fn alloc_node(&mut self, n: RegionNode) -> RegionNodeId {
        let id = RegionNodeId(self.len as u32);
        self.push(IrSlot::from_node(n));
        id
    }
    fn alloc_stmts(&mut self, stmts: &[Stmt]) -> Span {
        if stmts.is_empty() {
            return Span::EMPTY;
        }
        let start = self.len as u32;
        let mut i = 0;
        while i < stmts.len() {
            self.push(IrSlot::from_stmt(stmts[i]));
            i += 1;
        }
        Span { start, len: stmts.len() as u32 }
    }
    fn into_region(self, root: RegionNode) -> Region {
        if self.len == 0 && matches!(root, RegionNode::Block(s) if s.is_empty()) {
            return Region::empty();
        }
        match self.buf {
            PoolStorage::Inline(a) => {
                let mut pool = SlotPool::with_capacity(self.len);
                pool.extend_from_slice(&a[..self.len]);
                Region { root, pool }
            }
            PoolStorage::Heap(pool) => Region { root, pool: SlotPool::from_vec(pool) },
        }
    }
}

fn remap_vals_span(src: &Region, span: Span, scope: &Scope, out: &mut ExactPool) -> Span {
    if span.is_empty() {
        return Span::EMPTY;
    }
    let start = out.len as u32;
    let mut i = 0;
    while i < span.len {
        let v = src.try_val(span, i).unwrap_or(ValId(0));
        out.push(IrSlot::val(scope.lookup(v)));
        i += 1;
    }
    Span { start, len: span.len }
}

fn remap_fresh_vars_span(
    src: &Region,
    span: Span,
    scope: &mut Scope,
    next: &mut u32,
    out: &mut ExactPool,
) -> Span {
    if span.is_empty() {
        return Span::EMPTY;
    }
    let start = out.len as u32;
    let mut i = 0;
    while i < span.len {
        let (id, ty) = src.try_var(span, i).unwrap_or((ValId(0), ValType::I32));
        out.push(IrSlot::var(scope.fresh(id, next), ty));
        i += 1;
    }
    Span { start, len: span.len }
}

fn copy_tys_span(src: &Region, span: Span, out: &mut ExactPool) -> Span {
    if span.is_empty() {
        return Span::EMPTY;
    }
    let start = out.len as u32;
    let mut i = 0;
    while i < span.len {
        let t = src.try_ty(span, i).unwrap_or(ValType::I32);
        out.push(IrSlot::ty(t));
        i += 1;
    }
    Span { start, len: span.len }
}

fn remap_leaf_stmt(
    src: &Region,
    stmt: Stmt,
    scope: &mut Scope,
    next: &mut u32,
    inner_d: u32,
    norm_cont: bool,
    out: &mut ExactPool,
) -> Stmt {
    match stmt {
        Stmt::Let { dst, ty, op } => {
            let new_op = match op {
                Op::Copy(v) => Op::Copy(scope.lookup(v)),
                Op::Select { cond, true_val, false_val } => Op::Select {
                    cond: scope.lookup(cond),
                    true_val: scope.lookup(true_val),
                    false_val: scope.lookup(false_val),
                },
                Op::Un(u, v) => Op::Un(u, scope.lookup(v)),
                Op::Bin(b, l, r) => Op::Bin(b, scope.lookup(l), scope.lookup(r)),
                Op::Load { mem, addr, offset, width, signed, result_ty } => Op::Load {
                    mem,
                    addr: scope.lookup(addr),
                    offset,
                    width,
                    signed,
                    result_ty,
                },
                Op::MemoryGrow { mem, delta } => {
                    Op::MemoryGrow { mem, delta: scope.lookup(delta) }
                }
                other => other,
            };
            Stmt::Let { dst: scope.fresh(dst, next), ty, op: new_op }
        }
        Stmt::Effect(eff) => Stmt::Effect(match eff {
            EffectOp::Store { mem, addr, offset, width, val } => EffectOp::Store {
                mem,
                addr: scope.lookup(addr),
                offset,
                width,
                val: scope.lookup(val),
            },
            EffectOp::MemoryCopy { dst_mem, src_mem, dst, src, len } => EffectOp::MemoryCopy {
                dst_mem,
                src_mem,
                dst: scope.lookup(dst),
                src: scope.lookup(src),
                len: scope.lookup(len),
            },
            EffectOp::MemoryFill { mem, dst, val, len } => EffectOp::MemoryFill {
                mem,
                dst: scope.lookup(dst),
                val: scope.lookup(val),
                len: scope.lookup(len),
            },
            EffectOp::GlobalSet { id, val } => EffectOp::GlobalSet { id, val: scope.lookup(val) },
            other => other,
        }),
        Stmt::Call { results, target, args } => {
            let new_args = remap_vals_span(src, args, scope, out);
            let new_res = remap_fresh_vars_span(src, results, scope, next, out);
            Stmt::Call { results: new_res, target, args: new_args }
        }
        Stmt::Yield(vs) => Stmt::Yield(remap_vals_span(src, vs, scope, out)),
        Stmt::Return(vs) => Stmt::Return(remap_vals_span(src, vs, scope, out)),
        Stmt::Break { depth, cond, values } => Stmt::Break {
            depth,
            cond: cond.map(|c| scope.lookup(c)),
            values: remap_vals_span(src, values, scope, out),
        },
        Stmt::Continue { depth, cond, values } => {
            let new_cond = cond.map(|c| scope.lookup(c));
            let new_vals = remap_vals_span(src, values, scope, out);
            if norm_cont && depth == inner_d {
                Stmt::Break { depth, cond: new_cond, values: new_vals }
            } else {
                Stmt::Continue { depth, cond: new_cond, values: new_vals }
            }
        }
        Stmt::Region { .. } => Stmt::Effect(EffectOp::Nop),
    }
}

#[allow(clippy::too_many_arguments)]
fn remap_rec(
    src: &Region,
    node: RegionNode,
    limit: usize,
    scope: &mut Scope,
    next_fresh: &mut u32,
    depth: u32,
    is_loop_body_root: bool,
    norm_cont: bool,
    rec: usize,
    out: &mut ExactPool,
    stmt_buf: &mut [Stmt],
    buf_pos: usize,
) -> RegionNode {
    if rec >= MAX_VC_DEPTH {
        return RegionNode::Block(Span::EMPTY);
    }
    match node {
        RegionNode::Block(span) if span.is_empty() => RegionNode::Block(Span::EMPTY),
        RegionNode::Block(span) => {
            let inner_d = if is_loop_body_root { depth } else { depth + 1 };
            let saved_scope = scope.len();
            let mut end_pos = buf_pos;
            let mut i = 0;
            while i < span.len {
                let Some(stmt) = src.try_stmt(span, i) else { break };
                let mapped = if let Stmt::Region { results, region: sub_id } = stmt {
                    let sub_n =
                        src.try_node_below(sub_id, limit).unwrap_or(RegionNode::Block(Span::EMPTY));
                    let new_sub = remap_rec(
                        src,
                        sub_n,
                        sub_id.0 as usize,
                        scope,
                        next_fresh,
                        inner_d,
                        false,
                        norm_cont,
                        rec + 1,
                        out,
                        stmt_buf,
                        end_pos,
                    );
                    let new_sub_id = out.alloc_node(new_sub);
                    let new_res = remap_fresh_vars_span(src, results, scope, next_fresh, out);
                    Stmt::Region { results: new_res, region: new_sub_id }
                } else {
                    remap_leaf_stmt(src, stmt, scope, next_fresh, inner_d, norm_cont, out)
                };
                if end_pos < stmt_buf.len() {
                    stmt_buf[end_pos] = mapped;
                    end_pos += 1;
                }
                i += 1;
            }
            scope.truncate(saved_scope);
            RegionNode::Block(out.alloc_stmts(&stmt_buf[buf_pos..end_pos]))
        }
        RegionNode::IfElse { cond, then_region, else_region, results } => {
            let new_cond = scope.lookup(cond);
            let new_res = copy_tys_span(src, results, out);
            let then_n =
                src.try_node_below(then_region, limit).unwrap_or(RegionNode::Block(Span::EMPTY));
            let else_n =
                src.try_node_below(else_region, limit).unwrap_or(RegionNode::Block(Span::EMPTY));
            let new_then = remap_rec(
                src,
                then_n,
                then_region.0 as usize,
                scope,
                next_fresh,
                depth,
                false,
                norm_cont,
                rec + 1,
                out,
                stmt_buf,
                buf_pos,
            );
            let new_else = remap_rec(
                src,
                else_n,
                else_region.0 as usize,
                scope,
                next_fresh,
                depth,
                false,
                norm_cont,
                rec + 1,
                out,
                stmt_buf,
                buf_pos,
            );
            let then_id = out.alloc_node(new_then);
            let else_id = out.alloc_node(new_else);
            RegionNode::IfElse {
                cond: new_cond,
                then_region: then_id,
                else_region: else_id,
                results: new_res,
            }
        }
        RegionNode::BoundedLoop { max_iters, init_vars, state_vars, body } => {
            let new_inits = remap_vals_span(src, init_vars, scope, out);
            let saved = scope.len();
            let new_states = remap_fresh_vars_span(src, state_vars, scope, next_fresh, out);
            let body_n = src.try_node_below(body, limit).unwrap_or(RegionNode::Block(Span::EMPTY));
            let new_body = remap_rec(
                src,
                body_n,
                body.0 as usize,
                scope,
                next_fresh,
                depth + 1,
                true,
                norm_cont,
                rec + 1,
                out,
                stmt_buf,
                buf_pos,
            );
            scope.truncate(saved);
            let body_id = out.alloc_node(new_body);
            RegionNode::BoundedLoop {
                max_iters,
                init_vars: new_inits,
                state_vars: new_states,
                body: body_id,
            }
        }
        RegionNode::InvariantLoop {
            init_vars,
            state_vars,
            cond,
            invariant_pred,
            fuel_measure,
            body,
        } => {
            let new_inits = remap_vals_span(src, init_vars, scope, out);
            let saved = scope.len();
            let new_states = remap_fresh_vars_span(src, state_vars, scope, next_fresh, out);
            let cond_n = src.try_node_below(cond, limit).unwrap_or(RegionNode::Block(Span::EMPTY));
            let inv_n =
                src.try_node_below(invariant_pred, limit).unwrap_or(RegionNode::Block(Span::EMPTY));
            let fuel_n =
                src.try_node_below(fuel_measure, limit).unwrap_or(RegionNode::Block(Span::EMPTY));
            let body_n = src.try_node_below(body, limit).unwrap_or(RegionNode::Block(Span::EMPTY));
            let new_cond = remap_rec(
                src,
                cond_n,
                cond.0 as usize,
                scope,
                next_fresh,
                0,
                false,
                false,
                rec + 1,
                out,
                stmt_buf,
                buf_pos,
            );
            let new_inv = remap_rec(
                src,
                inv_n,
                invariant_pred.0 as usize,
                scope,
                next_fresh,
                0,
                false,
                false,
                rec + 1,
                out,
                stmt_buf,
                buf_pos,
            );
            let new_fuel = remap_rec(
                src,
                fuel_n,
                fuel_measure.0 as usize,
                scope,
                next_fresh,
                0,
                false,
                false,
                rec + 1,
                out,
                stmt_buf,
                buf_pos,
            );
            let new_body = remap_rec(
                src,
                body_n,
                body.0 as usize,
                scope,
                next_fresh,
                depth + 1,
                true,
                norm_cont,
                rec + 1,
                out,
                stmt_buf,
                buf_pos,
            );
            scope.truncate(saved);
            let cond_id = out.alloc_node(new_cond);
            let inv_id = out.alloc_node(new_inv);
            let fuel_id = out.alloc_node(new_fuel);
            let body_id = out.alloc_node(new_body);
            RegionNode::InvariantLoop {
                init_vars: new_inits,
                state_vars: new_states,
                cond: cond_id,
                invariant_pred: inv_id,
                fuel_measure: fuel_id,
                body: body_id,
            }
        }
    }
}

fn remap_slot(
    src: &Region,
    root_slot: IrSlot,
    limit: usize,
    initial_map: &[(ValId, ValId)],
    next_fresh: &mut u32,
    norm_root_continue: bool,
) -> Region {
    if root_slot.tag == TAG_NODE_BLOCK {
        if root_slot.w1 == 0 {
            return Region::empty();
        }
        if root_slot.w1 == 1
            && let Some(slot) =
                src.try_stmt_slot(Span { start: root_slot.w0, len: root_slot.w1 }, 0)
            && slot.tag == TAG_STMT_YIELD
            && slot.w1 == 1
            && let Some(v0) = src.try_val(Span { start: slot.w0, len: slot.w1 }, 0)
        {
            let mut mapped = v0;
            let mut i = initial_map.len();
            while i > 0 {
                i -= 1;
                if initial_map[i].0 == v0 {
                    mapped = initial_map[i].1;
                    break;
                }
            }
            return Region::yield_vals(&[mapped]);
        }
    }
    let Some(root) = root_slot.to_node() else {
        return Region::empty();
    };
    remap_node(src, root, limit, initial_map, next_fresh, norm_root_continue)
}

fn remap_node(
    src: &Region,
    root: RegionNode,
    limit: usize,
    initial_map: &[(ValId, ValId)],
    next_fresh: &mut u32,
    norm_root_continue: bool,
) -> Region {
    if let RegionNode::Block(s) = root {
        if s.is_empty() {
            return Region::empty();
        }
        if s.len == 1
            && let Some(slot) = src.try_stmt_slot(s, 0)
            && slot.tag == TAG_STMT_YIELD
            && slot.w1 == 1
            && let Some(v0) = src.try_val(Span { start: slot.w0, len: slot.w1 }, 0)
        {
            let mut mapped = v0;
            let mut i = initial_map.len();
            while i > 0 {
                i -= 1;
                if initial_map[i].0 == v0 {
                    mapped = initial_map[i].1;
                    break;
                }
            }
            return Region::yield_vals(&[mapped]);
        }
    }
    let lim = limit.min(src.pool.len());
    let max_elems = src.pool.len().saturating_mul(2).saturating_add(8);
    let mut scope = Scope::with_max_cap(initial_map, src.pool.len() + 1);
    let mut out = ExactPool::new(max_elems);
    let mut inline_stmts = [Stmt::Effect(EffectOp::Nop); 8];
    let mut heap_stmts: Box<[Stmt]> = if src.pool.len() < 8 {
        Box::new([])
    } else {
        vec![Stmt::Effect(EffectOp::Nop); src.pool.len() + 1].into_boxed_slice()
    };
    let stmt_buf: &mut [Stmt] =
        if src.pool.len() < 8 { &mut inline_stmts } else { &mut heap_stmts };
    let root_out = remap_rec(
        src,
        root,
        lim,
        &mut scope,
        next_fresh,
        0,
        norm_root_continue,
        norm_root_continue,
        0,
        &mut out,
        stmt_buf,
        0,
    );
    out.into_region(root_out)
}

/// Alpha-renames all locally defined `ValId`s in `region` using `initial_map`,
/// guaranteeing newly allocated `ValId`s never collide with free uses or `initial_map`.
pub fn remap_region_vals(
    region: &Region,
    initial_map: &[(ValId, ValId)],
    next_fresh: &mut u32,
) -> Region {
    let mut min_safe = max_val_id_in_region(region);
    let mut i = 0;
    while i < initial_map.len() {
        let (k, v) = initial_map[i];
        min_safe = min_safe.max(k.0.max(v.0).saturating_add(1));
        i += 1;
    }
    if *next_fresh < min_safe {
        *next_fresh = min_safe;
    }
    remap_node(region, region.root, region.pool.len(), initial_map, next_fresh, false)
}

fn single_yield_val(reg: &Region) -> Option<ValId> {
    let RegionNode::Block(s) = reg.root else { return None };
    if s.len != 1 {
        return None;
    }
    let slot = reg.try_stmt_slot(s, 0)?;
    if slot.tag == TAG_STMT_YIELD && slot.w1 == 1 {
        reg.try_val(Span { start: slot.w0, len: slot.w1 }, 0)
    } else {
        None
    }
}

fn push_sub_stmt(b: &mut RegionBuilder, results: &[(ValId, ValType)], reg: &Region) {
    if let RegionNode::Block(s) = reg.root {
        if s.is_empty() {
            if results.is_empty() {
                b.push_effect(EffectOp::Nop);
            } else {
                b.push_effect(EffectOp::Trap(TrapCode::Unreachable));
            }
            return;
        }
        if s.len == 1
            && let Some(slot) = reg.try_stmt_slot(s, 0)
            && slot.tag == TAG_STMT_YIELD
        {
            let vs = Span { start: slot.w0, len: slot.w1 };
            if vs.len == 1 && results.len() == 1
                && let Some(v0) = reg.try_val(vs, 0)
            {
                b.push_let(results[0].0, results[0].1, Op::Copy(v0));
                return;
            }
            if vs.is_empty() && results.is_empty() {
                b.push_effect(EffectOp::Nop);
                return;
            }
            if vs.len_usize() != results.len() {
                b.push_effect(EffectOp::Trap(TrapCode::Unreachable));
                return;
            }
        }
    }
    b.push_subregion(results, reg);
}

/// Splits an `InvariantLoop` deterministically into `VC_Init`, `VC_Preservation`, and `VC_Exit`.
pub fn split_invariant_loop(
    init_params: Vec<(ValId, ValType)>,
    precondition: Option<Region>,
    loop_region: &Region,
    postcondition: Region,
) -> Result<LoopVcs, VcError> {
    let RegionNode::InvariantLoop {
        init_vars,
        state_vars,
        cond,
        invariant_pred,
        fuel_measure,
        body,
    } = loop_region.root
    else {
        return Err(VcError::NotAnInvariantLoop);
    };
    if init_vars.len != state_vars.len {
        return Err(VcError::ArityMismatch);
    }
    let lp_lim = loop_region.pool.len();
    let get_node_slot = |id: RegionNodeId| -> Option<IrSlot> {
        let idx = id.0 as usize;
        if idx >= lp_lim {
            return None;
        }
        let slot = loop_region.pool[idx];
        if slot.is_node() { Some(slot) } else { None }
    };
    let (Some(cond_s), Some(inv_s), Some(fuel_s), Some(body_s)) = (
        get_node_slot(cond),
        get_node_slot(invariant_pred),
        get_node_slot(fuel_measure),
        get_node_slot(body),
    ) else {
        return Err(VcError::NotAnInvariantLoop);
    };
    if !precondition.as_ref().is_none_or(validate_read_only)
        || !validate_ro_slot_upto(loop_region, cond_s, cond.0 as usize, None)
        || !validate_ro_slot_upto(loop_region, inv_s, invariant_pred.0 as usize, None)
        || !validate_ro_slot_upto(loop_region, fuel_s, fuel_measure.0 as usize, None)
        || !validate_read_only(&postcondition)
    {
        return Err(VcError::ImpureSpecificationRegion);
    }
    if precondition
        .as_ref()
        .is_some_and(|p| has_escaping_flow_upto(p, p.root, p.pool.len(), false))
        || has_escaping_flow_slot_upto(loop_region, cond_s, cond.0 as usize, false)
        || has_escaping_flow_slot_upto(loop_region, inv_s, invariant_pred.0 as usize, false)
        || has_escaping_flow_slot_upto(loop_region, fuel_s, fuel_measure.0 as usize, false)
        || has_escaping_flow_upto(&postcondition, postcondition.root, postcondition.pool.len(), false)
        || has_escaping_flow_slot_upto(loop_region, body_s, body.0 as usize, true)
    {
        return Err(VcError::UnstructuredControlFlow);
    }

    let mut next_fresh = 1u32.max(max_val_id_in_region(loop_region)).max(max_val_id_in_region(&postcondition));
    bump_typed(&init_params, &mut next_fresh);
    if let Some(p) = &precondition {
        next_fresh = next_fresh.max(max_val_id_in_region(p));
    }
    let fresh = |nf: &mut u32| {
        let id = ValId(*nf);
        *nf = nf.saturating_add(1);
        id
    };

    let n_state = state_vars.len_usize();
    let mut loop_params = Vec::with_capacity(n_state + init_params.len());
    let mut init_map_inline = [(ValId(0), ValId(0)); 4];
    let mut init_map_spill = if n_state > 4 { Vec::with_capacity(n_state) } else { Vec::new() };
    let mut i = 0;
    while i < state_vars.len {
        let (sv_id, sv_ty) = loop_region.try_var(state_vars, i).ok_or(VcError::ArityMismatch)?;
        let iv_id = loop_region.try_val(init_vars, i).ok_or(VcError::ArityMismatch)?;
        loop_params.push((sv_id, sv_ty));
        if n_state <= 4 {
            init_map_inline[i as usize] = (sv_id, iv_id);
        } else {
            init_map_spill.push((sv_id, iv_id));
        }
        i += 1;
    }
    let init_map: &[(ValId, ValId)] =
        if n_state <= 4 { &init_map_inline[..n_state] } else { &init_map_spill };
    let mut ip_idx = 0;
    while ip_idx < init_params.len() {
        let (id, ty) = init_params[ip_idx];
        if !loop_params.iter().any(|&(existing, _)| existing == id) {
            loop_params.push((id, ty));
        }
        ip_idx += 1;
    }

    let init = VcObligation {
        kind: VcKind::Init,
        params: init_params,
        assumptions: match precondition {
            Some(p) => RegionList::single(p),
            None => RegionList::empty(),
        },
        goal: remap_slot(loop_region, inv_s, invariant_pred.0 as usize, init_map, &mut next_fresh, false),
    };

    let (c_val, ok_val, one, zero, f_before, f_after, inv_after, fuel_dec, chk_raw) = (
        fresh(&mut next_fresh),
        fresh(&mut next_fresh),
        fresh(&mut next_fresh),
        fresh(&mut next_fresh),
        fresh(&mut next_fresh),
        fresh(&mut next_fresh),
        fresh(&mut next_fresh),
        fresh(&mut next_fresh),
        fresh(&mut next_fresh),
    );
    let mut s_next = Vec::with_capacity(n_state);
    let mut after_map = Vec::with_capacity(n_state);
    let mut s_idx = 0;
    while s_idx < state_vars.len {
        let (sv_id, sv_ty) = loop_region.try_var(state_vars, s_idx).ok_or(VcError::ArityMismatch)?;
        let n = fresh(&mut next_fresh);
        s_next.push((n, sv_ty));
        after_map.push((sv_id, n));
        s_idx += 1;
    }

    let norm_body = remap_slot(loop_region, body_s, body.0 as usize, &[], &mut next_fresh, true);
    let body_block = if matches!(norm_body.root, RegionNode::Block(_)) {
        norm_body
    } else {
        let mut tmp = Vec::with_capacity(n_state);
        let mut tmp_ids = Vec::with_capacity(n_state);
        for &(_, ty) in &s_next {
            let id = fresh(&mut next_fresh);
            tmp.push((id, ty));
            tmp_ids.push(id);
        }
        let mut wb = RegionBuilder::new();
        wb.push_subregion(&tmp, &norm_body);
        wb.push_yield(&tmp_ids);
        wb.finish()
    };

    let remapped_cond = remap_slot(loop_region, cond_s, cond.0 as usize, &[], &mut next_fresh, false);
    let pres_goal = if remapped_cond.is_empty_block() {
        Region::single_slot(IrSlot::effect(EffectOp::Trap(TrapCode::Unreachable)))
    } else {
        let fuel_before_reg = remap_slot(loop_region, fuel_s, fuel_measure.0 as usize, &[], &mut next_fresh, false);
        let inv_after_reg = remap_slot(loop_region, inv_s, invariant_pred.0 as usize, &after_map, &mut next_fresh, false);
        let fuel_after_reg = remap_slot(loop_region, fuel_s, fuel_measure.0 as usize, &after_map, &mut next_fresh, false);

        let mut tb = RegionBuilder::new();
        push_sub_stmt(&mut tb, &[(f_before, ValType::I64)], &fuel_before_reg);
        push_sub_stmt(&mut tb, &s_next, &body_block);
        push_sub_stmt(&mut tb, &[(inv_after, ValType::I32)], &inv_after_reg);
        push_sub_stmt(&mut tb, &[(f_after, ValType::I64)], &fuel_after_reg);
        tb.push_let(zero, ValType::I32, Op::ConstI32(0));
        tb.push_let(fuel_dec, ValType::I32, Op::Bin(BinOp::I64LtU, f_after, f_before));
        tb.push_let(
            chk_raw,
            ValType::I32,
            Op::Select { cond: inv_after, true_val: fuel_dec, false_val: zero },
        );
        tb.push_yield(&[chk_raw]);
        let then_branch = tb.finish();

        let mut eb = RegionBuilder::new();
        eb.push_let(one, ValType::I32, Op::ConstI32(1));
        eb.push_yield(&[one]);
        let else_branch = eb.finish();

        if let Some(only_c) = single_yield_val(&remapped_cond) {
            Region::if_else(only_c, &then_branch, &else_branch, &[ValType::I32])
        } else {
            let if_reg = Region::if_else(c_val, &then_branch, &else_branch, &[ValType::I32]);
            let mut pb = RegionBuilder::new();
            push_sub_stmt(&mut pb, &[(c_val, ValType::I32)], &remapped_cond);
            pb.push_subregion(&[(ok_val, ValType::I32)], &if_reg);
            pb.push_yield(&[ok_val]);
            pb.finish()
        }
    };

    let preservation = VcObligation {
        kind: VcKind::Preservation,
        params: loop_params.clone(),
        assumptions: RegionList::single(remap_slot(
            loop_region,
            inv_s,
            invariant_pred.0 as usize,
            &[],
            &mut next_fresh,
            false,
        )),
        goal: pres_goal,
    };

    let (ec, ez) = (fresh(&mut next_fresh), fresh(&mut next_fresh));
    let exit_cond_reg = remap_slot(loop_region, cond_s, cond.0 as usize, &[], &mut next_fresh, false);
    let mut ncb = RegionBuilder::new();
    push_sub_stmt(&mut ncb, &[(ec, ValType::I32)], &exit_cond_reg);
    ncb.push_let(ez, ValType::I32, Op::Un(UnOp::I32Eqz, ec));
    ncb.push_yield(&[ez]);
    let not_cond = ncb.finish();

    let exit = VcObligation {
        kind: VcKind::Exit,
        params: loop_params,
        assumptions: RegionList::pair(
            remap_slot(loop_region, inv_s, invariant_pred.0 as usize, &[], &mut next_fresh, false),
            not_cond,
        ),
        goal: remap_node(&postcondition, postcondition.root, postcondition.pool.len(), &[], &mut next_fresh, false),
    };

    Ok(LoopVcs { init, preservation, exit })
}

/// Evaluates a concrete test point against one loop-free `VcObligation`.
pub fn eval_vc(
    module: &Module,
    registry: &StratumRegistry,
    vc: &VcObligation,
    args: &[Val],
    mut heap: HeapState,
) -> VcEvalResult {
    if args.len() != vc.params.len() {
        return VcEvalResult::Violated(None);
    }
    let mut inline_b = [(ValId(0), Val::I32(0)); 8];
    let mut spill_b: Vec<(ValId, Val)> = Vec::new();
    if vc.params.len() <= 8 {
        let mut i = 0;
        while i < vc.params.len() {
            if args[i].val_type() != vc.params[i].1 {
                return VcEvalResult::Violated(None);
            }
            inline_b[i] = (vc.params[i].0, args[i]);
            i += 1;
        }
    } else {
        spill_b.reserve(vc.params.len());
        let mut i = 0;
        while i < vc.params.len() {
            if args[i].val_type() != vc.params[i].1 {
                return VcEvalResult::Violated(None);
            }
            spill_b.push((vc.params[i].0, args[i]));
            i += 1;
        }
    }
    let bindings: &[(ValId, Val)] =
        if vc.params.len() <= 8 { &inline_b[..vc.params.len()] } else { &spill_b };

    let heap_empty = heap.memories.is_empty() && heap.globals.is_empty();
    let mut a_idx = 0;
    while a_idx < vc.assumptions.len() {
        let mut h_chk = if heap_empty {
            HeapState {
                memories: Vec::new(),
                globals: Vec::new(),
                fuel_remaining: heap.fuel_remaining,
            }
        } else {
            heap.clone()
        };
        let holds = matches!(
            eval_region_first(module, registry, &vc.assumptions[a_idx], bindings, &mut h_chk),
            Ok(Some(v)) if v.as_i32().unwrap_or(0) != 0
        );
        if !holds {
            return VcEvalResult::Vacuous;
        }
        a_idx += 1;
    }
    match eval_region_first(module, registry, &vc.goal, bindings, &mut heap) {
        Err(trap) => VcEvalResult::Violated(Some(trap)),
        Ok(Some(Val::I32(v))) if v != 0 => VcEvalResult::Holds,
        Ok(Some(Val::I64(v))) if v != 0 => VcEvalResult::Holds,
        Ok(_) => VcEvalResult::Violated(None),
    }
}

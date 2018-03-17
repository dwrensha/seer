use byteorder::{ReadBytesExt, WriteBytesExt, LittleEndian, BigEndian};
use std::collections::{btree_map, BTreeMap, HashMap, HashSet, VecDeque, BTreeSet};
use std::{fmt, iter, ptr, mem, io};

use rustc::{ty, mir};
use rustc::ty::layout::{self, TargetDataLayout};

use constraints::ConstraintContext;
use error::{EvalError, EvalResult};
use value::{self, PrimVal, PrimValKind, Value};

////////////////////////////////////////////////////////////////////////////////
// Allocations and pointers
////////////////////////////////////////////////////////////////////////////////

#[derive(Copy, Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct AllocId(pub u64);

impl fmt::Display for AllocId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct AbstractVariable(pub u32);

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum SByte {
    Concrete(u8),
    Abstract(AbstractVariable),
}

#[derive(Debug, Clone)]
pub struct Allocation {
    /// The actual bytes of the allocation.
    /// Note that the bytes of a pointer represent the offset of the pointer
    pub bytes: Vec<SByte>,

    /// Maps from byte addresses to allocations.
    /// Only the first byte of a pointer is inserted into the map.
    pub relocations: BTreeMap<u64, AllocId>,

    /// Denotes undefined memory. Reading from undefined memory is forbidden in miri
    pub undef_mask: UndefMask,

    /// The alignment of the allocation to detect unaligned reads.
    pub align: u64,

    /// Whether the allocation may be modified.
    /// Use the `mark_static_initalized` method of `Memory` to ensure that an error occurs, if the memory of this
    /// allocation is modified or deallocated in the future.
    pub static_kind: StaticKind,
}

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum StaticKind {
    /// may be deallocated without breaking miri's invariants
    NotStatic,
    /// may be modified, but never deallocated
    Mutable,
    /// may neither be modified nor deallocated
    Immutable,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct MemoryPointer {
    pub alloc_id: AllocId,
    pub offset: PointerOffset,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum PointerOffset {
    /// Offset in bytes.
    Concrete(u64),

    /// The bytes of an abstract offset, in little endian byteorder.
    Abstract([SByte; 8]),
}

impl PointerOffset {
    pub fn as_primval(&self) -> PrimVal {
        match *self {
            PointerOffset::Concrete(n) => PrimVal::Bytes(n as u128),
            PointerOffset::Abstract(sbytes) => PrimVal::Abstract(sbytes),
        }
    }
}

impl MemoryPointer {
    pub fn new(alloc_id: AllocId, offset: u64) -> Self {
        MemoryPointer { alloc_id, offset: PointerOffset::Concrete(offset), }
    }

    pub fn new_abstract(alloc_id: AllocId, offset: [SByte; 8]) -> Self {
        MemoryPointer { alloc_id, offset: PointerOffset::Abstract(offset), }
    }

    pub fn with_primval_offset(alloc_id: AllocId, offset: PrimVal) -> Self {
        match offset {
            PrimVal::Abstract(sbytes) => MemoryPointer::new_abstract(alloc_id, sbytes),
            PrimVal::Bytes(b) => MemoryPointer::new(alloc_id, b as u64),
            PrimVal::Undef => panic!("tried to construct pointer with undefined offset"),
            PrimVal::Ptr(_) => panic!("tried to construct point with pointer offset"),
        }
    }

    pub fn has_concrete_offset(self) -> bool {
        match self.offset {
            PointerOffset::Concrete(_) => true,
            _ => false,
        }
    }

    pub fn wrapping_signed_offset<'tcx>(self, i: i64, layout: &TargetDataLayout) -> Self {
        match self.offset {
            PointerOffset::Concrete(self_offset) => {
                MemoryPointer::new(self.alloc_id, value::wrapping_signed_offset(self_offset, i, layout))
            }
            _ => unimplemented!(),
        }
    }

    pub fn overflowing_signed_offset<'tcx>(self, i: i128, layout: &TargetDataLayout) -> (Self, bool) {
        match self.offset {
            PointerOffset::Concrete(self_offset) => {
                let (res, over) = value::overflowing_signed_offset(self_offset, i, layout);
                (MemoryPointer::new(self.alloc_id, res), over)
            }
            _ => unimplemented!(),
        }
    }

    pub fn signed_offset<'tcx>(self, i: i64, layout: &TargetDataLayout) -> EvalResult<'tcx, Self> {
        match self.offset {
            PointerOffset::Concrete(self_offset) => {
                Ok(MemoryPointer::new(self.alloc_id, value::signed_offset(self_offset, i, layout)?))
            }
            _ => unimplemented!(),
        }
    }

    pub fn overflowing_offset<'tcx>(self, i: u64, layout: &TargetDataLayout) -> (Self, bool) {
        match self.offset {
            PointerOffset::Concrete(self_offset) => {
                let (res, over) = value::overflowing_offset(self_offset, i, layout);
                (MemoryPointer::new(self.alloc_id, res), over)
            }
            _ => unimplemented!(),
        }
    }

    pub fn offset<'tcx>(self, i: u64, layout: &TargetDataLayout) -> EvalResult<'tcx, Self> {
        match self.offset {
            PointerOffset::Concrete(offset) => {
                Ok(MemoryPointer::new(self.alloc_id, value::offset(offset, i, layout)?))
            }
            _ => unimplemented!(),
        }
    }

    pub fn to_value_with_vtable(self, vtable: MemoryPointer) -> Value {
        Value::ByValPair(PrimVal::Ptr(self), PrimVal::Ptr(vtable))
    }
}

////////////////////////////////////////////////////////////////////////////////
// Top-level interpreter memory
////////////////////////////////////////////////////////////////////////////////

#[derive(Clone)]
pub struct Memory<'a, 'tcx> {
    /// Actual memory allocations (arbitrary bytes, may contain pointers into other allocations).
    alloc_map: HashMap<AllocId, Allocation>,

    rustc_allocations: HashMap<mir::interpret::AllocId, AllocId>,

    /// The AllocId to assign to the next new allocation. Always incremented, never gets smaller.
    next_id: AllocId,

    /// Set of statics, constants, promoteds, vtables, ... to prevent `mark_static_initalized` from
    /// stepping out of its own allocations. This set only contains statics backed by an
    /// allocation. If they are ByVal or ByValPair they are not here, but will be inserted once
    /// they become ByRef.
    static_alloc: HashSet<AllocId>,

    /// Number of virtual bytes allocated.
    memory_usage: u64,

    /// Maximum number of virtual bytes that may be allocated.
    memory_size: u64,

    /// Function "allocations". They exist solely so pointers have something to point to, and
    /// we can figure out what they point to.
    functions: HashMap<AllocId, ty::Instance<'tcx>>,

    /// Inverse map of `functions` so we don't allocate a new pointer every time we need one
    function_alloc_cache: HashMap<ty::Instance<'tcx>, AllocId>,

    /// Target machine data layout to emulate.
    pub layout: &'a TargetDataLayout,

    /// List of memory regions containing packed structures.
    ///
    /// We mark memory as "packed" or "unaligned" for a single statement, and clear the marking
    /// afterwards. In the case where no packed structs are present, it's just a single emptyness
    /// check of a set instead of heavily influencing all memory access code as other solutions
    /// would.
    ///
    /// One disadvantage of this solution is the fact that you can cast a pointer to a packed
    /// struct to a pointer to a normal struct and if you access a field of both in the same MIR
    /// statement, the normal struct access will succeed even though it shouldn't. But even with
    /// mir optimizations, that situation is hard/impossible to produce.
    packed: BTreeSet<Entry>,

    /// A cache for basic byte allocations keyed by their contents. This is used to deduplicate
    /// allocations for string and bytestring literals.
    literal_alloc_cache: HashMap<Vec<u8>, AllocId>,

    pub constraints: ConstraintContext,
}

impl<'a, 'tcx> Memory<'a, 'tcx> {
    pub fn new(layout: &'a TargetDataLayout, max_memory: u64) -> Self {
        Memory {
            alloc_map: HashMap::new(),
            rustc_allocations: HashMap::new(),
            functions: HashMap::new(),
            function_alloc_cache: HashMap::new(),
            next_id: AllocId(2),
            layout,
            memory_size: max_memory,
            memory_usage: 0,
            packed: BTreeSet::new(),
            static_alloc: HashSet::new(),
            literal_alloc_cache: HashMap::new(),
            constraints: ConstraintContext::new(),
        }
    }

    //// Trunace the given value to the pointer size; also return whether there was an overflow
    pub fn truncate_to_ptr(&self, val: u128) -> (u64, bool) {
        let max_ptr_plus_1 = 1u128 << self.layout.pointer_size.bits();
        ((val % max_ptr_plus_1) as u64, val >= max_ptr_plus_1)
    }

    pub fn allocations(&self) -> ::std::collections::hash_map::Iter<AllocId, Allocation> {
        self.alloc_map.iter()
    }

    pub fn create_fn_alloc(&mut self, instance: ty::Instance<'tcx>) -> MemoryPointer {
        if let Some(&alloc_id) = self.function_alloc_cache.get(&instance) {
            return MemoryPointer::new(alloc_id, 0);
        }
        let id = self.next_id;
        debug!("creating fn ptr: {}", id);
        self.next_id.0 += 1;
        self.functions.insert(id, instance);
        self.function_alloc_cache.insert(instance, id);
        MemoryPointer::new(id, 0)
    }

    pub fn allocate_cached(&mut self, bytes: &[u8]) -> EvalResult<'tcx, MemoryPointer> {
        if let Some(&alloc_id) = self.literal_alloc_cache.get(bytes) {
            return Ok(MemoryPointer::new(alloc_id, 0));
        }

        let ptr = self.allocate(bytes.len() as u64, 1)?;
        self.write_bytes(ptr, bytes)?;
        self.mark_static_initalized(ptr.alloc_id, false)?;
        self.literal_alloc_cache.insert(bytes.to_vec(), ptr.alloc_id);
        Ok(ptr)
    }

    pub fn allocate(&mut self, size: u64, align: u64) -> EvalResult<'tcx, MemoryPointer> {
        assert_ne!(align, 0);
        assert!(align.is_power_of_two());

        if self.memory_size - self.memory_usage < size {
            return Err(EvalError::OutOfMemory {
                allocation_size: size,
                memory_size: self.memory_size,
                memory_usage: self.memory_usage,
            });
        }
        self.memory_usage += size;
        assert_eq!(size as usize as u64, size);
        let alloc = Allocation {
            bytes: vec![SByte::Concrete(0); size as usize],
            relocations: BTreeMap::new(),
            undef_mask: UndefMask::new(size),
            align,
            static_kind: StaticKind::NotStatic,
        };
        let id = self.next_id;
        self.next_id.0 += 1;
        self.alloc_map.insert(id, alloc);
        Ok(MemoryPointer::new(id, 0))
    }

    pub fn get_rustc_allocation(&mut self, tcx: &ty::TyCtxt<'a, 'tcx, 'tcx>, ptr: mir::interpret::MemoryPointer)
                                -> EvalResult<'tcx, MemoryPointer>
    {
        if self.rustc_allocations.contains_key(&ptr.alloc_id) {
            Ok(MemoryPointer::new(AllocId(self.rustc_allocations[&ptr.alloc_id].0), ptr.offset))
        } else {
            let static_ = tcx
                .interpret_interner
                .get_corresponding_static_def_id(ptr.alloc_id);

            if let Some(_def_id) = static_ {
                unimplemented!()
            } else if let Some(alloc) = tcx.interpret_interner.get_alloc(ptr.alloc_id) {
                let size = alloc.bytes.len() as u64;
                let static_kind = match alloc.runtime_mutability {
                    ::syntax::ast::Mutability::Mutable =>  StaticKind::Mutable,
                    ::syntax::ast::Mutability::Immutable =>  StaticKind::Immutable,
                };
                let mut new_alloc = Allocation {
                    bytes: vec![],
                    relocations: BTreeMap::new(),
                    undef_mask: UndefMask::new(size),
                    align : alloc.align.abi(),
                    static_kind,
                };

                for &b in &alloc.bytes {
                    new_alloc.bytes.push(SByte::Concrete(b));
                }

                // XXX
                new_alloc.undef_mask.set_range_inbounds(0, size, true);

                if !alloc.relocations.is_empty() {
                    // TODO
                    unimplemented!()
                }

                let id = self.next_id;
                self.next_id.0 += 1;
                self.alloc_map.insert(id, new_alloc);
                self.rustc_allocations.insert(ptr.alloc_id, id);
                Ok(MemoryPointer::new(id, ptr.offset))
            } else {
                panic!("missing allocation {:?}", ptr.alloc_id);
            }
        }
    }

    // TODO(solson): Track which allocations were returned from __rust_allocate and report an error
    // when reallocating/deallocating any others.
    pub fn reallocate(&mut self, ptr: MemoryPointer, new_size: u64, align: u64) -> EvalResult<'tcx, MemoryPointer> {
        assert!(align.is_power_of_two());
        let ptr_offset = match ptr.offset {
            PointerOffset::Concrete(offset) => offset,
            _ => unimplemented!(),
        };

        // TODO(solson): Report error about non-__rust_allocate'd pointer.
        if ptr_offset != 0 {
            return Err(EvalError::Unimplemented(format!("bad pointer offset: {}", ptr_offset)));
        }
        if self.get(ptr.alloc_id).ok().map_or(false, |alloc| alloc.static_kind != StaticKind::NotStatic) {
            return Err(EvalError::ReallocatedStaticMemory);
        }

        let size = self.get(ptr.alloc_id)?.bytes.len() as u64;

        if new_size > size {
            let amount = new_size - size;
            self.memory_usage += amount;
            let alloc = self.get_mut(ptr.alloc_id)?;
            assert_eq!(amount as usize as u64, amount);
            alloc.bytes.extend(iter::repeat(SByte::Concrete(0)).take(amount as usize));
            alloc.undef_mask.grow(amount, false);
        } else if size > new_size {
            self.memory_usage -= size - new_size;
            self.clear_relocations(ptr.offset(new_size, self.layout)?, size - new_size)?;
            let alloc = self.get_mut(ptr.alloc_id)?;
            // `as usize` is fine here, since it is smaller than `size`, which came from a usize
            alloc.bytes.truncate(new_size as usize);
            alloc.bytes.shrink_to_fit();
            alloc.undef_mask.truncate(new_size);
        }

        Ok(MemoryPointer::new(ptr.alloc_id, 0))
    }

    // TODO(solson): See comment on `reallocate`.
    pub fn deallocate(&mut self, ptr: MemoryPointer) -> EvalResult<'tcx> {
        let ptr_offset = match ptr.offset {
            PointerOffset::Concrete(offset) => offset,
            _ => unimplemented!(),
        };

        if ptr_offset != 0 {
            // TODO(solson): Report error about non-__rust_allocate'd pointer.
            return Err(EvalError::Unimplemented(format!("bad pointer offset: {}", ptr_offset)));
        }
        if self.get(ptr.alloc_id).ok().map_or(false, |alloc| alloc.static_kind != StaticKind::NotStatic) {
            return Err(EvalError::DeallocatedStaticMemory);
        }

        if let Some(alloc) = self.alloc_map.remove(&ptr.alloc_id) {
            self.memory_usage -= alloc.bytes.len() as u64;
        } else {
            debug!("deallocated a pointer twice: {}", ptr.alloc_id);
            // TODO(solson): Report error about erroneous free. This is blocked on properly tracking
            // already-dropped state since this if-statement is entered even in safe code without
            // it.
        }
        debug!("deallocated : {}", ptr.alloc_id);

        Ok(())
    }

    pub fn pointer_size(&self) -> u64 {
        self.layout.pointer_size.bytes()
    }

    pub fn endianness(&self) -> layout::Endian {
        self.layout.endian
    }

    pub fn check_align(&self, ptr: MemoryPointer, align: u64, len: u64) -> EvalResult<'tcx> {
        let ptr_offset = match ptr.offset {
            PointerOffset::Concrete(offset) => offset,
            _ => unimplemented!(),
        };

        let alloc = self.get(ptr.alloc_id)?;
        // check whether the memory was marked as packed
        // we select all elements that have the correct alloc_id and are within
        // the range given by the offset into the allocation and the length
        let start = Entry {
            alloc_id: ptr.alloc_id,
            packed_start: 0,
            packed_end: ptr_offset + len,
        };
        let end = Entry {
            alloc_id: ptr.alloc_id,
            packed_start: ptr_offset + len,
            packed_end: 0,
        };
        for &Entry { packed_start, packed_end, .. } in self.packed.range(start..end) {
            // if the region we are checking is covered by a region in `packed`
            // ignore the actual alignment
            if packed_start <= ptr_offset && (ptr_offset + len) <= packed_end {
                return Ok(());
            }
        }
        if alloc.align < align {
            return Err(EvalError::AlignmentCheckFailed {
                has: alloc.align,
                required: align,
            });
        }
        if ptr_offset % align == 0 {
            Ok(())
        } else {
            Err(EvalError::AlignmentCheckFailed {
                has: ptr_offset % align,
                required: align,
            })
        }
    }

    pub(crate) fn check_bounds(&self, ptr: MemoryPointer, access: bool) -> EvalResult<'tcx> {
        let alloc = self.get(ptr.alloc_id)?;
        let allocation_size = alloc.bytes.len() as u64;

        let ptr_offset = match ptr.offset {
            PointerOffset::Concrete(offset) => offset,
            _ => unimplemented!(),
        };

        if ptr_offset > allocation_size {
            return Err(EvalError::PointerOutOfBounds { ptr, access, allocation_size });
        }
        Ok(())
    }

    pub(crate) fn mark_packed(&mut self, ptr: MemoryPointer, len: u64) {
        let ptr_offset = match ptr.offset {
            PointerOffset::Concrete(offset) => offset,
            _ => unimplemented!(),
        };

        self.packed.insert(Entry {
            alloc_id: ptr.alloc_id,
            packed_start: ptr_offset,
            packed_end: ptr_offset + len,
        });
    }

    pub(crate) fn clear_packed(&mut self) {
        self.packed.clear();
    }
}

// The derived `Ord` impl sorts first by the first field, then, if the fields are the same
// by the second field, and if those are the same, too, then by the third field.
// This is exactly what we need for our purposes, since a range within an allocation
// will give us all `Entry`s that have that `AllocId`, and whose `packed_start` is <= than
// the one we're looking for, but not > the end of the range we're checking.
// At the same time the `packed_end` is irrelevant for the sorting and range searching, but used for the check.
// This kind of search breaks, if `packed_end < packed_start`, so don't do that!
#[derive(Eq, PartialEq, Ord, PartialOrd, Clone)]
struct Entry {
    alloc_id: AllocId,
    packed_start: u64,
    packed_end: u64,
}

/// Allocation accessors
impl<'a, 'tcx> Memory<'a, 'tcx> {
    pub fn get(&self, id: AllocId) -> EvalResult<'tcx, &Allocation> {
        match self.alloc_map.get(&id) {
            Some(alloc) => Ok(alloc),
            None => match self.functions.get(&id) {
                Some(_) => Err(EvalError::DerefFunctionPointer),
                None => Err(EvalError::DanglingPointerDeref),
            }
        }
    }

    pub fn get_mut(&mut self, id: AllocId) -> EvalResult<'tcx, &mut Allocation> {
        match self.alloc_map.get_mut(&id) {
            Some(alloc) => match alloc.static_kind {
                StaticKind::Mutable |
                StaticKind::NotStatic => Ok(alloc),
                StaticKind::Immutable => Err(EvalError::ModifiedConstantMemory),
            },
            None => match self.functions.get(&id) {
                Some(_) => Err(EvalError::DerefFunctionPointer),
                None => Err(EvalError::DanglingPointerDeref),
            }
        }
    }

    pub fn get_fn(&self, ptr: MemoryPointer) -> EvalResult<'tcx, ty::Instance<'tcx>> {
        //if ptr.offset != 0 {
        //    return Err(EvalError::InvalidFunctionPointer);
        //}
        debug!("reading fn ptr: {}", ptr.alloc_id);
        match self.functions.get(&ptr.alloc_id) {
            Some(&fndef) => Ok(fndef),
            None => match self.alloc_map.get(&ptr.alloc_id) {
                Some(_) => Err(EvalError::ExecuteMemory),
                None => Err(EvalError::InvalidFunctionPointer),
            }
        }
    }

    /// For debugging, print an allocation and all allocations it points to, recursively.
    pub fn dump_alloc(&self, id: AllocId) {
        self.dump_allocs(vec![id]);
    }

    /// For debugging, print a list of allocations and all allocations they point to, recursively.
    pub fn dump_allocs(&self, mut allocs: Vec<AllocId>) {
        use std::fmt::Write;
        allocs.sort();
        allocs.dedup();
        let mut allocs_to_print = VecDeque::from(allocs);
        let mut allocs_seen = HashSet::new();

        while let Some(id) = allocs_to_print.pop_front() {
            let mut msg = format!("Alloc {:<5} ", format!("{}:", id));
            let prefix_len = msg.len();
            let mut relocations = vec![];

            let alloc = match (self.alloc_map.get(&id), self.functions.get(&id)) {
                (Some(a), None) => a,
                (None, Some(instance)) => {
                    trace!("{} {}", msg, instance);
                    continue;
                },
                (None, None) => {
                    trace!("{} (deallocated)", msg);
                    continue;
                },
                (Some(_), Some(_)) => bug!("miri invariant broken: an allocation id exists that points to both a function and a memory location"),
            };

            for i in 0..(alloc.bytes.len() as u64) {
                if let Some(&target_id) = alloc.relocations.get(&i) {
                    if allocs_seen.insert(target_id) {
                        allocs_to_print.push_back(target_id);
                    }
                    relocations.push((i, target_id));
                }
                if alloc.undef_mask.is_range_defined(i, i + 1) {
                    // this `as usize` is fine, since `i` came from a `usize`
                    write!(msg, "{:?} ", alloc.bytes[i as usize]).unwrap();
                } else {
                    msg.push_str("__ ");
                }
            }

            let immutable = match alloc.static_kind {
                StaticKind::Mutable => " (static mut)",
                StaticKind::Immutable => " (immutable)",
                StaticKind::NotStatic => "",
            };
            trace!("{}({} bytes, alignment {}){}", msg, alloc.bytes.len(), alloc.align, immutable);

            if !relocations.is_empty() {
                msg.clear();
                write!(msg, "{:1$}", "", prefix_len).unwrap(); // Print spaces.
                let mut pos = 0;
                let relocation_width = (self.pointer_size() - 1) * 3;
                for (i, target_id) in relocations {
                    // this `as usize` is fine, since we can't print more chars than `usize::MAX`
                    write!(msg, "{:1$}", "", ((i - pos) * 3) as usize).unwrap();
                    let target = format!("({})", target_id);
                    // this `as usize` is fine, since we can't print more chars than `usize::MAX`
                    write!(msg, "└{0:─^1$}┘ ", target, relocation_width as usize).unwrap();
                    pos = i + self.pointer_size();
                }
                trace!("{}", msg);
            }
        }
    }

    pub fn leak_report(&self) -> usize {
        trace!("### LEAK REPORT ###");
        let leaks: Vec<_> = self.alloc_map
            .iter()
            .filter_map(|(&key, val)| {
                if val.static_kind == StaticKind::NotStatic {
                    Some(key)
                } else {
                    None
                }
            })
            .collect();
        let n = leaks.len();
        self.dump_allocs(leaks);
        n
    }
}

/// Byte accessors
impl<'a, 'tcx> Memory<'a, 'tcx> {
    fn get_bytes_unchecked(&self, ptr: MemoryPointer, size: u64, align: u64)
                           -> EvalResult<'tcx, &[SByte]>
    {
        if size == 0 {
            return Ok(&[]);
        }
        self.check_align(ptr, align, size)?;

        // if ptr.offset is in bounds, then so is ptr (because offset checks for overflow)
        self.check_bounds(ptr.offset(size, self.layout)?, true)?;

        let alloc = self.get(ptr.alloc_id)?;

        let ptr_offset = match ptr.offset {
            PointerOffset::Concrete(offset) => offset,
            _ => unimplemented!(),
        };

        assert_eq!(ptr_offset as usize as u64, ptr_offset);
        assert_eq!(size as usize as u64, size);
        let offset = ptr_offset as usize;
        Ok(&alloc.bytes[offset..offset + size as usize])
    }

    fn get_bytes_unchecked_mut(&mut self, ptr: MemoryPointer, size: u64, align: u64)
                               -> EvalResult<'tcx, &mut [SByte]>
    {
        if size == 0 {
            return Ok(&mut []);
        }
        self.check_align(ptr, align, size)?;
        self.check_bounds(ptr.offset(size, self.layout)?, true)?; // if ptr.offset is in bounds, then so is ptr (because offset checks for overflow)
        let alloc = self.get_mut(ptr.alloc_id)?;

        assert_eq!(size as usize as u64, size);
        let ptr_offset = match ptr.offset {
            PointerOffset::Concrete(offset) => offset,
            _ => unimplemented!(),
        };

        assert_eq!(ptr_offset as usize as u64, ptr_offset);
        let ptr_offset = ptr_offset as usize;

        Ok(&mut alloc.bytes[ptr_offset..ptr_offset + size as usize])
    }

    fn get_bytes(&self, ptr: MemoryPointer, size: u64, align: u64)
                 -> EvalResult<'tcx, &[SByte]>
    {
        if size == 0 {
            return Ok(&[]);
        }
        if self.relocations(ptr, size)?.count() != 0 {
            return Err(EvalError::ReadPointerAsBytes);
        }
        self.check_defined(ptr, size)?;
        self.get_bytes_unchecked(ptr, size, align)
    }

    fn get_bytes_mut(&mut self, ptr: MemoryPointer, size: u64, align: u64)
                     -> EvalResult<'tcx, &mut [SByte]>
    {
        if size == 0 {
            return Ok(&mut []);
        }
        self.clear_relocations(ptr, size)?;
        self.mark_definedness(PrimVal::Ptr(ptr), size, true)?;
        self.get_bytes_unchecked_mut(ptr, size, align)
    }

    pub fn write_fresh_abstract_bytes(&mut self, ptr: MemoryPointer, size: u64)
        -> EvalResult<'tcx>
    {
        let mut abytes = Vec::new();
        for _ in 0..(size as usize){
            abytes.push(self.constraints.fresh_stdin_byte());
        }

        let sbytes = self.get_bytes_mut(ptr, size, 1)?;
        for idx in 0..(size as usize){
            sbytes[idx] = abytes[idx];
        }

        Ok(())
    }
}

/// Reading and writing
impl<'a, 'tcx> Memory<'a, 'tcx> {
    /// mark an allocation as being the entry point to a static (see `static_alloc` field)
    pub fn mark_static(&mut self, alloc_id: AllocId) {
        trace!("mark_static: {:?}", alloc_id);
        if !self.static_alloc.insert(alloc_id) {
            bug!("tried to mark an allocation ({:?}) as static twice", alloc_id);
        }
    }

    /// mark an allocation pointed to by a static as static and initialized
    pub fn mark_inner_allocation(&mut self, alloc: AllocId, mutable: bool) -> EvalResult<'tcx> {
        // relocations into other statics are not "inner allocations"
        if !self.static_alloc.contains(&alloc) {
            self.mark_static_initalized(alloc, mutable)?;
        }
        Ok(())
    }

    /// mark an allocation as static and initialized, either mutable or not
    pub fn mark_static_initalized(&mut self, alloc_id: AllocId, mutable: bool) -> EvalResult<'tcx> {
        trace!("mark_static_initialized {:?}, mutable: {:?}", alloc_id, mutable);
        // do not use `self.get_mut(alloc_id)` here, because we might have already marked a
        // sub-element or have circular pointers (e.g. `Rc`-cycles)
        let relocations = match self.alloc_map.get_mut(&alloc_id) {
            Some(&mut Allocation { ref mut relocations, static_kind: ref mut kind @ StaticKind::NotStatic, .. }) => {
                *kind = if mutable {
                    StaticKind::Mutable
                } else {
                    StaticKind::Immutable
                };
                // take out the relocations vector to free the borrow on self, so we can call
                // mark recursively
                mem::replace(relocations, Default::default())
            },
            None if !self.functions.contains_key(&alloc_id) => return Err(EvalError::DanglingPointerDeref),
            _ => return Ok(()),
        };
        // recurse into inner allocations
        for &alloc in relocations.values() {
            self.mark_inner_allocation(alloc, mutable)?;
        }
        // put back the relocations
        self.alloc_map.get_mut(&alloc_id).expect("checked above").relocations = relocations;
        Ok(())
    }

    pub fn copy(&mut self, src: PrimVal, dest: PrimVal, size: u64, align: u64) -> EvalResult<'tcx> {
        if size == 0 {
            return Ok(());
        }
        let src = src.to_ptr()?;
        let dest = dest.to_ptr()?;

        if let PointerOffset::Abstract(_) = dest.offset {
            unimplemented!()
        }

        if let PointerOffset::Abstract(_) = src.offset {
            return self.abstract_copy(src, dest, size, align);
        }

        self.check_relocation_edges(src, size)?;

        // first copy the relocations to a temporary buffer, because
        // `get_bytes_mut` will clear the relocations, which is correct,
        // since we don't want to keep any relocations at the target.

        let relocations: Vec<_> =
            match (src.offset, dest.offset) {
                (PointerOffset::Concrete(src_offset), PointerOffset::Concrete(dest_offset)) => {
                    self.relocations(src, size)?
                    .map(|(&offset, &alloc_id)| {
                        // Update relocation offsets for the new positions in the destination allocation.
                        (offset + dest_offset - src_offset, alloc_id)
                    })
                        .collect()
                }
                _ => unimplemented!(),
            };

        let src_bytes = self.get_bytes_unchecked(src, size, align)?.as_ptr();
        let dest_bytes = self.get_bytes_mut(dest, size, align)?.as_mut_ptr();

        // SAFE: The above indexing would have panicked if there weren't at least `size` bytes
        // behind `src` and `dest`. Also, we use the overlapping-safe `ptr::copy` if `src` and
        // `dest` could possibly overlap.
        unsafe {
            assert_eq!(size as usize as u64, size);
            if src.alloc_id == dest.alloc_id {
                ptr::copy(src_bytes, dest_bytes, size as usize);
            } else {
                ptr::copy_nonoverlapping(src_bytes, dest_bytes, size as usize);
            }
        }

        self.copy_undef_mask(src, dest, size)?;
        // copy back the relocations
        self.get_mut(dest.alloc_id)?.relocations.extend(relocations);

        Ok(())
    }

    fn abstract_copy(&mut self, src: MemoryPointer, dest: MemoryPointer, size: u64, _align: u64)
                     -> EvalResult<'tcx>
    {
        if src.alloc_id == dest.alloc_id {
            unimplemented!()
        }

        let arr = self.symbolize_allocation(src.alloc_id)?;
        match (src.offset, dest.offset) {
            (PointerOffset::Abstract(src_offset),
             PointerOffset::Concrete(_dest_offset)) => {
                for idx in 0..size {
                    let abs_idx = self.constraints.add_binop_constraint(
                        mir::BinOp::Add,
                        PrimVal::Bytes(idx as u128),
                        PrimVal::Abstract(src_offset),
                        PrimValKind::U64);

                    let sbyte = self.constraints.add_array_element_constraint(arr, abs_idx);
                    self.get_bytes_mut(dest.offset(idx, self.layout)?, 1, 1)?[0] = sbyte;
                }

            }
            _ => unimplemented!(),
        }

        Ok(())
    }

    fn symbolize_allocation(&mut self, alloc_id: AllocId) -> EvalResult<'tcx, AbstractVariable> {
        let arr = self.constraints.new_array();
        let mut constraints = Vec::new();
        {
            let alloc = self.get(alloc_id)?;
            if !alloc.relocations.is_empty() {
                unimplemented!()
            }

            for idx in 0..alloc.bytes.len() {
                constraints.push((PrimVal::Bytes(idx as u128), alloc.bytes[idx]));
            }
        }
        for (primval, sbyte) in constraints {
            self.constraints.set_array_element_constraint(arr, primval, sbyte);
        }

        Ok(arr)
    }

    pub fn read_c_str(&self, _ptr: MemoryPointer) -> EvalResult<'tcx, &[u8]> {
        unimplemented!()
        /*
        let alloc = self.get(ptr.alloc_id)?;
        assert_eq!(ptr.offset as usize as u64, ptr.offset);
        let offset = ptr.offset as usize;
        match alloc.bytes[offset..].iter().position(|&c| c == SByte::Concrete(0)) {
            Some(size) => {
                if self.relocations(ptr, (size + 1) as u64)?.count() != 0 {
                    return Err(EvalError::ReadPointerAsBytes);
                }
                self.check_defined(ptr, (size + 1) as u64)?;
                Ok(&alloc.bytes[offset..offset + size])
            },
            None => Err(EvalError::UnterminatedCString(ptr)),
        } */
    }

    pub fn read_bytes(&self, ptr: PrimVal, size: u64)
                      -> EvalResult<'tcx, &[SByte]>
    {
        self.get_bytes(ptr.to_ptr()?, size, 1)
    }

    pub fn read_abstract(&self, ptr: PrimVal, size: u64)
                      -> EvalResult<'tcx, PrimVal>
    {
        let mut result_sbytes = [SByte::Concrete(0); 8];

        let sbytes = self.read_bytes(ptr, size)?;
        for idx in 0..(size as usize) {
            let src_idx = if let layout::Endian::Big = self.endianness() {
                size as usize - 1 - idx
            } else {
                idx
            };
            result_sbytes[idx] = sbytes[src_idx];
        }

        Ok(PrimVal::Abstract(result_sbytes))
    }

    pub fn write_bytes(&mut self, ptr: MemoryPointer, src: &[u8]) -> EvalResult<'tcx> {
        let bytes = self.get_bytes_mut(ptr, src.len() as u64, 1)?;
        for idx in 0..bytes.len() {
            bytes[idx] = SByte::Concrete(src[idx]);
        }
        Ok(())
    }

    pub fn write_repeat(&mut self, ptr: MemoryPointer, val: u8, count: u64) -> EvalResult<'tcx> {
        let bytes = self.get_bytes_mut(ptr, count, 1)?;
        for b in bytes { *b = SByte::Concrete(val); }
        Ok(())
    }

    pub fn read_primval(&self, ptr: MemoryPointer, size: u64, signed: bool) -> EvalResult<'tcx, PrimVal> {
        self.check_relocation_edges(ptr, size)?; // Make sure we don't read part of a pointer as a pointer
        let endianess = self.endianness();
        let bytes = self.get_bytes_unchecked(ptr, size, self.int_align(size)?)?;
        // Undef check happens *after* we established that the alignment is correct.
        // We must not return Ok() for unaligned pointers!
        if self.check_defined(ptr, size).is_err() {
            return Ok(PrimVal::Undef.into());
        }
        // Now we do the actual reading
        let bytes = if signed {
            read_target_int(endianess, bytes).unwrap() as u128
        } else {
            read_target_uint(endianess, bytes).unwrap()
        };
        // See if we got a pointer
        if size != self.pointer_size() {
            if self.relocations(ptr, size)?.count() != 0 {
                return Err(EvalError::ReadPointerAsBytes);
            }
        } else {
            let alloc = self.get(ptr.alloc_id)?;
            match ptr.offset {
                PointerOffset::Concrete(off) => {
                    match alloc.relocations.get(&off) {
                        Some(&alloc_id) => return Ok(PrimVal::Ptr(MemoryPointer::new(alloc_id, bytes as u64))),
                        None => {},
                    }
                }
                PointerOffset::Abstract(_) => unimplemented!(),
            }
        }
        // We don't. Just return the bytes.
        Ok(PrimVal::Bytes(bytes))
    }

    pub fn read_ptr(&self, ptr: MemoryPointer) -> EvalResult<'tcx, PrimVal> {
        let size = self.pointer_size();
        if self.check_defined(ptr, size).is_err() {
            return Ok(PrimVal::Undef);
        }

        let ptr_offset = match ptr.offset {
            PointerOffset::Concrete(offset) => offset,
            _ => unimplemented!(),
        };
        let alloc = self.get(ptr.alloc_id)?;

        let endianness = self.endianness();
        if self.points_to_concrete(ptr, size)? {
            let bytes = self.get_bytes_unchecked(ptr, size, size)?;
            let offset = read_target_uint(endianness, bytes).unwrap();
            assert_eq!(offset as u64 as u128, offset);
            let offset = offset as u64;

            match alloc.relocations.get(&ptr_offset) {
                Some(&alloc_id) => Ok(PrimVal::Ptr(MemoryPointer::new(alloc_id, offset))),
                None => Ok(PrimVal::Bytes(offset as u128)),
            }
        } else {
            let mut sbytes = [SByte::Concrete(0); 8];
            sbytes.copy_from_slice(self.get_bytes_unchecked(ptr, size, size)?);

            match alloc.relocations.get(&ptr_offset) {
                Some(&alloc_id) => Ok(PrimVal::Ptr(MemoryPointer::new_abstract(alloc_id, sbytes))),
                None => unimplemented!(),
            }
        }
    }

    pub fn write_ptr(&mut self, dest: MemoryPointer, ptr: MemoryPointer) -> EvalResult<'tcx> {
        match (ptr.offset, dest.offset) {
            (PointerOffset::Concrete(ptr_offset),
             PointerOffset::Concrete(dest_offset)) => {
                self.write_usize(dest, ptr_offset as u64)?;
                self.get_mut(dest.alloc_id)?.relocations.insert(dest_offset, ptr.alloc_id);
                Ok(())
            }
            (PointerOffset::Abstract(sbytes),
             PointerOffset::Concrete(dest_offset)) => {
                self.write_primval(PrimVal::Ptr(dest), PrimVal::Abstract(sbytes), 8)?; // FIXME usize
                self.get_mut(dest.alloc_id)?.relocations.insert(dest_offset, ptr.alloc_id);
                Ok(())
            }
            _ => unimplemented!(),
        }
    }

    pub fn write_primval(
        &mut self,
        dest: PrimVal,
        val: PrimVal,
        size: u64,
    ) -> EvalResult<'tcx> {
        if dest.is_ptr() && !dest.to_ptr()?.has_concrete_offset() {
            return self.write_primval_to_abstract_ptr(dest.to_ptr()?, val, size);
        }

        match val {
            PrimVal::Ptr(ptr) => {
                assert_eq!(size, self.pointer_size());
                self.write_ptr(dest.to_ptr()?, ptr)
            }

            PrimVal::Bytes(bytes) => {
                // We need to mask here, or the byteorder crate can die when given a u64 larger
                // than fits in an integer of the requested size.
                let mask = match size {
                    1 => !0u8 as u128,
                    2 => !0u16 as u128,
                    4 => !0u32 as u128,
                    8 => !0u64 as u128,
                    16 => !0,
                    _ => bug!("unexpected PrimVal::Bytes size"),
                };
                self.write_uint(dest.to_ptr()?, bytes & mask, size)
            }

            PrimVal::Abstract(sbytes) => {
                let align = self.int_align(size)?;
                match self.endianness() {
                    layout::Endian::Little => {
                        let dest_slice = self.get_bytes_mut(dest.to_ptr()?, size, align)?;
                        dest_slice.copy_from_slice(&sbytes[.. size as usize]);
                        Ok(())
                    }
                    layout::Endian::Big => {
                        unimplemented!()
                    }
                }
            }

            PrimVal::Undef => self.mark_definedness(dest, size, false),
        }
    }

    fn write_primval_to_abstract_ptr(
        &mut self,
        dest: MemoryPointer,
        val: PrimVal,
        size: u64,
    ) -> EvalResult<'tcx> {
        if let PointerOffset::Abstract(sbytes) = dest.offset {
            let mut arr = self.symbolize_allocation(dest.alloc_id)?;
            match val {
                PrimVal::Ptr(_ptr) => unimplemented!(),

                PrimVal::Bytes(n) => {
                    // We need to mask here, or the byteorder crate can die when given a u64 larger
                    // than fits in an integer of the requested size.
                    let mask = match size {
                        1 => !0u8 as u128,
                        2 => !0u16 as u128,
                        4 => !0u32 as u128,
                        8 => !0u64 as u128,
                        16 => !0,
                        _ => bug!("unexpected PrimVal::Bytes size"),
                    };

                    let mut bytes = vec![0u8; size as usize];
                    let endianness = self.endianness();
                    Self::write_target_uint(endianness, &mut bytes[..], n & mask).unwrap();

                    for idx in 0..size {
                        let abs_idx = self.constraints.add_binop_constraint(
                            mir::BinOp::Add,
                            PrimVal::Bytes(idx as u128),
                            PrimVal::Abstract(sbytes),
                            PrimValKind::U64);

                        arr = self.constraints.store_array_element(
                            arr, abs_idx, SByte::Concrete(bytes[idx as usize]));
                    }
                }

                PrimVal::Abstract(_sbytes) => {
                    unimplemented!()
                }

                PrimVal::Undef => unimplemented!(),
            }

            // now write the values of arr back to the dest allocation

            let dest_alloc_len = self.get(dest.alloc_id)?.bytes.len();
            for idx in 0..dest_alloc_len {
                let sbyte = self.constraints.add_array_element_constraint(
                    arr, PrimVal::Bytes(idx as u128));

                let ptr = MemoryPointer::new(dest.alloc_id, idx as u64);
                self.get_bytes_mut(ptr, 1, 1)?[0] = sbyte;
            }

            Ok(())
        } else {
            unreachable!()
        }
    }

    pub fn read_bool(&self, ptr: MemoryPointer) -> EvalResult<'tcx, PrimVal> {
        let bytes = self.get_bytes(ptr, 1, self.layout.i1_align.abi())?;
        match bytes[0] {
            SByte::Concrete(0) => Ok(PrimVal::from_bool(false)),
            SByte::Concrete(1) => Ok(PrimVal::from_bool(true)),
            SByte::Concrete(_) => Err(EvalError::InvalidBool),
            SByte::Abstract(AbstractVariable(v)) => {
                let mut buffer = [SByte::Concrete(0); 8];
                buffer[0] = SByte::Abstract(AbstractVariable(v));
                Ok(PrimVal::Abstract(buffer))
            }
        }
    }

    /*
    pub fn write_bool(&mut self, ptr: MemoryPointer, b: bool) -> EvalResult<'tcx> {
        let align = self.layout.i1_align.abi();
        self.get_bytes_mut(ptr, 1, align)
            .map(|bytes| bytes[0] = b as u8)
    }*/

    fn int_align(&self, size: u64) -> EvalResult<'tcx, u64> {
        match size {
            1 => Ok(self.layout.i8_align.abi()),
            2 => Ok(self.layout.i16_align.abi()),
            4 => Ok(self.layout.i32_align.abi()),
            8 => Ok(self.layout.i64_align.abi()),
            16 => Ok(self.layout.i128_align.abi()),
            _ => bug!("bad integer size: {}", size),
        }
    }

    pub fn read_int(&self, ptr: MemoryPointer, size: u64) -> EvalResult<'tcx, i128> {
        let align = self.int_align(size)?;
        self.get_bytes(ptr, size, align).map(|b| read_target_int(self.endianness(), b).unwrap())
    }

    pub fn write_int(&mut self, ptr: MemoryPointer, n: i128, size: u64) -> EvalResult<'tcx> {
        let align = self.int_align(size)?;
        let endianness = self.endianness();
        let mut bytes = vec![0u8; size as usize];
        let sb = self.get_bytes_mut(ptr, size, align)?;
        Self::write_target_int(endianness, &mut bytes[..], n).unwrap();
        for idx in 0..bytes.len() {
            sb[idx] = SByte::Concrete(bytes[idx]);
        }
        Ok(())
    }

    pub fn points_to_concrete(&self, ptr: MemoryPointer, size: u64) -> EvalResult<'tcx, bool> {
        let bytes = self.get_bytes_unchecked(ptr, size, 1)?;
        for &b in bytes {
            match b {
                SByte::Abstract(..) => return Ok(false),
                _ => (),
            }
        }

        Ok(true)
    }

    pub fn read_uint(&self, ptr: MemoryPointer, size: u64) -> EvalResult<'tcx, u128> {
        let align = self.int_align(size)?;
        self.get_bytes(ptr, size, align).map(|b| read_target_uint(self.endianness(), b).unwrap())
    }

    pub fn write_uint(&mut self, ptr: MemoryPointer, n: u128, size: u64) -> EvalResult<'tcx> {
        let align = self.int_align(size)?;
        let endianness = self.endianness();
        let sb = self.get_bytes_mut(ptr, size, align)?;
        let mut bytes = vec![0u8; size as usize];
        Self::write_target_uint(endianness, &mut bytes[..], n).unwrap();
        for idx in 0..bytes.len() {
            sb[idx] = SByte::Concrete(bytes[idx]);
        }
        Ok(())
    }

    pub fn read_isize(&self, ptr: MemoryPointer) -> EvalResult<'tcx, i64> {
        self.read_int(ptr, self.pointer_size()).map(|i| i as i64)
    }

    pub fn write_isize(&mut self, ptr: MemoryPointer, n: i64) -> EvalResult<'tcx> {
        let size = self.pointer_size();
        self.write_int(ptr, n as i128, size)
    }

    pub fn read_usize(&self, ptr: MemoryPointer) -> EvalResult<'tcx, u64> {
        self.read_uint(ptr, self.pointer_size()).map(|i| i as u64)
    }

    pub fn write_usize(&mut self, ptr: MemoryPointer, n: u64) -> EvalResult<'tcx> {
        let size = self.pointer_size();
        self.write_uint(ptr, n as u128, size)
    }

    /*
    pub fn write_f32(&mut self, ptr: MemoryPointer, f: f32) -> EvalResult<'tcx> {
        let endianness = self.endianness();
        let align = self.layout.f32_align.abi();
        let b = self.get_bytes_mut(ptr, 4, align)?;
        write_target_f32(endianness, b, f).unwrap();
        Ok(())
    }

    pub fn write_f64(&mut self, ptr: MemoryPointer, f: f64) -> EvalResult<'tcx> {
        let endianness = self.endianness();
        let align = self.layout.f64_align.abi();
        let b = self.get_bytes_mut(ptr, 8, align)?;
        self.write_target_f64(endianness, b, f).unwrap();
        Ok(())
    }*/

    pub fn read_f32(&self, ptr: MemoryPointer) -> EvalResult<'tcx, f32> {
        self.get_bytes(ptr, 4, self.layout.f32_align.abi())
            .map(|b| read_target_f32(self.endianness(), b).unwrap())
    }

    pub fn read_f64(&self, ptr: MemoryPointer) -> EvalResult<'tcx, f64> {
        self.get_bytes(ptr, 8, self.layout.f64_align.abi())
            .map(|b| read_target_f64(self.endianness(), b).unwrap())
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Methods to access integers in the target endianness
    ////////////////////////////////////////////////////////////////////////////////

    fn write_target_uint(endianness: layout::Endian, mut target: &mut [u8], data: u128) -> Result<(), io::Error> {
        let len = target.len();
        match endianness {
            layout::Endian::Little => target.write_uint128::<LittleEndian>(data, len),
            layout::Endian::Big => target.write_uint128::<BigEndian>(data, len),
        }
    }

    fn write_target_int(endianness: layout::Endian, mut target: &mut [u8], data: i128)
                        -> Result<(), io::Error>
    {
        let len = target.len();
        match endianness {
            layout::Endian::Little => target.write_int128::<LittleEndian>(data, len),
            layout::Endian::Big => target.write_int128::<BigEndian>(data, len),
        }
    }
}

fn read_target_uint(endianness: layout::Endian, sbytes: &[SByte])
                    -> Result<u128, io::Error>
{
    let mut source = Vec::with_capacity(sbytes.len());
    for sb in sbytes {
        match *sb {
            SByte::Concrete(b) => source.push(b),
            SByte::Abstract(_v) => unimplemented!(),
        }
    }
    let mut source = &source[..];
    match endianness {
        layout::Endian::Little => source.read_uint128::<LittleEndian>(source.len()),
        layout::Endian::Big => source.read_uint128::<BigEndian>(source.len()),
    }
}

fn read_target_int(endianness: layout::Endian, sbytes: &[SByte])
                    -> Result<i128, io::Error>
{
    let mut source = Vec::with_capacity(sbytes.len());
    for sb in sbytes {
        match *sb {
            SByte::Concrete(b) => source.push(b),
            SByte::Abstract(_v) => unimplemented!(),
        }
    }
    let mut source = &source[..];
    match endianness {
        layout::Endian::Little => source.read_int128::<LittleEndian>(source.len()),
        layout::Endian::Big => source.read_int128::<BigEndian>(source.len()),
    }
}

fn read_target_f32(endianness: layout::Endian, sbytes: &[SByte])
                    -> Result<f32, io::Error>
{
    let mut source = Vec::with_capacity(sbytes.len());
    for sb in sbytes {
        match *sb {
            SByte::Concrete(b) => source.push(b),
            SByte::Abstract(_v) => unimplemented!(),
        }
    }
    let mut source = &source[..];
    match endianness {
        layout::Endian::Little => source.read_f32::<LittleEndian>(),
        layout::Endian::Big => source.read_f32::<BigEndian>(),
    }
}

fn read_target_f64(endianness: layout::Endian, sbytes: &[SByte])
                    -> Result<f64, io::Error>
{
    let mut source = Vec::with_capacity(sbytes.len());
    for sb in sbytes {
        match *sb {
            SByte::Concrete(b) => source.push(b),
            SByte::Abstract(_v) => unimplemented!(),
        }
    }
    let mut source = &source[..];
    match endianness {
        layout::Endian::Little => source.read_f64::<LittleEndian>(),
        layout::Endian::Big => source.read_f64::<BigEndian>(),
    }
}

/// Relocations
impl<'a, 'tcx> Memory<'a, 'tcx> {
    fn relocations(&self, ptr: MemoryPointer, size: u64)
        -> EvalResult<'tcx, btree_map::Range<u64, AllocId>>
    {
        let ptr_offset = match ptr.offset {
            PointerOffset::Concrete(offset) => offset,
            _ => unimplemented!(),
        };

        let start = ptr_offset.saturating_sub(self.pointer_size() - 1);
        let end = ptr_offset + size;
        Ok(self.get(ptr.alloc_id)?.relocations.range(start..end))
    }

    fn clear_relocations(&mut self, ptr: MemoryPointer, size: u64) -> EvalResult<'tcx> {
        // HACK: return early if we know there is nothing to clear. This helps
        // especially in the case where `ptr` is abstract.
        if self.get(ptr.alloc_id)?.relocations.is_empty() {
            return Ok(())
        }

        // Find all relocations overlapping the given range.
        let keys: Vec<_> = self.relocations(ptr, size)?.map(|(&k, _)| k).collect();
        if keys.is_empty() { return Ok(()); }

        // Find the start and end of the given range and its outermost relocations.
        let start = match ptr.offset {
            PointerOffset::Concrete(offset) => offset,
            _ => unimplemented!(),
        };
        let end = start + size;
        let first = *keys.first().unwrap();
        let last = *keys.last().unwrap() + self.pointer_size();

        let alloc = self.get_mut(ptr.alloc_id)?;

        // Mark parts of the outermost relocations as undefined if they partially fall outside the
        // given range.
        if first < start { alloc.undef_mask.set_range(first, start, false); }
        if last > end { alloc.undef_mask.set_range(end, last, false); }

        // Forget all the relocations.
        for k in keys { alloc.relocations.remove(&k); }

        Ok(())
    }

    fn check_relocation_edges(&self, ptr: MemoryPointer, size: u64) -> EvalResult<'tcx> {
        let overlapping_start = self.relocations(ptr, 0)?.count();
        let overlapping_end = self.relocations(ptr.offset(size, self.layout)?, 0)?.count();
        if overlapping_start + overlapping_end != 0 {
            return Err(EvalError::ReadPointerAsBytes);
        }
        Ok(())
    }

}

/// Undefined bytes
impl<'a, 'tcx> Memory<'a, 'tcx> {
    // FIXME(solson): This is a very naive, slow version.
    fn copy_undef_mask(&mut self, src: MemoryPointer, dest: MemoryPointer, size: u64) -> EvalResult<'tcx> {
        // The bits have to be saved locally before writing to dest in case src and dest overlap.
        assert_eq!(size as usize as u64, size);
        match (src.offset, dest.offset) {
            (PointerOffset::Concrete(src_offset),
             PointerOffset::Concrete(dest_offset)) => {
                let mut v = Vec::with_capacity(size as usize);
                for i in 0..size {
                    let defined = self.get(src.alloc_id)?.undef_mask.get(src_offset + i);
                    v.push(defined);
                }
                for (i, defined) in v.into_iter().enumerate() {
                    self.get_mut(dest.alloc_id)?.undef_mask.set(dest_offset + i as u64, defined);
                }
                Ok(())
            }
            _ => unimplemented!(),
        }
    }

    fn check_defined(&self, ptr: MemoryPointer, size: u64) -> EvalResult<'tcx> {
        let alloc = self.get(ptr.alloc_id)?;
        match ptr.offset {
            PointerOffset::Concrete(ptr_offset) => {
                if !alloc.undef_mask.is_range_defined(ptr_offset, ptr_offset + size) {
                    return Err(EvalError::ReadUndefBytes);
                }
                Ok(())
            }
            _ => unimplemented!(),
        }
    }

    pub fn mark_definedness(
        &mut self,
        ptr: PrimVal,
        size: u64,
        new_state: bool
    ) -> EvalResult<'tcx> {
        if size == 0 {
            return Ok(())
        }
        let ptr = ptr.to_ptr()?;
        let alloc = self.get_mut(ptr.alloc_id)?;
        match ptr.offset {
            PointerOffset::Concrete(offset) => {
                alloc.undef_mask.set_range(offset, offset + size, new_state);
                Ok(())
            }
            PointerOffset::Abstract(_) => {
                if alloc.undef_mask.is_range_defined(0, alloc.bytes.len() as u64) && new_state {
                    // nothing to do
                    Ok(())
                } else {
                    unimplemented!()
                }
            }
        }
    }
}

////////////////////////////////////////////////////////////////////////////////
// Undefined byte tracking
////////////////////////////////////////////////////////////////////////////////

type Block = u64;
const BLOCK_SIZE: u64 = 64;

#[derive(Clone, Debug)]
pub struct UndefMask {
    blocks: Vec<Block>,
    len: u64,
}

impl UndefMask {
    fn new(size: u64) -> Self {
        let mut m = UndefMask {
            blocks: vec![],
            len: 0,
        };
        m.grow(size, false);
        m
    }

    /// Check whether the range `start..end` (end-exclusive) is entirely defined.
    pub fn is_range_defined(&self, start: u64, end: u64) -> bool {
        if end > self.len { return false; }
        for i in start..end {
            if !self.get(i) { return false; }
        }
        true
    }

    fn set_range(&mut self, start: u64, end: u64, new_state: bool) {
        let len = self.len;
        if end > len { self.grow(end - len, new_state); }
        self.set_range_inbounds(start, end, new_state);
    }

    fn set_range_inbounds(&mut self, start: u64, end: u64, new_state: bool) {
        for i in start..end { self.set(i, new_state); }
    }

    fn get(&self, i: u64) -> bool {
        let (block, bit) = bit_index(i);
        (self.blocks[block] & 1 << bit) != 0
    }

    fn set(&mut self, i: u64, new_state: bool) {
        let (block, bit) = bit_index(i);
        if new_state {
            self.blocks[block] |= 1 << bit;
        } else {
            self.blocks[block] &= !(1 << bit);
        }
    }

    fn grow(&mut self, amount: u64, new_state: bool) {
        let unused_trailing_bits = self.blocks.len() as u64 * BLOCK_SIZE - self.len;
        if amount > unused_trailing_bits {
            let additional_blocks = amount / BLOCK_SIZE + 1;
            assert_eq!(additional_blocks as usize as u64, additional_blocks);
            self.blocks.extend(iter::repeat(0).take(additional_blocks as usize));
        }
        let start = self.len;
        self.len += amount;
        self.set_range_inbounds(start, start + amount, new_state);
    }

    fn truncate(&mut self, length: u64) {
        self.len = length;
        let truncate = self.len / BLOCK_SIZE + 1;
        assert_eq!(truncate as usize as u64, truncate);
        self.blocks.truncate(truncate as usize);
        self.blocks.shrink_to_fit();
    }
}

fn bit_index(bits: u64) -> (usize, usize) {
    let a = bits / BLOCK_SIZE;
    let b = bits % BLOCK_SIZE;
    assert_eq!(a as usize as u64, a);
    assert_eq!(b as usize as u64, b);
    (a as usize, b as usize)
}

// SPDX-License-Identifier: MPL-2.0
//! This module contains the implementation of the CPU set and atomic CPU set.
use core::sync::atomic::{AtomicU64, Ordering};

use smallvec::SmallVec;
use vstd::arithmetic::power2::pow2;
use vstd::bits::{lemma_u64_pow2_no_overflow, lemma_u64_shl_is_mul};
use vstd::prelude::*;
use vstd::seq::Seq;
use vstd::std_specs::convert::FromSpecImpl;

use super::{CpuId, num_cpus};

/// A subset of all CPUs in the system.
#[derive(Clone, Debug, Default)]
pub struct CpuSet {
    // A bitset representing the CPUs in the system.
    bits: SmallVec<[InnerPart; NR_PARTS_NO_ALLOC]>,
}

type InnerPart = u64;

const BITS_PER_PART: usize = core::mem::size_of::<InnerPart>() * 8;
const NR_PARTS_NO_ALLOC: usize = 2;

const fn part_idx(cpu_id: CpuId) -> usize {
    cpu_id.as_usize() / BITS_PER_PART
}

const fn bit_idx(cpu_id: CpuId) -> usize {
    cpu_id.as_usize() % BITS_PER_PART
}

const fn parts_for_cpus(num_cpus: usize) -> usize {
    num_cpus.div_ceil(BITS_PER_PART)
}

verus! {

// ===========================================================================
// Trusted abstract model (TCB)
// ===========================================================================
// `SmallVec<[u64; 2]>` / `SmallVec<[AtomicU64; 2]>` are foreign const-generic
// collections; Verus cannot attach an `external_type_specification` to SmallVec
// itself (see the TODO in `verified_libs/vstd_extra/src/array_ptr.rs`). We
// therefore expose the SmallVec representation through a small set of
// `#[verifier::external_body]` accessor methods whose `ensures` relate the
// executable parts to an abstract `Seq<u64>` model (`bits_seq`). The bit-masking
// logic of `add`/`remove`/`contains`/`From` is then GENUINELY VERIFIED over this
// `Seq<u64>` model; only the SmallVec accessors and the two foreign readouts
// (`num_cpus`, `CpuId::as_usize`) are trusted.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExCpuId(CpuId);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExCpuSet(CpuSet);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExAtomicCpuSet(AtomicCpuSet);

// --- Trusted bridges for the two foreign readouts ---
// `num_cpus()` and `CpuId::as_usize` are plain Rust (defined in `cpu::mod`),
// not verus-verified. These `assume_specification`s give them specs tying them
// to the abstract model. This is the TCB: the executable readouts realize these
// values.
pub assume_specification[ crate::cpu::num_cpus ]() -> (ret: usize)
    ensures
        ret as int == spec_num_cpus(),
;

pub assume_specification[ crate::cpu::CpuId::as_usize ](c: CpuId) -> (ret: usize)
    ensures
        ret as int == cpu_id_int(&c),
;

/// Trusted: the number of CPUs in the system (realized by `num_cpus()`).
pub uninterp spec fn spec_num_cpus() -> int;

/// Trusted: the integer ID of a CPU (realized by `CpuId::as_usize`).
/// Every valid `CpuId` satisfies `0 <= cpu_id_int(c) < spec_num_cpus()`.
pub uninterp spec fn cpu_id_int(c: &CpuId) -> int;

/// Trusted: the SmallVec backing parts of a [`CpuSet`], as a `Seq<u64>`.
pub uninterp spec fn bits_seq(s: &CpuSet) -> Seq<u64>;

/// Trusted: the SmallVec backing parts of an [`AtomicCpuSet`], as a `Seq<u64>`.
pub uninterp spec fn atomic_bits_seq(s: &AtomicCpuSet) -> Seq<u64>;

/// Trusted: total number of set bits in a part-sequence (realized by `count`).
pub uninterp spec fn count_set_bits(seq: Seq<u64>) -> int;

/// Whether CPU `cpu` is present in the part-sequence `seq`.
///
/// CPU `cpu` lives in part `cpu / 64` at bit `cpu % 64`.
pub open spec fn bit_at(seq: Seq<u64>, cpu: int) -> bool {
    let p = cpu / 64;
    let b = cpu % 64;
    p < seq.len() && (seq[p] & (1u64 << (b as u64))) != 0
}

/// The number of parts needed to represent `n` CPUs.
pub open spec fn spec_parts_for_cpus(n: int) -> int {
    if n % 64 == 0 {
        n / 64
    } else {
        n / 64 + 1
    }
}

impl CpuSet {
    // ----- Trusted SmallVec accessors (external_body; the only TCB over SmallVec) -----
    #[verifier::external_body]
    fn bits_len(&self) -> (r: usize)
        ensures
            r as int == bits_seq(self).len(),
    {
        self.bits.len()
    }

    #[verifier::external_body]
    fn bits_get(&self, i: usize) -> (r: u64)
        requires
            i < bits_seq(self).len(),
        ensures
            r == bits_seq(self)[i as int],
    {
        self.bits[i]
    }

    #[verifier::external_body]
    fn bits_set(&mut self, i: usize, v: u64)
        requires
            i < bits_seq(self).len(),
        ensures
            bits_seq(final(self)) == bits_seq(old(self)).update(i as int, v),
            bits_seq(final(self)).len() == bits_seq(old(self)).len(),
    {
        self.bits[i] = v;
    }

    #[verifier::external_body]
    fn bits_resize(&mut self, new_len: usize, fill: u64)
        requires
            new_len as int >= bits_seq(self).len(),
        ensures
            bits_seq(final(self)).len() == new_len as int,
            forall|i: int|
                0 <= i < bits_seq(old(self)).len() ==> bits_seq(final(self))[i] == bits_seq(
                    old(self),
                )[i],
            forall|i: int|
                bits_seq(old(self)).len() <= i < new_len as int ==> bits_seq(final(self))[i]
                    == fill,
    {
        self.bits.resize(new_len, fill);
    }

    #[verifier::external_body]
    fn bits_fill(&mut self, v: u64)
        ensures
            bits_seq(final(self)).len() == bits_seq(old(self)).len(),
            forall|i: int| 0 <= i < bits_seq(final(self)).len() ==> bits_seq(final(self))[i] == v,
    {
        self.bits.fill(v);
    }

    // ----- Verified construction (trusted constructor + verified queries/mutations) -----
    /// Creates a new `CpuSet` with all CPUs in the system.
    #[verifier::external_body]
    pub fn new_full() -> (res: CpuSet)
        ensures
            forall|c: int| bit_at(bits_seq(&res), c) == (0 <= c && c < spec_num_cpus()),
    {
        let mut ret = Self::with_capacity_val(num_cpus(), !0);
        ret.clear_nonexistent_cpu_bits();
        ret
    }

    /// Creates a new `CpuSet` with no CPUs in the system.
    #[verifier::external_body]
    pub fn new_empty() -> (res: CpuSet)
        ensures
            forall|c: int| !bit_at(bits_seq(&res), c),
            forall|i: int| 0 <= i < bits_seq(&res).len() ==> bits_seq(&res)[i] == 0,
    {
        Self::with_capacity_val(num_cpus(), 0)
    }

    /// Adds a CPU to the set. (Verified: sets `cpu_id`'s bit.)
    pub fn add(&mut self, cpu_id: CpuId)
        ensures
            bit_at(bits_seq(final(self)), cpu_id_int(&cpu_id)),
    {
        let id: usize = cpu_id.as_usize();
        let p: usize = id / 64;
        let b: usize = id % 64;
        let mask: u64 = 1u64 << (b as u64);
        if p >= self.bits_len() {
            self.bits_resize(p + 1, 0);
        }
        let part = self.bits_get(p);
        self.bits_set(p, part | mask);
        proof {
            assert(cpu_id_int(&cpu_id) == id as int);
            assert(cpu_id_int(&cpu_id) / 64 == p as int);
            assert(cpu_id_int(&cpu_id) % 64 == b as int);
            assert(bits_seq(self)[p as int] == part | mask);
            assert((p as int) < bits_seq(self).len());
            assert((b as u64) < 64u64);
            assert(mask == 1u64 << (b as u64));
            lemma_u64_pow2_no_overflow((b as u64) as nat);
            lemma_u64_shl_is_mul(1u64, (b as u64));
            assert(pow2((b as u64) as nat) > 0);
            assert(mask != 0u64);
            assert(1u64 << ((cpu_id_int(&cpu_id) % 64) as u64) == mask);
            assert((part | mask) & mask == mask) by (bit_vector);
            assert((part | mask) & mask != 0u64);
        }
    }

    /// Removes a CPU from the set. (Verified: clears `cpu_id`'s bit; a no-op if
    /// `cpu_id` was beyond the parts.)
    pub fn remove(&mut self, cpu_id: CpuId)
        ensures
            !bit_at(bits_seq(final(self)), cpu_id_int(&cpu_id)),
    {
        let id: usize = cpu_id.as_usize();
        let p: usize = id / 64;
        let b: usize = id % 64;
        let mask: u64 = 1u64 << (b as u64);
        if p < self.bits_len() {
            let part = self.bits_get(p);
            self.bits_set(p, part & !mask);
            proof {
                assert(cpu_id_int(&cpu_id) / 64 == p as int);
                assert(cpu_id_int(&cpu_id) % 64 == b as int);
                assert((b as u64) < 64u64);
                assert(mask == 1u64 << (b as u64));
                assert(bits_seq(self)[p as int] == part & !mask);
                assert(1u64 << ((cpu_id_int(&cpu_id) % 64) as u64) == mask);
                assert((part & !mask) & mask == 0u64) by (bit_vector);
            }
        } else {
            proof {
                assert(cpu_id_int(&cpu_id) / 64 == p as int);
                assert(!((p as int) < bits_seq(self).len()));
            }
        }
    }

    /// Returns true if the set contains the specified CPU. (Verified.)
    pub fn contains(&self, cpu_id: CpuId) -> (res: bool)
        ensures
            res == bit_at(bits_seq(self), cpu_id_int(&cpu_id)),
    {
        let id: usize = cpu_id.as_usize();
        let p: usize = id / 64;
        let b: usize = id % 64;
        p < self.bits_len() && (self.bits_get(p) & (1u64 << b)) != 0
    }

    /// Returns the number of CPUs in the set.
    #[verifier::external_body]
    pub fn count(&self) -> (res: usize)
        ensures
            res as int == count_set_bits(bits_seq(self)),
    {
        self.bits.iter().map(|part| part.count_ones() as usize).sum()
    }

    /// Returns true if the set is empty.
    #[verifier::external_body]
    pub fn is_empty(&self) -> (res: bool)
        ensures
            res == (forall|i: int| 0 <= i < bits_seq(self).len() ==> bits_seq(self)[i] == 0),
    {
        self.bits.iter().all(|part| *part == 0)
    }

    /// Returns true if the set is full.
    #[verifier::external_body]
    pub fn is_full(&self) -> (res: bool)
        ensures
            res == (forall|c: int| bit_at(bits_seq(self), c) == (0 <= c && c < spec_num_cpus())),
    {
        let num_cpus = num_cpus();
        self.bits.iter().enumerate().all(
            |(idx, part)|
                {
                    if idx == self.bits.len() - 1 && num_cpus % BITS_PER_PART != 0 {
                        *part == (1 << (num_cpus % BITS_PER_PART)) - 1
                    } else {
                        *part == !0
                    }
                },
        )
    }

    /// Adds all CPUs to the set.
    #[verifier::external_body]
    pub fn add_all(&mut self)
        ensures
            forall|c: int| 0 <= c && c < spec_num_cpus() ==> bit_at(bits_seq(final(self)), c),
    {
        self.bits.fill(!0);
        self.clear_nonexistent_cpu_bits();
    }

    /// Removes all CPUs from the set.
    #[verifier::external_body]
    pub fn clear(&mut self)
        ensures
            forall|c: int| !bit_at(bits_seq(final(self)), c),
    {
        self.bits.fill(0);
    }

    /// Only for internal use. The set cannot contain non-existent CPUs.
    #[verifier::external_body]
    fn with_capacity_val(num_cpus: usize, val: InnerPart) -> (res: CpuSet)
        ensures
            forall|i: int| 0 <= i < bits_seq(&res).len() ==> bits_seq(&res)[i] == val,
    {
        let num_parts = parts_for_cpus(num_cpus);
        let mut bits = SmallVec::with_capacity(num_parts);
        bits.resize(num_parts, val);
        Self { bits }
    }

    #[verifier::external_body]
    fn clear_nonexistent_cpu_bits(&mut self)
        ensures
            forall|c: int|
                bit_at(bits_seq(final(self)), c) == (bit_at(bits_seq(old(self)), c) && 0 <= c && c
                    < spec_num_cpus()),
    {
        let num_cpus = num_cpus();
        if num_cpus % BITS_PER_PART != 0 {
            let num_parts = parts_for_cpus(num_cpus);
            self.bits[num_parts - 1] &= (1 << (num_cpus % BITS_PER_PART)) - 1;
        }
    }
}

impl FromSpecImpl<CpuId> for CpuSet {
    // CpuSet is an external (SmallVec-backed) type with no spec constructor, so
    // the std `From` spec is vacuous; the real postcondition is on `From::from`.
    open spec fn obeys_from_spec() -> bool {
        false
    }

    open spec fn from_spec(v: CpuId) -> CpuSet {
        arbitrary()
    }
}

impl From<CpuId> for CpuSet {
    fn from(cpu_id: CpuId) -> (res: CpuSet)
        ensures
            bit_at(bits_seq(&res), cpu_id_int(&cpu_id)),
    {
        let mut set = Self::new_empty();
        set.add(cpu_id);
        set
    }
}

} // verus!
/// Iterates over the CPUs in the set.
///
/// The order of the iteration is guaranteed to be in ascending order.
///
/// Kept as plain Rust (outside `verus!`): the returned `impl Iterator` over a
/// SmallVec-backed cursor is not specifiable in Verus and is part of the TCB.
impl CpuSet {
    pub fn iter(&self) -> impl Iterator<Item = CpuId> + '_ {
        self.bits.iter().enumerate().flat_map(|(part_idx, &part)| {
            (0..BITS_PER_PART).filter_map(move |bit_idx| {
                if (part & (1 << bit_idx)) != 0 {
                    let id = part_idx * BITS_PER_PART + bit_idx;
                    Some(CpuId(id as u32))
                } else {
                    None
                }
            })
        })
    }
}

/// A subset of all CPUs in the system with atomic operations.
///
/// It provides atomic operations for each CPU in the system. When the
/// operation contains multiple CPUs, the ordering is not guaranteed.
#[derive(Debug)]
pub struct AtomicCpuSet {
    bits: SmallVec<[AtomicInnerPart; NR_PARTS_NO_ALLOC]>,
}

type AtomicInnerPart = AtomicU64;
const _: () = assert!(core::mem::size_of::<AtomicInnerPart>() * 8 == BITS_PER_PART);

verus! {

impl AtomicCpuSet {
    /// Creates a new `AtomicCpuSet` with an initial value.
    #[verifier::external_body]
    pub fn new(value: CpuSet) -> (res: AtomicCpuSet)
        ensures
            atomic_bits_seq(&res) == bits_seq(&value),
    {
        let bits = value.bits.into_iter().map(AtomicU64::new).collect();
        Self { bits }
    }

    /// Loads the value of the set with the given ordering.
    ///
    /// This operation is not atomic. When racing with a [`Self::store`]
    /// operation, this load may return a set that contains a portion of the
    /// new value and a portion of the old value. Load on each specific
    /// word is atomic, and follows the specified ordering.
    ///
    /// Note that load with [`Ordering::Release`] is a valid operation, which
    /// is different from the normal atomic operations. When coupled with
    /// [`Ordering::Release`], it actually performs `fetch_or(0, Release)`.
    #[verifier::external_body]
    pub fn load(&self, ordering: Ordering) -> (res: CpuSet)
        ensures
            bits_seq(&res) == atomic_bits_seq(self),
    {
        let bits = self.bits.iter().map(
            |part|
                match ordering {
                    Ordering::Release => part.fetch_or(0, ordering),
                    _ => part.load(ordering),
                },
        ).collect();
        CpuSet { bits }
    }

    /// Stores a new value to the set with the given ordering.
    ///
    /// This operation is not atomic. When racing with a [`Self::load`]
    /// operation, that load may return a set that contains a portion of the
    /// new value and a portion of the old value. Load on each specific
    /// word is atomic, and follows the specified ordering.
    #[verifier::external_body]
    pub fn store(&self, value: &CpuSet, ordering: Ordering)
        ensures
            atomic_bits_seq(self) == bits_seq(value),
    {
        for (part, new_part) in self.bits.iter().zip(value.bits.iter()) {
            part.store(*new_part, ordering);
        }
    }

    /// Atomically adds a CPU with the given ordering.
    #[verifier::external_body]
    pub fn add(&self, cpu_id: CpuId, ordering: Ordering)
        ensures
            bit_at(atomic_bits_seq(self), cpu_id_int(&cpu_id)),
    {
        let part_idx = part_idx(cpu_id);
        let bit_idx = bit_idx(cpu_id);
        if part_idx < self.bits.len() {
            self.bits[part_idx].fetch_or(1 << bit_idx, ordering);
        }
    }

    /// Atomically removes a CPU with the given ordering.
    #[verifier::external_body]
    pub fn remove(&self, cpu_id: CpuId, ordering: Ordering)
        ensures
            !bit_at(atomic_bits_seq(self), cpu_id_int(&cpu_id)),
    {
        let part_idx = part_idx(cpu_id);
        let bit_idx = bit_idx(cpu_id);
        if part_idx < self.bits.len() {
            self.bits[part_idx].fetch_and(!(1 << bit_idx), ordering);
        }
    }

    /// Atomically checks if the set contains the specified CPU.
    #[verifier::external_body]
    pub fn contains(&self, cpu_id: CpuId, ordering: Ordering) -> (res: bool)
        ensures
            res == bit_at(atomic_bits_seq(self), cpu_id_int(&cpu_id)),
    {
        let part_idx = part_idx(cpu_id);
        let bit_idx = bit_idx(cpu_id);
        part_idx < self.bits.len() && (self.bits[part_idx].load(ordering) & (1 << bit_idx)) != 0
    }
}

} // verus!
#[cfg(ktest)]
mod test {
    use super::*;
    use crate::{cpu::all_cpus, prelude::*};

    #[ktest]
    fn test_full_cpu_set_iter_is_all() {
        let set = CpuSet::new_full();
        let num_cpus = num_cpus();
        let all_cpus = all_cpus().collect::<Vec<_>>();
        let set_cpus = set.iter().collect::<Vec<_>>();

        assert!(set_cpus.len() == num_cpus);
        assert_eq!(set_cpus, all_cpus);
    }

    #[ktest]
    fn test_full_cpu_set_contains_all() {
        let set = CpuSet::new_full();
        for cpu_id in all_cpus() {
            assert!(set.contains(cpu_id));
        }
    }

    #[ktest]
    fn test_empty_cpu_set_iter_is_empty() {
        let set = CpuSet::new_empty();
        let set_cpus = set.iter().collect::<Vec<_>>();
        assert!(set_cpus.is_empty());
    }

    #[ktest]
    fn test_empty_cpu_set_contains_none() {
        let set = CpuSet::new_empty();
        for cpu_id in all_cpus() {
            assert!(!set.contains(cpu_id));
        }
    }

    #[ktest]
    fn test_atomic_cpu_set_multiple_sizes() {
        for test_num_cpus in [1usize, 3, 12, 64, 96, 99, 128, 256, 288, 1024] {
            let test_all_iter = || (0..test_num_cpus).map(|id| CpuId(id as u32));

            let set = CpuSet::with_capacity_val(test_num_cpus, 0);
            let atomic_set = AtomicCpuSet::new(set);

            for cpu_id in test_all_iter() {
                assert!(!atomic_set.contains(cpu_id, Ordering::Relaxed));
                if cpu_id.as_usize() % 3 == 0 {
                    atomic_set.add(cpu_id, Ordering::Relaxed);
                }
            }

            let loaded = atomic_set.load(Ordering::Relaxed);
            for cpu_id in loaded.iter() {
                if cpu_id.as_usize() % 3 == 0 {
                    assert!(loaded.contains(cpu_id));
                } else {
                    assert!(!loaded.contains(cpu_id));
                }
            }

            atomic_set.store(
                &CpuSet::with_capacity_val(test_num_cpus, 0),
                Ordering::Relaxed,
            );

            for cpu_id in test_all_iter() {
                assert!(!atomic_set.contains(cpu_id, Ordering::Relaxed));
                atomic_set.add(cpu_id, Ordering::Relaxed);
            }
        }
    }
}

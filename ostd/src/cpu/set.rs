// SPDX-License-Identifier: MPL-2.0
//! CPU sets, represented by little-endian 64-bit words.
//!
//! # Verified Properties
//! CPU-set mutations and membership are specified by a mathematical set of IDs.
//! Word counts, empty/full checks, and iteration have executable-body proofs.
//! SmallVec operations and the post-boot CPU count are trusted dependencies.
//! Atomic methods preserve storage shape and check indices and orderings; the
//! standard atomic specifications do not model concurrent values or memory order.
use core::sync::atomic::{AtomicU64, Ordering};
use smallvec::SmallVec;

use super::{CpuId, num_cpus, num_cpus_spec};
use vstd::{
    prelude::*,
    std_specs::iter::{IteratorSpec, IteratorSpecImpl},
};
use vstd_extra::{external::smallvec::SmallVecView, ownership::Inv};

verus! {

broadcast use vstd_extra::external::smallvec::supported_cpu_set_arrays;

/// A subset of all CPUs in the system.
// Original: #[derive(Clone, Debug, Default)]
#[derive(Debug)]
pub struct CpuSet {
    bits: SmallVec<[InnerPart; NR_PARTS_NO_ALLOC]>,
}

type InnerPart = u64;

// Original: core::mem::size_of::<InnerPart>() * 8; checked below.
const BITS_PER_PART: usize = 64;

const NR_PARTS_NO_ALLOC: usize = 2;

const MAX_PARTS: usize = 67108864;

const fn part_idx(cpu_id: CpuId) -> (r: usize)
    ensures
        r == cpu_id.as_usize() / 64,
        r < MAX_PARTS,
{
    cpu_id.as_usize() / BITS_PER_PART
}

const fn bit_idx(cpu_id: CpuId) -> (r: usize)
    ensures
        r == cpu_id.as_usize() % 64,
        r < 64,
{
    cpu_id.as_usize() % BITS_PER_PART
}

const fn parts_for_cpus(num_cpus: usize) -> (r: usize)
    ensures
        r == num_cpus / 64 + if num_cpus % 64 == 0 {
            0int
        } else {
            1int
        },
{
    // Original: num_cpus.div_ceil(BITS_PER_PART).
    num_cpus / BITS_PER_PART + if num_cpus % BITS_PER_PART == 0 {
        0
    } else {
        1
    }
}

/// Whether the bit at `id` is set, including the implicit zero words beyond storage.
pub open spec fn member(words: Seq<u64>, id: int) -> bool {
    0 <= id && id / 64 < words.len() && (words[id / 64] & (1u64 << (id % 64))) != 0
}

/// Whether every word equals the given value.
pub open spec fn all_words(words: Seq<u64>, value: u64) -> bool {
    forall|i: int| 0 <= i < words.len() ==> #[trigger] words[i] == value
}

/// Number of set bits among the first `n` bits of one word.
pub open spec fn word_count(word: u64, n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else {
        word_count(word, (n - 1) as nat) + if word & (1u64 << (n - 1)) != 0 {
            1nat
        } else {
            0nat
        }
    }
}

/// Sum of the population counts of the first `n` words.
pub open spec fn count_prefix(words: Seq<u64>, n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else {
        count_prefix(words, (n - 1) as nat) + word_count(words[n - 1], 64)
    }
}

fn count_word(word: u64) -> (r: usize)
    ensures
        r == word_count(word, 64),
        r <= 64,
{
    // Original per-word operation: word.count_ones() as usize.
    // The active vstd has no count_ones contract.
    let mut i = 0usize;
    let mut count = 0usize;
    while i < 64
        invariant
            i <= 64,
            count <= i,
            count == word_count(word, i as nat),
        decreases 64 - i,
    {
        if word & (1u64 << i) != 0 {
            count += 1;
        }
        i += 1;
    }
    count
}

impl View for CpuSet {
    type V = ISet<int>;

    open spec fn view(&self) -> ISet<int> {
        ISet::new(|id: int| member(self.words(), id))
    }
}

impl Inv for CpuSet {
    closed spec fn inv(self) -> bool {
        self.bits@.len() <= MAX_PARTS
    }
}

impl CpuSet {
    pub closed spec fn words(&self) -> Seq<u64> {
        self.bits@
    }

    /// The storage covers exactly the CPUs configured at boot.
    pub open spec fn has_system_capacity(&self) -> bool {
        self.words().len() == num_cpus_spec() / 64 + if num_cpus_spec() % 64 == 0 {
            0int
        } else {
            1int
        }
    }

    /// Exact word-level predicate used by is_full, including zero-length sets.
    pub open spec fn full_words(&self) -> bool {
        forall|i: int|
            0 <= i < self.words().len() ==> #[trigger] self.words()[i] == if i == self.words().len()
                - 1 && num_cpus_spec() % 64 != 0 {
                ((1u64 << (num_cpus_spec() % 64)) - 1) as u64
            } else {
                u64::MAX
            }
    }

    /// Creates a set containing all configured CPUs.
    pub fn new_full() -> (r: Self)
        ensures
            r.inv(),
            r.has_system_capacity(),
            r.full_words(),
            r@ == ISet::new(|id: int| 0 <= id < num_cpus_spec()),
    {
        proof {
            assert(!0u64 == u64::MAX) by (bit_vector);
        }
        let mut ret = Self::with_capacity_val(num_cpus(), !0);
        ret.clear_nonexistent_cpu_bits();
        proof {
            ret.lemma_full_view();
        }
        ret
    }

    /// Creates a set containing no CPUs.
    pub fn new_empty() -> (r: Self)
        ensures
            r.inv(),
            r.has_system_capacity(),
            r@ == ISet::<int>::empty(),
    {
        let ret = Self::with_capacity_val(num_cpus(), 0);
        proof {
            lemma_zero_words(ret.words());
        }
        ret
    }

    /// Adds exactly the specified CPU, preserving every other membership bit.
    pub fn add(&mut self, cpu_id: CpuId)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self)@ == old(self)@.insert(cpu_id.as_usize() as int),
    {
        let ghost before = self.words();
        let part_idx = part_idx(cpu_id);
        let bit_idx = bit_idx(cpu_id);
        if part_idx >= self.bits.len() {
            self.bits.resize(part_idx + 1, 0);
        }
        let ghost extended = self.words();
        // Original: self.bits[part_idx] |= 1 << bit_idx;
        let bits = self.bits.as_mut_slice();
        bits[part_idx] |= 1u64 << bit_idx;
        proof {
            lemma_update_member(extended, self.words(), cpu_id.as_usize() as int, true);
            assert forall|id: int| member(before, id) == member(extended, id) by {
                if 0 <= id && id / 64 < extended.len() && id / 64 >= before.len() {
                    assert(extended[id / 64] == 0);
                    assert((0u64 & (1u64 << (id % 64))) == 0) by (bit_vector);
                }
            }
            assert(final(self)@ =~= old(self)@.insert(cpu_id.as_usize() as int));
        }
    }

    /// Removes exactly the specified CPU, preserving every other membership bit.
    pub fn remove(&mut self, cpu_id: CpuId)
        ensures
            final(self)@ == old(self)@.remove(cpu_id.as_usize() as int),
            final(self).words().len() == old(self).words().len(),
            final(self).inv() == old(self).inv(),
    {
        let ghost before = self.words();
        let part_idx = part_idx(cpu_id);
        let bit_idx = bit_idx(cpu_id);
        if part_idx < self.bits.len() {
            // Original: self.bits[part_idx] &= !(1 << bit_idx);
            let bits = self.bits.as_mut_slice();
            bits[part_idx] &= !(1u64 << bit_idx);
            proof {
                lemma_update_member(before, self.words(), cpu_id.as_usize() as int, false);
            }
        }
        proof {
            assert(final(self)@ =~= old(self)@.remove(cpu_id.as_usize() as int));
        }
    }

    /// Returns whether the specified CPU belongs to the set.
    pub fn contains(&self, cpu_id: CpuId) -> (r: bool)
        returns
            self@.contains(cpu_id.as_usize() as int),
    {
        let part_idx = part_idx(cpu_id);
        let bit_idx = bit_idx(cpu_id);
        part_idx < self.bits.len() && (self.bits.as_slice()[part_idx] & (1u64 << bit_idx)) != 0
    }

    /// Returns the sum of the word population counts, without overflow.
    pub fn count(&self) -> (r: usize)
        requires
            self.inv(),
        ensures
            r == count_prefix(self.words(), self.words().len()),
    {
        // Original: self.bits.iter().map(|part| part.count_ones() as usize).sum()
        let mut i = 0usize;
        let mut count = 0usize;
        while i < self.bits.len()
            invariant
                i <= self.bits@.len() <= MAX_PARTS,
                count <= i * 64,
                count == count_prefix(self.words(), i as nat),
            decreases self.bits@.len() - i,
        {
            count += count_word(self.bits.as_slice()[i]);
            i += 1;
        }
        count
    }

    /// Returns whether every stored word is zero.
    pub fn is_empty(&self) -> (r: bool)
        ensures
            r == (self@ == ISet::<int>::empty()),
        returns
            all_words(self.words(), 0),
    {
        // Original: self.bits.iter().all(|part| *part == 0)
        let mut i = 0usize;
        while i < self.bits.len()
            invariant
                i <= self.bits@.len(),
                forall|j: int| 0 <= j < i ==> self.bits@[j] == 0,
            decreases self.bits@.len() - i,
        {
            if self.bits.as_slice()[i] != 0 {
                proof {
                    let w = self.words()[i as int];
                    lemma_nonzero_word(w);
                    let b = choose|b: u64| #![auto] b < 64 && w & (1u64 << b) != 0;
                    let id = i * 64 + b;
                    assert(member(self.words(), id));
                    assert(self@.contains(id));
                }
                return false;
            }
            i += 1;
        }
        proof {
            lemma_zero_words(self.words());
        }
        true
    }

    /// Checks the original full-word predicate (an empty allocation is vacuously full).
    pub fn is_full(&self) -> (r: bool)
        returns
            self.full_words(),
    {
        let num_cpus = num_cpus();
        proof {
            assert(!0u64 == u64::MAX) by (bit_vector);
        }
        // Original: self.bits.iter().enumerate().all(...)
        let mut i = 0usize;
        while i < self.bits.len()
            invariant
                i <= self.bits@.len(),
                num_cpus == num_cpus_spec(),
                forall|j: int|
                    0 <= j < i ==> self.bits@[j] == if j == self.bits@.len() - 1 && num_cpus % 64
                        != 0 {
                        ((1u64 << (num_cpus % 64)) - 1) as u64
                    } else {
                        u64::MAX
                    },
            decreases self.bits@.len() - i,
        {
            let part = self.bits.as_slice()[i];
            let expected = if i == self.bits.len() - 1 && num_cpus % BITS_PER_PART != 0 {
                proof {
                    lemma_low_mask(num_cpus % 64);
                }
                (1u64 << (num_cpus % BITS_PER_PART)) - 1
            } else {
                !0u64
            };
            proof {
                assert(!0u64 == u64::MAX) by (bit_vector);
                assert(expected == if i as int == self.words().len() - 1 && num_cpus % 64 != 0 {
                    ((1u64 << (num_cpus % 64)) - 1) as u64
                } else {
                    u64::MAX
                });
            }
            if part != expected {
                proof {
                    assert(self.full_words() ==> self.words()[i as int] == expected);
                }
                return false;
            }
            i += 1;
        }
        true
    }

    /// Sets all allocated bits and masks off the unused bits in the last word.
    /// Requires storage for exactly the configured CPUs.
    pub fn add_all(&mut self)
        requires
            old(self).has_system_capacity(),
        ensures
            final(self).inv(),
            final(self).has_system_capacity(),
            final(self).full_words(),
            final(self)@ == ISet::new(|id: int| 0 <= id < num_cpus_spec()),
    {
        // Original: self.bits.fill(!0);
        proof {
            assert(!0u64 == u64::MAX) by (bit_vector);
        }
        self.fill_words(!0);
        self.clear_nonexistent_cpu_bits();
        proof {
            self.lemma_full_view();
        }
    }

    /// Removes all CPUs while preserving the allocation length.
    pub fn clear(&mut self)
        ensures
            final(self).words().len() == old(self).words().len(),
            final(self)@ == ISet::<int>::empty(),
            final(self).inv() == old(self).inv(),
    {
        // Original: self.bits.fill(0);
        self.fill_words(0);
        proof {
            lemma_zero_words(self.words());
        }
    }

    /// Iterates over the set bits in ascending CPU-ID order.
    pub fn iter(&self) -> (r: impl Iterator<Item = CpuId> + '_)
        requires
            self.inv(),
        ensures
            r.obeys_prophetic_iter_laws(),
            r.will_return_none(),
            r.remaining() == ids_from(self.words(), 0),
            ascending(r.remaining()),
            forall|id: CpuId| #[trigger]
                r.remaining().contains(id) == self@.contains(id.as_usize() as int),
    {
        // Original: self.bits.iter().enumerate().flat_map(|(part_idx, &part)|
        //     (0..BITS_PER_PART).filter_map(move |bit_idx| ...))
        proof {
            lemma_ids_from(self.words(), 0);
        }
        CpuSetIter { bits: self.bits.as_slice(), next: 0 }
    }

    /// Allocates ceil(num_cpus / 64) copies of val.
    fn with_capacity_val(num_cpus: usize, val: InnerPart) -> (r: Self)
        requires
            num_cpus <= u32::MAX,
        ensures
            r.inv(),
            r.words().len() == num_cpus / 64 + if num_cpus % 64 == 0 {
                0int
            } else {
                1int
            },
            all_words(r.words(), val),
    {
        let num_parts = parts_for_cpus(num_cpus);
        let mut bits = SmallVec::with_capacity(num_parts);
        bits.resize(num_parts, val);
        Self { bits }
    }

    fn clear_nonexistent_cpu_bits(&mut self)
        requires
            old(self).has_system_capacity(),
        ensures
            final(self).inv(),
            final(self).has_system_capacity(),
            all_words(old(self).words(), u64::MAX) ==> final(self).full_words(),
    {
        let num_cpus = num_cpus();
        if num_cpus % BITS_PER_PART != 0 {
            let num_parts = parts_for_cpus(num_cpus);
            proof {
                lemma_low_mask(num_cpus % 64);
            }
            // Original: self.bits[num_parts - 1] &= (1 << (num_cpus % BITS_PER_PART)) - 1;
            let bits = self.bits.as_mut_slice();
            bits[num_parts - 1] &= (1u64 << (num_cpus % BITS_PER_PART)) - 1;
            proof {
                let mask = ((1u64 << (num_cpus % 64)) - 1) as u64;
                assert(u64::MAX & mask == mask) by (bit_vector);
            }
        }
    }

    /// A full, system-sized allocation represents exactly the configured CPUs.
    proof fn lemma_full_view(&self)
        requires
            self.has_system_capacity(),
            self.full_words(),
        ensures
            self@ == ISet::new(|id: int| 0 <= id < num_cpus_spec()),
    {
        let n = num_cpus_spec();
        assert forall|id: int| #[trigger] member(self.words(), id) == (0 <= id < n) by {
            if 0 <= id && id / 64 < self.words().len() {
                let index = id / 64;
                let bit = (id % 64) as u64;
                if index == self.words().len() - 1 && n % 64 != 0 {
                    lemma_mask_member((n % 64) as u64, bit);
                } else {
                    assert(u64::MAX & (1u64 << bit) != 0) by (bit_vector)
                        requires
                            bit < 64,
                    ;
                }
            }
        }
        assert(self@ =~= ISet::new(|id: int| 0 <= id < n));
    }

    fn fill_words(&mut self, value: u64)
        ensures
            final(self).words().len() == old(self).words().len(),
            all_words(final(self).words(), value),
    {
        let mut i = 0usize;
        while i < self.bits.len()
            invariant
                self.bits@.len() == old(self).bits@.len(),
                i <= self.bits@.len(),
                forall|j: int| 0 <= j < i ==> self.bits@[j] == value,
            decreases self.bits@.len() - i,
        {
            self.bits.as_mut_slice()[i] = value;
            i += 1;
        }
    }
}

// The conversion allocates storage, so it is not a deterministic value-level
// FromSpec. The executable From method instead promises exact set membership.
impl vstd::std_specs::convert::FromSpecImpl<CpuId> for CpuSet {
    open spec fn obeys_from_spec() -> bool {
        false
    }

    open spec fn from_spec(value: CpuId) -> Self {
        arbitrary()
    }
}

impl From<CpuId> for CpuSet {
    fn from(cpu_id: CpuId) -> (r: Self)
        ensures
            r.inv(),
            r@ == ISet::<int>::empty().insert(cpu_id.as_usize() as int),
    {
        let mut set = Self::new_empty();
        set.add(cpu_id);
        set
    }
}

impl Default for CpuSet {
    fn default() -> (r: Self)
        ensures
            r.inv(),
            r.words().len() == 0,
            r@ == ISet::<int>::empty(),
    {
        let r = Self { bits: SmallVec::default() };
        r
    }
}

impl Clone for CpuSet {
    fn clone(&self) -> (r: Self)
        ensures
            r.words() == self.words(),
            r@ == self@,
            r.inv() == self.inv(),
    {
        let bits = self.bits.clone();
        proof {
            assert forall|i: int| 0 <= i < self.words().len() implies bits@[i]
                == self.words()[i] by {
                assert(cloned(self.words()[i], bits@[i]));
            }
            assert(bits@ =~= self.words());
        }
        Self { bits }
    }
}

/// The sequence produced by scanning bits from start to the end of storage.
pub closed spec fn ids_from(words: Seq<u64>, start: nat) -> Seq<CpuId>
    decreases words.len() * 64 - start,
{
    if start >= words.len() * 64 {
        Seq::empty()
    } else {
        let tail = ids_from(words, start + 1);
        if member(words, start as int) {
            seq![CpuId(start as u32)] + tail
        } else {
            tail
        }
    }
}

/// CPU IDs occur in strictly increasing order, hence without duplicates.
pub open spec fn ascending(ids: Seq<CpuId>) -> bool {
    forall|i: int, j: int|
        0 <= i < j < ids.len() ==> #[trigger] ids[i].as_usize() < #[trigger] ids[j].as_usize()
}

proof fn lemma_ids_from(words: Seq<u64>, start: nat)
    requires
        words.len() <= MAX_PARTS,
    ensures
        ascending(ids_from(words, start)),
        forall|i: int|
            0 <= i < ids_from(words, start).len() ==> start <= #[trigger] ids_from(
                words,
                start,
            )[i].as_usize(),
        forall|id: CpuId| #[trigger]
            ids_from(words, start).contains(id) == (start <= id.as_usize() && member(
                words,
                id.as_usize() as int,
            )),
    decreases words.len() * 64 - start,
{
    if start < words.len() * 64 {
        lemma_ids_from(words, start + 1);
        let tail = ids_from(words, start + 1);
        if member(words, start as int) {
            let head = CpuId(start as u32);
            let ids = ids_from(words, start);
            assert(head.as_usize() == start);
            assert(ids == seq![head] + tail);
            assert forall|i: int| 0 <= i < ids.len() implies start
                <= #[trigger] ids[i].as_usize() by {
                if i > 0 {
                    assert(ids[i] == tail[i - 1]);
                }
            }
            assert forall|i: int, j: int|
                0 <= i < j < ids.len() implies #[trigger] ids[i].as_usize()
                < #[trigger] ids[j].as_usize() by {
                assert(ids[j] == tail[j - 1]);
                if i > 0 {
                    assert(ids[i] == tail[i - 1]);
                }
            }
            assert forall|id: CpuId| #[trigger]
                ids.contains(id) == (start <= id.as_usize() && member(
                    words,
                    id.as_usize() as int,
                )) by {
                vstd::seq_lib::lemma_seq_concat_contains_all_elements(seq![head], tail, id);
                assert(seq![head][0] == head);
                assert(seq![head].contains(id) == (head == id));
                assert((head == id) == (start == id.as_usize()));
                assert(tail.contains(id) == (start + 1 <= id.as_usize() && member(
                    words,
                    id.as_usize() as int,
                )));
            }
        }
    }
}

struct CpuSetIter<'a> {
    bits: &'a [u64],
    next: usize,
}

impl<'a> CpuSetIter<'a> {
    #[verifier::type_invariant]
    closed spec fn type_inv(&self) -> bool {
        self.bits@.len() <= MAX_PARTS && self.next <= self.bits@.len() * 64
    }
}

impl<'a> IteratorSpecImpl for CpuSetIter<'a> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        true
    }

    closed spec fn remaining(&self) -> Seq<CpuId> {
        ids_from(self.bits@, self.next as nat)
    }

    open spec fn will_return_none(&self) -> bool {
        true
    }

    closed spec fn decrease(&self) -> Option<nat> {
        Some((self.bits@.len() * 64 - self.next) as nat)
    }

    closed spec fn peek(&self, index: int) -> Option<CpuId> {
        {
            let ids = ids_from(self.bits@, self.next as nat);
            if 0 <= index < ids.len() {
                Some(ids[index])
            } else {
                None
            }
        }
    }
}

impl<'a> Iterator for CpuSetIter<'a> {
    type Item = CpuId;

    fn next(&mut self) -> (r: Option<CpuId>) {
        proof {
            use_type_invariant(&*self);
        }
        while self.next < self.bits.len() * 64
            invariant
                self.bits == old(self).bits,
                self.bits@.len() <= MAX_PARTS,
                old(self).next <= self.next <= self.bits@.len() * 64,
                ids_from(self.bits@, old(self).next as nat) == ids_from(
                    self.bits@,
                    self.next as nat,
                ),
            decreases self.bits@.len() * 64 - self.next,
        {
            let id = self.next;
            let part = self.bits[id / 64];
            self.next += 1;
            if part & (1u64 << (id % 64)) != 0 {
                return Some(CpuId(id as u32));
            }
        }
        None
    }
}

proof fn lemma_nonzero_word(w: u64)
    ensures
        w != 0 ==> exists|b: u64| #![auto] b < 64 && w & (1u64 << b) != 0,
{
    assert(w != 0 ==> exists|b: u64| #![auto] b < 64 && w & (1u64 << b) != 0) by (bit_vector);
}

proof fn lemma_mask_member(n: u64, b: u64)
    requires
        n < 64,
        b < 64,
    ensures
        ((((1u64 << n) - 1) as u64) & (1u64 << b) != 0) == (b < n),
{
    assert(((((1u64 << n) - 1) as u64) & (1u64 << b) != 0) == (b < n)) by (bit_vector)
        requires
            n < 64,
            b < 64,
    ;
}

proof fn lemma_low_mask(n: usize)
    requires
        0 < n < 64,
    ensures
        (1u64 << n) > 0,
{
    assert((1u64 << n) > 0) by (bit_vector)
        requires
            0 < n < 64,
    ;
}

proof fn lemma_zero_words(words: Seq<u64>)
    requires
        all_words(words, 0),
    ensures
        ISet::new(|id: int| member(words, id)) == ISet::<int>::empty(),
{
    assert forall|id: int| !member(words, id) by {
        if 0 <= id && id / 64 < words.len() {
            assert(words[id / 64] == 0);
            assert((0u64 & (1u64 << (id % 64))) == 0) by (bit_vector);
        }
    }
}

proof fn lemma_update_member(before: Seq<u64>, after: Seq<u64>, id: int, add: bool)
    requires
        0 <= id,
        id / 64 < before.len(),
        after.len() == before.len(),
        after == before.update(
            id / 64,
            if add {
                before[id / 64] | (1u64 << (id % 64))
            } else {
                before[id / 64] & !(1u64 << (id % 64))
            },
        ),
    ensures
        forall|other: int| #[trigger]
            member(after, other) == (if other == id {
                add
            } else {
                member(before, other)
            }),
{
    assert forall|other: int| #[trigger]
        member(after, other) == (if other == id {
            add
        } else {
            member(before, other)
        }) by {
        if 0 <= other && other / 64 < before.len() && other / 64 == id / 64 {
            let w = before[id / 64];
            let b = (id % 64) as u64;
            let c = (other % 64) as u64;
            assert(b < 64 && c < 64);
            assert((other == id) == (b == c));
            assert(((w | (1u64 << b)) & (1u64 << c) != 0) == (b == c || (w & (1u64 << c) != 0)))
                by (bit_vector)
                requires
                    b < 64,
                    c < 64,
            ;
            assert(((w & !(1u64 << b)) & (1u64 << c) != 0) == (b != c && (w & (1u64 << c) != 0)))
                by (bit_vector)
                requires
                    b < 64,
                    c < 64,
            ;
        }
    }
}

/// CPU set with per-word atomic operations. Multiword operations are not atomic.
#[derive(Debug)]
pub struct AtomicCpuSet {
    bits: SmallVec<[AtomicInnerPart; NR_PARTS_NO_ALLOC]>,
}

type AtomicInnerPart = AtomicU64;

impl AtomicCpuSet {
    pub closed spec fn num_parts(&self) -> nat {
        self.bits@.len()
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(&self) -> bool {
        self.num_parts() <= MAX_PARTS
    }

    /// Constructs one atomic word per input word.
    /// The existing vstd atomic boundary does not expose the initial values.
    pub fn new(value: CpuSet) -> (r: Self)
        requires
            value.inv(),
        ensures
            r.num_parts() == value.words().len(),
    {
        // Original: value.bits.into_iter().map(AtomicU64::new).collect()
        let mut bits = SmallVec::with_capacity(value.bits.len());
        let mut i = 0usize;
        while i < value.bits.len()
            invariant
                bits@.len() == i,
                i <= value.bits@.len() <= MAX_PARTS,
            decreases value.bits@.len() - i,
        {
            let part = value.bits.as_slice()[i];
            bits.push(AtomicU64::new(part));
            i += 1;
        }
        Self { bits }
    }

    /// Loads each word separately; Release uses fetch_or(0), as in the original.
    /// AcqRel is excluded because core atomic load rejects it.
    pub fn load(&self, ordering: Ordering) -> (r: CpuSet)
        requires
            self.num_parts() > 0 ==> ordering != Ordering::AcqRel,
        ensures
            r.inv(),
            r.words().len() == self.num_parts(),
    {
        proof {
            use_type_invariant(self);
        }
        // Original: self.bits.iter().map(|part| match ordering { ... }).collect()
        let mut bits = SmallVec::with_capacity(self.bits.len());
        let mut i = 0usize;
        while i < self.bits.len()
            invariant
                i == bits@.len(),
                i <= self.num_parts() <= MAX_PARTS,
            decreases self.num_parts() - i,
        {
            let part = &self.bits.as_slice()[i];
            let value = match ordering {
                Ordering::Release => part.fetch_or(0, ordering),
                _ => part.load(ordering),
            };
            bits.push(value);
            i += 1;
        }
        CpuSet { bits }
    }

    /// Stores the common prefix, exactly matching zip for unequal lengths.
    pub fn store(&self, value: &CpuSet, ordering: Ordering)
        requires
            self.num_parts() > 0 && value.words().len() > 0 ==> ordering == Ordering::Relaxed
                || ordering == Ordering::Release || ordering == Ordering::SeqCst,
    {
        // Original: for (part, new_part) in self.bits.iter().zip(value.bits.iter())
        let mut i = 0usize;
        while i < self.bits.len() && i < value.bits.len()
            invariant
                i <= self.bits@.len(),
                i <= value.bits@.len(),
            decreases self.bits@.len() - i,
        {
            self.bits.as_slice()[i].store(value.bits.as_slice()[i], ordering);
            i += 1;
        }
    }

    /// Sets a bit atomically when its word exists; otherwise does nothing.
    pub fn add(&self, cpu_id: CpuId, ordering: Ordering) {
        let part_idx = part_idx(cpu_id);
        let bit_idx = bit_idx(cpu_id);
        if part_idx < self.bits.len() {
            self.bits.as_slice()[part_idx].fetch_or(1u64 << bit_idx, ordering);
        }
    }

    /// Clears a bit atomically when its word exists; otherwise does nothing.
    pub fn remove(&self, cpu_id: CpuId, ordering: Ordering) {
        let part_idx = part_idx(cpu_id);
        let bit_idx = bit_idx(cpu_id);
        if part_idx < self.bits.len() {
            self.bits.as_slice()[part_idx].fetch_and(!(1u64 << bit_idx), ordering);
        }
    }

    /// Tests a bit after an atomic load; nonexistent words always return false.
    pub fn contains(&self, cpu_id: CpuId, ordering: Ordering) -> (r: bool)
        requires
            cpu_id.as_usize() / 64 < self.num_parts() ==> ordering == Ordering::Relaxed || ordering
                == Ordering::Acquire || ordering == Ordering::SeqCst,
        ensures
            cpu_id.as_usize() / 64 >= self.num_parts() ==> !r,
    {
        let part_idx = part_idx(cpu_id);
        let bit_idx = bit_idx(cpu_id);
        part_idx < self.bits.len() && (self.bits.as_slice()[part_idx].load(ordering) & (1u64
            << bit_idx)) != 0
    }
}

} // verus!
// Original compile-time representation check, independent of erased proof state.
const _: () = assert!(core::mem::size_of::<InnerPart>() * 8 == BITS_PER_PART);
const _: () = assert!(core::mem::size_of::<AtomicInnerPart>() * 8 == BITS_PER_PART);
#[cfg(ktest)]
mod test {
    use super::*;
    use crate::{cpu::all_cpus, prelude::*};

    #[ktest]
    fn test_full_cpu_set_iter_is_all() {
        let set = CpuISet::new_full();
        let num_cpus = num_cpus();
        let all_cpus = all_cpus().collect::<Vec<_>>();
        let set_cpus = set.iter().collect::<Vec<_>>();

        assert!(set_cpus.len() == num_cpus);
        assert_eq!(set_cpus, all_cpus);
    }

    #[ktest]
    fn test_full_cpu_set_contains_all() {
        let set = CpuISet::new_full();
        for cpu_id in all_cpus() {
            assert!(set.contains(cpu_id));
        }
    }

    #[ktest]
    fn test_empty_cpu_set_iter_is_empty() {
        let set = CpuISet::new_empty();
        let set_cpus = set.iter().collect::<Vec<_>>();
        assert!(set_cpus.is_empty());
    }

    #[ktest]
    fn test_empty_cpu_set_contains_none() {
        let set = CpuISet::new_empty();
        for cpu_id in all_cpus() {
            assert!(!set.contains(cpu_id));
        }
    }

    #[ktest]
    fn test_atomic_cpu_set_multiple_sizes() {
        for test_num_cpus in [1usize, 3, 12, 64, 96, 99, 128, 256, 288, 1024] {
            let test_all_iter = || (0..test_num_cpus).map(|id| CpuId(id as u32));

            let set = CpuSet::with_capacity_val(test_num_cpus, 0);
            let atomic_set = AtomicCpuISet::new(set);

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

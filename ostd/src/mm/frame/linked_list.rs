// SPDX-License-Identifier: MPL-2.0
//! Enabling linked lists of frames without heap allocation.
//!
//! This module leverages the customizability of the metadata system (see
//! [super::meta]) to allow any type of frame to be used in a linked list.
use vstd::prelude::*;

use vstd::seq_lib::*;
use vstd::simple_pptr::*;

use vstd_extra::cast_ptr::*;
use vstd_extra::drop_tracking::{Drop, DropObligation, TrackDrop};
use vstd_extra::ownership::*;

use crate::mm::frame::meta::{
    META_SLOT_SIZE, REF_COUNT_UNIQUE,
    mapping::{frame_to_meta, meta_to_frame},
};
use crate::mm::kspace::FRAME_METADATA_RANGE;
use crate::specs::arch::*;
use crate::specs::mm::frame::{
    linked_list::linked_list_owners::*,
    mapping::{frame_to_index, group_page_meta, index_to_meta, meta_to_index},
    meta_owners::{
        MetaSlotOwner, MetaSlotStorage, borrow_meta, borrow_meta_mut, typed_meta_value,
        typed_meta_wf,
    },
    meta_region_owners::MetaRegionOwners,
    unique::UniqueFrameOwner,
};

use super::{
    MetaSlot, mapping,
    meta::{AnyFrameMeta, get_slot},
    unique::UniqueFrame,
};
use crate::{
    arch::mm::PagingConsts,
    mm::{Paddr, Vaddr},
    //panic::abort,
};
use core::{
    ops::{Deref, DerefMut},
    ptr::NonNull,
    sync::atomic::{AtomicU64, Ordering},
};

verus! {

/// A linked list of frames.
///
/// Two key features that [`LinkedList`] is different from
/// [`alloc::collections::LinkedList`] is that:
///  1. It is intrusive, meaning that the links are part of the frame metadata.
///     This allows the linked list to be used without heap allocation. But it
///     disallows a frame to be in multiple linked lists at the same time.
///  2. The linked list exclusively own the frames, meaning that it takes
///     unique pointers [`UniqueFrame`]. And other bodies cannot
///     [`from_in_use`] a frame that is inside a linked list.
///  3. We also allow creating cursors at a specific frame, allowing $O(1)$
///     removal without iterating through the list at a cost of some checks.
///
/// # Example
///
/// To create metadata types that allows linked list links, wrap the metadata
/// type in [`Link`]:
///
/// ```rust
/// use ostd::{
///     mm::{frame::{linked_list::{Link, LinkedList}, Frame}, FrameAllocOptions},
///     impl_untyped_frame_meta_for,
/// };
///
/// #[derive(Debug)]
/// struct MyMeta { mark: usize }
///
/// type MyFrame = Frame<Link<MyMeta>>;
///
/// impl_untyped_frame_meta_for!(MyMeta);
///
/// let alloc_options = FrameAllocOptions::new();
/// let frame1 = alloc_options.alloc_frame_with(Link::new(MyMeta { mark: 1 })).unwrap();
/// let frame2 = alloc_options.alloc_frame_with(Link::new(MyMeta { mark: 2 })).unwrap();
///
/// let mut list = LinkedList::new();
/// list.push_front(frame1.try_into().unwrap());
/// list.push_front(frame2.try_into().unwrap());
///
/// let mut cursor = list.cursor_front_mut();
/// assert_eq!(cursor.current_meta().unwrap().mark, 2);
/// cursor.move_next();
/// assert_eq!(cursor.current_meta().unwrap().mark, 1);
/// ```
///
/// [`from_in_use`]: super::Frame::from_in_use
///
/// # Verified Properties
/// ## Verification Design
/// The linked list is abstractly represented by a [`LinkedListOwner`]:
/// ```rust
/// tracked struct LinkedListOwner<M: AnyFrameMeta + Repr<MetaSlotStorage>> {
///     pub list: Seq<LinkOwner>,
///     pub list_id: u64,
/// }
/// ```
/// The raw slot and storage permissions for each link are parked in the global
/// [`MetaRegionOwners`], while [`LinkedListOwner`] owns the corresponding
/// type-specific `Link<M>::ReprPerm`. Cursor accessors borrow these independent
/// components together when projecting a `Link<M>`.
/// ## Invariant
/// The linked list uniquely owns the raw frames that it contains, so they cannot be used by other
/// data structures. The frame metadata field `in_list` is equal to `list_id` for all links in the list.
/// The per-link well-formedness against the region (pptr/inner_perms wiring,
/// `next`/`prev` pointer chain) is captured by
/// [`LinkedListOwner::relate_region`] (opaque, with per-position
/// [`LinkedListOwner::relate_region_at`]). The cursor exposes this via
/// [`CursorOwner::wf_with_region`] and [`CursorMut::wf_region`].
/// ## Safety
/// A given linked list can only have one cursor at a time, so there are no data races.
/// The `prev` and `next` fields of the metadata for each link always points to valid
/// links in the list, so the structure is memory safe (will not read or write invalid memory).
pub struct LinkedList<M: AnyFrameMeta + Repr<MetaSlotSmall>> {
    pub front: Option<ReprPtr<MetaSlotStorage, Link<M>>>,
    pub back: Option<ReprPtr<MetaSlotStorage, Link<M>>>,
    /// The number of frames in the list.
    pub size: usize,
    /// A lazily initialized ID, used to check whether a frame is in the list.
    /// 0 means uninitialized.
    pub list_id: u64,
}

/// A cursor that can mutate the linked list links.
///
/// The cursor points to either a frame or the "ghost" non-element. It points
/// to the "ghost" non-element when the cursor surpasses the back of the list.
pub struct CursorMut<'a, M: AnyFrameMeta + Repr<MetaSlotSmall>> {
    pub list: &'a mut LinkedList<M>,
    pub current: Option<ReprPtr<MetaSlotStorage, Link<M>>>,
}

#[verifier::spinoff_prover]
proof fn lemma_meta_region_inv_at(regions: MetaRegionOwners, i: int)
    requires
        regions.inv(),
        regions.contains(i),
    ensures
        regions.slot_owners[i].inv(),
        regions.slots[i].is_init(),
        regions.slots[i].addr() == index_to_meta(i),
        regions.slots[i].value().wf(regions.slot_owners[i]),
        regions.slot_owners[i].slot_vaddr == regions.slots[i].addr(),
{
}

/// Localizes the "no existing slot aliases the inserted frame" universal fact
/// into its own prover query, so the `MetaRegionOwners::inv` and map-insert
/// quantifiers do not get over-instantiated inside `insert_before`'s body.
#[verifier::spinoff_prover]
proof fn lemma_insert_before_slot_distinct<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    owner0: LinkedListOwner<M>,
    regions0: MetaRegionOwners,
    frame_idx: int,
    nn: int,
)
    requires
        owner0.relate_region(regions0),
        regions0.inv(),
        regions0.contains(frame_idx),
        regions0.slot_owners[frame_idx].inner_perms.in_list.value() == 0,
        0 <= nn <= owner0.list.len() as int,
    ensures
        forall|p: int|
            #![trigger regions0.slot_owners[meta_to_index(owner0.list[p].paddr)]]
            (0 <= p < owner0.list.len() as int) ==> frame_idx != meta_to_index(
                owner0.list[p].paddr,
            ),
{
    assert forall|p: int|
        #![trigger regions0.slot_owners[meta_to_index(owner0.list[p].paddr)]]
        0 <= p < owner0.list.len() as int implies frame_idx != meta_to_index(
        owner0.list[p].paddr,
    ) by {
        owner0.relate_region_at_facts(regions0, p);
        if frame_idx == meta_to_index(owner0.list[p].paddr) {
            assert(regions0.slot_owners[meta_to_index(
                owner0.list[p].paddr,
            )].inner_perms.in_list.value() == owner0.list_id);
        }
    }
}

/// Collects the read-only facts needed by `insert_before` before any slot is
/// rewired.  This keeps unfolding `relate_region` and `MetaRegionOwners::inv`
/// out of the executable function's solver query.
#[verifier::spinoff_prover]
proof fn lemma_insert_before_setup<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    owner0: CursorOwner<M>,
    regions0: MetaRegionOwners,
    frame_idx: int,
)
    requires
        owner0.wf_with_region(regions0),
        regions0.inv(),
        regions0.contains(frame_idx),
        regions0.slot_owners[frame_idx].inner_perms.in_list.value() == 0,
    ensures
        owner0.list_own.repr_perms.len() == owner0.list_own.list.len(),
        owner0.list_own.list.len() > 0 ==> owner0.list_own.list_id != 0,
        owner0.list_own.list.len() < usize::MAX,
        regions0.slot_owners[frame_idx].inv(),
        regions0.slots[frame_idx].is_init(),
        regions0.slots[frame_idx].addr() == index_to_meta(frame_idx),
        regions0.slots[frame_idx].value().wf(regions0.slot_owners[frame_idx]),
        regions0.slot_owners[frame_idx].slot_vaddr == regions0.slots[frame_idx].addr(),
        owner0.index > 0 ==> owner0.list_own.relate_region_at(regions0, owner0.index - 1),
        owner0.index < owner0.list_own.list.len() ==> owner0.list_own.relate_region_at(
            regions0,
            owner0.index,
        ),
        forall|p: int|
            #![trigger regions0.slot_owners[meta_to_index(owner0.list_own.list[p].paddr)]]
            (0 <= p < owner0.list_own.list.len()) ==> frame_idx != meta_to_index(
                owner0.list_own.list[p].paddr,
            ),
{
    assert(owner0.list_own.relate_region(regions0));
    assert(owner0.list_own.repr_perms.len() == owner0.list_own.list.len()) by {};
    assert(owner0.list_own.list.len() > 0 ==> owner0.list_own.list_id != 0) by {};
    owner0.list_own.length_lt_usize_max(regions0);
    if owner0.index > 0 {
        let _ = owner0.list_own.list[owner0.index - 1];
        assert(owner0.list_own.relate_region_at(regions0, owner0.index - 1)) by {};
    }
    if owner0.index < owner0.list_own.list.len() {
        let _ = owner0.list_own.list[owner0.index];
        assert(owner0.list_own.relate_region_at(regions0, owner0.index)) by {};
    }
    lemma_insert_before_slot_distinct(owner0.list_own, regions0, frame_idx, owner0.index);
}

/// Instantiates the list-wide region relation at one selected position.
#[verifier::spinoff_prover]
proof fn lemma_linked_list_relate_region_at<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    owner: LinkedListOwner<M>,
    regions: MetaRegionOwners,
    index: int,
)
    requires
        owner.relate_region(regions),
        0 <= index < owner.list.len(),
    ensures
        owner.relate_region_at(regions, index),
{
    let _ = owner.list[index];
    reveal(LinkedListOwner::relate_region);
}

#[verifier::opaque]
spec fn take_current_regions_preserved(
    regions: MetaRegionOwners,
    old_regions: MetaRegionOwners,
    removed_idx: int,
) -> bool {
    &&& regions.slots.dom() == old_regions.slots.dom()
    &&& forall|j: int|
        #![trigger old_regions.slot_owners[j]]
        j != removed_idx ==> {
            &&& regions.slot_owners[j].usage == old_regions.slot_owners[j].usage
            &&& regions.slot_owners[j].slot_vaddr == old_regions.slot_owners[j].slot_vaddr
            &&& regions.slot_owners[j].paths_in_pt == old_regions.slot_owners[j].paths_in_pt
            &&& regions.slot_owners[j].inner_perms.ref_count.value()
                == old_regions.slot_owners[j].inner_perms.ref_count.value()
            &&& regions.slot_owners[j].inner_perms.in_list.value()
                == old_regions.slot_owners[j].inner_perms.in_list.value()
        }
}

#[verifier::opaque]
spec fn take_current_regions_unchanged_except(
    regions: MetaRegionOwners,
    old_regions: MetaRegionOwners,
    changed_idx: int,
) -> bool {
    &&& regions.slots == old_regions.slots
    &&& regions.slot_owners.dom() == old_regions.slot_owners.dom()
    &&& forall|j: int|
        #![trigger regions.slot_owners[j]]
        j != changed_idx ==> regions.slot_owners[j] == old_regions.slot_owners[j]
}

proof fn lemma_take_current_regions_preserved_at(
    regions: MetaRegionOwners,
    old_regions: MetaRegionOwners,
    removed_idx: int,
    index: int,
)
    requires
        take_current_regions_preserved(regions, old_regions, removed_idx),
        index != removed_idx,
    ensures
        regions.slot_owners[index].usage == old_regions.slot_owners[index].usage,
        regions.slot_owners[index].slot_vaddr == old_regions.slot_owners[index].slot_vaddr,
        regions.slot_owners[index].paths_in_pt == old_regions.slot_owners[index].paths_in_pt,
        regions.slot_owners[index].inner_perms.ref_count.value()
            == old_regions.slot_owners[index].inner_perms.ref_count.value(),
        regions.slot_owners[index].inner_perms.in_list.value()
            == old_regions.slot_owners[index].inner_perms.in_list.value(),
{
    reveal(take_current_regions_preserved);
}

#[verifier::spinoff_prover]
proof fn lemma_take_current_regions_preserved_init(
    regions: MetaRegionOwners,
    old_regions: MetaRegionOwners,
    removed_idx: int,
)
    requires
        regions.slots.dom() == old_regions.slots.dom(),
        regions.slot_owners == old_regions.slot_owners,
    ensures
        take_current_regions_preserved(regions, old_regions, removed_idx),
{
    reveal(take_current_regions_preserved);
}

#[verifier::spinoff_prover]
proof fn lemma_take_current_regions_preserved_update(
    before: MetaRegionOwners,
    after: MetaRegionOwners,
    old_regions: MetaRegionOwners,
    removed_idx: int,
    updated_idx: int,
)
    requires
        take_current_regions_preserved(before, old_regions, removed_idx),
        after.slots.dom() == before.slots.dom(),
        forall|j: int|
            #![trigger after.slot_owners[j]]
            j != updated_idx ==> after.slot_owners[j] == before.slot_owners[j],
        updated_idx != removed_idx ==> {
            &&& after.slot_owners[updated_idx].usage == before.slot_owners[updated_idx].usage
            &&& after.slot_owners[updated_idx].slot_vaddr
                == before.slot_owners[updated_idx].slot_vaddr
            &&& after.slot_owners[updated_idx].paths_in_pt
                == before.slot_owners[updated_idx].paths_in_pt
            &&& after.slot_owners[updated_idx].inner_perms.ref_count.value()
                == before.slot_owners[updated_idx].inner_perms.ref_count.value()
            &&& after.slot_owners[updated_idx].inner_perms.in_list.value()
                == before.slot_owners[updated_idx].inner_perms.in_list.value()
        },
    ensures
        take_current_regions_preserved(after, old_regions, removed_idx),
{
    reveal(take_current_regions_preserved);
    assert forall|j: int| #![trigger old_regions.slot_owners[j]] j != removed_idx implies {
        &&& after.slot_owners[j].usage == old_regions.slot_owners[j].usage
        &&& after.slot_owners[j].slot_vaddr == old_regions.slot_owners[j].slot_vaddr
        &&& after.slot_owners[j].paths_in_pt == old_regions.slot_owners[j].paths_in_pt
        &&& after.slot_owners[j].inner_perms.ref_count.value()
            == old_regions.slot_owners[j].inner_perms.ref_count.value()
        &&& after.slot_owners[j].inner_perms.in_list.value()
            == old_regions.slot_owners[j].inner_perms.in_list.value()
    } by {
        if j == updated_idx {
        }
    }
}

#[verifier::spinoff_prover]
proof fn lemma_take_current_regions_preserved_transitive(
    regions: MetaRegionOwners,
    middle_regions: MetaRegionOwners,
    old_regions: MetaRegionOwners,
    removed_idx: int,
)
    requires
        take_current_regions_preserved(regions, middle_regions, removed_idx),
        take_current_regions_preserved(middle_regions, old_regions, removed_idx),
    ensures
        take_current_regions_preserved(regions, old_regions, removed_idx),
{
    reveal(take_current_regions_preserved);
}

#[verifier::spinoff_prover]
proof fn lemma_take_current_regions_unchanged_except_transitive(
    regions: MetaRegionOwners,
    middle_regions: MetaRegionOwners,
    old_regions: MetaRegionOwners,
    changed_idx: int,
)
    requires
        take_current_regions_unchanged_except(regions, middle_regions, changed_idx),
        take_current_regions_unchanged_except(middle_regions, old_regions, changed_idx),
    ensures
        take_current_regions_unchanged_except(regions, old_regions, changed_idx),
{
    reveal(take_current_regions_unchanged_except);
}

#[verifier::spinoff_prover]
proof fn lemma_take_current_local_ready_preserved<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    old: LinkedListOwner<M>,
    old_regions: MetaRegionOwners,
    new: LinkedListOwner<M>,
    middle_regions: MetaRegionOwners,
    regions: MetaRegionOwners,
    removed: int,
    removed_idx: int,
)
    requires
        0 <= removed < old.list.len(),
        old.relate_region(old_regions),
        new.list == old.list.remove(removed),
        removed_idx == meta_to_index(old.list[removed].paddr),
        take_current_local_ready(old, old_regions, new, middle_regions, removed),
        take_current_regions_unchanged_except(regions, middle_regions, removed_idx),
    ensures
        take_current_local_ready(old, old_regions, new, regions, removed),
{
    reveal(take_current_local_ready);
    reveal(take_current_regions_unchanged_except);
    assert forall|p: int|
        #![trigger meta_to_index(old.list[p].paddr)]
        (0 <= p < old.list.len() && p != removed) implies ({
        let i = meta_to_index(old.list[p].paddr);
        let np = if p < removed {
            p
        } else {
            p - 1
        };
        &&& regions.contains(i)
        &&& regions.slots[i].addr() == old.list[p].paddr
        &&& regions.slots[i].pptr() == old_regions.slots[i].pptr()
        &&& regions.slot_owners[i].inner_perms.ref_count.value() == REF_COUNT_UNIQUE
        &&& regions.slot_owners[i].usage is Frame
        &&& regions.slot_owners[i].inner_perms.in_list.value() == new.list_id
        &&& new.meta_wf_at(regions, np)
        &&& regions.slots[i].addr() % META_SLOT_SIZE == 0
        &&& FRAME_METADATA_RANGE.start <= regions.slots[i].addr() < FRAME_METADATA_RANGE.start
            + MAX_NR_PAGES * META_SLOT_SIZE
    }) by {
        let i = meta_to_index(old.list[p].paddr);
        let np = if p < removed {
            p
        } else {
            p - 1
        };
        lemma_linked_list_relate_region_at(old, old_regions, p);
        old.relate_region_at_facts(old_regions, p);
        assert(i != removed_idx) by {
            let _ = old.list[p];
            let _ = old.list[removed];
            reveal(LinkedListOwner::relate_region);
        };
        assert(regions.slots == middle_regions.slots);
        assert(middle_regions.contains(i));
        assert(regions.contains(i));
        assert(regions.slot_owners[i] == middle_regions.slot_owners[i]);
        assert(regions.slots[i] == middle_regions.slots[i]);
        assert(new.list[np] == old.list[p]);
        assert(middle_regions.slots[i].pptr() == old_regions.slots[i].pptr());
        assert(new.meta_wf_at(middle_regions, np));
        assert(new.meta_wf_at(regions, np));
    }
}

#[verifier::spinoff_prover]
proof fn lemma_take_current_pointer_state_preserved<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    old: LinkedListOwner<M>,
    old_regions: MetaRegionOwners,
    new: LinkedListOwner<M>,
    middle_regions: MetaRegionOwners,
    regions: MetaRegionOwners,
    removed: int,
    removed_idx: int,
    prev_done: bool,
    next_done: bool,
)
    requires
        0 <= removed < old.list.len(),
        old.relate_region(old_regions),
        new.list == old.list.remove(removed),
        removed_idx == meta_to_index(old.list[removed].paddr),
        take_current_pointer_state(
            old,
            old_regions,
            new,
            middle_regions,
            removed,
            prev_done,
            next_done,
        ),
        take_current_regions_unchanged_except(regions, middle_regions, removed_idx),
    ensures
        take_current_pointer_state(old, old_regions, new, regions, removed, prev_done, next_done),
{
    reveal(take_current_pointer_state);
    reveal(take_current_regions_unchanged_except);
    assert forall|p: int|
        #![trigger meta_to_index(old.list[p].paddr)]
        (0 <= p < old.list.len() && p != removed) implies ({
        let np = if p < removed {
            p
        } else {
            p - 1
        };
        let fp = new.meta_value_at(regions, np);
        &&& (prev_done && p == removed - 1 ==> fp.next == old.meta_value_at(
            old_regions,
            removed,
        ).next)
        &&& (!(prev_done && p == removed - 1) ==> fp.next == old.meta_value_at(old_regions, p).next)
        &&& (next_done && p == removed + 1 ==> fp.prev == old.meta_value_at(
            old_regions,
            removed,
        ).prev)
        &&& (!(next_done && p == removed + 1) ==> fp.prev == old.meta_value_at(old_regions, p).prev)
    }) by {
        let i = meta_to_index(old.list[p].paddr);
        let np = if p < removed {
            p
        } else {
            p - 1
        };
        assert(i != removed_idx) by {
            let _ = old.list[p];
            let _ = old.list[removed];
            reveal(LinkedListOwner::relate_region);
        };
        assert(new.list[np] == old.list[p]);
        assert(regions.slot_owners[i] == middle_regions.slot_owners[i]);
    }
}

#[verifier::opaque]
spec fn take_current_local_ready<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    old: LinkedListOwner<M>,
    old_regions: MetaRegionOwners,
    new: LinkedListOwner<M>,
    regions: MetaRegionOwners,
    removed: int,
) -> bool {
    forall|p: int|
        #![trigger meta_to_index(old.list[p].paddr)]
        (0 <= p < old.list.len() && p != removed) ==> ({
            let i = meta_to_index(old.list[p].paddr);
            let np = if p < removed {
                p
            } else {
                p - 1
            };
            &&& regions.contains(i)
            &&& regions.slots[i].addr() == old.list[p].paddr
            &&& regions.slots[i].pptr() == old_regions.slots[i].pptr()
            &&& regions.slot_owners[i].inner_perms.ref_count.value() == REF_COUNT_UNIQUE
            &&& regions.slot_owners[i].usage is Frame
            &&& regions.slot_owners[i].inner_perms.in_list.value() == new.list_id
            &&& new.meta_wf_at(regions, np)
            &&& regions.slots[i].addr() % META_SLOT_SIZE == 0
            &&& FRAME_METADATA_RANGE.start <= regions.slots[i].addr() < FRAME_METADATA_RANGE.start
                + MAX_NR_PAGES * META_SLOT_SIZE
        })
}

#[verifier::opaque]
spec fn take_current_pointer_state<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    old: LinkedListOwner<M>,
    old_regions: MetaRegionOwners,
    new: LinkedListOwner<M>,
    regions: MetaRegionOwners,
    removed: int,
    prev_done: bool,
    next_done: bool,
) -> bool {
    forall|p: int|
        #![trigger meta_to_index(old.list[p].paddr)]
        (0 <= p < old.list.len() && p != removed) ==> ({
            let np = if p < removed {
                p
            } else {
                p - 1
            };
            let fp = new.meta_value_at(regions, np);
            &&& (prev_done && p == removed - 1 ==> fp.next == old.meta_value_at(
                old_regions,
                removed,
            ).next)
            &&& (!(prev_done && p == removed - 1) ==> fp.next == old.meta_value_at(
                old_regions,
                p,
            ).next)
            &&& (next_done && p == removed + 1 ==> fp.prev == old.meta_value_at(
                old_regions,
                removed,
            ).prev)
            &&& (!(next_done && p == removed + 1) ==> fp.prev == old.meta_value_at(
                old_regions,
                p,
            ).prev)
        })
}

#[verifier::spinoff_prover]
proof fn lemma_take_current_pointer_state_init<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    old: LinkedListOwner<M>,
    old_regions: MetaRegionOwners,
    new: LinkedListOwner<M>,
    regions: MetaRegionOwners,
    removed: int,
)
    requires
        0 <= removed < old.list.len(),
        old.relate_region(old_regions),
        new.list == old.list.remove(removed),
        new.repr_perms == old.repr_perms.remove(removed),
        regions.slot_owners == old_regions.slot_owners,
    ensures
        take_current_pointer_state(old, old_regions, new, regions, removed, false, false),
{
    reveal(take_current_pointer_state);
    assert forall|p: int|
        #![trigger meta_to_index(old.list[p].paddr)]
        (0 <= p < old.list.len() && p != removed) implies ({
        let np = if p < removed {
            p
        } else {
            p - 1
        };
        let fp = new.meta_value_at(regions, np);
        &&& fp.next == old.meta_value_at(old_regions, p).next
        &&& fp.prev == old.meta_value_at(old_regions, p).prev
    }) by {
        lemma_linked_list_relate_region_at(old, old_regions, p);
        old.relate_region_at_facts(old_regions, p);
    }
}

#[verifier::spinoff_prover]
proof fn lemma_take_current_pointer_state_prev_vacuous<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    old: LinkedListOwner<M>,
    old_regions: MetaRegionOwners,
    new: LinkedListOwner<M>,
    regions: MetaRegionOwners,
    removed: int,
)
    requires
        removed == 0,
        take_current_pointer_state(old, old_regions, new, regions, removed, false, false),
    ensures
        take_current_pointer_state(old, old_regions, new, regions, removed, true, false),
{
    reveal(take_current_pointer_state);
}

#[verifier::spinoff_prover]
proof fn lemma_take_current_pointer_state_next_vacuous<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    old: LinkedListOwner<M>,
    old_regions: MetaRegionOwners,
    new: LinkedListOwner<M>,
    regions: MetaRegionOwners,
    removed: int,
)
    requires
        removed == old.list.len() - 1,
        take_current_pointer_state(old, old_regions, new, regions, removed, true, false),
    ensures
        take_current_pointer_state(old, old_regions, new, regions, removed, true, true),
{
    reveal(take_current_pointer_state);
}

#[verifier::spinoff_prover]
proof fn lemma_take_current_pointer_state_update<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    old: LinkedListOwner<M>,
    old_regions: MetaRegionOwners,
    before: LinkedListOwner<M>,
    before_regions: MetaRegionOwners,
    after: LinkedListOwner<M>,
    after_regions: MetaRegionOwners,
    removed: int,
    updated_old_pos: int,
    updated_pos: int,
    updated_idx: int,
    old_prev_done: bool,
    old_next_done: bool,
    new_prev_done: bool,
    new_next_done: bool,
)
    requires
        0 <= removed < old.list.len(),
        0 <= updated_old_pos < old.list.len(),
        old.relate_region(old_regions),
        take_current_pointer_state(
            old,
            old_regions,
            before,
            before_regions,
            removed,
            old_prev_done,
            old_next_done,
        ),
        take_current_local_ready(old, old_regions, before, before_regions, removed),
        take_current_local_ready(old, old_regions, after, after_regions, removed),
        before.list == old.list.remove(removed),
        before.repr_perms.len() == before.list.len(),
        0 <= updated_pos < before.list.len(),
        updated_old_pos != removed,
        updated_pos == if updated_old_pos < removed {
            updated_old_pos
        } else {
            updated_old_pos - 1
        },
        after.list == before.list,
        after.repr_perms.len() == after.list.len(),
        after.repr_perms == before.repr_perms.update(updated_pos, after.repr_perms[updated_pos]),
        after_regions.slot_owners == before_regions.slot_owners.insert(
            updated_idx,
            after_regions.slot_owners[updated_idx],
        ),
        updated_idx == meta_to_index(old.list[updated_old_pos].paddr),
        ({
            let fp = after.meta_value_at(after_regions, updated_pos);
            &&& (new_prev_done && updated_old_pos == removed - 1 ==> fp.next == old.meta_value_at(
                old_regions,
                removed,
            ).next)
            &&& (!(new_prev_done && updated_old_pos == removed - 1) ==> fp.next
                == old.meta_value_at(old_regions, updated_old_pos).next)
            &&& (new_next_done && updated_old_pos == removed + 1 ==> fp.prev == old.meta_value_at(
                old_regions,
                removed,
            ).prev)
            &&& (!(new_next_done && updated_old_pos == removed + 1) ==> fp.prev
                == old.meta_value_at(old_regions, updated_old_pos).prev)
        }),
        old_prev_done != new_prev_done ==> updated_old_pos == removed - 1,
        old_next_done != new_next_done ==> updated_old_pos == removed + 1,
    ensures
        take_current_pointer_state(
            old,
            old_regions,
            after,
            after_regions,
            removed,
            new_prev_done,
            new_next_done,
        ),
{
    reveal(take_current_pointer_state);
    reveal(take_current_local_ready);
    assert forall|p: int|
        #![trigger meta_to_index(old.list[p].paddr)]
        (0 <= p < old.list.len() && p != removed) implies ({
        let np = if p < removed {
            p
        } else {
            p - 1
        };
        let fp = after.meta_value_at(after_regions, np);
        &&& (new_prev_done && p == removed - 1 ==> fp.next == old.meta_value_at(
            old_regions,
            removed,
        ).next)
        &&& (!(new_prev_done && p == removed - 1) ==> fp.next == old.meta_value_at(
            old_regions,
            p,
        ).next)
        &&& (new_next_done && p == removed + 1 ==> fp.prev == old.meta_value_at(
            old_regions,
            removed,
        ).prev)
        &&& (!(new_next_done && p == removed + 1) ==> fp.prev == old.meta_value_at(
            old_regions,
            p,
        ).prev)
    }) by {
        let np = if p < removed {
            p
        } else {
            p - 1
        };
        if p != updated_old_pos {
            assert(np != updated_pos);
            assert(after.repr_perms[np] == before.repr_perms[np]);
            assert(meta_to_index(old.list[p].paddr) != updated_idx) by {
                let _ = old.list[p];
                let _ = old.list[updated_old_pos];
                reveal(LinkedListOwner::relate_region);
            };
            assert(after_regions.slot_owners[meta_to_index(old.list[p].paddr)]
                == before_regions.slot_owners[meta_to_index(old.list[p].paddr)]);
        }
    }
}

#[verifier::spinoff_prover]
proof fn lemma_take_current_local_ready_init<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    old: LinkedListOwner<M>,
    old_regions: MetaRegionOwners,
    new: LinkedListOwner<M>,
    regions: MetaRegionOwners,
    removed: int,
)
    requires
        0 <= removed < old.list.len(),
        old.relate_region(old_regions),
        new.list == old.list.remove(removed),
        new.repr_perms == old.repr_perms.remove(removed),
        new.list_id == old.list_id,
        regions.slots == old_regions.slots,
        regions.slot_owners == old_regions.slot_owners,
    ensures
        take_current_local_ready(old, old_regions, new, regions, removed),
{
    reveal(take_current_local_ready);
    assert forall|p: int|
        #![trigger meta_to_index(old.list[p].paddr)]
        (0 <= p < old.list.len() && p != removed) implies ({
        let i = meta_to_index(old.list[p].paddr);
        let np = if p < removed {
            p
        } else {
            p - 1
        };
        &&& regions.contains(i)
        &&& regions.slots[i].addr() == old.list[p].paddr
        &&& regions.slots[i].pptr() == old_regions.slots[i].pptr()
        &&& regions.slot_owners[i].inner_perms.ref_count.value() == REF_COUNT_UNIQUE
        &&& regions.slot_owners[i].usage is Frame
        &&& regions.slot_owners[i].inner_perms.in_list.value() == new.list_id
        &&& new.meta_wf_at(regions, np)
        &&& regions.slots[i].addr() % META_SLOT_SIZE == 0
        &&& FRAME_METADATA_RANGE.start <= regions.slots[i].addr() < FRAME_METADATA_RANGE.start
            + MAX_NR_PAGES * META_SLOT_SIZE
    }) by {
        lemma_linked_list_relate_region_at(old, old_regions, p);
        old.relate_region_at_facts(old_regions, p);
    }
}

#[verifier::spinoff_prover]
proof fn lemma_take_current_local_ready_update<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    old: LinkedListOwner<M>,
    old_regions: MetaRegionOwners,
    before: LinkedListOwner<M>,
    before_regions: MetaRegionOwners,
    after: LinkedListOwner<M>,
    after_regions: MetaRegionOwners,
    removed: int,
    updated_pos: int,
    updated_idx: int,
)
    requires
        0 <= removed < old.list.len(),
        old.relate_region(old_regions),
        take_current_local_ready(old, old_regions, before, before_regions, removed),
        0 <= updated_pos < before.list.len(),
        before.list == old.list.remove(removed),
        before.repr_perms.len() == before.list.len(),
        after.list == before.list,
        after.list_id == before.list_id,
        after.repr_perms.len() == after.list.len(),
        after.repr_perms == before.repr_perms.update(updated_pos, after.repr_perms[updated_pos]),
        after_regions.slots == before_regions.slots,
        after_regions.slot_owners == before_regions.slot_owners.insert(
            updated_idx,
            after_regions.slot_owners[updated_idx],
        ),
        updated_idx == meta_to_index(after.list[updated_pos].paddr),
        ({
            let i = updated_idx;
            &&& after_regions.contains(i)
            &&& after_regions.slots[i].addr() == after.list[updated_pos].paddr
            &&& after_regions.slots[i].pptr() == old_regions.slots[i].pptr()
            &&& after_regions.slot_owners[i].inner_perms.ref_count.value() == REF_COUNT_UNIQUE
            &&& after_regions.slot_owners[i].usage is Frame
            &&& after_regions.slot_owners[i].inner_perms.in_list.value() == after.list_id
            &&& after.meta_wf_at(after_regions, updated_pos)
            &&& after_regions.slots[i].addr() % META_SLOT_SIZE == 0
            &&& FRAME_METADATA_RANGE.start <= after_regions.slots[i].addr()
                < FRAME_METADATA_RANGE.start + MAX_NR_PAGES * META_SLOT_SIZE
        }),
    ensures
        take_current_local_ready(old, old_regions, after, after_regions, removed),
{
    reveal(take_current_local_ready);
    assert forall|p: int|
        #![trigger meta_to_index(old.list[p].paddr)]
        (0 <= p < old.list.len() && p != removed) implies ({
        let i = meta_to_index(old.list[p].paddr);
        let np = if p < removed {
            p
        } else {
            p - 1
        };
        &&& after_regions.contains(i)
        &&& after_regions.slots[i].addr() == old.list[p].paddr
        &&& after_regions.slots[i].pptr() == old_regions.slots[i].pptr()
        &&& after_regions.slot_owners[i].inner_perms.ref_count.value() == REF_COUNT_UNIQUE
        &&& after_regions.slot_owners[i].usage is Frame
        &&& after_regions.slot_owners[i].inner_perms.in_list.value() == after.list_id
        &&& after.meta_wf_at(after_regions, np)
        &&& after_regions.slots[i].addr() % META_SLOT_SIZE == 0
        &&& FRAME_METADATA_RANGE.start <= after_regions.slots[i].addr() < FRAME_METADATA_RANGE.start
            + MAX_NR_PAGES * META_SLOT_SIZE
    }) by {
        let np = if p < removed {
            p
        } else {
            p - 1
        };
        lemma_linked_list_relate_region_at(old, old_regions, p);
        old.relate_region_at_facts(old_regions, p);
        assert(0 <= np < before.list.len());
        assert(before.list[np] == old.list[p]);
        assert(after.list[np] == old.list[p]);
        if np == updated_pos {
            assert(meta_to_index(old.list[p].paddr) == updated_idx);
        } else {
            assert(after.list[np] == before.list[np]);
            assert(after.repr_perms[np] == before.repr_perms[np]);
            assert(meta_to_index(old.list[p].paddr) != updated_idx);
            assert(after_regions.slot_owners[meta_to_index(old.list[p].paddr)]
                == before_regions.slot_owners[meta_to_index(old.list[p].paddr)]);
        }
    }
}

#[verifier::opaque]
spec fn take_current_pop_ready<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    old: LinkedListOwner<M>,
    old_regions: MetaRegionOwners,
    new: LinkedListOwner<M>,
    regions: MetaRegionOwners,
    removed: int,
    removed_idx: int,
) -> bool {
    &&& removed_idx == meta_to_index(old.list[removed].paddr)
    &&& forall|p: int|
        #![trigger meta_to_index(old.list[p].paddr)]
        (0 <= p < old.list.len() && p != removed) ==> ({
            let i = meta_to_index(old.list[p].paddr);
            let np = if p < removed {
                p
            } else {
                p - 1
            };
            let fp = new.meta_value_at(regions, np);
            &&& regions.contains(i)
            &&& regions.slots[i].addr() == old.list[p].paddr
            &&& regions.slots[i].pptr() == old_regions.slots[i].pptr()
            &&& regions.slot_owners[i].inner_perms.ref_count.value() == REF_COUNT_UNIQUE
            &&& regions.slot_owners[i].usage is Frame
            &&& regions.slot_owners[i].inner_perms.in_list.value() == new.list_id
            &&& new.meta_wf_at(regions, np)
            &&& regions.slots[i].addr() % META_SLOT_SIZE == 0
            &&& FRAME_METADATA_RANGE.start <= regions.slots[i].addr() < FRAME_METADATA_RANGE.start
                + MAX_NR_PAGES * META_SLOT_SIZE
            &&& (p == removed - 1 ==> fp.next == old.meta_value_at(old_regions, removed).next)
            &&& (p != removed - 1 ==> fp.next == old.meta_value_at(old_regions, p).next)
            &&& (p == removed + 1 ==> fp.prev == old.meta_value_at(old_regions, removed).prev)
            &&& (p != removed + 1 ==> fp.prev == old.meta_value_at(old_regions, p).prev)
        })
}

#[verifier::spinoff_prover]
proof fn lemma_take_current_pop_ready_from_parts<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    old: LinkedListOwner<M>,
    old_regions: MetaRegionOwners,
    new: LinkedListOwner<M>,
    regions: MetaRegionOwners,
    removed: int,
    removed_idx: int,
)
    requires
        removed_idx == meta_to_index(old.list[removed].paddr),
        take_current_local_ready(old, old_regions, new, regions, removed),
        take_current_pointer_state(old, old_regions, new, regions, removed, true, true),
    ensures
        take_current_pop_ready(old, old_regions, new, regions, removed, removed_idx),
{
    reveal(take_current_pop_ready);
    reveal(take_current_local_ready);
    reveal(take_current_pointer_state);
}

#[verifier::spinoff_prover]
proof fn lemma_take_current_pop_preserves_relate_region<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    old: LinkedListOwner<M>,
    old_regions: MetaRegionOwners,
    new: LinkedListOwner<M>,
    regions: MetaRegionOwners,
    removed: int,
    removed_idx: int,
)
    requires
        0 <= removed < old.list.len(),
        old.relate_region(old_regions),
        new.list == old.list.remove(removed),
        new.repr_perms.len() == new.list.len(),
        new.list_id == old.list_id,
        take_current_pop_ready(old, old_regions, new, regions, removed, removed_idx),
    ensures
        new.relate_region(regions),
{
    reveal(take_current_pop_ready);
    LinkedListOwner::pop_preserves_relate_region(old, old_regions, new, regions, removed);
}

#[verifier::spinoff_prover]
/// Collects the relation facts for the current link and its two neighbors.
proof fn lemma_take_current_setup<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    owner0: CursorOwner<M>,
    regions0: MetaRegionOwners,
)
    requires
        owner0.wf_with_region(regions0),
        0 <= owner0.index < owner0.list_own.list.len(),
    ensures
        owner0.list_own.relate_region(regions0),
        owner0.list_own.repr_perms.len() == owner0.list_own.list.len(),
        owner0.list_own.relate_region_at(regions0, owner0.index),
        owner0.index > 0 ==> owner0.list_own.relate_region_at(regions0, owner0.index - 1),
        owner0.index < owner0.list_own.list.len() - 1 ==> owner0.list_own.relate_region_at(
            regions0,
            owner0.index + 1,
        ),
{
    reveal(CursorOwner::wf_with_region);
    assert(owner0.list_own.relate_region(regions0));
    lemma_linked_list_relate_region_at(owner0.list_own, regions0, owner0.index);
    if owner0.index > 0 {
        lemma_linked_list_relate_region_at(owner0.list_own, regions0, owner0.index - 1);
    }
    if owner0.index < owner0.list_own.list.len() - 1 {
        lemma_linked_list_relate_region_at(owner0.list_own, regions0, owner0.index + 1);
    }
}

#[verus_spec(
    with Tracked(owner): Tracked<&mut UniqueFrameOwner<Link<M>>>,
        Tracked(regions): Tracked<&mut MetaRegionOwners>
)]
#[verifier::spinoff_prover]
fn clear_take_current_links<M: AnyFrameMeta + Repr<MetaSlotSmall>>(frame: &mut UniqueFrame<Link<M>>)
    requires
        old(owner).inv(),
        old(frame).wf(*old(owner)),
        old(regions).inv(),
        old(owner).global_inv(*old(regions)),
    ensures
        *final(frame) == *old(frame),
        final(owner).meta_own == old(owner).meta_own,
        final(owner).slot_index == old(owner).slot_index,
        final(owner).inv(),
        final(owner).meta_wf(*final(regions)),
        final(frame).wf(*final(owner)),
        final(regions).inv(),
        final(owner).global_inv(*final(regions)),
        final(owner).meta_value(*final(regions)).next is None,
        final(owner).meta_value(*final(regions)).prev is None,
        final(regions).slots == old(regions).slots,
        final(regions).slots.dom() == old(regions).slots.dom(),
        final(regions).slot_owners.dom() == old(regions).slot_owners.dom(),
        final(regions).slot_owners[final(owner).slot_index].slot_vaddr == old(
            regions,
        ).slot_owners[old(owner).slot_index].slot_vaddr,
        final(regions).slot_owners[final(owner).slot_index].usage == old(regions).slot_owners[old(
            owner,
        ).slot_index].usage,
        final(regions).slot_owners[final(owner).slot_index].inner_perms.ref_count == old(
            regions,
        ).slot_owners[old(owner).slot_index].inner_perms.ref_count,
        final(regions).slot_owners[final(owner).slot_index].inner_perms.in_list == old(
            regions,
        ).slot_owners[old(owner).slot_index].inner_perms.in_list,
        final(regions).slot_owners[final(owner).slot_index].paths_in_pt == old(
            regions,
        ).slot_owners[old(owner).slot_index].paths_in_pt,
        final(regions).frame_obligations == old(regions).frame_obligations,
        take_current_regions_preserved(*final(regions), *old(regions), old(owner).slot_index),
        take_current_regions_unchanged_except(
            *final(regions),
            *old(regions),
            old(owner).slot_index,
        ),
{
    let ghost regions0 = *regions;
    let ghost idx = owner.slot_index;
    proof {
        lemma_take_current_regions_preserved_init(*regions, regions0, idx);
    }

    let ghost regions_before_next = *regions;
    (#[verus_spec(with Tracked(owner), Tracked(regions))]
    frame.meta_mut()).next = None;
    proof {
        lemma_take_current_regions_preserved_update(
            regions_before_next,
            *regions,
            regions0,
            idx,
            idx,
        );
    }

    let ghost regions_before_prev = *regions;
    (#[verus_spec(with Tracked(owner), Tracked(regions))]
    frame.meta_mut()).prev = None;
    proof {
        lemma_take_current_regions_preserved_update(
            regions_before_prev,
            *regions,
            regions0,
            idx,
            idx,
        );
        assert(owner.global_inv(*regions)) by {
            reveal(UniqueFrameOwner::global_inv);
        };
        assert(take_current_regions_unchanged_except(*regions, regions0, idx)) by {
            reveal(take_current_regions_unchanged_except);
        };
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> LinkedList<M> {
    /// Creates a new linked list.
    pub const fn new() -> Self {
        Self { front: None, back: None, size: 0, list_id: 0 }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> Default for LinkedList<M> {
    fn default() -> Self {
        Self::new()
    }
}

#[verus_verify]
impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> LinkedList<M> {
    /// Gets the number of frames in the linked list.
    #[verus_spec(s =>
        with
            Tracked(owner): Tracked<LinkedListOwner<M>>,
        requires
            self.wf(owner),
            owner.inv(),
        ensures
            s == owner@.list.len(),
    )]
    pub fn size(&self) -> usize {
        proof {
            LinkedListOwner::<M>::view_preserves_len(owner.list);
        }
        self.size
    }

    /// Tells if the linked list is empty.
    #[verus_spec(b =>
        with
            Tracked(owner): Tracked<LinkedListOwner<M>>,
        requires
            self.wf(owner),
            owner.inv(),
        ensures
            b ==> self.size == 0 && self.front is None && self.back is None,
            !b ==> self.size > 0 && self.front is Some && self.back is Some,
    )]
    pub fn is_empty(&self) -> bool {
        let is_empty = self.size == 0;
        is_empty
    }

    /// Pushes a frame to the front of the linked list.
    /// # Verified Properties
    /// ## Preconditions
    /// The list must be well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects. The new frame must be active, so that it is
    /// valid to call `into_raw` on it inside of `insert_before`.
    /// ## Postconditions
    /// The new frame is inserted at the front of the list, and the cursor is moved to the new frame.
    /// The list invariants are preserved.
    /// ## Safety
    /// See [`insert_before`] for the safety guarantees.
    #[verus_spec(
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(owner): Tracked<&mut LinkedListOwner<M>>,
            Tracked(frame_own): Tracked<&mut UniqueFrameOwner<Link<M>>>,
        requires
            old(self).wf_region(*old(owner), *old(regions)),
            old(owner).relate_region(*old(regions)),
            old(frame_own).inv(),
            old(frame_own).global_inv(*old(regions)),
            frame.wf(*old(frame_own)),
            old(frame_own).frame_link_inv(*old(regions)),
            old(regions).inv(),
        ensures
            final(owner).relate_region(*final(regions)),
            final(regions).inv(),
            final(owner).list == old(owner).list.insert(0, final(frame_own).meta_own),
            old(owner).list_id != 0 ==> final(owner).list_id == old(owner).list_id,
            final(owner).list_id != 0,
            final(frame_own).meta_own.paddr == old(frame_own).meta_own.paddr,
            final(frame_own).meta_own.in_list == final(owner).list_id,
    )]
    pub fn push_front(&mut self, frame: UniqueFrame<Link<M>>) {
        let current = self.front;
        let tracked owner0 = LinkedListOwner::tracked_take(owner);
        let tracked mut cursor_own = CursorOwner::tracked_front_owner(owner0);
        let mut cursor = CursorMut { list: self, current };

        #[verus_spec(with Tracked(regions), Tracked(&mut cursor_own), Tracked(frame_own))]
        cursor.insert_before(frame);

        proof {
            *owner = cursor_own.list_own;
        }
    }

    /// Pops a frame from the front of the linked list.
    /// # Verified Properties
    /// ## Preconditions
    /// The list must be well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects. The list must be non-empty, so that the
    /// current frame is valid.
    /// ## Postconditions
    /// The front frame is removed from the list, and the cursor is moved to the next frame.
    /// The list invariants are preserved.
    /// ## Safety
    /// See [`take_current`] for the safety guarantees.
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(owner): Tracked<LinkedListOwner<M>>,
            Tracked(frame_own): Tracked<UniqueFrameOwner<Link<M>>>,
        requires
            old(regions).inv(),
            old(self).wf_region(owner, *old(regions)),
            owner.relate_region(*old(regions)),
        ensures
            owner.list.len() == 0 ==> r.is_none(),
            r.is_some() ==> (r->0).1@@.meta == owner.list[0]@,
            r.is_some() ==> (r->0).1@.frame_link_inv(*final(regions)),
    )]
    pub fn pop_front(&mut self) -> Option<
        (UniqueFrame<Link<M>>, Tracked<UniqueFrameOwner<Link<M>>>),
    > {
        let tracked mut cursor_own = CursorOwner::tracked_front_owner(owner);
        let current = self.front;
        let mut cursor = CursorMut { list: self, current };

        proof {
            if owner.list.len() > 0 {
                owner.relate_region_at_facts(*regions, 0);
            }
        }

        #[verus_spec(with Tracked(regions), Tracked(&mut cursor_own))]
        cursor.take_current()
    }

    /// Pushes a frame to the back of the linked list.
    /// # Verified Properties
    /// ## Preconditions
    /// The list must be well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects. The new frame must be active, so that it is
    /// valid to call `into_raw` on it inside of `insert_before`.
    /// ## Postconditions
    /// - The new frame is inserted at the back of the list, and the cursor is moved to the new frame.
    /// - The list invariants are preserved.
    /// ## Safety
    /// See [`insert_before`] for the safety guarantees.
    #[verus_spec(
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(owner): Tracked<&mut LinkedListOwner<M>>,
            Tracked(frame_own): Tracked<&mut UniqueFrameOwner<Link<M>>>,
        requires
            old(self).wf_region(*old(owner), *old(regions)),
            old(owner).relate_region(*old(regions)),
            old(frame_own).inv(),
            old(frame_own).global_inv(*old(regions)),
            frame.wf(*old(frame_own)),
            old(frame_own).frame_link_inv(*old(regions)),
            old(regions).inv(),
        ensures
            final(owner).relate_region(*final(regions)),
            final(regions).inv(),
            old(owner).list.len() > 0 ==> final(owner).list == old(owner).list.insert(
                old(owner).list.len() - 1, final(frame_own).meta_own),
            old(owner).list.len() == 0 ==> final(owner).list == old(owner).list.insert(
                0, final(frame_own).meta_own),
            // Id preserved when already minted; a fresh (empty) list adopts a
            // non-zero id.
            old(owner).list_id != 0 ==> final(owner).list_id == old(owner).list_id,
            final(owner).list_id != 0,
            final(frame_own).meta_own.paddr == old(frame_own).meta_own.paddr,
            final(frame_own).meta_own.in_list == final(owner).list_id,
    )]
    pub fn push_back(&mut self, frame: UniqueFrame<Link<M>>) {
        let current = self.back;
        let tracked mut cursor_own = CursorOwner::tracked_back_owner(*owner);
        let mut cursor = CursorMut { list: self, current };

        #[verus_spec(with Tracked(regions), Tracked(&mut cursor_own), Tracked(frame_own))]
        cursor.insert_before(frame);

        proof {
            *owner = cursor_own.list_own;
        }
    }

    /// Pops a frame from the back of the linked list.
    /// # Verified Properties
    /// ## Preconditions
    /// - The list must be well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects.
    /// - The list must be non-empty, so that the
    /// current frame is valid.
    /// ## Postconditions
    /// - The back frame is removed from the list, and the cursor is moved to the "ghost" non-element.
    /// - The list invariants are preserved.
    /// ## Safety
    /// See [`take_current`] for the safety guarantees.
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(owner): Tracked<LinkedListOwner<M>>,
            Tracked(frame_own): Tracked<UniqueFrameOwner<Link<M>>>,
        requires
            old(regions).inv(),
            old(self).wf_region(owner, *old(regions)),
            owner.relate_region(*old(regions)),
        ensures
            owner.list.len() == 0 ==> r.is_none(),
            r.is_some() ==> (r->0).1@@.meta == owner.list[owner.list.len() - 1]@,
            r.is_some() ==> (r->0).1@.frame_link_inv(*final(regions)),
    )]
    pub fn pop_back(&mut self) -> Option<
        (UniqueFrame<Link<M>>, Tracked<UniqueFrameOwner<Link<M>>>),
    > {
        let current = self.back;
        let tracked mut cursor_own = CursorOwner::tracked_back_owner(owner);
        let mut cursor = CursorMut { list: self, current };

        proof {
            if owner.list.len() > 0 {
                owner.relate_region_at_facts(*regions, owner.list.len() - 1);
            }
        }

        #[verus_spec(with Tracked(regions), Tracked(&mut cursor_own))]
        cursor.take_current()
    }

    /// Tells if a frame is in the list.
    /// # Verified Properties
    /// ## Preconditions
    /// - The list must be well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects.
    /// - The frame must be a valid, active frame.
    /// ## Postconditions
    /// The function returns `true` if the frame is in the list, `false` otherwise.
    /// ## Safety
    /// - `lazy_get_id` uses atomic memory accesses, so there are no data races.
    /// - We assume that the ID allocator has an available ID if the list previously didn't have one,
    /// but the consequence if that is not the case is a failsafe panic.
    /// - Everything else conforms to the safe interface.
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(slot_own): Tracked<&MetaSlotOwner>,
            Tracked(owner): Tracked<&mut LinkedListOwner<M>>,
        requires
            slot_own.inv(),
            old(regions).inv(),
        ensures
            old(owner).list_id != 0 ==> *final(owner) == *old(owner),
    )]
    pub fn contains(&mut self, frame: Paddr) -> bool {
        proof_decl! {
        let ghost idx = frame_to_index(frame);
            if valid_frame_paddr(frame) {
                regions.inv_implies_correct_addr(frame);
            }
        let tracked slot_perm = if valid_frame_paddr(frame) {
            Some(*regions.slots.tracked_borrow(idx))
        } else {
            None
        };
        }
        let Ok(slot) = (#[verus_spec(with Tracked(slot_perm))]
        crate::mm::frame::meta::get_slot(frame)) else {
            return false;
        };

        let tracked mut slot_own = regions.slot_owners.tracked_borrow_mut(idx);

        let tracked mut inner_perms = slot_own.tracked_borrow_mut_inner_perms();

        slot.in_list.load(Tracked(&mut inner_perms.in_list)) == #[verus_spec(with Tracked(owner))]
        self.lazy_get_id()
    }

    /// Gets a cursor at the specified frame if the frame is in the list.
    ///
    /// This method fails if the frame is not in the list.
    /// # Verified Properties
    /// ## Preconditions
    /// - The list must be well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects.
    /// - The frame should be raw (because it is owned by the list)
    /// ## Postconditions
    /// - This functions post-conditions are incomplete due to refactoring of the permission model.
    /// When complete, it will guarantee that the cursor is well-formed and points to the matching
    /// element in the list.
    /// ## Safety
    /// - `lazy_get_id` uses atomic memory accesses, so there are no data races.
    /// - We assume that the ID allocator has an available ID if the list previously didn't have one,
    /// but the consequence if that is not the case is a failsafe panic.
    /// - Everything else conforms to the safe interface.
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(owner): Tracked<LinkedListOwner<M>>,
            -> cursor_owner: Tracked<Option<CursorOwner<M>>>,
        requires
            old(regions).inv(),
        ensures
            !valid_frame_paddr(frame) ==> r is None,
            final(regions).inv(),
            final(regions).slots == old(regions).slots,
            final(regions).slot_owners.dom() == old(regions).slot_owners.dom(),
    )]
    pub fn cursor_mut_at(&mut self, frame: Paddr) -> Option<CursorMut<'_, M>> {
        proof_decl! {
            let ghost idx = frame_to_index(frame);
            if valid_frame_paddr(frame) {
                regions.inv_implies_correct_addr(frame);
            }

            let tracked slot_perm = if valid_frame_paddr(frame) {
                Some(*regions.slots.tracked_borrow(idx))
            } else {
                None
            };
        }
        let Ok(slot) = (#[verus_spec(with Tracked(slot_perm))]
        crate::mm::frame::meta::get_slot(frame)) else {
            return {
                proof_with!(|= Tracked(None));
                None
            };
        };

        let tracked mut slot_own = regions.slot_owners.tracked_borrow_mut(idx);
        let tracked mut inner_perms = slot_own.tracked_borrow_mut_inner_perms();

        let contains = slot.in_list.load(Tracked(&mut inner_perms.in_list))
            == #[verus_spec(with Tracked(&owner))]
        self.lazy_get_id();

        if contains {
            proof_decl!{
                let ghost link = owner.list.filter(|link: LinkOwner| link.paddr == frame).first();
                let ghost index = owner.list.index_of(link);
                let tracked cursor_owner = CursorOwner::tracked_cursor_mut_at_owner(owner, index);
            }

            let meta_ptr = ReprPtr::<MetaSlotStorage, Link<M>>::from_pptr(
                PPtr::<MetaSlotStorage>::from_addr(frame_to_meta(frame)),
            );
            proof_with!(|= Tracked(Some(cursor_owner)));
            Some(CursorMut { list: self, current: Some(meta_ptr) })
        } else {
            proof_with!(|= Tracked(None));
            None
        }
    }

    /// Gets a cursor at the front that can mutate the linked list links.
    ///
    /// If the list is empty, the cursor points to the "ghost" non-element.
    /// # Verified Properties
    /// ## Preconditions
    /// - The list must be well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects.
    /// ## Postconditions
    /// - The cursor is well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects. The list invariants are preserved.
    /// - See [`CursorOwner::front_owner`] for the precise specification.
    /// ## Safety
    /// - This function only uses the list permission, so there are no illegal memory accesses.
    /// - No data races are possible.
    #[verus_spec(r =>
        with
            Tracked(owner): Tracked<LinkedListOwner<M>>,
        requires
            old(self).wf(owner),
            owner.inv(),
        ensures
            r.0.wf(r.1@),
            r.1@.inv(),
            r.1@ == CursorOwner::front_owner(owner),
    )]
    pub fn cursor_front_mut(&mut self) -> (CursorMut<'_, M>, Tracked<CursorOwner<M>>) {
        let current = self.front;

        (CursorMut { list: self, current }, Tracked(CursorOwner::tracked_front_owner(owner)))
    }

    /// Gets a cursor at the back that can mutate the linked list links.
    ///
    /// If the list is empty, the cursor points to the "ghost" non-element.
    /// # Verified Properties
    /// ## Preconditions
    /// - The list must be well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects.
    /// ## Postconditions
    /// - The cursor is well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects. The list invariants are preserved.
    /// See [`CursorOwner::back_owner`] for the precise specification.
    /// ## Safety
    /// - This function only uses the list permission, so there are no illegal memory accesses.
    /// - No data races are possible.
    #[verus_spec(
        with
            Tracked(owner): Tracked<LinkedListOwner<M>>,
    )]
    pub fn cursor_back_mut(&mut self) -> (res: (CursorMut<'_, M>, Tracked<CursorOwner<M>>))
        requires
            old(self).wf(owner),
            owner.inv(),
        ensures
            res.0.wf(res.1@),
            res.1@.inv(),
            res.1@ == CursorOwner::back_owner(owner),
    {
        let current = self.back;

        (CursorMut { list: self, current }, Tracked(CursorOwner::tracked_back_owner(owner)))
    }

    /// Gets a cursor at the "ghost" non-element that can mutate the linked list links.
    #[verus_spec(
        with Tracked(owner): Tracked<&mut LinkedListOwner<M>>
    )]
    fn cursor_at_ghost_mut(&mut self) -> CursorMut<'_, M> {
        CursorMut { list: self, current: None }
    }

    /// # Verification Assumption
    /// We assume that there is an available ID for `lazy_get_id` to return.
    /// This is safe because it will panic if the ID allocator is exhausted.
    #[verifier::external_body]
    #[verus_spec(
        with Tracked(owner): Tracked<& LinkedListOwner<M>>
    )]
    fn lazy_get_id(&mut self) -> (id: u64)
        ensures
            owner.list_id != 0 ==> id == owner.list_id,
            final(self).size == old(self).size,
            final(self).front == old(self).front,
            final(self).back == old(self).back,
            old(self).list_id != 0 ==> final(self).list_id == old(self).list_id,
            id != 0,
            final(self).list_id == id,
    {
        unimplemented!()/*        // FIXME: Self-incrementing IDs may overflow, while `core::pin::Pin`
        // is not compatible with locks. Think about a better solution.
        static LIST_ID_ALLOCATOR: AtomicU64 = AtomicU64::new(1);
        const MAX_LIST_ID: u64 = i64::MAX as u64;

        if self.list_id == 0 {
            let id = LIST_ID_ALLOCATOR.fetch_add(1, Ordering::Relaxed);
            if id >= MAX_LIST_ID {
//                log::error!("The frame list ID allocator has exhausted.");
//                abort();
                unimplemented!()
            }
            self.list_id = id;
            id
        } else {
            self.list_id
        }*/

    }
}

impl<'a, M: AnyFrameMeta + Repr<MetaSlotSmall>> CursorMut<'a, M> {
    /// Moves the cursor to the next frame towards the back.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this will
    /// move it to the first element of the [`LinkedList`]. If it is pointing
    /// to the last element of the LinkedList then this will move it to the
    /// "ghost" non-element.
    #[verus_spec(
        with Tracked(owner): Tracked<CursorOwner<M>>,
            Tracked(regions): Tracked<&MetaRegionOwners>,
    )]
    pub fn move_next(&mut self)
        requires
            owner.wf_with_region(*regions),
            old(self).wf_region(owner, *regions),
        ensures
            owner.move_next_owner_spec()@ == owner@.move_next_spec(),
            owner.move_next_owner_spec().wf_with_region(*regions),
            final(self).wf_region(owner.move_next_owner_spec(), *regions),
    {
        proof {
            if self.current is Some {
                owner.list_own.relate_region_at_facts(*regions, owner.index);
            }
            if owner.index < owner.length() - 1 {
                owner.list_own.relate_region_at_facts(*regions, owner.index + 1);
            }
        }

        self.current = match self.current {
            // SAFETY: The cursor is pointing to a valid element.
            Some(current) => {
                proof_decl!{
                    let ghost idx = meta_to_index(current.addr());
                    let tracked points_to = regions.slots.tracked_borrow(idx);
                    let tracked slot_owner = regions.slot_owners.tracked_borrow(idx);
                    let tracked repr_perm = owner.list_own.repr_perms.tracked_borrow(owner.index);
                }
                proof {
                    assert(regions.contains(idx));
                }
                let link = borrow_meta(
                    current,
                    Tracked(points_to),
                    Tracked(&slot_owner.inner_perms.storage),
                    Tracked(repr_perm),
                );
                link.next
            },
            None => self.list.front,
        };

        proof {
            LinkedListOwner::<M>::view_preserves_len(owner.list_own.list);
            assert(owner.move_next_owner_spec()@.fore == owner@.move_next_spec().fore);
            assert(owner.move_next_owner_spec()@.rear == owner@.move_next_spec().rear);
        }
    }

    /// Moves the cursor to the previous frame towards the front.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this will
    /// move it to the last element of the [`LinkedList`]. If it is pointing
    /// to the first element of the LinkedList then this will move it to the
    /// "ghost" non-element.
    #[verus_spec(
        with Tracked(owner): Tracked<CursorOwner<M>>,
            Tracked(regions): Tracked<&MetaRegionOwners>,
    )]
    pub fn move_prev(&mut self)
        requires
            owner.wf_with_region(*regions),
            old(self).wf_region(owner, *regions),
        ensures
            owner.move_prev_owner_spec()@ == owner@.move_prev_spec(),
            owner.move_prev_owner_spec().wf_with_region(*regions),
            final(self).wf_region(owner.move_prev_owner_spec(), *regions),
    {
        proof {
            if self.current is Some {
                owner.list_own.relate_region_at_facts(*regions, owner.index);
            }
            if 0 < owner.index {
                owner.list_own.relate_region_at_facts(*regions, owner.index - 1);
            }
        }

        self.current = match self.current {
            // SAFETY: The cursor is pointing to a valid element.
            Some(current) => {
                proof_decl!{
                    let ghost idx = meta_to_index(current.addr());
                    let tracked points_to = regions.slots.tracked_borrow(idx);
                    let tracked slot_owner = regions.slot_owners.tracked_borrow(idx);
                    let tracked repr_perm = owner.list_own.repr_perms.tracked_borrow(owner.index);
                }
                proof {
                    assert(regions.contains(idx));
                }

                let link = borrow_meta(
                    current,
                    Tracked(points_to),
                    Tracked(&slot_owner.inner_perms.storage),
                    Tracked(repr_perm),
                );
                link.prev
            },
            None => self.list.back,
        };

        proof {
            LinkedListOwner::<M>::view_preserves_len(owner.list_own.list);

            if owner@.list_model.list.len() > 0 {
                if owner@.fore.len() > 0 {
                    assert(owner.move_prev_owner_spec()@.fore == owner@.move_prev_spec().fore);
                    assert(owner.move_prev_owner_spec()@.rear == owner@.move_prev_spec().rear);
                    if owner@.rear.len() > 0 {
                        owner.list_own.relate_region_at_facts(*regions, owner.index);
                    }
                } else {
                    owner.list_own.relate_region_at_facts(*regions, owner.index);
                    assert(owner.move_prev_owner_spec()@.rear == owner@.move_prev_spec().rear);
                    assert(owner@.rear == owner@.list_model.list);
                }
            }
        }
    }

    /// Gets the mutable reference to the current frame's metadata.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// The cursor must be well-formed with respect to the tracked `CursorOwner`.
    /// ## Postconditions
    /// If the cursor is on an element, returns `Some(&mut meta)` borrowing the
    /// current link's metadata. The cursor state and list shape are otherwise
    /// unchanged; the current metadata permission remains borrowed while the
    /// returned reference is live.
    /// ## Safety
    /// The `&mut self` guarantees exclusive access to the cursor; the tracked
    /// `CursorOwner` guarantees the perm for the current link is live.
    #[verus_spec(
        with Tracked(owner): Tracked<&'b mut CursorOwner<M>>,
            Tracked(regions): Tracked<&'b mut MetaRegionOwners>,
    )]
    pub fn current_meta<'b>(&'b mut self) -> (res: Option<&'b mut M>)
        requires
            old(self).wf_region(*old(owner), *old(regions)),
            old(owner).wf_with_region(*old(regions)),
            old(regions).inv(),
        ensures
            final(owner).index == old(owner).index,
            final(owner).list_own.list == old(owner).list_own.list,
            final(owner).list_own.list_id == old(owner).list_own.list_id,
            *final(self) == *old(self),
            res.is_some() == (0 <= final(owner).index < final(owner).length()),
            final(regions).slots.dom() == old(regions).slots.dom(),
            final(regions).slot_owners.dom() == old(regions).slot_owners.dom(),
    {
        // Verus does not support option.map very well.
        // self.current.map(|current| {
        //     let link_mut = unsafe { &mut *(current.ptr.addr() as *mut Link<M>) };
        //     &mut link_mut.meta
        // })
        match self.current {
            Some(current) => {
                proof {
                    owner.list_own.relate_region_at_facts(*regions, owner.index);
                }
                let ghost idx = meta_to_index(current.addr());
                proof {
                    assert(regions.contains(idx));
                }
                let tracked points_to = regions.slots.tracked_borrow(idx);
                let tracked slot_owner = regions.slot_owners.tracked_borrow_mut(idx);
                let tracked repr_perm = owner.list_own.repr_perms.tracked_borrow_mut(owner.index);
                Some(
                    &mut borrow_meta_mut(
                        current,
                        Tracked(points_to),
                        Tracked(slot_owner),
                        Tracked(repr_perm),
                    ).meta,
                )
            },
            None => None,
        }
    }

    /// Takes the current pointing frame out of the linked list.
    ///
    /// If successful, the frame is returned and the cursor is moved to the
    /// next frame. If the cursor is pointing to the back of the list then it
    /// is moved to the "ghost" non-element.
    /// # Verified Properties
    /// ## Preconditions
    /// The cursor must be well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects. The list must be non-empty, so that the
    /// current frame is valid.
    /// ## Postconditions
    /// The current frame is removed from the list, and the cursor is moved to the next frame.
    /// The list invariants are preserved.
    /// ## Safety
    /// This function calls `from_raw` on the frame, but we guarantee that the frame is forgotten
    /// if it is in the list. So, double-free will not occur. All loads and stores are through track
    /// tracked permissions, so there are no illegal memory accesses. No data races are possible.
    #[verus_spec(
        with Tracked(regions) : Tracked<&mut MetaRegionOwners>,
            Tracked(owner) : Tracked<&mut CursorOwner<M>>
    )]
    #[verifier::spinoff_prover]
    pub fn take_current(&mut self) -> (res: Option<
        (UniqueFrame<Link<M>>, Tracked<UniqueFrameOwner<Link<M>>>),
    >)
        requires
            old(self).wf_region(*old(owner), *old(regions)),
            old(owner).wf_with_region(*old(regions)),
            old(regions).inv(),
        ensures
            old(owner).length() == 0 ==> res.is_none(),
            old(self).current.is_some() ==> res.is_some(),
            res.is_some() ==> (res->0).1@@.meta == old(owner).list_own.list[old(owner).index]@,
            res.is_some() ==> final(owner)@ == old(owner)@.remove(),
            res.is_some() ==> (res->0).1@.frame_link_inv(*final(regions)),
            // Invariant preservation
            res.is_some() ==> final(owner).wf_with_region(*final(regions)),
            res.is_some() ==> final(self).wf_region(*final(owner), *final(regions)),
            res.is_none() ==> *final(owner) == *old(owner),
            final(regions).inv(),
            // Structural: remove_owner_spec
            res.is_some() ==> final(owner).index == old(owner).index,
            res.is_some() ==> final(owner).list_own.list == old(owner).list_own.list.remove(
                old(owner).index,
            ),
            final(owner).list_own.list_id == old(owner).list_own.list_id,
            res.is_some() ==> {
                let paddr = old(self).current->0.addr();
                let idx = meta_to_index(paddr);
                &&& final(regions).slots.dom() == old(regions).slots.dom()
                &&& final(regions).slot_owners[idx].inner_perms.ref_count.value()
                    == REF_COUNT_UNIQUE
                &&& final(regions).slot_owners[idx].inner_perms.in_list.value() == 0
                &&& final(regions).slot_owners[idx].inner_perms.storage.is_init()
                &&& final(regions).slot_owners[idx].inner_perms.vtable_ptr.is_init()
                &&& final(regions).slot_owners[idx].slot_vaddr == index_to_meta(idx)
                &&& final(regions).slot_owners[idx].paths_in_pt == old(
                    regions,
                ).slot_owners[idx].paths_in_pt
            },
            res.is_some() ==> forall|j: int|
                #![trigger final(regions).slot_owners[j]]
                j != meta_to_index(old(self).current->0.addr()) ==> {
                    &&& final(regions).slot_owners[j].usage == old(regions).slot_owners[j].usage
                    &&& final(regions).slot_owners[j].slot_vaddr == old(
                        regions,
                    ).slot_owners[j].slot_vaddr
                    &&& final(regions).slot_owners[j].paths_in_pt == old(
                        regions,
                    ).slot_owners[j].paths_in_pt
                },
            res.is_none() ==> *final(regions) == *old(regions),
            // Properties of the returned frame needed for UniqueFrame::drop
            res.is_some() ==> (res->0).0.wf((res->0).1@),
            res.is_some() ==> (res->0).1@.inv(),
            res.is_some() ==> (res->0).1@.slot_index == meta_to_index(old(self).current->0.addr()),
            res.is_some() ==> (res->0).0.ptr.addr() == old(self).current->0.addr(),
            res.is_some() ==> final(regions).frame_obligations == old(
                regions,
            ).frame_obligations.insert(meta_to_index(old(self).current->0.addr())),
    {
        hide(LinkedListOwner::relate_region);
        hide(<MetaRegionOwners as Inv>::inv);
        let ghost owner0 = *owner;
        let ghost regions0 = *regions;

        let current = self.current?;

        proof {
            assert(0 <= owner.index < owner.list_own.list.len());
            lemma_take_current_setup(*owner, *regions);
            owner.list_own.relate_region_at_facts(*regions, owner.index);
            lemma_meta_region_inv_at(
                regions0,
                meta_to_index(owner0.list_own.list[owner0.index].paddr),
            );
            if owner.index > 0 {
                owner.list_own.relate_region_at_facts(*regions, owner.index - 1);
                lemma_meta_region_inv_at(
                    regions0,
                    meta_to_index(owner0.list_own.list[owner0.index - 1].paddr),
                );
            }
            if owner.index < owner.list_own.list.len() - 1 {
                owner.list_own.relate_region_at_facts(*regions, owner.index + 1);
                lemma_meta_region_inv_at(
                    regions0,
                    meta_to_index(owner0.list_own.list[owner0.index + 1].paddr),
                );
            }
        }

        let meta_ptr = current.addr();
        let paddr = meta_to_frame(meta_ptr);
        let ghost idx = frame_to_index(paddr);

        let tracked mut cur_own = owner.list_own.list.tracked_remove(owner.index);
        let tracked cur_repr_perm = owner.list_own.repr_perms.tracked_remove(owner.index);

        let (mut frame, Tracked(mut frame_own)) = unsafe {
            // SAFETY: The frame was forgotten when inserted into the linked list.
            #[verus_spec(with Tracked(regions), Tracked(cur_own), Tracked(cur_repr_perm))]
            UniqueFrame::<Link<M>>::from_raw(paddr)
        };

        proof {
            assert(frame_own.inv());
            assert(frame_own.global_inv(*regions)) by {
                reveal(UniqueFrameOwner::global_inv);
            };
            lemma_take_current_regions_preserved_init(*regions, regions0, idx);
            lemma_take_current_local_ready_init(
                owner0.list_own,
                regions0,
                owner.list_own,
                *regions,
                owner0.index,
            );
            lemma_take_current_pointer_state_init(
                owner0.list_own,
                regions0,
                owner.list_own,
                *regions,
                owner0.index,
            );
        }

        let next_ptr = (#[verus_spec(with Tracked(&frame_own), Tracked(&*regions))]
        frame.meta()).next;
        let prev_ptr = (#[verus_spec(with Tracked(&frame_own), Tracked(&*regions))]
        frame.meta()).prev;

        if let Some(prev) = prev_ptr {
            let ghost prev_idx = meta_to_index(owner.list_own.list[owner.index - 1].paddr);
            let ghost owner_before_prev = owner.list_own;
            let ghost regions_before_prev = *regions;
            let tracked prev_points_to = regions.slots.tracked_borrow(prev_idx);
            let tracked prev_slot_owner = regions.slot_owners.tracked_borrow_mut(prev_idx);
            let tracked prev_repr_perm = owner.list_own.repr_perms.tracked_borrow_mut(
                owner.index - 1,
            );
            let prev_meta = borrow_meta_mut(
                prev,
                Tracked(prev_points_to),
                Tracked(prev_slot_owner),
                Tracked(prev_repr_perm),
            );
            prev_meta.next = next_ptr;

            proof {
                assert(regions.inv()) by {
                    reveal(<MetaRegionOwners as Inv>::inv);
                };
                lemma_take_current_regions_preserved_update(
                    regions_before_prev,
                    *regions,
                    regions0,
                    idx,
                    prev_idx,
                );
                lemma_take_current_local_ready_update(
                    owner0.list_own,
                    regions0,
                    owner_before_prev,
                    regions_before_prev,
                    owner.list_own,
                    *regions,
                    owner0.index,
                    owner.index - 1,
                    prev_idx,
                );
                lemma_take_current_pointer_state_update(
                    owner0.list_own,
                    regions0,
                    owner_before_prev,
                    regions_before_prev,
                    owner.list_own,
                    *regions,
                    owner0.index,
                    owner0.index - 1,
                    owner.index - 1,
                    prev_idx,
                    false,
                    false,
                    true,
                    false,
                );
            }

        } else {
            self.list.front = next_ptr;
            proof {
                lemma_take_current_pointer_state_prev_vacuous(
                    owner0.list_own,
                    regions0,
                    owner.list_own,
                    *regions,
                    owner0.index,
                );
            }
        }

        if let Some(next) = next_ptr {
            let ghost next_idx = meta_to_index(owner.list_own.list[owner.index].paddr);
            let ghost owner_before_next = owner.list_own;
            let ghost regions_before_next = *regions;
            proof {
                let ghost old_next = owner0.index + 1;
                let _ = owner0.list_own.list[old_next];
                owner0.list_own.relate_region_at_facts(regions0, old_next);
                assert(owner.list_own.list[owner.index] == owner0.list_own.list[old_next]);
                assert(owner.list_own.repr_perms[owner.index]
                    == owner0.list_own.repr_perms[old_next]);
                if let Some(prev) = prev_ptr {
                    let ghost old_prev = owner0.index - 1;
                    assert(meta_to_index(owner0.list_own.list[old_prev].paddr) != next_idx) by {
                        let _ = owner0.list_own.list[old_prev];
                        let _ = owner0.list_own.list[old_next];
                        reveal(LinkedListOwner::relate_region);
                    };
                    assert(meta_to_index(prev.addr()) != next_idx);
                }
                assert(regions.slot_owners[next_idx] == regions0.slot_owners[next_idx]);
                assert(owner.list_own.meta_wf_at(*regions, owner.index));
            }
            let tracked next_points_to = regions.slots.tracked_borrow(next_idx);
            let tracked next_slot_owner = regions.slot_owners.tracked_borrow_mut(next_idx);
            let tracked next_repr_perm = owner.list_own.repr_perms.tracked_borrow_mut(owner.index);
            let next_meta = borrow_meta_mut(
                next,
                Tracked(next_points_to),
                Tracked(next_slot_owner),
                Tracked(next_repr_perm),
            );
            next_meta.prev = prev_ptr;

            proof {
                assert(regions.inv()) by {
                    reveal(<MetaRegionOwners as Inv>::inv);
                };
                lemma_take_current_regions_preserved_update(
                    regions_before_next,
                    *regions,
                    regions0,
                    idx,
                    next_idx,
                );
                lemma_take_current_local_ready_update(
                    owner0.list_own,
                    regions0,
                    owner_before_next,
                    regions_before_next,
                    owner.list_own,
                    *regions,
                    owner0.index,
                    owner.index,
                    next_idx,
                );
                lemma_take_current_pointer_state_update(
                    owner0.list_own,
                    regions0,
                    owner_before_next,
                    regions_before_next,
                    owner.list_own,
                    *regions,
                    owner0.index,
                    owner0.index + 1,
                    owner.index,
                    next_idx,
                    true,
                    false,
                    true,
                    true,
                );
            }

            self.current = Some(next);
        } else {
            self.list.back = prev_ptr;

            self.current = None;
            proof {
                lemma_take_current_pointer_state_next_vacuous(
                    owner0.list_own,
                    regions0,
                    owner.list_own,
                    *regions,
                    owner0.index,
                );
            }
        }

        proof {
            assert(frame_own.global_inv(*regions)) by {
                reveal(UniqueFrameOwner::global_inv);
            };
        }

        let ghost regions_before_clear = *regions;
        (#[verus_spec(with Tracked(&mut frame_own), Tracked(regions))]
        clear_take_current_links(&mut frame));
        proof {
            lemma_take_current_regions_preserved_transitive(
                *regions,
                regions_before_clear,
                regions0,
                idx,
            );
        }

        let ghost regions_before_in_list = *regions;
        let tracked frame_outer = regions.slots.tracked_borrow(idx);
        let tracked mut frame_so = regions.slot_owners.tracked_borrow_mut(idx);
        let tracked mut fip = frame_so.tracked_borrow_mut_inner_perms();
        #[verus_spec(with Tracked(&frame_outer))]
        let slot = frame.slot();
        slot.in_list.store(Tracked(&mut fip.in_list), 0);
        proof {
            assert(regions.inv()) by {
                reveal(<MetaRegionOwners as Inv>::inv);
            };
            lemma_meta_region_inv_at(*regions, idx);
            assert(regions.slot_owners[idx].paths_in_pt == regions0.slot_owners[idx].paths_in_pt);
            lemma_take_current_regions_preserved_update(
                regions_before_in_list,
                *regions,
                regions0,
                idx,
                idx,
            );
            assert(take_current_regions_unchanged_except(*regions, regions_before_in_list, idx))
                by {
                reveal(take_current_regions_unchanged_except);
                assert(regions.slots == regions_before_in_list.slots);
                assert(regions.slot_owners.dom() == regions_before_in_list.slot_owners.dom());
                assert forall|j: int|
                    #![trigger regions.slot_owners[j]]
                    j != idx implies regions.slot_owners[j]
                    == regions_before_in_list.slot_owners[j] by {}
            };
            lemma_take_current_regions_unchanged_except_transitive(
                *regions,
                regions_before_in_list,
                regions_before_clear,
                idx,
            );
        }

        self.list.size = self.list.size - 1;

        proof {
            let ghost oldl = owner0.list_own;
            let ghost nn = owner0.index as int;
            lemma_take_current_local_ready_preserved(
                oldl,
                regions0,
                owner.list_own,
                regions_before_clear,
                *regions,
                nn,
                idx,
            );
            lemma_take_current_pointer_state_preserved(
                oldl,
                regions0,
                owner.list_own,
                regions_before_clear,
                *regions,
                nn,
                idx,
                true,
                true,
            );
            lemma_take_current_pop_ready_from_parts(
                oldl,
                regions0,
                owner.list_own,
                *regions,
                nn,
                idx,
            );
            lemma_take_current_pop_preserves_relate_region(
                oldl,
                regions0,
                owner.list_own,
                *regions,
                nn,
                idx,
            );
            assert forall|j: int| #![trigger regions.slot_owners[j]] j != idx implies {
                &&& regions.slot_owners[j].usage == regions0.slot_owners[j].usage
                &&& regions.slot_owners[j].slot_vaddr == regions0.slot_owners[j].slot_vaddr
                &&& regions.slot_owners[j].paths_in_pt == regions0.slot_owners[j].paths_in_pt
            } by {
                lemma_take_current_regions_preserved_at(*regions, regions0, idx, j);
            }
            owner0.remove_owner_spec_implies_model_spec(*owner);
        }
        Some((frame, Tracked(frame_own)))
    }

    /// Inserts a frame before the current frame.
    ///
    /// If the cursor is pointing at the "ghost" non-element then the new
    /// element is inserted at the back of the [`LinkedList`].
    /// # Verified Properties
    /// ## Preconditions
    /// The cursor must be well-formed, with the pointers to its links' metadata slots matching the tracked permission objects.
    /// - The new frame must be active, so that it is valid to call `into_raw` on it.
    /// ## Postconditions
    /// - The new frame is inserted into the list, immediately before the current index.
    /// - The list invariants are preserved.
    /// ## Safety
    /// - This function calls `into_raw` on the frame, so the caller must ensure that the frame is active and
    /// has not been forgotten already to avoid a memory leak. If the caller attempts to insert a forgotten frame,
    /// the invariant around `into_raw` and `from_raw` will be violated. But, it is the safe failure case in that
    /// it will not cause a double-free. (Note: we should be able to move this requirement into the `UniqueFrame` invariants.)
    #[verus_spec(
        with Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(owner): Tracked<&mut CursorOwner<M>>,
            Tracked(frame_own): Tracked<&mut UniqueFrameOwner<Link<M>>>
    )]
    #[verifier::spinoff_prover]
    pub fn insert_before(&mut self, mut frame: UniqueFrame<Link<M>>)
        requires
            old(self).wf_region(*old(owner), *old(regions)),
            old(owner).wf_with_region(*old(regions)),
            old(regions).inv(),
            old(frame_own).inv(),
            old(frame_own).global_inv(*old(regions)),
            frame.wf(*old(frame_own)),
            old(frame_own).frame_link_inv(*old(regions)),
        ensures
            final(owner).wf_with_region(*final(regions)),
            final(self).wf_region(*final(owner), *final(regions)),
            final(regions).inv(),
            final(owner).list_own.list == old(owner).list_own.list.insert(
                old(owner).index,
                final(frame_own).meta_own,
            ),
            // The id is preserved when it was already minted; a `list_id == 0`
            // (necessarily empty) list adopts a freshly-minted non-zero id.
            old(owner).list_own.list_id != 0 ==> final(owner).list_own.list_id == old(
                owner,
            ).list_own.list_id,
            final(owner).list_own.list_id != 0,
            final(owner).index == old(owner).index + 1,
            final(frame_own).meta_own.paddr == old(frame_own).meta_own.paddr,
            final(frame_own).meta_own.in_list == final(owner).list_own.list_id,
            final(owner)@ == old(owner)@.insert(final(frame_own).meta_own@),
    {
        hide(LinkedListOwner::relate_region);
        hide(<MetaRegionOwners as Inv>::inv);
        let ghost owner0 = *owner;
        let ghost regions0 = *regions;
        let ghost nn = owner.index as int;

        proof {
            assert(regions0.contains(frame_own.slot_index));
            lemma_insert_before_setup(owner0, regions0, frame_own.slot_index);
            if nn > 0 {
                owner.list_own.relate_region_at_facts(*regions, nn - 1);
                lemma_meta_region_inv_at(
                    regions0,
                    meta_to_index(owner0.list_own.list[nn - 1].paddr),
                );
            }
            if nn < owner.list_own.list.len() {
                owner.list_own.relate_region_at_facts(*regions, nn);
                lemma_meta_region_inv_at(regions0, meta_to_index(owner0.list_own.list[nn].paddr));
            }
        }

        let frame_ptr = ReprPtr::<MetaSlotStorage, Link<M>>::from_pptr(
            PPtr::<MetaSlotStorage>::from_addr(frame.ptr.addr()),
        );

        if let Some(current) = self.current {
            proof_decl!{
                let ghost idx = meta_to_index(current.addr());
                let tracked points_to = regions.slots.tracked_borrow(idx);
                let tracked slot_owner = regions.slot_owners.tracked_borrow(idx);
                let tracked repr_perm = owner.list_own.repr_perms.tracked_borrow(owner.index);
            }

            // Read current's prev pointer.
            let opt_prev_link: Option<ReprPtr<MetaSlotStorage, Link<M>>> = borrow_meta(
                current,
                Tracked(points_to),
                Tracked(&slot_owner.inner_perms.storage),
                Tracked(repr_perm),
            ).prev;

            if let Some(prev_link) = opt_prev_link {
                let prev = prev_link;

                (#[verus_spec(with Tracked(frame_own), Tracked(regions))]
                frame.meta_mut()).prev = Some(prev_link);
                (#[verus_spec(with Tracked(frame_own), Tracked(regions))]
                frame.meta_mut()).next = Some(current);

                let ghost prev_idx = meta_to_index(owner.list_own.list[nn - 1].paddr);
                proof {
                    assert(prev_idx != idx) by {
                        reveal(LinkedListOwner::relate_region);
                    };
                }
                let tracked prev_points_to = regions.slots.tracked_borrow(prev_idx);
                let tracked prev_slot_owner = regions.slot_owners.tracked_borrow_mut(prev_idx);
                let tracked prev_repr_perm = owner.list_own.repr_perms.tracked_borrow_mut(nn - 1);
                let prev_meta = borrow_meta_mut(
                    prev,
                    Tracked(prev_points_to),
                    Tracked(prev_slot_owner),
                    Tracked(prev_repr_perm),
                );
                prev_meta.next = Some(frame_ptr);

                let ghost current_idx = meta_to_index(owner.list_own.list[nn].paddr);
                let tracked current_points_to = regions.slots.tracked_borrow(current_idx);
                let tracked current_slot_owner = regions.slot_owners.tracked_borrow_mut(
                    current_idx,
                );
                let tracked current_repr_perm = owner.list_own.repr_perms.tracked_borrow_mut(nn);
                let current_meta = borrow_meta_mut(
                    current,
                    Tracked(current_points_to),
                    Tracked(current_slot_owner),
                    Tracked(current_repr_perm),
                );
                current_meta.prev = Some(frame_ptr);
            } else {
                (#[verus_spec(with Tracked(frame_own), Tracked(regions))]
                frame.meta_mut()).next = Some(current);

                let ghost current_idx = meta_to_index(owner.list_own.list[nn].paddr);
                let tracked current_points_to = regions.slots.tracked_borrow(current_idx);
                let tracked current_slot_owner = regions.slot_owners.tracked_borrow_mut(
                    current_idx,
                );
                let tracked current_repr_perm = owner.list_own.repr_perms.tracked_borrow_mut(nn);
                let current_meta = borrow_meta_mut(
                    current,
                    Tracked(current_points_to),
                    Tracked(current_slot_owner),
                    Tracked(current_repr_perm),
                );
                current_meta.prev = Some(frame_ptr);
                self.list.front = Some(frame_ptr);
            }
        } else {
            if let Some(back) = self.list.back {
                (#[verus_spec(with Tracked(frame_own), Tracked(regions))]
                frame.meta_mut()).prev = Some(back);

                let ghost back_idx = meta_to_index(owner.list_own.list[nn - 1].paddr);
                proof {
                    assert(0 <= nn - 1 < owner.list_own.repr_perms.len());
                }
                let tracked back_points_to = regions.slots.tracked_borrow(back_idx);
                let tracked back_slot_owner = regions.slot_owners.tracked_borrow_mut(back_idx);
                let tracked back_repr_perm = owner.list_own.repr_perms.tracked_borrow_mut(nn - 1);
                let back_meta = borrow_meta_mut(
                    back,
                    Tracked(back_points_to),
                    Tracked(back_slot_owner),
                    Tracked(back_repr_perm),
                );
                back_meta.next = Some(frame_ptr);
                self.list.back = Some(frame_ptr);
            } else {
                // EMPTY list: just point both ends at the inserted frame.
                self.list.front = Some(frame_ptr);
                self.list.back = Some(frame_ptr);
            }
        }

        #[verus_spec(with Tracked(&owner.list_own))]
        let list_id = self.list.lazy_get_id();

        proof {
            assert(owner0.list_own.list.len() > 0 ==> list_id == owner0.list_own.list_id);
        }
        let tracked frame_outer = regions.slots.tracked_borrow_mut(frame_own.slot_index);
        let tracked mut frame_so = regions.slot_owners.tracked_borrow_mut(frame_own.slot_index);
        let tracked mut fip = frame_so.tracked_borrow_mut_inner_perms();
        #[verus_spec(with Tracked(frame_outer))]
        let slot = frame.slot();
        slot.in_list.store(Tracked(&mut fip.in_list), list_id);
        proof {
            assert(regions.inv()) by {
                reveal(<MetaRegionOwners as Inv>::inv);
            };
        }

        #[verus_spec(with Tracked(&*frame_own), Tracked(regions))]
        let _ = frame.into_raw();

        self.list.size = self.list.size + 1;

        proof {
            let tracked frame_repr_perm = frame_own.repr_perm.tracked_take();
            CursorOwner::<M>::tracked_list_insert(
                owner,
                &mut frame_own.meta_own,
                frame_repr_perm,
                list_id,
            );

            let oldl = owner0.list_own;
            let nn = owner0.index as int;
            let flink = frame_own.meta_own;
            let ins = frame_own.slot_index;

            assert(owner.list_own.relate_region(*regions)) by {
                assert forall|p: int|
                    #![trigger
                        owner.list_own.insert_old_slot_post_at(
                            *regions,
                            oldl,
                            regions0,
                            nn,
                            flink,
                            p,
                        )]
                    (0 <= p < oldl.list.len()) implies owner.list_own.insert_old_slot_post_at(
                    *regions,
                    oldl,
                    regions0,
                    nn,
                    flink,
                    p,
                ) by {
                    reveal(LinkedListOwner::insert_old_slot_post_at);
                    assert(oldl.relate_region_at(regions0, p)) by {
                        reveal(LinkedListOwner::relate_region);
                    };
                    oldl.relate_region_at_facts(regions0, p);
                    if nn - 1 >= 0 && nn - 1 < oldl.list.len() && p != nn - 1 {
                        assert(meta_to_index(oldl.list[p].paddr) != meta_to_index(
                            oldl.list[nn - 1].paddr,
                        )) by {
                            reveal(LinkedListOwner::relate_region);
                        };
                    }
                    if nn >= 0 && nn < oldl.list.len() && p != nn {
                        assert(meta_to_index(oldl.list[p].paddr) != meta_to_index(
                            oldl.list[nn].paddr,
                        )) by {
                            reveal(LinkedListOwner::relate_region);
                        };
                    }
                }

                LinkedListOwner::insert_preserves_relate_region(
                    oldl,
                    regions0,
                    owner.list_own,
                    *regions,
                    nn,
                    flink,
                );
            };

            owner0.insert_owner_spec_implies_model_spec(flink, *owner);
        }
    }

    /// Provides a reference to the linked list.
    pub fn as_list(&self) -> &LinkedList<M> {
        self.list
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> TrackDrop for LinkedList<M> {
    type State = (LinkedListOwner<M>, MetaRegionOwners);

    /// Real key: the list's `list_id`. The token carries the identity of
    /// the list it belongs to, so a token forged for one list can't be
    /// used to discharge another (the `consume_requires` key match
    /// refuses the mismatch). A multiset ledger over `list_id` is not
    /// added because every live `LinkedList` already has a unique
    /// `LinkedListOwner` in scope — the per-instance discipline is
    /// state-side, not ledger-side.
    type Obligation = DropObligation<u64>;

    open spec fn tracked_redeem_requires(self, s: Self::State) -> bool {
        true
    }

    open spec fn tracked_redeem_ensures(
        self,
        s0: Self::State,
        s1: Self::State,
        obl: Self::Obligation,
    ) -> bool {
        &&& s0 =~= s1
        &&& obl.value() == self.list_id
    }

    proof fn tracked_redeem(self, tracked s: &mut Self::State) -> (tracked obl: Self::Obligation) {
        DropObligation::tracked_mint(self.list_id)
    }

    open spec fn drop_requires(self, s: Self::State, obl: Self::Obligation) -> bool {
        &&& self.wf(s.0)
        &&& s.0.inv()
        &&& s.1.inv()
        &&& forall|i: int|
            #![trigger s.0.list[i]]
            0 <= i < s.0.list.len() ==> s.1.contains(meta_to_index(s.0.list[i].paddr))
        &&& forall|i: int|
            #![trigger s.0.list[i]]
            0 <= i < s.0.list.len() ==> {
                let idx = meta_to_index(s.0.list[i].paddr);
                s.1.contains(idx)
            }
        &&& forall|i: int|
            #![trigger s.0.list[i]]
            0 <= i < s.0.list.len() ==> {
                let idx = meta_to_index(s.0.list[i].paddr);
                s.1.slot_owners[idx].inner_perms.ref_count.value() == REF_COUNT_UNIQUE
            }
        &&& forall|i: int|
            #![trigger s.0.list[i]]
            0 <= i < s.0.list.len() ==> {
                let idx = meta_to_index(s.0.list[i].paddr);
                s.1.frame_obligations.count(idx) == 0
            }
        &&& forall|i: int|
            #![trigger s.0.list[i]]
            0 <= i < s.0.list.len() ==> {
                let idx = meta_to_index(s.0.list[i].paddr);
                s.1.slot_owners[idx].paths_in_pt.is_empty()
            }
        &&& forall|i: int, j: int|
            #![trigger s.0.list[i], s.0.list[j]]
            0 <= i < j < s.0.list.len() ==> meta_to_index(s.0.list[i].paddr) != meta_to_index(
                s.0.list[j].paddr,
            )
        &&& s.0.relate_region(s.1)
        &&& obl.value() == self.list_id
    }

    open spec fn drop_ensures(
        self,
        s0: Self::State,
        s1: Self::State,
        obl: Self::Obligation,
    ) -> bool {
        &&& s1.0.list.len() == 0
        &&& forall|i: int|
            #![trigger s0.0.list[i]]
            0 <= i < s0.0.list.len() ==> {
                let idx = meta_to_index(s0.0.list[i].paddr);
                s1.1.frame_obligations.count(idx) == s0.1.frame_obligations.count(idx)
            }
        &&& forall|idx: int|
            #![trigger s1.1.slot_owners[idx]]
            (forall|i: int|
                #![trigger s0.0.list[i]]
                0 <= i < s0.0.list.len() ==> idx != meta_to_index(s0.0.list[i].paddr)) ==> {
                &&& s1.1.frame_obligations.count(idx) == s0.1.frame_obligations.count(idx)
                &&& s1.1.slot_owners[idx].usage == s0.1.slot_owners[idx].usage
                &&& s1.1.slot_owners[idx].slot_vaddr == s0.1.slot_owners[idx].slot_vaddr
                &&& s1.1.slot_owners[idx].paths_in_pt == s0.1.slot_owners[idx].paths_in_pt
            }
        &&& s1.1.slots.dom() =~= s0.1.slots.dom()
        &&& s1.1.inv()
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> Drop for LinkedList<M> {
    #[verifier::spinoff_prover]
    fn drop(
        self,
        Tracked(s): Tracked<&mut Self::State>,
        Tracked(obl): Tracked<DropObligation<u64>>,
    ) {
        proof_decl! {
            let tracked mut list_own: LinkedListOwner<M>;
        }
        let ghost original_list = s.0.list;
        let ghost original_list_id = s.0.list_id;
        let ghost n = original_list.len();
        let ghost original_regions = s.1;
        proof {
            list_own = LinkedListOwner::<M>::tracked_take(&mut s.0);
        }
        let tracked regions: &mut MetaRegionOwners = &mut s.1;
        let mut this = self;

        #[verus_spec(with Tracked(list_own))]
        let cursor_pair = this.cursor_front_mut();
        let (mut cursor, Tracked(mut cursor_own)) = cursor_pair;

        proof {
            if n > 0 {
                cursor_own.list_own.relate_region_at_facts(*regions, 0);
                cursor_own.list_own.relate_region_at_facts(*regions, n - 1);
            }
        }

        let ghost mut k: int = 0;

        loop
            invariant_except_break
                cursor.wf_region(cursor_own, *regions),
                cursor.current.is_some() <==> k < n,
            invariant
                cursor_own.wf_with_region(*regions),
                cursor_own.list_own.list_id == original_list_id,
                cursor_own.index == 0,
                regions.inv(),
                cursor_own.list_own.list.len() == n - k,
                0 <= k <= n,
                // The remaining list is a suffix of the original
                forall|j: int|
                    #![trigger cursor_own.list_own.list[j]]
                    0 <= j < n - k ==> cursor_own.list_own.list[j] == original_list[j + k],
                // Elements already taken have their in-list obligation redeemed (count 0)
                forall|j: int|
                    #![trigger original_list[j]]
                    0 <= j < k ==> {
                        let idx = meta_to_index(original_list[j].paddr);
                        regions.frame_obligations.count(idx) == 0
                    },
                // slots values inside the original_list.
                forall|idx: int|
                    #![trigger regions.slot_owners[idx]]
                    (forall|j: int|
                        #![trigger original_list[j]]
                        0 <= j < n ==> idx != meta_to_index(original_list[j].paddr)) ==> {
                        &&& regions.frame_obligations.count(idx)
                            == original_regions.frame_obligations.count(idx)
                        &&& regions.slot_owners[idx].usage
                            == original_regions.slot_owners[idx].usage
                        &&& regions.slot_owners[idx].slot_vaddr
                            == original_regions.slot_owners[idx].slot_vaddr
                        &&& regions.slot_owners[idx].paths_in_pt
                            == original_regions.slot_owners[idx].paths_in_pt
                    },
                regions.slots.dom() == original_regions.slots.dom(),
                // `paths_in_pt.is_empty()` precondition).
                forall|j: int|
                    #![trigger original_list[j]]
                    k <= j < n ==> {
                        let idx = meta_to_index(original_list[j].paddr);
                        &&& regions.frame_obligations.count(idx)
                            == original_regions.frame_obligations.count(idx)
                        &&& regions.slot_owners[idx].paths_in_pt
                            == original_regions.slot_owners[idx].paths_in_pt
                    },
                // Each remaining element's slot is in slot_owners
                forall|j: int|
                    #![trigger original_list[j]]
                    k <= j < n ==> regions.contains(meta_to_index(original_list[j].paddr)),
                // Distinct slot indices in original list (from drop_requires)
                forall|i: int, j: int|
                    #![trigger original_list[i], original_list[j]]
                    0 <= i < j < n ==> meta_to_index(original_list[i].paddr) != meta_to_index(
                        original_list[j].paddr,
                    ),
                forall|j: int|
                    #![trigger original_list[j]]
                    0 <= j < n ==> {
                        let idx = meta_to_index(original_list[j].paddr);
                        &&& original_regions.contains(idx)
                        &&& original_regions.frame_obligations.count(idx) == 0
                        &&& original_regions.slot_owners[idx].paths_in_pt.is_empty()
                        &&& original_regions.slot_owners[idx].inner_perms.ref_count.value()
                            == REF_COUNT_UNIQUE
                    },
            ensures
                k == n,
                cursor_own.list_own.list.len() == 0,
            decreases n - k,
        {
            #[verus_spec(with Tracked(regions), Tracked(&mut cursor_own))]
            let entry = cursor.take_current();

            if let Some(current) = entry {
                let (mut frame, frame_own_tracked) = current;
                let tracked frame_own = frame_own_tracked.get();
                let ghost regions_pre_drop = *regions;

                // Drop the frame, returning its slot to regions
                #[verus_spec(with Tracked(frame_own), Tracked(regions))]
                frame.drop();

                proof {
                    assert forall|i: int|
                        #![trigger cursor_own.list_own.list[i]]
                        0 <= i < cursor_own.list_own.list.len() implies ({
                        let idx = meta_to_index(cursor_own.list_own.list[i].paddr);
                        &&& regions.contains(idx)
                        &&& regions.slot_owners[idx] == regions_pre_drop.slot_owners[idx]
                        &&& regions.frame_obligations.count(idx)
                            == regions_pre_drop.frame_obligations.count(idx)
                    }) by {
                        let idx = meta_to_index(cursor_own.list_own.list[i].paddr);
                        let ghost _trig_k = original_list[k as int];
                        let ghost _trig_ik = original_list[i + k + 1];
                        assert(cursor_own.list_own.list[i] == original_list[i + k + 1]);

                        cursor_own.list_own.relate_region_at_facts(regions_pre_drop, i);
                    };
                    cursor_own.list_own.relate_region_preserved_external_change(
                        regions_pre_drop,
                        *regions,
                    );

                    assert forall|j: int|
                        #![trigger cursor_own.list_own.list[j]]
                        0 <= j < n - k - 1 implies cursor_own.list_own.list[j] == original_list[j
                        + k + 1] by {};

                    assert forall|j: int| #![trigger original_list[j]] 0 <= j < k implies ({
                        let idx = meta_to_index(original_list[j].paddr);
                        regions.frame_obligations.count(idx) == 0
                    }) by {
                        let ghost _a = original_list[j as int];
                        let ghost _b = original_list[k as int];
                    };

                    k = k + 1;
                }
            } else {
                break;
            }
        }

        // `s.1` is already updated in place via the re-borrow `regions`;
        // restore `s.0` to the cursor's final (empty) `list_own`.
        proof {
            let tracked mut final_list_own = cursor_own.list_own;
            vstd::modes::tracked_swap(&mut s.0, &mut final_list_own);
            final_list_own.tracked_destroy_empty();
        }
    }
}

// SAFETY: `Link<M>` is `Send` and `Sync` if `M` is `Send` and `Sync` because
// we only access these unsafe cells when the frame is not shared. This is
// enforced by `UniqueFrame`.
// #[verifier::external]
// unsafe impl<M> Send for LinkedList<M> where Link<M>: AnyFrameMeta {}
// #[verifier::external]
// unsafe impl<M> Sync for LinkedList<M> where Link<M>: AnyFrameMeta {}
/// A link in the linked list.
pub struct Link<M: AnyFrameMeta + Repr<MetaSlotSmall>> {
    pub next: Option<ReprPtr<MetaSlotStorage, Link<M>>>,
    pub prev: Option<ReprPtr<MetaSlotStorage, Link<M>>>,
    pub meta: M,
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> Deref for Link<M> {
    type Target = M;

    fn deref(&self) -> &Self::Target {
        &self.meta
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> DerefMut for Link<M> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.meta
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> Link<M> {
    /// Creates a new linked list metadata.
    pub const fn new(meta: M) -> Self {
        Self { next: None, prev: None, meta }
    }
}

// SAFETY: If `M::on_drop` reads the page using the provided `VmReader`,
// the safety is upheld by the one who implements `AnyFrameMeta` for `M`.
unsafe impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> AnyFrameMeta for Link<M> {
    open spec fn on_drop_pre(
        &self,
        reader: crate::mm::VmReader<'_, crate::mm::Infallible>,
        regions: crate::specs::mm::frame::meta_region_owners::MetaRegionOwners,
        vm_io_owner: crate::specs::mm::io::VmIoOwner,
    ) -> bool {
        self.meta.on_drop_pre(reader, regions, vm_io_owner)
    }

    fn on_drop(
        &mut self,
        reader: &mut crate::mm::VmReader<crate::mm::Infallible>,
        regions: Tracked<&mut crate::specs::mm::frame::meta_region_owners::MetaRegionOwners>,
        vm_io_owner: Tracked<&mut crate::specs::mm::io::VmIoOwner>,
    ) {
        self.meta.on_drop(reader, regions, vm_io_owner);
    }

    fn is_untyped(&self) -> bool {
        self.meta.is_untyped()
    }

    uninterp spec fn vtable_ptr(&self) -> usize;
}

} // verus!

// SPDX-License-Identifier: MPL-2.0
use vstd::prelude::*;
use vstd_extra::{assert, assert_eq, prelude::Inv};

use crate::specs::{
    arch::lemma_paddr_to_vaddr_properties,
    mm::{
        frame::meta_region_owners::MetaRegionOwners,
        page_table::{Guards, lemma_page_size_spec_values},
    },
};
use crate::util::range_alloc::{AllocationSnapshot, has_capacity};

use crate::arch::mm::PagingConsts;
use crate::mm::{
    PAGE_SIZE, Paddr,
    frame::max_paddr,
    kspace::{
        KernelPtConfig, LINEAR_MAPPING_BASE_VADDR, MappedItem, VMALLOC_VADDR_RANGE,
        kvirt_area::{KVirtArea, KVirtAreaOwner},
        paddr_to_vaddr,
    },
    page_prop::{CachePolicy, PageFlags, PageProperty, PrivilegedPageFlags},
    page_table::PageTableGuard,
};

#[verus_spec(returns PageProperty::new_user(PageFlags::RW, CachePolicy::Writeback))]
fn default_prop() -> PageProperty {
    PageProperty::new_user(PageFlags::RW, CachePolicy::Writeback)
}

/* #[ktest]
fn kvirt_area_tracked_map_pages() {
    let size = 2 * PAGE_SIZE;
    let frames = FrameAllocOptions::default()
        .alloc_segment_with(2, |_| ())
        .unwrap();
    let start_paddr = frames.start_paddr();

    let kvirt_area = KVirtArea::map_frames(size, 0, frames.into_iter().collect(), default_prop());

    assert_eq!(kvirt_area.len(), size);
    assert!(kvirt_area.start() >= VMALLOC_VADDR_RANGE.start);
    assert!(kvirt_area.end() <= VMALLOC_VADDR_RANGE.end);

    for i in 0..2 {
        let addr = kvirt_area.start() + i * PAGE_SIZE;
        let MappedItem::Tracked(page, _) = kvirt_area.query(addr).unwrap() else {
            panic!("Expected a tracked page");
        };
        assert_eq!(page.start_paddr(), start_paddr + (i * PAGE_SIZE));
    }
}

*/

/*#[ktest]*/
#[verus_spec(
    with Tracked(snapshot): Tracked<AllocationSnapshot>,
         Tracked(owner): Tracked<KVirtAreaOwner>,
         Tracked(root_guard): Tracked<PageTableGuard<'_, KernelPtConfig>>,
         Tracked(regions): Tracked<&mut MetaRegionOwners>,
         Tracked(guards): Tracked<&mut Guards>,
    requires
        has_capacity(&snapshot, (2 * PAGE_SIZE) as usize),
        old(regions).inv(),
        owner.inv(),
        owner.pt_owner.metaregion_sound(*old(regions)),
        owner.pt_owner.0.value().node().relate_guard(root_guard),
)]
fn kvirt_area_untracked_map_pages() {
    let max_paddr = max_paddr();

    let size = 2 * PAGE_SIZE;
    let pa_range = max_paddr..max_paddr + 2 * PAGE_SIZE as Paddr;

    proof! {
        lemma_page_size_spec_values::<PagingConsts>();
        broadcast use PageFlags::lemma_consts;
        broadcast use PrivilegedPageFlags::lemma_consts;
        let prop = PageProperty::new_user(PageFlags::RW, CachePolicy::Writeback);
        assert(PageFlags::RW.bits() == 3);
        assert(PageFlags::AVAIL1.bits() == 64);
        assert(3u8 & 64u8 == 0) by (bit_vector);
        assert(PageFlags::R.bits() == 1);
        assert(!prop.flags.contains(PageFlags::AVAIL1));
        assert(prop.flags.bits() == 3);
        assert(prop.priv_flags.bits() == 1);
        PageFlags::lemma_all_constant();
        PrivilegedPageFlags::lemma_all_constant();
        assert(0u8 | 1 | 2 | 4 | 3 | 5 | 7 | 8 | 16 | 64 | 128 == 0xdfu8) by (bit_vector);
        assert(PageFlags::all().bits() == 0xdf);
        assert(1u8 & (0u8 | 1 | 2 | 0) == 1) by (bit_vector);
        assert(1u8 & PrivilegedPageFlags::all().bits() == 1);
        assert(3u8 & 0xdfu8 == 3 && 3u8 & 1u8 == 1) by (bit_vector);
        assert(prop.inv());
        assert(prop.flags.bits() & PageFlags::R.bits() == PageFlags::R.bits());
    }
    proof_decl! {
        let tracked mut active: KVirtAreaOwner;
        let ghost prop = PageProperty::new_user(PageFlags::RW, CachePolicy::Writeback);
    }
    let kvirt_area = unsafe {
        #[verus_spec(with Tracked(snapshot), Tracked(owner), Tracked(root_guard), Tracked(regions), Tracked(guards) => Tracked(active))]
        KVirtArea::map_untracked_frames(size, 0, pa_range.clone(), default_prop())
    };

    assert_eq!(kvirt_area.len(), size);
    assert!(kvirt_area.start() >= VMALLOC_VADDR_RANGE.start);
    assert!(kvirt_area.end() <= VMALLOC_VADDR_RANGE.end);

    #[verus_spec(invariant
        kvirt_area.len() == size,
        kvirt_area.inv(),
        active.inv(),
        active.has_root_guard(),
        active.pt_owner.0.level() == 0,
        VMALLOC_VADDR_RANGE.start <= kvirt_area.range.start,
        kvirt_area.range.end <= VMALLOC_VADDR_RANGE.end,
        !prop.flags.contains(PageFlags::AVAIL1),
        forall|j: int| 0 <= j < 2 ==> active.pt_owner@.mappings.contains(
            #[trigger] KVirtAreaOwner::base_page((kvirt_area.range.start + j * PAGE_SIZE) as usize,
                (pa_range.start + j * PAGE_SIZE) as Paddr, prop)),
        regions.inv(),
        active.pt_owner.metaregion_sound(*regions),
        size == 2 * PAGE_SIZE,
        pa_range.end == pa_range.start + size,
    )]
    for i in 0..2 {
        let addr = kvirt_area.start() + i * PAGE_SIZE;

        proof_decl! { let ghost guard = active.root_guard(); }
        proof! {
            active.lemma_untracked_page_query(kvirt_area, addr, (pa_range.start + i * PAGE_SIZE) as Paddr, prop, *regions);
        }
        let MappedItem::Untracked(pa, level, _) =
            (#[verus_spec(with Tracked(active), Ghost(guard), Tracked(regions), Tracked(guards) => Tracked(active))]
            kvirt_area.query(addr)).unwrap() else {
            panic!("Expected a untracked page");
        };
        assert_eq!(pa, pa_range.start + (i * PAGE_SIZE) as Paddr);
        assert_eq!(level, 1);
    }
}

/* #[ktest]
fn kvirt_area_tracked_drop() {
    let size = 2 * PAGE_SIZE;
    let frames = FrameAllocOptions::default()
        .alloc_segment_with(2, |_| ())
        .unwrap();

    let kvirt_area = KVirtArea::map_frames(size, 0, frames.into_iter().collect(), default_prop());

    drop(kvirt_area);

    // After dropping, the virtual address range should be freed and no longer mapped.
    let kvirt_area = KVirtArea::map_frames(size, 0, alloc::vec::Vec::new(), default_prop());
    assert_eq!(kvirt_area.query(kvirt_area.start()), None);
}

#[ktest]
fn kvirt_area_untracked_drop() {
    let max_paddr = max_paddr();

    let size = 2 * PAGE_SIZE;
    let pa_range = max_paddr..max_paddr + 2 * PAGE_SIZE as Paddr;

    let kvirt_area = unsafe { KVirtArea::map_untracked_frames(size, 0, pa_range, default_prop()) };

    drop(kvirt_area);

    // After dropping, the virtual address range should be freed and no longer mapped.
    let kvirt_area = unsafe { KVirtArea::map_untracked_frames(size, 0, 0..0, default_prop()) };
    assert!(kvirt_area.query(kvirt_area.start()).is_none());
} */

/* #[ktest] */
#[verus_spec]
fn manual_paddr_to_vaddr() {
    let pa = 0x1000;
    proof! {
        assert(0x1000 + LINEAR_MAPPING_BASE_VADDR < usize::MAX) by (compute_only);
        assert(0x1000 < crate::mm::kspace::VMALLOC_BASE_VADDR - LINEAR_MAPPING_BASE_VADDR)
            by (compute_only);
        lemma_paddr_to_vaddr_properties(0x1000);
    }
    let va = paddr_to_vaddr(pa);

    assert_eq!(va, LINEAR_MAPPING_BASE_VADDR + pa);
}

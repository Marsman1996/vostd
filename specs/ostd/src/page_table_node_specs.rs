use vstd::prelude::*;

use vstd_extra::ownership::*;

use aster_common::prelude::*;

verus! {

impl<C: PageTableConfig> Child<C> {
    #[rustc_allow_incoherent_impl]
    pub open spec fn into_pte_pt_spec(
        self,
        slot_own: MetaSlotOwner,
        slot_perm: vstd::simple_pptr::PointsTo<MetaSlot>,
    ) -> C::E {
        C::E::new_pt_spec(meta_to_frame(slot_own.self_addr))
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn into_pte_frame_spec(self, tuple: (Paddr, PagingLevel, PageProperty)) -> C::E {
        let (paddr, level, prop) = tuple;
        C::E::new_page_spec(paddr, level, prop)
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn into_pte_none_spec(self) -> C::E {
        C::E::new_absent_spec()
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn from_pte_frame_spec(pte: C::E, level: PagingLevel) -> Self {
        Self::Frame(pte.paddr(), level, pte.prop())
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn from_pte_pt_spec(paddr: Paddr, regions: MetaRegionOwners) -> Self {
        Self::PageTable(PageTableNode::from_raw_spec(paddr))
    }
}

} // verus!

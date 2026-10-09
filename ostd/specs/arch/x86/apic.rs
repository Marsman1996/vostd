// SPDX-License-Identifier: MPL-2.0
//! Local-APIC access model. Hardware assumptions live in `vstd_extra::external`.
//!
//! Bootstrap must certify the exclusive session's CPU, privilege, and mapping;
//! runtime guard integration remains outstanding. APIC_BASE tracks mode, and
//! x2APIC ICR writes record submissions. Delivery, EOI, and timer progress are absent.
use vstd::{prelude::*, resource::Loc};

use vstd_extra::{
    external::io::{IoAccess, certified_io_access},
    resource::ghost_resource::excl::ExclusiveGhost,
};

verus! {

/// Fixed, physical, edge IPI to one explicit APIC ID (not a logical CPU number).
pub ghost struct IpiCommand {
    pub destination_apic_id: u32,
    pub vector: u8,
}

impl IpiCommand {
    pub open spec fn wf(self) -> bool {
        self.vector >= 32 && self.destination_apic_id != u32::MAX
    }

    pub open spec fn encode_x2(self) -> u64 {
        ((self.destination_apic_id as u64) << 32) | self.vector as u64
    }

    pub proof fn lemma_encode_x2(self)
        requires
            self.wf(),
        ensures
            valid_x2_icr(self.encode_x2()),
            decode_x2_icr(self.encode_x2()) == self,
    {
        let d = self.destination_apic_id;
        let v = self.vector;
        let raw = self.encode_x2();
        assert(raw as u32 == v as u32 && raw as u8 == v && (raw >> 32) as u32 == d) by (bit_vector)
            requires
                raw == ((d as u64) << 32) | v as u64,
        ;
        assert(valid_icr_low(raw as u32) && raw & 0xc_0000u64 == 0) by (bit_vector)
            requires
                raw == ((d as u64) << 32) | v as u64,
                v >= 32,
        ;
    }
}

// Bit 14 is ignored for an edge-triggered Fixed IPI; shorthand/broadcast are excluded.
pub open spec fn valid_x2_icr(raw: u64) -> bool {
    valid_icr_low(raw as u32) && raw & 0xc_0000u64 == 0 && (raw >> 32) as u32 != u32::MAX
}

pub open spec fn decode_x2_icr(raw: u64) -> IpiCommand {
    IpiCommand { destination_apic_id: (raw >> 32) as u32, vector: raw as u8 }
}

/// Access-relevant state of one pinned, privileged local-APIC session.
pub ghost struct ApicAccessView {
    // Session-local history of x2APIC ICR writes, retained after hardware consumes them.
    pub x2_submissions: Seq<IpiCommand>,
    pub cpu: usize,
    pub current_cpu: usize,
    pub pinned: bool,
    pub cpl: u8,
    pub apic_supported: bool,
    pub x2apic_supported: bool,
    pub tsc_deadline_supported: bool,
    pub base_msr: u64,
    pub mmio_vaddr: usize,
    pub mmio_paddr: usize,
    pub mmio_mapped: bool,
    pub mmio_uncached: bool,
}

impl ApicAccessView {
    /// Structural consistency; physical truth comes from the boot certificate.
    pub open spec fn wf(self) -> bool {
        &&& self.pinned
        &&& self.cpu == self.current_cpu
        &&& self.cpl == 0
        &&& self.apic_supported
        &&& self.base_msr & !0xf_ffff_fd00u64 == 0
        &&& self.base_msr & 0xc00 != 0x400
        &&& (self.x2apic() ==> self.x2apic_supported)
        &&& (self.mmio_mapped ==> {
            &&& self.mmio_uncached
            &&& self.mmio_vaddr % 4096 == 0
            &&& self.mmio_vaddr + 4096 <= usize::MAX
            &&& self.mmio_paddr == (self.base_msr & 0xf_ffff_f000) as usize
        })
    }

    /// Hardware globally enabled in xAPIC mode.
    pub open spec fn xapic(self) -> bool {
        self.base_msr & 0xc00 == 0x800
    }

    /// Hardware globally enabled in x2APIC mode.
    pub open spec fn x2apic(self) -> bool {
        self.base_msr & 0xc00 == 0xc00
    }

    /// Whether a u32 MMIO register read is supported by this session.
    pub open spec fn mmio_read(self, base: usize, offset: u32) -> bool {
        &&& self.xapic()
        &&& self.mmio_mapped
        &&& base == self.mmio_vaddr
        &&& readable_offset(offset)
    }

    pub open spec fn mmio_read_addr(self, addr: usize) -> bool {
        self.mmio_vaddr <= addr < self.mmio_vaddr + 1024 && self.mmio_read(
            self.mmio_vaddr,
            (addr - self.mmio_vaddr) as u32,
        )
    }

    pub open spec fn mmio_write_addr(self, addr: usize, value: u32) -> bool {
        self.mmio_vaddr <= addr < self.mmio_vaddr + 1024 && self.mmio_write(
            self.mmio_vaddr,
            (addr - self.mmio_vaddr) as u32,
            value,
        )
    }

    /// Whether a u32 MMIO register write is supported by this session.
    pub open spec fn mmio_write(self, base: usize, offset: u32, value: u32) -> bool {
        &&& self.xapic()
        &&& self.mmio_mapped
        &&& base == self.mmio_vaddr
        &&& writable_offset(offset, value)
        &&& (offset == 0x320 && ((value >> 17) & 3) == 2 ==> self.tsc_deadline_supported)
    }

    /// Whether an MSR read uses a supported, readable APIC register.
    pub open spec fn msr_read(self, reg: u32) -> bool {
        reg == 0x1b || (self.x2apic() && (reg == 0x802 || reg == 0x803 || reg == 0x828 || reg
            == 0x830 || reg == 0x839))
    }

    /// Whether an MSR write respects this session's mode and register policy.
    pub open spec fn msr_write(self, reg: u32, value: u64) -> bool {
        if reg == 0x1b {
            &&& value & !0xf_ffff_fd00u64 == 0
            &&& value & 0xf_ffff_f000 == self.base_msr & 0xf_ffff_f000
            &&& (value & 0xc00 == 0x800 || value & 0xc00 == 0xc00)
            &&& (value & 0xc00 == 0xc00 ==> {
                &&& self.x2apic_supported
                &&& self.base_msr & 0x800 != 0
            })
            &&& (self.x2apic() ==> value & 0xc00 == 0xc00)
        } else {
            &&& self.x2apic()
            &&& if reg == 0x830 {
                valid_x2_icr(value)
            } else {
                &&& value <= u32::MAX
                &&& match reg {
                    0x80b | 0x828 => value == 0,
                    0x80f => value & !0x1ffu64 == 0,
                    0x832 => valid_lvt_timer(value) && (((value >> 17) & 3) == 2
                        ==> self.tsc_deadline_supported),
                    0x838 => true,
                    0x83e => value & !0xbu64 == 0,
                    _ => false,
                }
            }
        }
    }

    /// Enabling xAPIC at the existing physical base satisfies APIC_BASE policy.
    pub proof fn lemma_enable_xapic(self)
        requires
            self.wf(),
            !self.x2apic(),
        ensures
            self.msr_write(0x1b, (self.base_msr & 0xf_ffff_f000) | 0x800),
            self.after_msr_write(0x1b, (self.base_msr & 0xf_ffff_f000) | 0x800).xapic(),
    {
        let b = self.base_msr;
        assert({
            let n = (b & 0xf_ffff_f000u64) | 0x800u64;
            n & !0xf_ffff_fd00u64 == 0 && n & 0xf_ffff_f000u64 == b & 0xf_ffff_f000u64 && n
                & 0xc00u64 == 0x800u64
        }) by (bit_vector);
    }

    /// Enabling x2APIC is legal only from an already globally enabled APIC.
    pub proof fn lemma_enable_x2apic(self)
        requires
            self.wf(),
            self.x2apic_supported,
            self.base_msr & 0x800 != 0,
        ensures
            self.msr_write(0x1b, self.base_msr | 0xc00),
            self.after_msr_write(0x1b, self.base_msr | 0xc00).x2apic(),
            self.base_msr & 0xc00 == 0xc00 ==> self.base_msr | 0xc00 == self.base_msr,
    {
        let b = self.base_msr;
        assert({
            let n = b | 0xc00u64;
            n & !0xf_ffff_fd00u64 == 0 && n & 0xf_ffff_f000u64 == b & 0xf_ffff_f000u64 && n
                & 0xc00u64 == 0xc00u64 && (b & 0xc00u64 == 0xc00u64 ==> n == b)
        }) by (bit_vector)
            requires
                b & !0xf_ffff_fd00u64 == 0,
        ;
    }

    /// Mode changes preserve history; x2APIC ICR writes append one command.
    pub open spec fn after_msr_write(self, reg: u32, value: u64) -> Self {
        if reg == 0x1b {
            Self { base_msr: value, ..self }
        } else if reg == 0x830 {
            Self { x2_submissions: self.x2_submissions.push(decode_x2_icr(value)), ..self }
        } else {
            self
        }
    }
}

/// Stable identity of the physical APIC authority for one logical CPU.
pub uninterp spec fn platform_apic_id(cpu: usize) -> Loc;

/// Bootstrap must establish the initial hardware/CPU/guard/mapping connection.
/// This predicate has no axiom or constructor that makes it true.
pub uninterp spec fn boot_apic_resource(id: Loc, state: ApicAccessView) -> bool;

/// Linear authority for a pinned APIC session; fields cannot be forged by clients.
pub tracked struct ApicAccess {
    resource: ExclusiveGhost<ApicAccessView>,
}

impl View for ApicAccess {
    type V = ApicAccessView;

    closed spec fn view(&self) -> Self::V {
        self.resource.view()
    }
}

impl ApicAccess {
    /// Identity of the physical APIC authority.
    pub closed spec fn id(self) -> Loc {
        self.resource.id()
    }

    /// The session has a consistent state and the physical authority's identity.
    pub open spec fn wf(self) -> bool {
        &&& self.id() == platform_apic_id(self@.cpu)
        &&& self@.wf()
        &&& certified_io_access(self)
    }

    pub closed spec fn certified_boot_resource(resource: ExclusiveGhost<ApicAccessView>) -> bool {
        certified_io_access(ApicAccess { resource })
    }

    /// Wraps a caller-supplied boot resource without allocating or certifying it.
    pub proof fn from_boot_resource(
        tracked resource: ExclusiveGhost<ApicAccessView>,
    ) -> (tracked res: Self)
        requires
            resource.wf(),
            resource.id() == platform_apic_id(resource.view().cpu),
            resource.view().wf(),
            boot_apic_resource(resource.id(), resource.view()),
            Self::certified_boot_resource(resource),
        ensures
            res.wf(),
            res.id() == resource.id(),
            res@ == resource.view(),
    {
        Self { resource }
    }

    /// Two sessions for the same CPU cannot simultaneously hold its authority.
    pub proof fn lemma_exclusive(tracked &mut self, tracked other: &Self)
        requires
            old(self).wf(),
            other.wf(),
        ensures
            *final(self) == *old(self),
            final(self)@.cpu != other@.cpu,
    {
        self.resource.validate_with_other(&other.resource);
    }
}

/// Readable offsets used by the current APIC implementation.
pub open spec fn readable_offset(offset: u32) -> bool {
    offset == 0x20 || offset == 0x30 || offset == 0x280 || offset == 0x300 || offset == 0x390
}

/// Writable offsets and values used by the current APIC implementation.
pub open spec fn writable_offset(offset: u32, value: u32) -> bool {
    match offset {
        0xb0 | 0x280 => value == 0,
        0xf0 => value & !0x1ffu32 == 0,
        0x300 => valid_icr_low(value),
        0x310 => value & 0x00ff_ffff == 0,
        0x320 => valid_lvt_timer(value as u64),
        0x380 => true,
        0x3e0 => value & !0xbu32 == 0,
        _ => false,
    }
}

// The OSTD model supplies register policy and hardware effects; the library
// only assumes them for a platform-certified resource.
impl IoAccess for ApicAccess {
    open spec fn mmio_read_ok(self, addr: usize) -> bool {
        self.wf() && self@.mmio_read_addr(addr)
    }

    open spec fn mmio_write_ok(self, addr: usize, value: u32) -> bool {
        self.wf() && self@.mmio_write_addr(addr, value)
    }

    open spec fn msr_read_ok(self, reg: u32) -> bool {
        self.wf() && self@.msr_read(reg)
    }

    open spec fn msr_write_ok(self, reg: u32, value: u64) -> bool {
        self.wf() && self@.msr_write(reg, value)
    }

    open spec fn msr_read_value(self, reg: u32, value: u64) -> bool {
        (reg == 0x1b ==> value == self@.base_msr) && (reg == 0x830 ==> value & 0x1000u64 == 0)
    }

    open spec fn msr_write_effect(self, next: Self, reg: u32, value: u64) -> bool {
        &&& next.wf()
        &&& next.id() == self.id()
        &&& next@ == self@.after_msr_write(reg, value)
        &&& (reg != 0x1b && reg != 0x830 ==> next == self)
    }
}

/// Timer LVT encoding subset: vector, mask, and the three defined timer modes.
pub open spec fn valid_lvt_timer(value: u64) -> bool {
    value <= u32::MAX && value & !0x7_00ffu64 == 0 && ((value >> 17) & 3) != 3
}

/// First-stage ICR subset: Fixed, physical, edge, with a non-exception vector.
/// INIT/SIPI and other delivery modes need their own later protocol model.
pub open spec fn valid_icr_low(value: u32) -> bool {
    value & 0xfff3_3000 == 0 && ((value >> 8) & 7) == 0 && (value & 0x8800) == 0 && (value & 0xff)
        >= 32
}

} // verus!

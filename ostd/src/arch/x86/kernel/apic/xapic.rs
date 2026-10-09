// SPDX-License-Identifier: MPL-2.0
//! CPU-local xAPIC MMIO backend.
//!
//! Requires the access session and mapping modeled in `specs::arch::apic`.
//! The existing `send_ipi` body remains trusted.
#![expect(dead_code)]

use vstd::prelude::*;
use vstd_extra::debug_assert;

#[cfg(verus_keep_ghost_body)]
use vstd_extra::external::x86::MsrAccess;

use crate::specs::arch::apic::ApicAccess;

// Attach verification resources without changing qualified core::ptr calls.
#[cfg(verus_keep_ghost_body)]
mod core {
    pub use ::core::*;
    pub use vstd_extra::external::ptr;
}

use x86::apic::xapic;

use super::ApicTimer;
use crate::mm;

verus! {

// `align_of` has no primitive axiom; pin it (compiler-checked, not trusted).
global layout u32 is size == 4, align == 4;

const IA32_APIC_BASE_MSR: u32 = 0x1B;

// Processor is a BSP
const IA32_APIC_BASE_MSR_BSP: u32 = 0x100;

// Enable bit
const IA32_APIC_BASE_MSR_ENABLE: u64 = 0x800;

const APIC_LVT_MASK_BITS: u32 = 1 << 16;

// Ghost<usize> has no Debug implementation; retain the original derive
// in the erased executable, where the proof-only CPU field is absent.
#[cfg_attr(not(verus_keep_ghost_body), derive(Debug))]
pub struct XApic {
    mmio_start: *mut u32,
    #[cfg(verus_keep_ghost_body)]
    ghost_cpu: Ghost<usize>,
}

impl XApic {
    /// CPU associated with this instance by its constructor's access resource.
    pub closed spec fn cpu_spec(self) -> usize {
        self.ghost_cpu@
    }

    // The register file fits in the address space and is u32-aligned.
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.mmio_start@.addr + 1024 <= usize::MAX && self.mmio_start@.addr % 4 == 0
    }

    /// Base of this instance's MMIO window.
    pub closed spec fn mmio_addr(self) -> usize {
        self.mmio_start@.addr
    }

    /// Trusted result of the existing CPUID.01H:EDX[8] implementation.
    /// This differs from the architectural APIC flag at bit 9; no support
    /// guarantee is derived from this predicate.
    pub uninterp spec fn has_xapic_spec(cpu: usize) -> bool;
}

} // verus!
// Instances are local to their CPU.
impl !Send for XApic {}
impl !Sync for XApic {}

#[verus_verify]
impl XApic {
    /* Existing trusted constructor: the verifier rejects the integer-to-pointer
     * cast. The session supplies the mapping; this function does not certify it.
     */
    #[verus_verify(external_body)]
    #[verus_spec(ret =>
        with Tracked(access): Tracked<&mut ApicAccess>
        requires
            old(access).wf(),
            old(access)@.mmio_mapped,
            old(access)@.mmio_vaddr == mm::paddr_to_vaddr(old(access)@.mmio_paddr),
        ensures
            *final(access) == *old(access),
            ret.is_some() == XApic::has_xapic_spec(old(access)@.cpu),
            ret matches Some(x) ==> {
                &&& x.mmio_addr() == old(access)@.mmio_vaddr
                &&& x.cpu_spec() == old(access)@.cpu
                &&& x.mmio_addr() + 1024 <= usize::MAX
                &&& x.mmio_addr() % 4 == 0
            },
    )]
    pub fn new() -> Option<Self> {
        if !(#[verus_spec(with Tracked(&mut *access))]
        Self::has_xapic())
        {
            return None;
        }
        let address = mm::paddr_to_vaddr(
            #[verus_spec(with Tracked(&mut *access))]
            get_xapic_base_address(),
        );
        /* Associate the erased instance metadata with the supplied CPU resource.
         * Origin Rust: Some(Self { mmio_start: address as *mut u32 })
         */
        proof_with! { ghost_cpu: Ghost(access@.cpu) }
        let apic = Self {
            mmio_start: address as *mut u32,
        };
        Some(apic)
    }

    /// Reads a register from the MMIO region.
    #[verus_spec(
        with Tracked(access): Tracked<&mut ApicAccess>
        requires
            old(access).wf(),
            self.cpu_spec() == old(access)@.cpu,
            old(access)@.mmio_read(self.mmio_addr(), offset),
            offset % 4 == 0,
            offset < 1024,
        ensures *final(access) == *old(access),
    )]
    fn read(&self, offset: u32) -> u32 {
        assert!(offset as usize % 4 == 0);
        let index = offset as usize / 4;
        debug_assert!(index < 256);
        proof! { assert(index * 4 == offset); }

        /* MMIO lies outside Rust allocations; add requires allocation bounds.
         * Origin Rust: unsafe { core::ptr::read_volatile(self.mmio_start.add(index)) }
         */
        unsafe {
            proof_with!(Tracked(&mut *access));
            core::ptr::read_volatile(self.mmio_start.wrapping_add(index))
        }
    }

    /// Writes a register in the MMIO region.
    #[verus_spec(
        with Tracked(access): Tracked<&mut ApicAccess>
        requires
            old(access).wf(),
            self.cpu_spec() == old(access)@.cpu,
            old(access)@.mmio_write(self.mmio_addr(), offset, val),
            offset % 4 == 0,
            offset < 1024,
        ensures *final(access) == *old(access),
    )]
    fn write(&self, offset: u32, val: u32) {
        assert!(offset as usize % 4 == 0);
        let index = offset as usize / 4;
        debug_assert!(index < 256);
        proof! { assert(index * 4 == offset); }

        /* MMIO lies outside Rust allocations; preserve the original address.
         * Origin Rust: unsafe { core::ptr::write_volatile(self.mmio_start.add(index), val) }
         */
        unsafe {
            proof_with!(Tracked(&mut *access));
            core::ptr::write_volatile(self.mmio_start.wrapping_add(index), val)
        }
    }
    #[verus_spec(
        with Tracked(access): Tracked<&mut ApicAccess>
        requires
            old(access).wf(),
            self.cpu_spec() == old(access)@.cpu,
            old(access)@.mmio_mapped,
            self.mmio_addr() == old(access)@.mmio_vaddr,
            !old(access)@.x2apic(),
        ensures
            final(access).wf(),
            final(access).id() == old(access).id(),
            final(access)@ == old(access)@.after_msr_write(
                0x1b, (old(access)@.base_msr & 0xf_ffff_f000) | 0x800),
            final(self).access_ok(*final(access)),
    )]
    pub fn enable(&mut self) {
        proof! {
            access@.lemma_enable_xapic();
        }
        // Enable xAPIC
        /* Reborrow the erased resource separately for the two original calls.
         * Origin Rust: set_apic_base_address(get_xapic_base_address());
         */
        proof_with!(Tracked(&mut *access));
        let address = get_xapic_base_address();
        proof_with!(Tracked(&mut *access));
        set_apic_base_address(address);

        // Enable the software APIC with spurious vector 15.
        let svr: u32 = (1 << 8) | 15;
        proof! { assert(svr & !0x1ffu32 == 0) by (bit_vector) requires svr == (1u32 << 8) | 15u32; }
        proof_with!(Tracked(&mut *access));
        self.write(xapic::XAPIC_SVR, svr);
    }

    /* `__cpuid` has no verifier model; trusted body under `external_body`. */
    #[verus_verify(external_body)]
    #[verus_spec(
        with Tracked(access): Tracked<&mut ApicAccess>
        requires old(access).wf(),
        ensures *final(access) == *old(access),
        returns XApic::has_xapic_spec(old(access)@.cpu),
    )]
    pub(super) fn has_xapic() -> bool {
        let value = unsafe { core::arch::x86_64::__cpuid(1) };
        value.edx & 0x100 != 0
    }
}

// `#[verus_spec(with ...)]` does not support trait methods on this toolchain;
// explicit Tracked arguments carry the erased resource across the trait boundary.
verus! {

impl super::Apic for XApic {
    open spec fn x2apic_backend(&self) -> bool {
        false
    }

    open spec fn icr_access_ok(&self, access: ApicAccess, icr: super::Icr) -> bool {
        !icr.is_x2apic_spec() && access@.mmio_write(
            self.mmio_addr(),
            0x310,
            (icr.raw_spec() >> 32) as u32,
        ) && access@.mmio_write(self.mmio_addr(), 0x300, icr.raw_spec() as u32)
    }

    fn id(&self, Tracked(access): Tracked<&mut ApicAccess>) -> u32 {
        #[verus_spec(with Tracked(&mut *access))]
        self.read(xapic::XAPIC_ID)
    }

    fn version(&self, Tracked(access): Tracked<&mut ApicAccess>) -> u32 {
        #[verus_spec(with Tracked(&mut *access))]
        self.read(xapic::XAPIC_VERSION)
    }

    fn eoi(&self, Tracked(access): Tracked<&mut ApicAccess>) {
        #[verus_spec(with Tracked(&mut *access))]
        self.write(xapic::XAPIC_EOI, 0);
    }

    // Existing trusted body: submission and polling are not verified.
    #[verus_verify(external_body)]
    unsafe fn send_ipi(&self, icr: super::Icr, Tracked(access): Tracked<&mut ApicAccess>) {
        let _guard = crate::trap::irq::disable_local();
        #[verus_spec(with Tracked(&mut *access))]
        self.write(xapic::XAPIC_ESR, 0);
        // The upper 32 bits of ICR must be written into XAPIC_ICR1 first,
        // because writing into XAPIC_ICR0 will trigger the action of
        // interrupt sending.
        #[verus_spec(with Tracked(&mut *access))]
        self.write(xapic::XAPIC_ICR1, icr.upper());
        #[verus_spec(with Tracked(&mut *access))]
        self.write(xapic::XAPIC_ICR0, icr.lower());
        loop {
            let icr = #[verus_spec(with Tracked(&mut *access))]
            self.read(xapic::XAPIC_ICR0);
            if ((icr >> 12) & 0x1) == 0 {
                break;
            }
            if #[verus_spec(with Tracked(&mut *access))]
            self.read(xapic::XAPIC_ESR) > 0 {
                break;
            }
        }
    }
}

impl ApicTimer for XApic {
    closed spec fn access_ok(&self, access: ApicAccess) -> bool {
        self.cpu_spec() == access@.cpu && access@.xapic() && access@.mmio_mapped && self.mmio_addr()
            == access@.mmio_vaddr
    }

    fn set_timer_init_count(&self, value: u64, Tracked(access): Tracked<&mut ApicAccess>) {
        #[verus_spec(with Tracked(&mut *access))]
        self.write(xapic::XAPIC_TIMER_INIT_COUNT, value as u32);
    }

    fn timer_current_count(&self, Tracked(access): Tracked<&mut ApicAccess>) -> u64 {
        (#[verus_spec(with Tracked(&mut *access))]
        self.read(xapic::XAPIC_TIMER_CURRENT_COUNT)) as u64
    }

    fn set_lvt_timer(&self, value: u64, Tracked(access): Tracked<&mut ApicAccess>) {
        #[verus_spec(with Tracked(&mut *access))]
        self.write(xapic::XAPIC_LVT_TIMER, value as u32);
    }

    fn set_timer_div_config(
        &self,
        div_config: super::DivideConfig,
        Tracked(access): Tracked<&mut ApicAccess>,
    ) {
        proof {
            div_config.lemma_register_value();
        }

        #[verus_spec(with Tracked(&mut *access))]
        self.write(xapic::XAPIC_TIMER_DIV_CONF, div_config as u32);
    }
}

} // verus!
/// Sets APIC base address and enables it
#[verus_verify]
#[verus_spec(
    with Tracked(access): Tracked<&mut ApicAccess>
    requires
        old(access).wf(),
        !old(access)@.x2apic(),
        address == (old(access)@.base_msr & 0xf_ffff_f000) as usize,
    ensures
        final(access).wf(),
        final(access).id() == old(access).id(),
        final(access)@ == old(access)@.after_msr_write(0x1b, address as u64 | 0x800),
)]
fn set_apic_base_address(address: usize) {
    proof! {
        access@.lemma_enable_xapic();
    }
    unsafe {
        #[verus_spec(with Tracked(&mut *access))]
        x86_64::registers::model_specific::Msr::new(IA32_APIC_BASE_MSR)
            .write(address as u64 | IA32_APIC_BASE_MSR_ENABLE);
    }
}

/// Gets xAPIC base address
#[verus_verify]
#[verus_spec(ret =>
    with Tracked(access): Tracked<&mut ApicAccess>
    requires old(access).wf(),
    ensures
        *final(access) == *old(access),
        ret == (old(access)@.base_msr & 0xf_ffff_f000) as usize,
)]
pub(super) fn get_xapic_base_address() -> usize {
    unsafe {
        (#[verus_spec(with Tracked(&mut *access))]
        x86_64::registers::model_specific::Msr::new(IA32_APIC_BASE_MSR).read()
            & 0xf_ffff_f000) as usize
    }
}

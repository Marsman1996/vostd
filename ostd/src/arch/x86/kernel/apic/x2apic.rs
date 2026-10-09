// SPDX-License-Identifier: MPL-2.0
//! CPU-local x2APIC MSR backend.
//!
//! Requires the access session modeled in `specs::arch::apic`.
use vstd::prelude::*;

#[cfg(verus_keep_ghost_body)]
use vstd_extra::external::x86::{_VERUS_VERIFIED_rdmsr, _VERUS_VERIFIED_wrmsr};

use crate::specs::arch::apic::ApicAccess;

use x86::msr::{
    IA32_APIC_BASE, IA32_X2APIC_APICID, IA32_X2APIC_CUR_COUNT, IA32_X2APIC_DIV_CONF,
    IA32_X2APIC_EOI, IA32_X2APIC_ESR, IA32_X2APIC_ICR, IA32_X2APIC_INIT_COUNT,
    IA32_X2APIC_LVT_TIMER, IA32_X2APIC_SIVR, IA32_X2APIC_VERSION, rdmsr, wrmsr,
};

use super::ApicTimer;

verus! {

// Ghost<usize> has no Debug implementation; retain the original derive
// in the erased executable, where the proof-only CPU field is absent.
#[cfg_attr(not(verus_keep_ghost_body), derive(Debug))]
pub struct X2Apic {
    _private: (),
    #[cfg(verus_keep_ghost_body)]
    ghost_cpu: Ghost<usize>,
}

impl X2Apic {
    /// CPU associated with this instance by its constructor's access resource.
    pub closed spec fn cpu_spec(self) -> usize {
        self.ghost_cpu@
    }
}

} // verus!
// Instances are local to their CPU.
impl !Send for X2Apic {}
impl !Sync for X2Apic {}

#[verus_verify]
impl X2Apic {
    #[verus_spec(ret =>
        with Tracked(access): Tracked<&mut ApicAccess>
        requires old(access).wf(),
        ensures
            *final(access) == *old(access),
            ret.is_some() == old(access)@.x2apic_supported,
            ret matches Some(x) ==> x.cpu_spec() == old(access)@.cpu,
    )]
    pub(crate) fn new() -> Option<Self> {
        if !(#[verus_spec(with Tracked(&mut *access))]
        Self::has_x2apic())
        {
            return None;
        }
        /* Attach erased CPU metadata from the caller's access resource.
         * Origin Rust: Some(Self { _private: () })
         */
        proof_with! { ghost_cpu: Ghost(access@.cpu) }
        let apic = Self { _private: () };
        Some(apic)
    }

    /* `__cpuid` has no verifier model; trusted body under `external_body`. */
    #[verus_verify(external_body)]
    #[verus_spec(
        with Tracked(access): Tracked<&mut ApicAccess>
        requires old(access).wf(),
        ensures *final(access) == *old(access),
        returns old(access)@.x2apic_supported,
    )]
    pub(super) fn has_x2apic() -> bool {
        let value = unsafe { core::arch::x86_64::__cpuid(1) };
        value.ecx & 0x20_0000 != 0
    }
    #[verus_spec(
        with Tracked(access): Tracked<&mut ApicAccess>
        requires
            old(access).wf(), old(access)@.x2apic_supported,
            old(access)@.base_msr & 0x800 != 0,
            self.cpu_spec() == old(access)@.cpu,
        ensures
            final(access).wf(),
            final(access).id() == old(access).id(),
            final(access)@ == old(access)@.after_msr_write(0x1b, old(access)@.base_msr | 0xc00),
            final(self).access_ok(*final(access)),
    )]
    pub fn enable(&mut self) {
        const X2APIC_ENABLE_BITS: u64 = {
            // IA32_APIC_BASE MSR's EN bit: xAPIC global enable/disable
            const EN_BIT_IDX: u8 = 11;
            // IA32_APIC_BASE MSR's EXTD bit: Enable x2APIC mode
            const EXTD_BIT_IDX: u8 = 10;
            (1 << EN_BIT_IDX) | (1 << EXTD_BIT_IDX)
        };
        proof! {
            access@.lemma_enable_x2apic();
            assert(X2APIC_ENABLE_BITS == 0xc00) by (bit_vector);
        }
        // SAFETY: The access session establishes privilege, mode, and register permissions.
        unsafe {
            // Enable x2APIC mode globally
            proof_with!(Tracked(&mut *access));
            let mut base = rdmsr(IA32_APIC_BASE);
            // Enable x2APIC and xAPIC if they are not enabled by default
            if base & X2APIC_ENABLE_BITS != X2APIC_ENABLE_BITS {
                base |= X2APIC_ENABLE_BITS;
                proof_with!(Tracked(&mut *access));
                wrmsr(IA32_APIC_BASE, base);
            }

            // Enable the software APIC with spurious vector 15.
            let svr: u64 = (1 << 8) | 15;
            proof! { assert(svr & !0x1ffu64 == 0 && svr <= u32::MAX) by (bit_vector) requires svr == (1u64 << 8) | 15u64; }
            proof_with!(Tracked(&mut *access));
            wrmsr(IA32_X2APIC_SIVR, svr);
        }
    }
}

// Explicit Tracked arguments are necessary because `with` is unsupported on traits.
verus! {

impl super::Apic for X2Apic {
    open spec fn x2apic_backend(&self) -> bool {
        true
    }

    open spec fn icr_access_ok(&self, access: ApicAccess, icr: super::Icr) -> bool {
        icr.is_x2apic_spec() && access@.msr_write(0x830, icr.raw_spec())
    }

    fn id(&self, Tracked(access): Tracked<&mut ApicAccess>) -> u32 {
        unsafe {
            (#[verus_spec(with Tracked(&mut *access))]
            rdmsr(IA32_X2APIC_APICID)) as u32
        }
    }

    fn version(&self, Tracked(access): Tracked<&mut ApicAccess>) -> u32 {
        unsafe {
            (#[verus_spec(with Tracked(&mut *access))]
            rdmsr(IA32_X2APIC_VERSION)) as u32
        }
    }

    fn eoi(&self, Tracked(access): Tracked<&mut ApicAccess>) {
        unsafe {
            #[verus_spec(with Tracked(&mut *access))]
            wrmsr(IA32_X2APIC_EOI, 0);
        }
    }

    unsafe fn send_ipi(&self, icr: super::Icr, Tracked(access): Tracked<&mut ApicAccess>) {
        let _guard = crate::trap::irq::disable_local();
        // SAFETY: The caller supplies authority for this CPU and permits the ICR encoding.
        unsafe {
            #[verus_spec(with Tracked(&mut *access))]
            wrmsr(IA32_X2APIC_ESR, 0);
            /* Carry authority and access the renamed field.
             * Origin Rust: wrmsr(IA32_X2APIC_ICR, icr.0)
             */
            #[verus_spec(with Tracked(&mut *access))]
            wrmsr(IA32_X2APIC_ICR, icr.raw);
            let ghost submitted = access@;
            loop
                invariant
                    access.wf(),
                    self.access_ok(*access),
                    access@ == submitted,
                    access.id() == old(access).id(),
                    submitted == old(access)@.after_msr_write(0x830, icr.raw_spec()),
                decreases 0nat,
            {
                let icr = #[verus_spec(with Tracked(&mut *access))]
                rdmsr(IA32_X2APIC_ICR);
                proof {
                    assert(((icr >> 12) & 0x1) == 0) by (bit_vector)
                        requires
                            icr & 0x1000u64 == 0,
                    ;
                }
                if ((icr >> 12) & 0x1) == 0 {
                    break;
                }
                if #[verus_spec(with Tracked(&mut *access))]
                rdmsr(IA32_X2APIC_ESR) > 0 {
                    break;
                }
            }
        }
    }
}

impl ApicTimer for X2Apic {
    closed spec fn access_ok(&self, access: ApicAccess) -> bool {
        self.cpu_spec() == access@.cpu && access@.x2apic()
    }

    fn set_timer_init_count(&self, value: u64, Tracked(access): Tracked<&mut ApicAccess>) {
        unsafe {
            #[verus_spec(with Tracked(&mut *access))]
            wrmsr(IA32_X2APIC_INIT_COUNT, value);
        }
    }

    fn timer_current_count(&self, Tracked(access): Tracked<&mut ApicAccess>) -> u64 {
        unsafe {
            #[verus_spec(with Tracked(&mut *access))]
            rdmsr(IA32_X2APIC_CUR_COUNT)
        }
    }

    fn set_lvt_timer(&self, value: u64, Tracked(access): Tracked<&mut ApicAccess>) {
        unsafe {
            #[verus_spec(with Tracked(&mut *access))]
            wrmsr(IA32_X2APIC_LVT_TIMER, value);
        }
    }

    fn set_timer_div_config(
        &self,
        div_config: super::DivideConfig,
        Tracked(access): Tracked<&mut ApicAccess>,
    ) {
        proof {
            div_config.lemma_register_value();
        }
        unsafe {
            #[verus_spec(with Tracked(&mut *access))]
            wrmsr(IA32_X2APIC_DIV_CONF, div_config as u64);
        }
    }
}

} // verus!

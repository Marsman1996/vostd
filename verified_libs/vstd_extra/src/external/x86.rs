//! External specifications for the [`x86` crate](https://crates.io/crates/x86)
//! (0.52.0) constants and MSR accessors. Constant values are trusted to match
//! the crate sources; the original constants are re-exported below. Also models the
//! [`x86_64` crate](https://crates.io/crates/x86_64) (0.14.13) MSR accessors.
use vstd::prelude::*;

pub use x86::apic::xapic::{
    XAPIC_EOI, XAPIC_ESR, XAPIC_ICR0, XAPIC_ICR1, XAPIC_ID, XAPIC_LVT_TIMER, XAPIC_SVR,
    XAPIC_TIMER_CURRENT_COUNT, XAPIC_TIMER_DIV_CONF, XAPIC_TIMER_INIT_COUNT, XAPIC_VERSION,
};
pub use x86::msr::{
    IA32_APIC_BASE, IA32_X2APIC_APICID, IA32_X2APIC_CUR_COUNT, IA32_X2APIC_DIV_CONF,
    IA32_X2APIC_EOI, IA32_X2APIC_ESR, IA32_X2APIC_ICR, IA32_X2APIC_INIT_COUNT,
    IA32_X2APIC_LVT_TIMER, IA32_X2APIC_SIVR, IA32_X2APIC_VERSION,
};
use x86_64::registers::model_specific::Msr;

use super::io::{IoAccess, certified_io_access};

verus! {

pub assume_specification[ x86::apic::xapic::XAPIC_ID ] -> u32
    returns
        0x020u32,
;

pub assume_specification[ x86::apic::xapic::XAPIC_VERSION ] -> u32
    returns
        0x030u32,
;

pub assume_specification[ x86::apic::xapic::XAPIC_EOI ] -> u32
    returns
        0x0B0u32,
;

pub assume_specification[ x86::apic::xapic::XAPIC_SVR ] -> u32
    returns
        0x0F0u32,
;

pub assume_specification[ x86::apic::xapic::XAPIC_ESR ] -> u32
    returns
        0x280u32,
;

pub assume_specification[ x86::apic::xapic::XAPIC_ICR0 ] -> u32
    returns
        0x300u32,
;

pub assume_specification[ x86::apic::xapic::XAPIC_ICR1 ] -> u32
    returns
        0x310u32,
;

pub assume_specification[ x86::apic::xapic::XAPIC_LVT_TIMER ] -> u32
    returns
        0x320u32,
;

pub assume_specification[ x86::apic::xapic::XAPIC_TIMER_INIT_COUNT ] -> u32
    returns
        0x380u32,
;

pub assume_specification[ x86::apic::xapic::XAPIC_TIMER_CURRENT_COUNT ] -> u32
    returns
        0x390u32,
;

pub assume_specification[ x86::apic::xapic::XAPIC_TIMER_DIV_CONF ] -> u32
    returns
        0x3E0u32,
;

pub assume_specification[ x86::msr::IA32_APIC_BASE ] -> u32
    returns
        0x1bu32,
;

pub assume_specification[ x86::msr::IA32_X2APIC_APICID ] -> u32
    returns
        0x802u32,
;

pub assume_specification[ x86::msr::IA32_X2APIC_VERSION ] -> u32
    returns
        0x803u32,
;

pub assume_specification[ x86::msr::IA32_X2APIC_EOI ] -> u32
    returns
        0x80bu32,
;

pub assume_specification[ x86::msr::IA32_X2APIC_SIVR ] -> u32
    returns
        0x80fu32,
;

pub assume_specification[ x86::msr::IA32_X2APIC_ESR ] -> u32
    returns
        0x828u32,
;

pub assume_specification[ x86::msr::IA32_X2APIC_ICR ] -> u32
    returns
        0x830u32,
;

pub assume_specification[ x86::msr::IA32_X2APIC_LVT_TIMER ] -> u32
    returns
        0x832u32,
;

pub assume_specification[ x86::msr::IA32_X2APIC_INIT_COUNT ] -> u32
    returns
        0x838u32,
;

pub assume_specification[ x86::msr::IA32_X2APIC_CUR_COUNT ] -> u32
    returns
        0x839u32,
;

pub assume_specification[ x86::msr::IA32_X2APIC_DIV_CONF ] -> u32
    returns
        0x83eu32,
;

// Verification-only proxies retain the original x86 0.52.0 MSR primitives.
#[cfg(verus_keep_ghost)]
#[verifier::external]
pub unsafe fn _VERUS_VERIFIED_rdmsr<A: IoAccess>(reg: u32, access: Tracked<&mut A>) -> u64 {
    unsafe { x86::msr::rdmsr(reg) }
}

#[cfg(verus_keep_ghost)]
pub assume_specification<A: IoAccess>[ _VERUS_VERIFIED_rdmsr::<A> ](
    reg: u32,
    Tracked(access): Tracked<&mut A>,
) -> (ret: u64)
    requires
        certified_io_access(*old(access)),
        old(access).msr_read_ok(reg),
    ensures
        *final(access) == *old(access),
        old(access).msr_read_value(reg, ret),
;

#[cfg(verus_keep_ghost)]
#[verifier::external]
pub unsafe fn _VERUS_VERIFIED_wrmsr<A: IoAccess>(reg: u32, value: u64, access: Tracked<&mut A>) {
    unsafe { x86::msr::wrmsr(reg, value) }
}

#[cfg(verus_keep_ghost)]
pub assume_specification<A: IoAccess>[ _VERUS_VERIFIED_wrmsr::<A> ](
    reg: u32,
    value: u64,
    Tracked(access): Tracked<&mut A>,
)
    requires
        certified_io_access(*old(access)),
        old(access).msr_write_ok(reg, value),
    ensures
        certified_io_access(*final(access)),
        old(access).msr_write_effect(*final(access), reg, value),
;

/// Opaque external wrapper for the x86_64 crate's MSR handle.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExMsr(Msr);

/// Index stored by an opaque Msr handle (x86_64 0.14.13, Msr::new).
pub uninterp spec fn msr_index(msr: Msr) -> u32;

/// [`Msr::new`](https://docs.rs/x86_64/0.14.13/x86_64/registers/model_specific/struct.Msr.html#method.new).
pub assume_specification[ Msr::new ](reg: u32) -> (ret: Msr)
    ensures
        msr_index(ret) == reg,
    opens_invariants none
    no_unwind
;

// The extension trait exists only for verifier method resolution. Erasure calls
// x86_64 0.14.13 Msr::read/write directly, including their original asm options.
#[cfg(verus_keep_ghost)]
#[verifier::external]
pub trait MsrAccess {
    unsafe fn _VERUS_VERIFIED_read<A: IoAccess>(&self, access: Tracked<&mut A>) -> u64;

    unsafe fn _VERUS_VERIFIED_write<A: IoAccess>(&mut self, value: u64, access: Tracked<&mut A>);
}

#[cfg(verus_keep_ghost)]
#[verifier::external]
impl MsrAccess for Msr {
    unsafe fn _VERUS_VERIFIED_read<A: IoAccess>(&self, access: Tracked<&mut A>) -> u64 {
        unsafe { self.read() }
    }

    unsafe fn _VERUS_VERIFIED_write<A: IoAccess>(&mut self, value: u64, access: Tracked<&mut A>) {
        unsafe { self.write(value) }
    }
}

#[cfg(verus_keep_ghost)]
pub assume_specification<A: IoAccess>[ <Msr as MsrAccess>::_VERUS_VERIFIED_read::<A> ](
    msr: &Msr,
    Tracked(access): Tracked<&mut A>,
) -> (ret: u64)
    requires
        certified_io_access(*old(access)),
        old(access).msr_read_ok(msr_index(*msr)),
    ensures
        *final(access) == *old(access),
        old(access).msr_read_value(msr_index(*msr), ret),
;

#[cfg(verus_keep_ghost)]
pub assume_specification<A: IoAccess>[ <Msr as MsrAccess>::_VERUS_VERIFIED_write::<A> ](
    msr: &mut Msr,
    value: u64,
    Tracked(access): Tracked<&mut A>,
)
    requires
        certified_io_access(*old(access)),
        old(access).msr_write_ok(msr_index(*old(msr)), value),
    ensures
        *final(msr) == *old(msr),
        certified_io_access(*final(access)),
        old(access).msr_write_effect(*final(access), msr_index(*old(msr)), value),
;

} // verus!

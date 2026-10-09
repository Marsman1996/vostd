// SPDX-License-Identifier: MPL-2.0
//! Resource interface for external device access. Defining a policy does not
//! grant permission: the platform must certify its connection to hardware.
use vstd::prelude::*;

verus! {

pub trait IoAccess: Sized {
    spec fn mmio_read_ok(self, addr: usize) -> bool;

    spec fn mmio_write_ok(self, addr: usize, value: u32) -> bool;

    spec fn msr_read_ok(self, reg: u32) -> bool;

    spec fn msr_write_ok(self, reg: u32, value: u64) -> bool;

    spec fn msr_read_value(self, reg: u32, value: u64) -> bool;

    spec fn msr_write_effect(self, next: Self, reg: u32, value: u64) -> bool;
}

/// Certifies that this resource's policy and effects describe its real device.
/// No axiom makes a caller-defined policy acquire hardware authority.
pub uninterp spec fn certified_io_access<A>(access: A) -> bool;

} // verus!

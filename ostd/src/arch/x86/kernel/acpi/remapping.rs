// SPDX-License-Identifier: MPL-2.0
#![expect(dead_code)]

//! Remapping structures of DMAR table.
//!
//! This file defines these structures and provides a `Debug` implementation to see the value
//! inside these structures.
//!
//! Most of the introduction are copied from Intel vt-directed-io-specification.
use ostd_pod::{decode_pod, from_bytes_spec};
use vstd::{
    prelude::*,
    seq::{
        lemma_seq_ext_equal, lemma_seq_new_index, lemma_seq_new_len,
        lemma_seq_push_index_different, lemma_seq_push_index_same, lemma_seq_push_len,
    },
    utf8::{encode_utf8, valid_utf8},
};

use alloc::{borrow::ToOwned, string::String, vec::Vec};
use core::fmt::Debug;

use ostd_pod::Pod;

verus! {

/// DMA-remapping hardware unit definition (DRHD).
///
/// A DRHD structure uniquely represents a remapping hardware unit present in the platform.
/// There must be at least one instance of this structure for each PCI segment in the platform.
#[derive(Debug, Clone)]
pub struct Drhd {
    header: DrhdHeader,
    device_scopes: Vec<DeviceScope>,
}

} // verus!
#[verus_verify]
impl Drhd {
    #[verus_verify(dual_spec)]
    pub fn register_base_addr(&self) -> u64 {
        self.header.register_base_addr
    }
}

verus! {

impl Drhd {
    /// The DRHD header of the remapping hardware unit.
    pub closed spec fn header_spec(self) -> DrhdHeader {
        self.header
    }
}

#[repr(C)]
#[derive(Debug, Clone, Copy /*, Pod*/)]
pub struct DrhdHeader {
    typ: u16,
    length: u16,
    flags: u8,
    size: u8,
    segment_num: u16,
    register_base_addr: u64,
}

// SAFETY: The `DrhdHeader` struct is `repr(C)` and all its fields are plain old
// data, so any bit pattern is a valid value.
unsafe impl Pod for DrhdHeader {

}

impl DrhdHeader {
    pub closed spec fn length_spec(self) -> u16 {
        self.length
    }
}

/// Reserved Memory Region Reporting (RMRR).
///
/// BIOS allocated reserved memory ranges that may be DMA targets.
/// It may report each such reserved memory region through the RMRR structures, along
/// with the devices that requires access to the specified reserved memory region.
#[derive(Debug, Clone)]
pub struct Rmrr {
    header: RmrrHeader,
    device_scopes: Vec<DeviceScope>,
}

impl Rmrr {
    /// The RMRR header of the reserved memory region.
    pub closed spec fn header_spec(self) -> RmrrHeader {
        self.header
    }
}

#[repr(C)]
#[derive(Debug, Clone, Copy /*, Pod*/)]
pub struct RmrrHeader {
    typ: u16,
    length: u16,
    reserved: u16,
    segment_num: u16,
    reserved_memory_region_base_addr: u64,
    reserved_memory_region_limit_addr: u64,
}

// SAFETY: The `RmrrHeader` struct is `repr(C)` and all its fields are plain
// old data, so any bit pattern is a valid value.
unsafe impl Pod for RmrrHeader {

}

impl RmrrHeader {
    pub closed spec fn length_spec(self) -> u16 {
        self.length
    }
}

/// Root Port ATS Capability Reporting (ATSR).
///
/// This structure is applicable only for platforms supporting Device-TLBs as reported through the
/// Extended Capability Register.
#[derive(Debug, Clone)]
pub struct Atsr {
    header: AtsrHeader,
    device_scopes: Vec<DeviceScope>,
}

impl Atsr {
    /// The ATSR header of the root port ATS capability.
    pub closed spec fn header_spec(self) -> AtsrHeader {
        self.header
    }
}

#[repr(C)]
#[derive(Debug, Clone, Copy /*, Pod*/)]
pub struct AtsrHeader {
    typ: u16,
    length: u16,
    flags: u8,
    reserved: u8,
    segment_num: u16,
}

// SAFETY: The `AtsrHeader` struct is `repr(C)` and all its fields are plain old
// data, so any bit pattern is a valid value.
unsafe impl Pod for AtsrHeader {

}

impl AtsrHeader {
    pub closed spec fn length_spec(self) -> u16 {
        self.length
    }
}

/// Remapping Hardware Status Affinity (RHSA).
///
/// It is applicable for platforms supporting non-uniform memory (NUMA),
/// where Remapping hardware units spans across nodes.
/// This optional structure provides the association between each Remapping hardware unit (identified
/// by its espective Base Address) and the proximity domain to which that hardware unit belongs.
#[repr(C)]
#[derive(Debug, Clone, Copy /*, Pod*/)]
pub struct Rhsa {
    typ: u16,
    length: u16,
    flags: u32,
    register_base_addr: u64,
    proximity_domain: u32,
}

// SAFETY: The `Rhsa` struct is `repr(C)` and all its fields are plain old data,
// so any bit pattern is a valid value.
unsafe impl Pod for Rhsa {

}

/// ACPI Name-space Device Declaration (ANDD).
///
/// An ANDD structure uniquely represents an ACPI name-space
/// enumerated device capable of issuing DMA requests in the platform.
#[derive(Debug, Clone)]
pub struct Andd {
    header: AnddHeader,
    acpi_object_name: String,
}

impl Andd {
    /// The ANDD header of the ACPI name-space device.
    pub closed spec fn header_spec(self) -> AnddHeader {
        self.header
    }

    /// The characters of the ACPI object name.
    pub closed spec fn acpi_object_name_spec(self) -> Seq<char> {
        self.acpi_object_name@
    }
}

#[repr(C)]
#[derive(Debug, Clone, Copy /*, Pod*/)]
pub struct AnddHeader {
    typ: u16,
    length: u16,
    reserved: [u8; 3],
    acpi_device_num: u8,
}

// SAFETY: The `AnddHeader` struct is `repr(C)` and all its fields are plain
// old data, so any bit pattern is a valid value.
unsafe impl Pod for AnddHeader {

}

/// SoC Integrated Address Translation Cache (SATC).
///
/// The SATC reporting structure identifies devices that have address translation cache (ATC),
/// as defined by the PCI Express Base Specification.
#[derive(Debug, Clone)]
pub struct Satc {
    header: SatcHeader,
    device_scopes: Vec<DeviceScope>,
}

impl Satc {
    /// The SATC header of the SoC integrated address translation cache.
    pub closed spec fn header_spec(self) -> SatcHeader {
        self.header
    }
}

#[repr(C)]
#[derive(Debug, Clone, Copy /*, Pod*/)]
pub struct SatcHeader {
    typ: u16,
    length: u16,
    flags: u8,
    reserved: u8,
    segment_num: u16,
}

// SAFETY: The `SatcHeader` struct is `repr(C)` and all its fields are plain old
// data, so any bit pattern is a valid value.
unsafe impl Pod for SatcHeader {

}

impl SatcHeader {
    pub closed spec fn length_spec(self) -> u16 {
        self.length
    }
}

/// SoC Integrated Device Property Reporting (SIDP).
///
/// The (SIDP) reporting structure identifies devices that have special
/// properties and that may put restrictions on how system software must configure remapping
/// structures that govern such devices in a platform where remapping hardware is enabled.
#[derive(Debug, Clone)]
pub struct Sidp {
    header: SidpHeader,
    device_scopes: Vec<DeviceScope>,
}

impl Sidp {
    /// The SIDP header of the SoC integrated device.
    pub closed spec fn header_spec(self) -> SidpHeader {
        self.header
    }
}

#[repr(C)]
#[derive(Debug, Clone, Copy /*, Pod*/)]
pub struct SidpHeader {
    typ: u16,
    length: u16,
    reserved: u16,
    segment_num: u16,
}

// SAFETY: The `SidpHeader` struct is `repr(C)` and all its fields are plain old
// data, so any bit pattern is a valid value.
unsafe impl Pod for SidpHeader {

}

impl SidpHeader {
    pub closed spec fn length_spec(self) -> u16 {
        self.length
    }
}

/// The Device Scope Structure is made up of Device Scope Entries. Each Device Scope Entry may be
/// used to indicate a PCI endpoint device
#[derive(Debug, Clone)]
pub struct DeviceScope {
    header: DeviceScopeHeader,
    path: Vec<(u8, u8)>,
}

impl DeviceScope {
    /// The header of the Device Scope Entry.
    pub closed spec fn header_spec(self) -> DeviceScopeHeader {
        self.header
    }

    /// The parsed path of the Device Scope Entry, as a sequence of byte pairs.
    pub closed spec fn path_spec(self) -> Seq<(u8, u8)> {
        self.path@
    }
}

#[repr(C)]
#[derive(Debug, Clone, Copy /*, Pod*/)]
pub struct DeviceScopeHeader {
    typ: u8,
    length: u8,
    flags: u8,
    reserved: u8,
    enum_id: u8,
    start_bus_number: u8,
}

// SAFETY: The `DeviceScopeHeader` struct is `repr(C)` and all its fields are
// plain old data, so any bit pattern is a valid value.
unsafe impl Pod for DeviceScopeHeader {

}

impl DeviceScopeHeader {
    /// The total length of the Device Scope Entry.
    pub closed spec fn length_spec(self) -> u8 {
        self.length
    }
}

/// The sequence of byte pairs read from `bytes[start..end]`, two bytes per element.
pub open spec fn path_pairs_spec(bytes: Seq<u8>, start: int, end: int) -> Seq<(u8, u8)> {
    Seq::new(((end - start) / 2) as nat, |i: int| (bytes[start + 2 * i], bytes[start + 2 * i + 1]))
}

/// Whether `bytes[start..end]` is a sequence of complete device-scope entries.
pub closed spec fn valid_device_scopes(bytes: Seq<u8>, start: int, end: int) -> bool
    decreases end - start,
{
    &&& 0 <= start <= end <= bytes.len()
    &&& if start == end {
        true
    } else {
        let remaining = bytes.subrange(start, end);
        let scope_len = from_bytes_spec::<DeviceScopeHeader>(remaining).length_spec() as int;
        &&& 0 < scope_len
        &&& core::mem::size_of::<DeviceScopeHeader>() <= scope_len <= end - start
        &&& (scope_len - core::mem::size_of::<DeviceScopeHeader>()) % 2 == 0
        &&& valid_device_scopes(bytes, start + scope_len, end)
    }
}

} // verus!
macro_rules! impl_from_bytes {
    ($(($struct:tt, $header_struct:tt),)*) => {
        $(#[verus_verify]
        impl $struct {
            #[doc = concat!("Parses a [`", stringify!($struct), "`] from bytes.")]
            ///
            /// # Panics
            ///
            #[doc = concat!(
                "This method may panic if the bytes do not represent a valid [`",
                stringify!($struct),
                "`].",
            )]
            #[verus_spec(ret =>
                requires
                    bytes@.len() >= core::mem::size_of::<$header_struct>(),
                    from_bytes_spec::<$header_struct>(bytes@).length_spec() as int
                        == bytes@.len(),
                    valid_device_scopes(
                        bytes@,
                        core::mem::size_of::<$header_struct>() as int,
                        bytes@.len() as int,
                    ),
                ensures
                    ret.header_spec() == decode_pod::<$header_struct>(
                        bytes@.subrange(0, core::mem::size_of::<$header_struct>() as int),
                    ),
            )]
            pub fn from_bytes(bytes: &[u8]) -> Self {
                let header = $header_struct::from_bytes(bytes);
                debug_assert!(header.length as usize == bytes.len());

                let mut index = core::mem::size_of::<$header_struct>();
                let mut device_scopes = Vec::new();
                #[verus_spec(invariant
                    core::mem::size_of::<$header_struct>() <= index <= header.length,
                    header.length as usize == bytes@.len(),
                    valid_device_scopes(bytes@, index as int, bytes@.len() as int),
                    decreases header.length as usize - index,
                )]
                while index != (header.length as usize) {
                    let val = DeviceScope::from_bytes_prefix(&bytes[index..]);
                    index += val.header.length as usize;
                    device_scopes.push(val);
                }

                Self{
                    header,
                    device_scopes,
                }
            }
        })*
    };
}

impl_from_bytes!(
    (Drhd, DrhdHeader),
    (Rmrr, RmrrHeader),
    (Atsr, AtsrHeader),
    (Satc, SatcHeader),
    (Sidp, SidpHeader),
);

#[verus_verify]
impl DeviceScope {
    /// Parses a [`DeviceScope`] from a prefix of the bytes.
    ///
    /// # Panics
    ///
    /// This method may panic if the byte prefix does not represent a valid [`DeviceScope`].
    #[verus_spec(ret =>
        requires
            core::mem::size_of::<DeviceScopeHeader>()
                <= from_bytes_spec::<DeviceScopeHeader>(bytes@).length_spec()
                <= bytes@.len(),
            (
                (from_bytes_spec::<DeviceScopeHeader>(bytes@).length_spec() as usize)
                    - core::mem::size_of::<DeviceScopeHeader>()
            ) % 2 == 0,
        ensures
            ret.header_spec() == decode_pod::<DeviceScopeHeader>(
                bytes@.subrange(0, core::mem::size_of::<DeviceScopeHeader>() as int),
            ),
            ret.path_spec() =~= path_pairs_spec(
                bytes@,
                core::mem::size_of::<DeviceScopeHeader>() as int,
                ret.header_spec().length_spec() as int,
            ),
    )]
    fn from_bytes_prefix(bytes: &[u8]) -> Self {
        let header = DeviceScopeHeader::from_bytes(bytes);
        // debug_assert!((header.length as usize) <= bytes.len());

        let mut index = core::mem::size_of::<DeviceScopeHeader>();
        // debug_assert!((header.length as usize) >= index);

        let mut path = Vec::new();
        proof! {
            assert(header == from_bytes_spec::<DeviceScopeHeader>(bytes@));
            assert(bytes@.len() >= header.length);
        }
        #[verus_spec(invariant
            core::mem::size_of::<DeviceScopeHeader>() <= index <= header.length,
            (header.length as usize - index) % 2 == 0,
            (index - core::mem::size_of::<DeviceScopeHeader>()) % 2 == 0,
            bytes@.len() >= header.length,
            path@ =~= path_pairs_spec(
                bytes@,
                core::mem::size_of::<DeviceScopeHeader>() as int,
                index as int,
            ),
            decreases header.length as usize - index,
        )]
        while index != (header.length as usize) {
            let val = (bytes[index], bytes[index + 1]);
            path.push(val);
            proof! {
                lemma_path_pairs_step(
                    bytes@,
                    core::mem::size_of::<DeviceScopeHeader>() as int,
                    (index + 2) as int,
                );
                assert(path@ =~= path_pairs_spec(
                    bytes@,
                    core::mem::size_of::<DeviceScopeHeader>() as int,
                    (index + 2) as int,
                ));
            }
            index += 2;
        }

        Self { header, path }
    }
}

#[verus_verify]
impl Rhsa {
    /// Parses an [`Rhsa`] from the bytes.
    ///
    /// # Panics
    ///
    /// This method may panic if the bytes do not represent a valid [`Rhsa`].
    #[verus_spec(
        requires
            bytes@.len() >= core::mem::size_of::<Self>(),
        returns
            decode_pod::<Self>(bytes@.subrange(0, core::mem::size_of::<Self>() as int)),
    )]
    pub fn from_bytes(bytes: &[u8]) -> Self {
        let val = <Self as Pod>::from_bytes(bytes);
        // debug_assert_eq!(val.length as usize, bytes.len());

        val
    }
}

#[verus_verify]
impl Andd {
    /// Parses an [`Andd`] from the bytes.
    ///
    /// # Panics
    ///
    /// This method may panic if the bytes do not represent a valid [`Andd`].
    #[verus_spec(ret =>
        requires
            bytes@.len() >= core::mem::size_of::<AnddHeader>(),
            valid_utf8(
                bytes@.subrange(
                    core::mem::size_of::<AnddHeader>() as int,
                    bytes@.len() as int,
                ),
            ),
        ensures
            ret.header_spec() == decode_pod::<AnddHeader>(
                bytes@.subrange(0, core::mem::size_of::<AnddHeader>() as int),
            ),
            encode_utf8(ret.acpi_object_name_spec()) =~= bytes@.subrange(
                core::mem::size_of::<AnddHeader>() as int,
                bytes@.len() as int,
            ),
    )]
    pub fn from_bytes(bytes: &[u8]) -> Self {
        let header = AnddHeader::from_bytes(bytes);
        // debug_assert_eq!(header.length as usize, bytes.len());

        let header_len = core::mem::size_of::<AnddHeader>();
        let acpi_object_name = core::str::from_utf8(&bytes[header_len..])
            .unwrap()
            .to_owned();

        Self {
            header,
            acpi_object_name,
        }
    }
}

// Auxiliary proof functions

verus! {

/// One accumulation step: the byte pairs of `bytes[start..end)` are the byte
/// pairs of `bytes[start..end-2)` with the last pair appended.
proof fn lemma_path_pairs_step(bytes: Seq<u8>, start: int, end: int)
    requires
        start + 2 <= end <= bytes.len(),
        (end - start) % 2 == 0,
    ensures
        path_pairs_spec(bytes, start, end) == path_pairs_spec(bytes, start, end - 2).push(
            (bytes[end - 2], bytes[end - 1]),
        ),
{
    let f = |i: int| (bytes[start + 2 * i], bytes[start + 2 * i + 1]);
    let n = ((end - start) / 2) as nat;
    let first = path_pairs_spec(bytes, start, end);
    let rest = path_pairs_spec(bytes, start, end - 2);
    assert(first =~= Seq::new(n, f));
    assert(rest =~= Seq::new((n - 1) as nat, f));
    lemma_seq_new_len(n, f);
    lemma_seq_new_len((n - 1) as nat, f);
    lemma_seq_push_len(rest, (bytes[end - 2], bytes[end - 1]));
    assert forall|i: int| 0 <= i < n implies first[i] == rest.push(
        (bytes[end - 2], bytes[end - 1]),
    )[i] by {
        lemma_seq_new_index(n, f, i);
        if i < n - 1 {
            lemma_seq_new_index((n - 1) as nat, f, i);
            lemma_seq_push_index_different(rest, (bytes[end - 2], bytes[end - 1]), i);
        } else {
            lemma_seq_push_index_same(rest, (bytes[end - 2], bytes[end - 1]), i);
        }
    };
    lemma_seq_ext_equal(first, rest.push((bytes[end - 2], bytes[end - 1])));
}

} // verus!

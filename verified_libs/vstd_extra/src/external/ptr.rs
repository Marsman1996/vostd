use core::marker::PointeeSized;
use vstd::{
    prelude::*,
    raw_ptr::{PtrData, ptr_mut_from_data},
};

use super::io::{IoAccess, certified_io_access};

#[cfg(verus_keep_ghost)]
pub use core::ptr::{read_volatile, write_volatile};

verus! {

pub assume_specification<T: PointeeSized>[ <*const T>::map_addr ](
    ptr: *const T,
    f: impl FnOnce(usize) -> usize,
) -> (ret: *const T)
    requires
        f.requires((ptr@.addr,)),
    ensures
        ret@.metadata == ptr@.metadata,
        ret@.provenance == ptr@.provenance,
        f.ensures((ptr@.addr,), ret@.addr),
;

pub assume_specification<T: PointeeSized>[ <*mut T>::map_addr ](
    ptr: *mut T,
    f: impl FnOnce(usize) -> usize,
) -> (ret: *mut T)
    requires
        f.requires((ptr@.addr,)),
    ensures
        ret@.metadata == ptr@.metadata,
        ret@.provenance == ptr@.provenance,
        f.ensures((ptr@.addr,), ret@.addr),
;

#[verifier::inline]
pub open spec fn ptr_cast_spec<T: PointeeSized, U>(ptr: *const T) -> *const U {
    ptr as *const U
}

#[verifier::inline]
pub open spec fn ptr_mut_cast_spec<T: PointeeSized, U>(ptr: *mut T) -> *mut U {
    ptr as *mut U
}

#[verifier::inline]
pub open spec fn ptr_mut_cast_const_spec<T: PointeeSized>(ptr: *mut T) -> *const T {
    ptr as *const T
}

#[verifier::inline]
pub open spec fn ptr_cast_mut_spec<T: PointeeSized>(ptr: *const T) -> *mut T {
    ptr as *mut T
}

#[verifier::inline]
pub open spec fn ptr_is_null_spec<T: PointeeSized>(ptr: *const T) -> bool {
    ptr.addr() == 0
}

#[verifier::inline]
pub open spec fn ptr_mut_is_null_spec<T: PointeeSized>(ptr: *mut T) -> bool {
    ptr.addr() == 0
}

#[verifier::when_used_as_spec(ptr_cast_spec)]
pub assume_specification<T: PointeeSized, U>[ <*const T>::cast::<U> ](ptr: *const T) -> *const U
    returns
        ptr as *const U,
    opens_invariants none
    no_unwind
;

#[verifier::when_used_as_spec(ptr_mut_cast_spec)]
pub assume_specification<T: PointeeSized, U>[ <*mut T>::cast::<U> ](ptr: *mut T) -> *mut U
    returns
        ptr as *mut U,
    opens_invariants none
    no_unwind
;

#[verifier::when_used_as_spec(ptr_mut_cast_const_spec)]
pub assume_specification<T: PointeeSized>[ <*mut T>::cast_const ](ptr: *mut T) -> *const T
    returns
        ptr as *const T,
    opens_invariants none
    no_unwind
;

#[verifier::when_used_as_spec(ptr_cast_mut_spec)]
pub assume_specification<T: PointeeSized>[ <*const T>::cast_mut ](ptr: *const T) -> *mut T
    returns
        ptr as *mut T,
    opens_invariants none
    no_unwind
;

/// [<*const T>::is_null](https://doc.rust-lang.org/std/primitive.pointer.html#method.is_null) only checks the raw data pointer.
#[verifier::when_used_as_spec(ptr_is_null_spec)]
pub assume_specification<T: PointeeSized>[ <*const T>::is_null ](ptr: *const T) -> bool
    returns
        ptr.addr() == 0,
    opens_invariants none
    no_unwind
;

/// [<*mut T>::is_null](https://doc.rust-lang.org/std/primitive.pointer.html#method.is_null) only checks the raw data pointer.
#[verifier::when_used_as_spec(ptr_mut_is_null_spec)]
pub assume_specification<T: PointeeSized>[ <*mut T>::is_null ](ptr: *mut T) -> bool
    returns
        ptr.addr() == 0,
    opens_invariants none
    no_unwind
;

// Rust 1.98.1, library/core/src/ptr/{mod,mut_ptr}.rs: u32 device access.
// These proxies are selected only by verus_spec(with ...); erasure calls core
// directly. u32 restricts the device value validity and access width.
#[cfg(verus_keep_ghost)]
#[verifier::external]
pub unsafe fn _VERUS_VERIFIED_read_volatile<A: IoAccess>(
    src: *const u32,
    access: Tracked<&mut A>,
) -> u32 {
    unsafe { core::ptr::read_volatile(src) }
}

#[cfg(verus_keep_ghost)]
pub assume_specification<A: IoAccess>[ _VERUS_VERIFIED_read_volatile::<A> ](
    src: *const u32,
    Tracked(access): Tracked<&mut A>,
) -> u32
    requires
        certified_io_access(*old(access)),
        old(access).mmio_read_ok(src.addr()),
    ensures
        *final(access) == *old(access),
;

#[cfg(verus_keep_ghost)]
#[verifier::external]
pub unsafe fn _VERUS_VERIFIED_write_volatile<A: IoAccess>(
    dst: *mut u32,
    value: u32,
    access: Tracked<&mut A>,
) {
    unsafe { core::ptr::write_volatile(dst, value) }
}

#[cfg(verus_keep_ghost)]
pub assume_specification<A: IoAccess>[ _VERUS_VERIFIED_write_volatile::<A> ](
    dst: *mut u32,
    value: u32,
    Tracked(access): Tracked<&mut A>,
)
    requires
        certified_io_access(*old(access)),
        old(access).mmio_write_ok(dst.addr(), value),
    ensures
        *final(access) == *old(access),
;

/// [<*mut T>::add](https://doc.rust-lang.org/std/primitive.pointer.html#method.add):
/// advance the address by `count * size_of::<T>()` bytes, preserving provenance and
/// metadata.
#[verifier::inline]
pub open spec fn ptr_mut_add_spec<T: PointeeSized + Sized>(p: *mut T, count: usize) -> *mut T {
    ptr_mut_from_data(
        PtrData::<T> { addr: (p.addr() + count * (size_of::<T>() as usize)) as usize, ..p@ },
    )
}

/// [<*mut T>::add](https://doc.rust-lang.org/std/primitive.pointer.html#method.add);
/// debug builds panic on offset overflow, so the no-overflow preconditions carry
/// `no_unwind when`.
#[verifier::when_used_as_spec(ptr_mut_add_spec)]
pub assume_specification<T>[ <*mut T>::add ](p: *mut T, count: usize) -> (ret: *mut T)
    requires
        p.addr() + count * (size_of::<T>() as usize) <= usize::MAX,
        count * (size_of::<T>() as usize) <= isize::MAX,
    ensures
        ret == ptr_mut_add_spec(p, count),
    opens_invariants none
    no_unwind when p.addr() + count * (size_of::<T>() as usize) <= usize::MAX && count * (size_of::<
    T,
>() as usize) <= isize::MAX
;

// Unlike add, wrapping_add also supports device addresses outside allocations.
#[verifier::when_used_as_spec(ptr_mut_add_spec)]
pub assume_specification<T>[ <*mut T>::wrapping_add ](p: *mut T, count: usize) -> *mut T
    returns
        ptr_mut_add_spec(p, count),
    opens_invariants none
    no_unwind
;

} // verus!

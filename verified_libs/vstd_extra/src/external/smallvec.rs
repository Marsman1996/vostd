//! Trusted specifications for smallvec 1.15.0, used by CPU sets.
//!
//! The sequence records elements (atomic elements are identities, not snapshots
//! of their mutable contents). Allocation failure is outside the model, as for
//! vstd's Vec. Capacity bounds exclude allocation-layout overflow.
use smallvec::{Array, SmallVec};
use vstd::prelude::*;

verus! {

#[verifier::external_trait_specification]
pub unsafe trait ExArray {
    type ExternalTraitSpecificationFor: Array;

    type Item;

    fn size() -> usize;
}

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(A)]
pub struct ExSmallVec<A: Array>(SmallVec<A>);

pub trait SmallVecView<A: Array> {
    spec fn view(&self) -> Seq<A::Item>;
}

impl<A: Array> SmallVecView<A> for SmallVec<A> {
    uninterp spec fn view(&self) -> Seq<A::Item>;
}

/// Only the two CPU-set representations are admitted to this model.
pub uninterp spec fn supported_array<A: Array>() -> bool;

pub broadcast axiom fn supported_cpu_set_arrays()
    ensures
        #[trigger] supported_array::<[u64; 2]>(),
        #[trigger] supported_array::<[core::sync::atomic::AtomicU64; 2]>(),
;

pub assume_specification<A: Array>[ SmallVec::<A>::with_capacity ](n: usize) -> (r: SmallVec<A>)
    requires
        supported_array::<A>(),
        n <= 67108864,
    ensures
        r@ == Seq::<A::Item>::empty(),
;

pub assume_specification<A: Array>[ SmallVec::<A>::len ](v: &SmallVec<A>) -> (r: usize)
    requires
        supported_array::<A>(),
    ensures
        r == v@.len(),
;

pub assume_specification<A: Array>[ SmallVec::<A>::as_slice ](v: &SmallVec<A>) -> (r: &[A::Item])
    requires
        supported_array::<A>(),
    ensures
        r@ == v@,
;

pub assume_specification<A: Array>[ SmallVec::<A>::as_mut_slice ](v: &mut SmallVec<A>) -> (r:
    &mut [A::Item])
    requires
        supported_array::<A>(),
    ensures
        r@ == old(v)@,
        final(v)@ == final(r)@,
;

pub assume_specification<A: Array>[ SmallVec::<A>::push ](v: &mut SmallVec<A>, value: A::Item)
    requires
        supported_array::<A>(),
        old(v)@.len() < 67108864,
    ensures
        final(v)@ == old(v)@.push(value),
;

pub assume_specification<A: Array>[ SmallVec::<A>::resize ](
    v: &mut SmallVec<A>,
    len: usize,
    value: A::Item,
) where A::Item: Clone
    requires
        supported_array::<A>(),
        len <= 67108864,
        forall|x: A::Item| #[trigger] cloned(value, x) ==> x == value,
    ensures
        final(v)@.len() == len,
        forall|i: int|
            0 <= i < len ==> #[trigger] final(v)@[i] == (if i < old(v)@.len() {
                old(v)@[i]
            } else {
                value
            }),
;

pub assume_specification<A: Array>[ <SmallVec<A> as Default>::default ]() -> (r: SmallVec<A>)
    ensures
        supported_array::<A>() ==> r@ == Seq::<A::Item>::empty(),
;

pub assume_specification<A: Array>[ <SmallVec<A> as Clone>::clone ](v: &SmallVec<A>) -> (r:
    SmallVec<A>) where A::Item: Clone
    ensures
        supported_array::<A>() ==> r@.len() == v@.len(),
        supported_array::<A>() ==> forall|i: int|
            0 <= i < v@.len() ==> #[trigger] cloned(v@[i], r@[i]),
;

} // verus!

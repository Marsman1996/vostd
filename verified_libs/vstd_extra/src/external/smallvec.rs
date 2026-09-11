//! Specifications for `smallvec::SmallVec`, a foreign const-generic collection.
//!
//! `SmallVec<A: Array>` is foreign; before it can be specified, Verus must be
//! told about the `smallvec::Array` trait (and its associated `Item` type) via
//! `external_trait_specification`. The collection is then modelled as a
//! `Seq<A::Item>` through `View` (so `smallvec@` yields the part sequence).
//!
//! These specs are trusted (TCB): their `ensures` are assumed, matching the
//! `smallvec` 1.13.2 semantics. They are centralized here per the coding
//! guideline "centralize trusted boundaries", so any OSTD caller of `SmallVec`
//! reuses the same model.
use smallvec::{Array, SmallVec};
use vstd::prelude::*;
use vstd::seq::Seq;

verus! {

/// Verus declaration of Rust's `smallvec::Array` trait (foreign), exposing its
/// associated `Item` type. Required so `SmallVec<A: Array>` can be bounded.
#[verifier::external_trait_specification]
pub trait ExArray {
    type ExternalTraitSpecificationFor: Array;
    type Item;
}

/// Verus declaration of `smallvec::SmallVec<A>` as an opaque external type.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(A)]
pub struct ExSmallVec<A: Array>(SmallVec<A>);

/// Spec-side view of a `SmallVec<A>` as its `Seq<A::Item>` part sequence.
/// (A local trait is used rather than `vstd::View` because the latter is private
/// and would violate the orphan rule for the foreign `SmallVec`.)
pub trait SmallVecSpecFns<A: Array> {
    spec fn view(&self) -> Seq<A::Item>;
}

impl<A: Array> SmallVecSpecFns<A> for SmallVec<A> {
    uninterp spec fn view(&self) -> Seq<A::Item>;
}

/// `SmallVec::new()` is the empty sequence.
pub assume_specification<A: Array>[ SmallVec::<A>::new ]() -> (ret: SmallVec<A>)
    ensures
        ret.view() == Seq::empty(),
;

/// `SmallVec::with_capacity(_)` is the empty sequence (capacity is exec-only).
pub assume_specification<A: Array>[ SmallVec::<A>::with_capacity ](
    capacity: usize,
) -> (ret: SmallVec<A>)
    ensures
        ret.view() == Seq::empty(),
;

/// `SmallVec::len(&self)` is the sequence length.
pub assume_specification<A: Array>[ SmallVec::<A>::len ](s: &SmallVec<A>) -> (ret: usize)
    ensures
        ret == s.view().len(),
;

// `SmallVec::resize` is NOT specified here: its real signature requires
// `where A::Item: Clone`, and `assume_specification` does not support `where`
// clauses. Callers that need to grow a `SmallVec` must use a localized
// `external_body` wrapper (per the guideline "test the direct form, record any
// concrete obstacle, then add a wrapper"). Indexing (`Index`/`IndexMut`), which
// returns references, is likewise left to localized wrappers.

} // verus!


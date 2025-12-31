use vstd::prelude::*;

verus! {

// ============================================================================
// QC Language Case Study: Identifiers
// Identifiers for variables in a typed imperative language
// ============================================================================

// ----------------------------------------------------------------------------
// Identifier Type
// ----------------------------------------------------------------------------

/// Identifiers are represented as natural numbers for simplicity.
/// This allows for easy comparison and fresh identifier generation.
pub type Id = nat;

// Predefined variable names for examples
pub spec const X_ID: Id = 0;
pub spec const Y_ID: Id = 1;
pub spec const Z_ID: Id = 2;
pub spec const F_ID: Id = 3;
pub spec const G_ID: Id = 4;

// ----------------------------------------------------------------------------
// Fresh Identifier Generation
// ----------------------------------------------------------------------------

/// Generate a fresh identifier that is greater than all ids in a given set.
/// Uses max + 1 strategy.
pub open spec fn fresh_id_for_set(used: Set<Id>) -> Id {
    if used.is_empty() {
        0
    } else {
        (choose|id: Id| used.contains(id) && forall|id2: Id| used.contains(id2) ==> id2 <= id) + 1
    }
}

/// A simpler fresh id: just return the given bound + 1
pub open spec fn fresh_id(bound: Id) -> Id {
    bound + 1
}

/// Check if an id is fresh with respect to a bound
pub open spec fn is_fresh(id: Id, bound: Id) -> bool {
    id > bound
}

/// Check if an id is fresh with respect to a set
pub open spec fn is_fresh_for_set(id: Id, used: Set<Id>) -> bool {
    !used.contains(id)
}

// ----------------------------------------------------------------------------
// Identifier Equality (decidable)
// ----------------------------------------------------------------------------

/// Identifiers have decidable equality since they are natural numbers
pub open spec fn id_eq(x: Id, y: Id) -> bool {
    x == y
}

/// Decidability: either x == y or x != y
pub proof fn id_eq_decidable(x: Id, y: Id)
    ensures id_eq(x, y) || !id_eq(x, y)
{
    // Trivially true by classical logic
}

// ----------------------------------------------------------------------------
// Identifier Ordering
// ----------------------------------------------------------------------------

/// Less than ordering on identifiers
pub open spec fn id_lt(x: Id, y: Id) -> bool {
    x < y
}

/// Less than or equal ordering
pub open spec fn id_le(x: Id, y: Id) -> bool {
    x <= y
}

/// Ordering is total
pub proof fn id_lt_total(x: Id, y: Id)
    ensures id_lt(x, y) || x == y || id_lt(y, x)
{
    // Natural numbers have total ordering
}

/// Ordering is transitive
pub proof fn id_lt_trans(x: Id, y: Id, z: Id)
    requires
        id_lt(x, y),
        id_lt(y, z),
    ensures id_lt(x, z)
{
}

// ----------------------------------------------------------------------------
// Fresh Identifier Properties
// ----------------------------------------------------------------------------

/// Fresh id is indeed fresh
pub proof fn fresh_id_is_fresh(bound: Id)
    ensures is_fresh(fresh_id(bound), bound)
{
    assert(fresh_id(bound) > bound);
}

/// Fresh id is greater than bound
pub proof fn fresh_id_gt_bound(bound: Id)
    ensures fresh_id(bound) > bound
{
}

/// Two consecutive fresh ids are different
pub proof fn fresh_ids_different(bound1: Id, bound2: Id)
    requires bound1 != bound2
    ensures fresh_id(bound1) != fresh_id(bound2)
{
}

// ----------------------------------------------------------------------------
// Identifier Set Operations
// ----------------------------------------------------------------------------

/// Compute the maximum id in a finite set (if non-empty)
pub open spec fn max_id(s: Set<Id>) -> Id
    recommends !s.is_empty()
{
    choose|id: Id| s.contains(id) && forall|id2: Id| s.contains(id2) ==> id2 <= id
}

/// A fresh id for a singleton set
pub proof fn fresh_for_singleton(x: Id)
    ensures is_fresh_for_set(x + 1, Set::empty().insert(x))
{
    let s = Set::empty().insert(x);
    assert(!s.contains(x + 1));
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

/// Example: Predefined ids are distinct
pub proof fn example_predefined_ids_distinct()
    ensures
        X_ID != Y_ID && X_ID != Z_ID && X_ID != F_ID && X_ID != G_ID,
        Y_ID != Z_ID && Y_ID != F_ID && Y_ID != G_ID,
        Z_ID != F_ID && Z_ID != G_ID,
        F_ID != G_ID,
{
}

/// Example: Fresh id generation
pub proof fn example_fresh_id()
{
    let bound: nat = 5;
    assert(fresh_id(bound) == 6);
    assert(is_fresh(6nat, 5nat));
}

/// Example: Id equality
pub proof fn example_id_equality()
{
    assert(id_eq(X_ID, X_ID));
    assert(!id_eq(X_ID, Y_ID));
    assert(id_eq(0nat, 0nat));
}

/// Example: Id ordering
pub proof fn example_id_ordering()
{
    assert(id_lt(X_ID, Y_ID));  // 0 < 1
    assert(id_lt(Y_ID, Z_ID));  // 1 < 2
    assert(id_le(X_ID, X_ID));  // 0 <= 0
    assert(id_le(X_ID, Y_ID));  // 0 <= 1
}

/// Example: Fresh for set
pub proof fn example_fresh_for_set()
{
    let s: Set<Id> = Set::empty().insert(0nat).insert(1nat).insert(2nat);
    assert(!s.contains(3nat));
    assert(is_fresh_for_set(3nat, s));
}

// ----------------------------------------------------------------------------
// Identifier Sequences
// ----------------------------------------------------------------------------

/// Generate a sequence of n fresh identifiers starting from a bound
pub open spec fn fresh_ids(bound: Id, n: nat) -> Seq<Id>
    decreases n
{
    if n == 0 {
        Seq::empty()
    } else {
        Seq::new(n, |i: int| bound + 1 + i as nat)
    }
}

/// All ids in fresh_ids are fresh w.r.t. bound
pub proof fn fresh_ids_all_fresh(bound: Id, n: nat)
    ensures forall|i: int| 0 <= i < n as int ==> (#[trigger] fresh_ids(bound, n)[i]) > bound
{
    if n > 0 {
        assert forall|i: int| 0 <= i < n as int implies (#[trigger] fresh_ids(bound, n)[i]) > bound by {
            assert(fresh_ids(bound, n)[i] == bound + 1 + i as nat);
        }
    }
}

/// All ids in fresh_ids are distinct
pub proof fn fresh_ids_distinct(bound: Id, n: nat)
    ensures forall|i: int, j: int|
        0 <= i < n as int && 0 <= j < n as int && i != j
        ==> (#[trigger] fresh_ids(bound, n)[i]) != (#[trigger] fresh_ids(bound, n)[j])
{
    if n > 0 {
        assert forall|i: int, j: int|
            0 <= i < n as int && 0 <= j < n as int && i != j
            implies (#[trigger] fresh_ids(bound, n)[i]) != (#[trigger] fresh_ids(bound, n)[j]) by {
            assert(fresh_ids(bound, n)[i] == bound + 1 + i as nat);
            assert(fresh_ids(bound, n)[j] == bound + 1 + j as nat);
        }
    }
}

/// Length of fresh_ids sequence
pub proof fn fresh_ids_length(bound: Id, n: nat)
    ensures fresh_ids(bound, n).len() == n
{
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_lang_ident_examples_verify()
{
    example_predefined_ids_distinct();
    example_fresh_id();
    example_id_equality();
    example_id_ordering();
    example_fresh_for_set();

    // Property proofs
    fresh_id_is_fresh(10nat);
    fresh_id_gt_bound(5nat);
    id_eq_decidable(X_ID, Y_ID);
    id_lt_total(X_ID, Z_ID);

    // Fresh ids sequence
    fresh_ids_all_fresh(0nat, 5nat);
    fresh_ids_distinct(0nat, 5nat);
    fresh_ids_length(0nat, 5nat);
}

pub fn main() {
    proof {
        qc_lang_ident_examples_verify();
    }
}

} // verus!

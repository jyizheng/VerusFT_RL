use vstd::prelude::*;

verus! {

// ============================================================================
// QC: List Predicate Decidability (QuickChick-style)
// Models decidable predicates for lists: membership, all, any
// ============================================================================

// ----------------------------------------------------------------------------
// Decidability Result Type
// ----------------------------------------------------------------------------

pub enum Dec {
    Yes,
    No,
}

pub open spec fn dec_to_bool(d: Dec) -> bool {
    match d {
        Dec::Yes => true,
        Dec::No => false,
    }
}

pub open spec fn bool_to_dec(b: bool) -> Dec {
    if b { Dec::Yes } else { Dec::No }
}

// ----------------------------------------------------------------------------
// List Membership Decidability
// ----------------------------------------------------------------------------

/// Check if element is in list (helper)
pub open spec fn list_contains_helper<T>(s: Seq<T>, x: T, eq: spec_fn(T, T) -> bool, i: int) -> bool
    decreases s.len() - i when i >= 0
{
    if i >= s.len() {
        false
    } else if eq(s[i], x) {
        true
    } else {
        list_contains_helper(s, x, eq, i + 1)
    }
}

/// Check if element is in list
pub open spec fn list_contains<T>(s: Seq<T>, x: T, eq: spec_fn(T, T) -> bool) -> bool {
    list_contains_helper(s, x, eq, 0)
}

/// Membership is decidable given decidable equality
pub open spec fn dec_member<T>(s: Seq<T>, x: T, eq: spec_fn(T, T) -> bool) -> Dec {
    bool_to_dec(list_contains(s, x, eq))
}

/// Membership for nat lists
pub open spec fn dec_member_nat(s: Seq<nat>, x: nat) -> Dec {
    dec_member(s, x, |a: nat, b: nat| a == b)
}

// ----------------------------------------------------------------------------
// List All Predicate Decidability
// ----------------------------------------------------------------------------

/// Check if all elements satisfy predicate (helper)
pub open spec fn list_all_helper<T>(s: Seq<T>, p: spec_fn(T) -> bool, i: int) -> bool
    decreases s.len() - i when i >= 0
{
    if i >= s.len() {
        true
    } else if !p(s[i]) {
        false
    } else {
        list_all_helper(s, p, i + 1)
    }
}

/// Check if all elements satisfy predicate
pub open spec fn list_all<T>(s: Seq<T>, p: spec_fn(T) -> bool) -> bool {
    list_all_helper(s, p, 0)
}

/// All predicate is decidable given decidable element predicate
pub open spec fn dec_all<T>(s: Seq<T>, p: spec_fn(T) -> bool) -> Dec {
    bool_to_dec(list_all(s, p))
}

/// All for nat lists with a condition
pub open spec fn dec_all_nat(s: Seq<nat>, p: spec_fn(nat) -> bool) -> Dec {
    dec_all(s, p)
}

// ----------------------------------------------------------------------------
// List Any Predicate Decidability
// ----------------------------------------------------------------------------

/// Check if any element satisfies predicate (helper)
pub open spec fn list_any_helper<T>(s: Seq<T>, p: spec_fn(T) -> bool, i: int) -> bool
    decreases s.len() - i when i >= 0
{
    if i >= s.len() {
        false
    } else if p(s[i]) {
        true
    } else {
        list_any_helper(s, p, i + 1)
    }
}

/// Check if any element satisfies predicate
pub open spec fn list_any<T>(s: Seq<T>, p: spec_fn(T) -> bool) -> bool {
    list_any_helper(s, p, 0)
}

/// Any predicate is decidable given decidable element predicate
pub open spec fn dec_any<T>(s: Seq<T>, p: spec_fn(T) -> bool) -> Dec {
    bool_to_dec(list_any(s, p))
}

/// Any for nat lists with a condition
pub open spec fn dec_any_nat(s: Seq<nat>, p: spec_fn(nat) -> bool) -> Dec {
    dec_any(s, p)
}

// ----------------------------------------------------------------------------
// List None Predicate Decidability
// ----------------------------------------------------------------------------

/// Check if no element satisfies predicate
pub open spec fn list_none<T>(s: Seq<T>, p: spec_fn(T) -> bool) -> bool {
    !list_any(s, p)
}

/// None predicate is decidable
pub open spec fn dec_none<T>(s: Seq<T>, p: spec_fn(T) -> bool) -> Dec {
    bool_to_dec(list_none(s, p))
}

// ----------------------------------------------------------------------------
// Soundness Proofs
// ----------------------------------------------------------------------------

/// Membership soundness: dec_member correctly reflects list_contains
pub proof fn dec_member_sound<T>(s: Seq<T>, x: T, eq: spec_fn(T, T) -> bool)
    ensures dec_to_bool(dec_member(s, x, eq)) == list_contains(s, x, eq)
{
}

/// All soundness: dec_all correctly reflects list_all
pub proof fn dec_all_sound<T>(s: Seq<T>, p: spec_fn(T) -> bool)
    ensures dec_to_bool(dec_all(s, p)) == list_all(s, p)
{
}

/// Any soundness: dec_any correctly reflects list_any
pub proof fn dec_any_sound<T>(s: Seq<T>, p: spec_fn(T) -> bool)
    ensures dec_to_bool(dec_any(s, p)) == list_any(s, p)
{
}

/// None soundness: dec_none correctly reflects list_none
pub proof fn dec_none_sound<T>(s: Seq<T>, p: spec_fn(T) -> bool)
    ensures dec_to_bool(dec_none(s, p)) == list_none(s, p)
{
}

// ----------------------------------------------------------------------------
// All-Any Duality
// ----------------------------------------------------------------------------

/// None is negation of any
pub proof fn dec_none_any_duality<T>(s: Seq<T>, p: spec_fn(T) -> bool)
    ensures dec_to_bool(dec_none(s, p)) == !dec_to_bool(dec_any(s, p))
{
}

// ----------------------------------------------------------------------------
// Empty List Properties
// ----------------------------------------------------------------------------

/// Empty list: all trivially holds
pub proof fn dec_all_empty<T>(p: spec_fn(T) -> bool)
    ensures dec_to_bool(dec_all(Seq::<T>::empty(), p))
{
}

/// Empty list: any trivially fails
pub proof fn dec_any_empty<T>(p: spec_fn(T) -> bool)
    ensures !dec_to_bool(dec_any(Seq::<T>::empty(), p))
{
}

/// Empty list: membership fails
pub proof fn dec_member_empty<T>(x: T, eq: spec_fn(T, T) -> bool)
    ensures !dec_to_bool(dec_member(Seq::<T>::empty(), x, eq))
{
}

// ----------------------------------------------------------------------------
// Sorted and Distinct Decidability
// ----------------------------------------------------------------------------

/// Check if list is sorted (ascending)
pub open spec fn list_sorted_helper(s: Seq<nat>, i: int) -> bool
    decreases s.len() - i when i >= 0
{
    if i >= s.len() - 1 {
        true
    } else if s[i] > s[i + 1] {
        false
    } else {
        list_sorted_helper(s, i + 1)
    }
}

pub open spec fn list_sorted(s: Seq<nat>) -> bool {
    list_sorted_helper(s, 0)
}

/// Sorted is decidable
pub open spec fn dec_sorted(s: Seq<nat>) -> Dec {
    bool_to_dec(list_sorted(s))
}

/// Check if list has distinct elements
pub open spec fn list_distinct_helper(s: Seq<nat>, i: int, j: int) -> bool
    decreases s.len() - i, s.len() - j when i >= 0 && j >= 0
{
    if i >= s.len() {
        true
    } else if j >= s.len() {
        list_distinct_helper(s, i + 1, i + 2)
    } else if s[i] == s[j] {
        false
    } else {
        list_distinct_helper(s, i, j + 1)
    }
}

pub open spec fn list_distinct(s: Seq<nat>) -> bool {
    list_distinct_helper(s, 0, 1)
}

/// Distinct is decidable
pub open spec fn dec_distinct(s: Seq<nat>) -> Dec {
    bool_to_dec(list_distinct(s))
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_dec_member()
{
    reveal_with_fuel(list_contains_helper, 8);

    let s = seq![1nat, 2, 3, 4, 5];

    // Check membership for elements that exist
    assert(dec_to_bool(dec_member_nat(s, 3)));
    assert(dec_to_bool(dec_member_nat(s, 1)));
    assert(dec_to_bool(dec_member_nat(s, 5)));

    // Check membership for elements that don't exist
    // Using a shorter sequence for verification efficiency
    let s2 = seq![1nat, 2, 3];
    assert(!dec_to_bool(dec_member_nat(s2, 5)));
}

pub proof fn example_dec_all()
{
    reveal_with_fuel(list_all_helper, 5);

    let s = seq![2nat, 4, 6, 8];

    // All elements are even
    let is_even = |n: nat| n % 2 == 0;
    assert(dec_to_bool(dec_all_nat(s, is_even)));

    // Not all elements are > 5
    let gt_five = |n: nat| n > 5;
    assert(!dec_to_bool(dec_all_nat(s, gt_five)));
}

pub proof fn example_dec_any()
{
    reveal_with_fuel(list_any_helper, 5);

    let s = seq![1nat, 3, 5, 7];

    // Any element > 5
    let gt_five = |n: nat| n > 5;
    assert(dec_to_bool(dec_any_nat(s, gt_five)));

    // Any element is even
    let is_even = |n: nat| n % 2 == 0;
    assert(!dec_to_bool(dec_any_nat(s, is_even)));
}

pub proof fn example_dec_empty()
{
    let empty: Seq<nat> = Seq::empty();

    // All trivially true for empty
    dec_all_empty(|n: nat| n > 100);
    assert(dec_to_bool(dec_all(empty, |n: nat| n > 100)));

    // Any trivially false for empty
    dec_any_empty(|n: nat| n > 0);
    assert(!dec_to_bool(dec_any(empty, |n: nat| n > 0)));

    // Membership trivially false for empty
    dec_member_empty(5nat, |a: nat, b: nat| a == b);
    assert(!dec_to_bool(dec_member_nat(empty, 5)));
}

pub proof fn example_dec_sorted()
{
    reveal_with_fuel(list_sorted_helper, 5);

    let sorted = seq![1nat, 2, 3, 4, 5];
    let unsorted = seq![1nat, 3, 2, 4, 5];

    assert(dec_to_bool(dec_sorted(sorted)));
    assert(!dec_to_bool(dec_sorted(unsorted)));
}

pub proof fn example_dec_distinct()
{
    reveal_with_fuel(list_distinct_helper, 15);

    // Use shorter sequences for verification efficiency
    let distinct = seq![1nat, 2, 3];
    let duplicates = seq![1nat, 2, 1];

    assert(dec_to_bool(dec_distinct(distinct)));
    assert(!dec_to_bool(dec_distinct(duplicates)));
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_dec_list_verify()
{
    example_dec_member();
    example_dec_all();
    example_dec_any();
    example_dec_empty();
    example_dec_sorted();
    example_dec_distinct();
}

pub fn main() {
    proof {
        qc_dec_list_verify();
    }
}

} // verus!

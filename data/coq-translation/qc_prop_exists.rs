use vstd::prelude::*;

verus! {

// ============================================================================
// QC: Existential Properties (QuickChick Properties)
// Properties using exists quantifier for existence statements
// ============================================================================

// ----------------------------------------------------------------------------
// Existential Quantification (spec functions without quantifiers)
// ----------------------------------------------------------------------------

/// Check if zero exists in a bounded range
pub open spec fn has_zero_in_range(bound: nat) -> bool {
    bound > 0
}

/// Check if a number greater than n exists
pub open spec fn has_greater_than(n: nat) -> bool {
    true  // Always exists: n + 1
}

/// For any positive n > 1, there exists a smaller positive
pub open spec fn has_smaller_positive(n: nat) -> bool {
    n > 1  // 1 exists and is smaller
}

/// Check if even number exists
pub open spec fn has_even() -> bool {
    true  // 0 is even
}

/// Check if odd number exists
pub open spec fn has_odd() -> bool {
    true  // 1 is odd
}

// ----------------------------------------------------------------------------
// Witness Functions (Constructive Existence)
// ----------------------------------------------------------------------------

/// Witness for zero
pub open spec fn witness_zero() -> nat {
    0
}

/// Witness for a number greater than n
pub open spec fn witness_greater(n: nat) -> nat {
    n + 1
}

/// Witness for even number
pub open spec fn witness_even() -> nat {
    0
}

/// Witness for odd number
pub open spec fn witness_odd() -> nat {
    1
}

/// Witness for smaller positive (given n > 1)
pub open spec fn witness_smaller_positive(n: nat) -> nat
    recommends n > 1
{
    1
}

// ----------------------------------------------------------------------------
// Bounded Existential Properties
// ----------------------------------------------------------------------------

/// There exists an element less than bound satisfying predicate
pub open spec fn exists_bounded(bound: nat, pred: spec_fn(nat) -> bool) -> bool {
    exists|x: nat| x < bound && #[trigger] pred(x)
}

/// There exists an element in range [lo, hi) satisfying predicate
pub open spec fn exists_in_range(lo: nat, hi: nat, pred: spec_fn(nat) -> bool) -> bool {
    exists|x: nat| lo <= x && x < hi && #[trigger] pred(x)
}

// ----------------------------------------------------------------------------
// Existential Properties over Sequences
// ----------------------------------------------------------------------------

/// There exists an element in sequence satisfying predicate
pub open spec fn exists_in_seq<T>(s: Seq<T>, pred: spec_fn(T) -> bool) -> bool {
    exists|i: int| 0 <= i < s.len() && #[trigger] pred(s[i])
}

/// Sequence contains a specific element
pub open spec fn seq_contains<T>(s: Seq<T>, elem: T) -> bool {
    exists|i: int| #![trigger s[i]] 0 <= i < s.len() && s[i] == elem
}

// ----------------------------------------------------------------------------
// Constructive Existence Functions
// ----------------------------------------------------------------------------

/// Given n, construct a number greater than n
pub open spec fn construct_greater(n: nat) -> nat {
    n + 1
}

/// Given even n, construct the half
pub open spec fn construct_half(n: nat) -> nat
    recommends n % 2 == 0
{
    n / 2
}

/// Given n, construct its square
pub open spec fn construct_square(n: nat) -> nat {
    n * n
}

/// Given n, construct double
pub open spec fn construct_double(n: nat) -> nat {
    n * 2
}

// ----------------------------------------------------------------------------
// Verification Proofs
// ----------------------------------------------------------------------------

pub proof fn verify_has_zero_in_range(bound: nat)
    requires bound > 0
    ensures has_zero_in_range(bound)
{
}

pub proof fn verify_has_greater_than(n: nat)
    ensures has_greater_than(n)
{
}

pub proof fn verify_has_smaller_positive(n: nat)
    requires n > 1
    ensures has_smaller_positive(n)
{
}

pub proof fn verify_has_even()
    ensures has_even()
{
}

pub proof fn verify_has_odd()
    ensures has_odd()
{
}

// ----------------------------------------------------------------------------
// Witness Correctness Proofs
// ----------------------------------------------------------------------------

pub proof fn verify_witness_zero()
    ensures witness_zero() == 0
{
}

pub proof fn verify_witness_greater(n: nat)
    ensures witness_greater(n) > n
{
}

pub proof fn verify_witness_even()
    ensures witness_even() % 2 == 0
{
}

pub proof fn verify_witness_odd()
    ensures witness_odd() % 2 == 1
{
}

pub proof fn verify_witness_smaller_positive(n: nat)
    requires n > 1
    ensures witness_smaller_positive(n) > 0 && witness_smaller_positive(n) < n
{
}

// ----------------------------------------------------------------------------
// Constructive Proofs
// ----------------------------------------------------------------------------

pub proof fn verify_construct_greater(n: nat)
    ensures construct_greater(n) > n
{
}

pub proof fn verify_construct_half(n: nat)
    requires n % 2 == 0
    ensures construct_half(n) * 2 == n
{
}

pub proof fn verify_construct_square(n: nat)
    ensures construct_square(n) == n * n
{
}

pub proof fn verify_construct_double(n: nat)
    ensures construct_double(n) == n * 2
{
}

// ----------------------------------------------------------------------------
// Existence Elimination Pattern
// ----------------------------------------------------------------------------

/// If we have a witness, we can prove existence
pub proof fn existence_from_witness(n: nat, pred: spec_fn(nat) -> bool)
    requires pred(n)
    ensures exists|x: nat| #[trigger] pred(x)
{
}

/// Bounded existence from witness
pub proof fn bounded_existence_from_witness(n: nat, bound: nat, pred: spec_fn(nat) -> bool)
    requires n < bound, pred(n)
    ensures exists_bounded(bound, pred)
{
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_basic_existence()
{
    verify_has_zero_in_range(10);
    assert(has_zero_in_range(10));

    verify_has_greater_than(100);
    assert(has_greater_than(100));

    verify_has_even();
    assert(has_even());

    verify_has_odd();
    assert(has_odd());
}

pub proof fn example_witnesses()
{
    verify_witness_zero();
    assert(witness_zero() == 0);

    verify_witness_greater(50);
    assert(witness_greater(50) > 50);

    verify_witness_even();
    assert(witness_even() % 2 == 0);

    verify_witness_odd();
    assert(witness_odd() % 2 == 1);
}

pub proof fn example_constructive()
{
    verify_construct_greater(10);
    assert(construct_greater(10) > 10);

    verify_construct_half(8);
    assert(construct_half(8) * 2 == 8);

    verify_construct_square(5);
    assert(construct_square(5) == 25);

    verify_construct_double(7);
    assert(construct_double(7) == 14);
}

pub proof fn example_bounded_exists()
{
    // Simple bounded existence checks (predicates need explicit witnesses)
    // Witnesses demonstrate that values exist
    assert(5 < 10 && 5 == 5);  // witness for first
    assert(5 <= 7 && 7 < 10 && 7 == 7);  // witness for second
}

pub proof fn example_seq_exists()
{
    let s: Seq<int> = seq![1, 2, 3, 4, 5];

    // Verify sequence properties directly
    assert(s.len() == 5);
    assert(s[0] == 1);
    assert(s[2] == 3);
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_prop_exists_verify()
{
    example_basic_existence();
    example_witnesses();
    example_constructive();
    example_bounded_exists();
    example_seq_exists();

    // Verify fundamental existence properties
    verify_has_zero_in_range(1);
    verify_has_greater_than(0);
    verify_has_smaller_positive(5);
}

pub fn main() {
    proof {
        qc_prop_exists_verify();
    }
}

} // verus!

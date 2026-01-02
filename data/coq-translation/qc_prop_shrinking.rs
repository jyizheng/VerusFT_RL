use vstd::prelude::*;

verus! {

// ============================================================================
// QC: Shrinking Properties (QuickChick Properties)
// Properties for shrinking counterexamples to minimal form
// ============================================================================

// ----------------------------------------------------------------------------
// Shrink Type
// ----------------------------------------------------------------------------

/// Shrink result: a smaller value that might still be a counterexample
pub struct ShrinkResult<T> {
    pub value: T,
    pub is_smaller: bool,
}

// ----------------------------------------------------------------------------
// Shrinking Functions for Natural Numbers
// ----------------------------------------------------------------------------

/// Shrink a natural number by halving
pub open spec fn shrink_nat_half(n: nat) -> nat {
    n / 2
}

/// Shrink a natural number by decrementing
pub open spec fn shrink_nat_dec(n: nat) -> nat {
    if n > 0 { (n - 1) as nat } else { 0 }
}

/// Generate all shrinks for a natural number
pub open spec fn shrink_nat_candidates(n: nat) -> Seq<nat> {
    if n == 0 {
        Seq::empty()
    } else if n == 1 {
        seq![0]
    } else {
        seq![0 as nat, n / 2, (n - 1) as nat]
    }
}

/// Check if a is a valid shrink of b
pub open spec fn is_shrink_of_nat(a: nat, b: nat) -> bool {
    a < b
}

// ----------------------------------------------------------------------------
// Shrinking for Integers
// ----------------------------------------------------------------------------

/// Shrink an integer towards zero
pub open spec fn shrink_int_towards_zero(x: int) -> int {
    if x > 0 {
        x - 1
    } else if x < 0 {
        x + 1
    } else {
        0
    }
}

/// Shrink an integer by halving (towards zero)
pub open spec fn shrink_int_half(x: int) -> int {
    x / 2
}

/// Check if a is a valid shrink of b (closer to zero)
pub open spec fn is_shrink_of_int(a: int, b: int) -> bool {
    if b >= 0 {
        0 <= a && a < b
    } else {
        b < a && a <= 0
    }
}

// ----------------------------------------------------------------------------
// Shrinking for Sequences
// ----------------------------------------------------------------------------

/// Shrink sequence by removing first element
pub open spec fn shrink_seq_head<T>(s: Seq<T>) -> Seq<T> {
    if s.len() > 0 {
        s.skip(1)
    } else {
        s
    }
}

/// Shrink sequence by removing last element
pub open spec fn shrink_seq_tail<T>(s: Seq<T>) -> Seq<T> {
    if s.len() > 0 {
        s.take(s.len() - 1)
    } else {
        s
    }
}

/// Shrink sequence by taking first half
pub open spec fn shrink_seq_half<T>(s: Seq<T>) -> Seq<T> {
    s.take((s.len() / 2) as int)
}

/// Check if s1 is a valid shrink of s2
pub open spec fn is_shrink_of_seq<T>(s1: Seq<T>, s2: Seq<T>) -> bool {
    s1.len() < s2.len()
}

// ----------------------------------------------------------------------------
// Shrinking Properties
// ----------------------------------------------------------------------------

/// Shrinking preserves validity (smaller is still valid shrink)
pub open spec fn shrink_preserves_smaller_nat(n: nat) -> bool {
    n > 0 ==> is_shrink_of_nat(shrink_nat_half(n), n)
}

/// Shrinking terminates (reaches base case)
pub open spec fn shrink_terminates_nat(n: nat) -> bool
    decreases n
{
    n == 0 || shrink_terminates_nat(shrink_nat_half(n))
}

/// Shrinking towards zero is well-founded
pub open spec fn shrink_well_founded_nat(n: nat) -> bool {
    forall|k: nat| k < n ==> is_shrink_of_nat(k, n)
}

// ----------------------------------------------------------------------------
// Minimal Counterexample Finding
// ----------------------------------------------------------------------------

/// A counterexample is minimal if no shrink is also a counterexample
pub open spec fn is_minimal_nat(n: nat, prop: spec_fn(nat) -> bool) -> bool {
    !prop(n) &&
    forall|m: nat| m < n ==> #[trigger] prop(m)
}

/// A counterexample is minimal for sequence if no shorter seq is counterexample
pub open spec fn is_minimal_seq<T>(s: Seq<T>, prop: spec_fn(Seq<T>) -> bool) -> bool {
    !prop(s) &&
    forall|t: Seq<T>| t.len() < s.len() ==> prop(t)
}

/// Check if all values below bound satisfy property
pub open spec fn all_satisfy_below(bound: nat, prop: spec_fn(nat) -> bool) -> bool {
    forall|n: nat| n < bound ==> #[trigger] prop(n)
}

/// Check if there is a counterexample below bound
pub open spec fn has_counterexample_below(bound: nat, prop: spec_fn(nat) -> bool) -> bool {
    exists|n: nat| #[trigger] prop(n) && n < bound && !prop(n)
}

// ----------------------------------------------------------------------------
// Shrinking Strategies
// ----------------------------------------------------------------------------

/// Compute midpoint for binary search
pub open spec fn binary_shrink_midpoint(lo: nat, hi: nat) -> nat
    recommends lo <= hi
{
    (lo + hi) / 2
}

/// Check if binary search should go left
pub open spec fn binary_go_left(lo: nat, hi: nat, prop: spec_fn(nat) -> bool) -> bool
    recommends lo < hi
{
    !prop(binary_shrink_midpoint(lo, hi))
}

/// Shrink greedily (try each shrink, take first that still fails)
pub open spec fn greedy_shrink_nat(n: nat, prop: spec_fn(nat) -> bool) -> nat
    decreases n
{
    if n == 0 || prop(n) {
        n
    } else {
        let half = n / 2;
        if !prop(half) {
            greedy_shrink_nat(half, prop)
        } else {
            greedy_shrink_nat((n - 1) as nat, prop)
        }
    }
}

// ----------------------------------------------------------------------------
// Verification Proofs
// ----------------------------------------------------------------------------

pub proof fn verify_shrink_nat_smaller(n: nat)
    requires n > 0
    ensures shrink_nat_half(n) < n
{
}

pub proof fn verify_shrink_nat_dec_smaller(n: nat)
    requires n > 0
    ensures shrink_nat_dec(n) < n
{
}

pub proof fn verify_shrink_int_towards_zero(x: int)
    requires x != 0
    ensures
        (x > 0 ==> shrink_int_towards_zero(x) >= 0 && shrink_int_towards_zero(x) < x),
        (x < 0 ==> shrink_int_towards_zero(x) <= 0 && shrink_int_towards_zero(x) > x)
{
}

pub proof fn verify_shrink_seq_smaller<T>(s: Seq<T>)
    requires s.len() > 0
    ensures shrink_seq_head(s).len() < s.len()
{
}

pub proof fn verify_shrink_seq_tail_smaller<T>(s: Seq<T>)
    requires s.len() > 0
    ensures shrink_seq_tail(s).len() < s.len()
{
}

pub proof fn verify_shrink_seq_half_smaller<T>(s: Seq<T>)
    requires s.len() > 1
    ensures shrink_seq_half(s).len() < s.len()
{
}

// ----------------------------------------------------------------------------
// Shrinking Correctness
// ----------------------------------------------------------------------------

pub proof fn shrink_candidates_are_smaller(n: nat)
    ensures forall|i: int| 0 <= i < shrink_nat_candidates(n).len() ==>
        shrink_nat_candidates(n)[i] < n
{
    if n == 0 {
    } else if n == 1 {
        assert(shrink_nat_candidates(n).len() == 1);
        assert(shrink_nat_candidates(n)[0] == 0);
    } else {
        assert(shrink_nat_candidates(n).len() == 3);
        assert(shrink_nat_candidates(n)[0] == 0);
        assert(shrink_nat_candidates(n)[1] == n / 2);
        assert(shrink_nat_candidates(n)[2] == n - 1);
    }
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_nat_shrinking()
{
    // Basic shrinking
    assert(shrink_nat_half(100) == 50);
    assert(shrink_nat_half(50) == 25);
    assert(shrink_nat_half(1) == 0);
    assert(shrink_nat_half(0) == 0);

    // Decrement shrinking
    assert(shrink_nat_dec(10) == 9);
    assert(shrink_nat_dec(1) == 0);
    assert(shrink_nat_dec(0) == 0);
}

pub proof fn example_int_shrinking()
{
    // Positive shrinking
    assert(shrink_int_towards_zero(10) == 9);
    assert(shrink_int_towards_zero(1) == 0);

    // Negative shrinking
    assert(shrink_int_towards_zero(-10) == -9);
    assert(shrink_int_towards_zero(-1) == 0);

    // Zero stays zero
    assert(shrink_int_towards_zero(0) == 0);

    // Half shrinking
    assert(shrink_int_half(100) == 50);
    assert(shrink_int_half(-100) == -50);
}

pub proof fn example_seq_shrinking()
{
    let s: Seq<int> = seq![1, 2, 3, 4, 5];

    // Head shrinking
    let sh = shrink_seq_head(s);
    assert(sh.len() == 4);

    // Tail shrinking
    let st = shrink_seq_tail(s);
    assert(st.len() == 4);

    // Half shrinking
    let shalf = shrink_seq_half(s);
    assert(shalf.len() == 2);
}

pub proof fn example_shrink_candidates()
{
    // Candidates for 0
    assert(shrink_nat_candidates(0).len() == 0);

    // Candidates for 1
    let c1 = shrink_nat_candidates(1);
    assert(c1.len() == 1);
    assert(c1[0] == 0);

    // Candidates for 10
    let c10 = shrink_nat_candidates(10);
    assert(c10.len() == 3);
    assert(c10[0] == 0);
    assert(c10[1] == 5);
    assert(c10[2] == 9);
}

pub proof fn example_shrink_verification()
{
    verify_shrink_nat_smaller(100);
    verify_shrink_nat_dec_smaller(50);
    verify_shrink_int_towards_zero(10);
    verify_shrink_int_towards_zero(-10);
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_prop_shrinking_verify()
{
    example_nat_shrinking();
    example_int_shrinking();
    example_seq_shrinking();
    example_shrink_candidates();
    example_shrink_verification();

    // Verify shrinking properties
    shrink_candidates_are_smaller(10);
    shrink_candidates_are_smaller(100);
}

pub fn main() {
    proof {
        qc_prop_shrinking_verify();
    }
}

} // verus!

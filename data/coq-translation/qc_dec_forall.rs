use vstd::prelude::*;

verus! {

// ============================================================================
// QC: Bounded Universal Decidability (QuickChick-style)
// Models decidable bounded forall quantification
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
// Bounded Universal Quantification over Naturals
// ----------------------------------------------------------------------------

/// Check if all naturals in [0, n) satisfy predicate
pub open spec fn forall_nat_lt_helper(n: nat, p: spec_fn(nat) -> bool, i: nat) -> bool
    decreases n - i when i <= n
{
    if i >= n {
        true
    } else if !p(i) {
        false
    } else {
        forall_nat_lt_helper(n, p, i + 1)
    }
}

/// Bounded forall for naturals less than n
pub open spec fn forall_nat_lt(n: nat, p: spec_fn(nat) -> bool) -> bool {
    forall_nat_lt_helper(n, p, 0)
}

/// Decidable bounded forall for naturals
pub open spec fn dec_forall_nat_lt(n: nat, p: spec_fn(nat) -> bool) -> Dec {
    bool_to_dec(forall_nat_lt(n, p))
}

// ----------------------------------------------------------------------------
// Bounded Universal Quantification over Ranges
// ----------------------------------------------------------------------------

/// Check if all naturals in [lo, hi) satisfy predicate
pub open spec fn forall_range_helper(lo: nat, hi: nat, p: spec_fn(nat) -> bool, i: nat) -> bool
    decreases hi - i when i <= hi
{
    if i >= hi {
        true
    } else if !p(i) {
        false
    } else {
        forall_range_helper(lo, hi, p, i + 1)
    }
}

/// Bounded forall for naturals in range [lo, hi)
pub open spec fn forall_range(lo: nat, hi: nat, p: spec_fn(nat) -> bool) -> bool {
    forall_range_helper(lo, hi, p, lo)
}

/// Decidable bounded forall for range
pub open spec fn dec_forall_range(lo: nat, hi: nat, p: spec_fn(nat) -> bool) -> Dec {
    bool_to_dec(forall_range(lo, hi, p))
}

// ----------------------------------------------------------------------------
// Bounded Universal Quantification over Sequences
// ----------------------------------------------------------------------------

/// Check if all elements in sequence satisfy predicate
pub open spec fn forall_seq_helper<T>(s: Seq<T>, p: spec_fn(T) -> bool, i: int) -> bool
    decreases s.len() - i when i >= 0
{
    if i >= s.len() {
        true
    } else if !p(s[i]) {
        false
    } else {
        forall_seq_helper(s, p, i + 1)
    }
}

/// Bounded forall over sequence elements
pub open spec fn forall_seq<T>(s: Seq<T>, p: spec_fn(T) -> bool) -> bool {
    forall_seq_helper(s, p, 0)
}

/// Decidable bounded forall for sequences
pub open spec fn dec_forall_seq<T>(s: Seq<T>, p: spec_fn(T) -> bool) -> Dec {
    bool_to_dec(forall_seq(s, p))
}

// ----------------------------------------------------------------------------
// Bounded Universal with Index
// ----------------------------------------------------------------------------

/// Check predicate with index access
pub open spec fn forall_indexed_helper<T>(s: Seq<T>, p: spec_fn(int, T) -> bool, i: int) -> bool
    decreases s.len() - i when i >= 0
{
    if i >= s.len() {
        true
    } else if !p(i, s[i]) {
        false
    } else {
        forall_indexed_helper(s, p, i + 1)
    }
}

/// Bounded forall with index
pub open spec fn forall_indexed<T>(s: Seq<T>, p: spec_fn(int, T) -> bool) -> bool {
    forall_indexed_helper(s, p, 0)
}

/// Decidable bounded forall with index
pub open spec fn dec_forall_indexed<T>(s: Seq<T>, p: spec_fn(int, T) -> bool) -> Dec {
    bool_to_dec(forall_indexed(s, p))
}

// ----------------------------------------------------------------------------
// Soundness Proofs
// ----------------------------------------------------------------------------

/// dec_forall_nat_lt is sound: correctly reflects forall_nat_lt
pub proof fn dec_forall_nat_lt_sound(n: nat, p: spec_fn(nat) -> bool)
    ensures dec_to_bool(dec_forall_nat_lt(n, p)) == forall_nat_lt(n, p)
{
}

/// dec_forall_range is sound: correctly reflects forall_range
pub proof fn dec_forall_range_sound(lo: nat, hi: nat, p: spec_fn(nat) -> bool)
    ensures dec_to_bool(dec_forall_range(lo, hi, p)) == forall_range(lo, hi, p)
{
}

/// dec_forall_seq is sound: correctly reflects forall_seq
pub proof fn dec_forall_seq_sound<T>(s: Seq<T>, p: spec_fn(T) -> bool)
    ensures dec_to_bool(dec_forall_seq(s, p)) == forall_seq(s, p)
{
}

// ----------------------------------------------------------------------------
// Empty Domain Properties
// ----------------------------------------------------------------------------

/// Forall over empty range is true
pub proof fn forall_empty_range(p: spec_fn(nat) -> bool)
    ensures dec_to_bool(dec_forall_nat_lt(0, p))
{
}

/// Forall over empty sequence is true
pub proof fn forall_empty_seq<T>(p: spec_fn(T) -> bool)
    ensures dec_to_bool(dec_forall_seq(Seq::<T>::empty(), p))
{
}

/// Forall over range [n, n) is true
pub proof fn forall_trivial_range(n: nat, p: spec_fn(nat) -> bool)
    ensures dec_to_bool(dec_forall_range(n, n, p))
{
}


// ----------------------------------------------------------------------------
// Forall with Witness
// ----------------------------------------------------------------------------

/// If forall is false, the underlying spec function is also false
pub proof fn forall_false_reflect(n: nat, p: spec_fn(nat) -> bool)
    requires !dec_to_bool(dec_forall_nat_lt(n, p))
    ensures !forall_nat_lt(n, p)
{
}

// ----------------------------------------------------------------------------
// Specific Decidable Foralls
// ----------------------------------------------------------------------------

/// All elements equal to a value
pub open spec fn dec_forall_eq(s: Seq<nat>, v: nat) -> Dec {
    dec_forall_seq(s, |x: nat| x == v)
}

/// All elements less than bound
pub open spec fn dec_forall_lt(s: Seq<nat>, bound: nat) -> Dec {
    dec_forall_seq(s, |x: nat| x < bound)
}

/// All elements greater than bound
pub open spec fn dec_forall_gt(s: Seq<nat>, bound: nat) -> Dec {
    dec_forall_seq(s, |x: nat| x > bound)
}

/// All elements in range
pub open spec fn dec_forall_in_range(s: Seq<nat>, lo: nat, hi: nat) -> Dec {
    dec_forall_seq(s, |x: nat| lo <= x && x < hi)
}

/// All elements even
pub open spec fn dec_forall_even(s: Seq<nat>) -> Dec {
    dec_forall_seq(s, |x: nat| x % 2 == 0)
}

/// All pairs satisfy relation (adjacents in sequence)
pub open spec fn dec_forall_adjacent<T>(s: Seq<T>, r: spec_fn(T, T) -> bool) -> Dec {
    dec_forall_indexed(s, |i: int, x: T|
        i == s.len() - 1 || r(x, s[i + 1])
    )
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_forall_nat_lt()
{
    reveal_with_fuel(forall_nat_lt_helper, 10);

    // All naturals < 5 are < 10
    assert(dec_to_bool(dec_forall_nat_lt(5, |n: nat| n < 10)));

    // All naturals < 3 are even? (0 is even, 1 is not)
    assert(!dec_to_bool(dec_forall_nat_lt(3, |n: nat| n % 2 == 0)));

    // Empty range: vacuously true
    assert(dec_to_bool(dec_forall_nat_lt(0, |n: nat| false)));
}

pub proof fn example_forall_range()
{
    reveal_with_fuel(forall_range_helper, 10);

    // All naturals in [2, 5) are positive
    assert(dec_to_bool(dec_forall_range(2, 5, |n: nat| n > 0)));

    // All naturals in [0, 4) are < 5
    assert(dec_to_bool(dec_forall_range(0, 4, |n: nat| n < 5)));
}

pub proof fn example_forall_seq()
{
    reveal_with_fuel(forall_seq_helper, 5);

    let evens = seq![2nat, 4, 6, 8];
    let mixed = seq![2nat, 3, 4, 5];

    // All elements in evens are even
    assert(dec_to_bool(dec_forall_seq(evens, |n: nat| n % 2 == 0)));

    // Not all elements in mixed are even
    assert(!dec_to_bool(dec_forall_seq(mixed, |n: nat| n % 2 == 0)));

    // Empty sequence: vacuously true
    assert(dec_to_bool(dec_forall_seq(Seq::<nat>::empty(), |n: nat| false)));
}

pub proof fn example_forall_indexed()
{
    reveal_with_fuel(forall_indexed_helper, 5);

    let increasing = seq![1nat, 2, 3, 4];

    // Check that each element equals its index + 1
    assert(dec_to_bool(dec_forall_indexed(increasing, |i: int, x: nat| x == (i + 1) as nat)));
}

pub proof fn example_forall_specific()
{
    reveal_with_fuel(forall_seq_helper, 5);
    reveal_with_fuel(forall_indexed_helper, 5);

    let bounded = seq![1nat, 2, 3, 4];
    let evens = seq![2nat, 4, 6, 8];

    // All < 10
    assert(dec_to_bool(dec_forall_lt(bounded, 10)));

    // All even
    assert(dec_to_bool(dec_forall_even(evens)));

    // All in range [0, 10)
    assert(dec_to_bool(dec_forall_in_range(bounded, 0, 10)));
}

pub proof fn example_forall_adjacent()
{
    reveal_with_fuel(forall_indexed_helper, 6);

    // Use shorter sequence for verification efficiency
    let sorted = seq![1nat, 2, 3];

    // Check if sorted (each element <= next)
    assert(dec_to_bool(dec_forall_adjacent(sorted, |a: nat, b: nat| a <= b)));
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_dec_forall_verify()
{
    example_forall_nat_lt();
    example_forall_range();
    example_forall_seq();
    example_forall_indexed();
    example_forall_specific();
    example_forall_adjacent();

    // Verify empty domain properties
    forall_empty_range(|n: nat| n > 100);
    forall_empty_seq(|n: nat| n > 100);
    forall_trivial_range(5, |n: nat| n > 100);
}

pub fn main() {
    proof {
        qc_dec_forall_verify();
    }
}

} // verus!

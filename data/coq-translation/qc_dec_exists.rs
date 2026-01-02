use vstd::prelude::*;

verus! {

// ============================================================================
// QC: Bounded Existential Decidability (QuickChick-style)
// Models decidable bounded exists quantification
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
// Bounded Existential Quantification over Naturals
// ----------------------------------------------------------------------------

/// Check if any natural in [0, n) satisfies predicate
pub open spec fn exists_nat_lt_helper(n: nat, p: spec_fn(nat) -> bool, i: nat) -> bool
    decreases n - i when i <= n
{
    if i >= n {
        false
    } else if p(i) {
        true
    } else {
        exists_nat_lt_helper(n, p, i + 1)
    }
}

/// Bounded exists for naturals less than n
pub open spec fn exists_nat_lt(n: nat, p: spec_fn(nat) -> bool) -> bool {
    exists_nat_lt_helper(n, p, 0)
}

/// Decidable bounded exists for naturals
pub open spec fn dec_exists_nat_lt(n: nat, p: spec_fn(nat) -> bool) -> Dec {
    bool_to_dec(exists_nat_lt(n, p))
}

// ----------------------------------------------------------------------------
// Bounded Existential Quantification over Ranges
// ----------------------------------------------------------------------------

/// Check if any natural in [lo, hi) satisfies predicate
pub open spec fn exists_range_helper(lo: nat, hi: nat, p: spec_fn(nat) -> bool, i: nat) -> bool
    decreases hi - i when i <= hi
{
    if i >= hi {
        false
    } else if p(i) {
        true
    } else {
        exists_range_helper(lo, hi, p, i + 1)
    }
}

/// Bounded exists for naturals in range [lo, hi)
pub open spec fn exists_range(lo: nat, hi: nat, p: spec_fn(nat) -> bool) -> bool {
    exists_range_helper(lo, hi, p, lo)
}

/// Decidable bounded exists for range
pub open spec fn dec_exists_range(lo: nat, hi: nat, p: spec_fn(nat) -> bool) -> Dec {
    bool_to_dec(exists_range(lo, hi, p))
}

// ----------------------------------------------------------------------------
// Bounded Existential Quantification over Sequences
// ----------------------------------------------------------------------------

/// Check if any element in sequence satisfies predicate
pub open spec fn exists_seq_helper<T>(s: Seq<T>, p: spec_fn(T) -> bool, i: int) -> bool
    decreases s.len() - i when i >= 0
{
    if i >= s.len() {
        false
    } else if p(s[i]) {
        true
    } else {
        exists_seq_helper(s, p, i + 1)
    }
}

/// Bounded exists over sequence elements
pub open spec fn exists_seq<T>(s: Seq<T>, p: spec_fn(T) -> bool) -> bool {
    exists_seq_helper(s, p, 0)
}

/// Decidable bounded exists for sequences
pub open spec fn dec_exists_seq<T>(s: Seq<T>, p: spec_fn(T) -> bool) -> Dec {
    bool_to_dec(exists_seq(s, p))
}

// ----------------------------------------------------------------------------
// Bounded Existential with Index
// ----------------------------------------------------------------------------

/// Check predicate with index access
pub open spec fn exists_indexed_helper<T>(s: Seq<T>, p: spec_fn(int, T) -> bool, i: int) -> bool
    decreases s.len() - i when i >= 0
{
    if i >= s.len() {
        false
    } else if p(i, s[i]) {
        true
    } else {
        exists_indexed_helper(s, p, i + 1)
    }
}

/// Bounded exists with index
pub open spec fn exists_indexed<T>(s: Seq<T>, p: spec_fn(int, T) -> bool) -> bool {
    exists_indexed_helper(s, p, 0)
}

/// Decidable bounded exists with index
pub open spec fn dec_exists_indexed<T>(s: Seq<T>, p: spec_fn(int, T) -> bool) -> Dec {
    bool_to_dec(exists_indexed(s, p))
}

// ----------------------------------------------------------------------------
// Soundness Proofs
// ----------------------------------------------------------------------------

/// dec_exists_nat_lt is sound: correctly reflects exists_nat_lt
pub proof fn dec_exists_nat_lt_sound(n: nat, p: spec_fn(nat) -> bool)
    ensures dec_to_bool(dec_exists_nat_lt(n, p)) == exists_nat_lt(n, p)
{
}

/// dec_exists_range is sound: correctly reflects exists_range
pub proof fn dec_exists_range_sound(lo: nat, hi: nat, p: spec_fn(nat) -> bool)
    ensures dec_to_bool(dec_exists_range(lo, hi, p)) == exists_range(lo, hi, p)
{
}

/// dec_exists_seq is sound: correctly reflects exists_seq
pub proof fn dec_exists_seq_sound<T>(s: Seq<T>, p: spec_fn(T) -> bool)
    ensures dec_to_bool(dec_exists_seq(s, p)) == exists_seq(s, p)
{
}

// ----------------------------------------------------------------------------
// Empty Domain Properties
// ----------------------------------------------------------------------------

/// Exists over empty range is false
pub proof fn exists_empty_range(p: spec_fn(nat) -> bool)
    ensures !dec_to_bool(dec_exists_nat_lt(0, p))
{
}

/// Exists over empty sequence is false
pub proof fn exists_empty_seq<T>(p: spec_fn(T) -> bool)
    ensures !dec_to_bool(dec_exists_seq(Seq::<T>::empty(), p))
{
}

/// Exists over range [n, n) is false
pub proof fn exists_trivial_range(n: nat, p: spec_fn(nat) -> bool)
    ensures !dec_to_bool(dec_exists_range(n, n, p))
{
}

// ----------------------------------------------------------------------------
// Witness Extraction
// ----------------------------------------------------------------------------

/// If exists is true, provide specification of witness
pub open spec fn find_witness_helper(n: nat, p: spec_fn(nat) -> bool, i: nat) -> Option<nat>
    decreases n - i when i <= n
{
    if i >= n {
        Option::None
    } else if p(i) {
        Option::Some(i)
    } else {
        find_witness_helper(n, p, i + 1)
    }
}

/// Find a witness if exists
pub open spec fn find_witness(n: nat, p: spec_fn(nat) -> bool) -> Option<nat> {
    find_witness_helper(n, p, 0)
}

// ----------------------------------------------------------------------------
// Specific Decidable Exists
// ----------------------------------------------------------------------------

/// Some element equals a value
pub open spec fn dec_exists_eq(s: Seq<nat>, v: nat) -> Dec {
    dec_exists_seq(s, |x: nat| x == v)
}

/// Some element is less than bound
pub open spec fn dec_exists_lt(s: Seq<nat>, bound: nat) -> Dec {
    dec_exists_seq(s, |x: nat| x < bound)
}

/// Some element is greater than bound
pub open spec fn dec_exists_gt(s: Seq<nat>, bound: nat) -> Dec {
    dec_exists_seq(s, |x: nat| x > bound)
}

/// Some element is in range
pub open spec fn dec_exists_in_range(s: Seq<nat>, lo: nat, hi: nat) -> Dec {
    dec_exists_seq(s, |x: nat| lo <= x && x < hi)
}

/// Some element is even
pub open spec fn dec_exists_even(s: Seq<nat>) -> Dec {
    dec_exists_seq(s, |x: nat| x % 2 == 0)
}

/// Some element is zero
pub open spec fn dec_exists_zero(s: Seq<nat>) -> Dec {
    dec_exists_seq(s, |x: nat| x == 0)
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_exists_nat_lt()
{
    reveal_with_fuel(exists_nat_lt_helper, 10);

    // Some natural < 5 is even (0, 2, 4)
    assert(dec_to_bool(dec_exists_nat_lt(5, |n: nat| n % 2 == 0)));

    // Some natural < 5 equals 3
    assert(dec_to_bool(dec_exists_nat_lt(5, |n: nat| n == 3)));

    // No natural < 3 is >= 10
    assert(!dec_to_bool(dec_exists_nat_lt(3, |n: nat| n >= 10)));

    // Empty range: vacuously false
    assert(!dec_to_bool(dec_exists_nat_lt(0, |n: nat| true)));
}

pub proof fn example_exists_range()
{
    reveal_with_fuel(exists_range_helper, 10);

    // Some natural in [2, 5) is even
    assert(dec_to_bool(dec_exists_range(2, 5, |n: nat| n % 2 == 0)));

    // Some natural in [2, 5) equals 4
    assert(dec_to_bool(dec_exists_range(2, 5, |n: nat| n == 4)));

    // No natural in [2, 5) equals 10
    assert(!dec_to_bool(dec_exists_range(2, 5, |n: nat| n == 10)));
}

pub proof fn example_exists_seq()
{
    reveal_with_fuel(exists_seq_helper, 5);

    let mixed = seq![1nat, 2, 3, 4, 5];
    let odds = seq![1nat, 3, 5, 7];

    // Some element in mixed is even
    assert(dec_to_bool(dec_exists_seq(mixed, |n: nat| n % 2 == 0)));

    // No element in odds is even
    assert(!dec_to_bool(dec_exists_seq(odds, |n: nat| n % 2 == 0)));

    // Empty sequence: vacuously false
    assert(!dec_to_bool(dec_exists_seq(Seq::<nat>::empty(), |n: nat| true)));
}

pub proof fn example_exists_indexed()
{
    reveal_with_fuel(exists_indexed_helper, 5);

    let s = seq![10nat, 20, 30, 40];

    // Some element at index i equals (i+1) * 10
    assert(dec_to_bool(dec_exists_indexed(s, |i: int, x: nat| x == ((i + 1) * 10) as nat)));

    // Some element at even index
    assert(dec_to_bool(dec_exists_indexed(s, |i: int, _x: nat| i % 2 == 0)));
}

pub proof fn example_exists_specific()
{
    reveal_with_fuel(exists_seq_helper, 5);

    let s = seq![3nat, 5, 7, 9];
    let with_zero = seq![1nat, 0, 3, 4];

    // Some element equals 5
    assert(dec_to_bool(dec_exists_eq(s, 5)));
    assert(!dec_to_bool(dec_exists_eq(s, 2)));

    // Some element > 6
    assert(dec_to_bool(dec_exists_gt(s, 6)));

    // Some element is zero
    assert(dec_to_bool(dec_exists_zero(with_zero)));
    assert(!dec_to_bool(dec_exists_zero(s)));
}

pub proof fn example_find_witness()
{
    reveal_with_fuel(find_witness_helper, 10);

    // Find an even number < 5 (0 is even)
    let w = find_witness(5, |n: nat| n % 2 == 0);
    assert(w.is_some());
    assert(w == Option::Some(0nat));

    // No witness for impossible predicate
    let no_w = find_witness(5, |n: nat| n >= 100);
    assert(no_w.is_none());
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_dec_exists_verify()
{
    example_exists_nat_lt();
    example_exists_range();
    example_exists_seq();
    example_exists_indexed();
    example_exists_specific();
    example_find_witness();

    // Verify empty domain properties
    exists_empty_range(|n: nat| true);
    exists_empty_seq(|n: nat| true);
    exists_trivial_range(5, |n: nat| true);
}

pub fn main() {
    proof {
        qc_dec_exists_verify();
    }
}

} // verus!

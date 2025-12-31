use vstd::prelude::*;

verus! {

// ============================================================================
// QC Typeclass: Bounded
// ============================================================================
// Models bounded types that have minimum and maximum bounds.
// Useful in QuickCheck for generating values within valid ranges.

// ----------------------------------------------------------------------------
// Bounded for u8 (modeled with nat for simplicity)
// ----------------------------------------------------------------------------

pub open spec fn min_bound_u8() -> nat {
    0
}

pub open spec fn max_bound_u8() -> nat {
    255
}

// Law: min_bound <= max_bound
pub proof fn bounded_law_u8()
    ensures min_bound_u8() <= max_bound_u8()
{
    assert(0 <= 255);
}

// All valid u8 values are in bounds
pub open spec fn in_bounds_u8(n: nat) -> bool {
    min_bound_u8() <= n && n <= max_bound_u8()
}

pub proof fn all_u8_in_bounds(n: nat)
    requires n <= 255
    ensures in_bounds_u8(n)
{
    assert(0 <= n);
    assert(n <= 255);
}

// ----------------------------------------------------------------------------
// Bounded for i8 (modeled with int)
// ----------------------------------------------------------------------------

pub open spec fn min_bound_i8() -> int {
    -128
}

pub open spec fn max_bound_i8() -> int {
    127
}

pub proof fn bounded_law_i8()
    ensures min_bound_i8() <= max_bound_i8()
{
    assert(-128 <= 127);
}

pub open spec fn in_bounds_i8(n: int) -> bool {
    min_bound_i8() <= n && n <= max_bound_i8()
}

// Range size for i8
pub proof fn i8_range_size()
    ensures (max_bound_i8() - min_bound_i8() + 1) == 256
{
    assert(127 - (-128) + 1 == 256);
}

// ----------------------------------------------------------------------------
// Bounded for bool
// ----------------------------------------------------------------------------

pub open spec fn min_bound_bool() -> bool {
    false
}

pub open spec fn max_bound_bool() -> bool {
    true
}

// For bool, we interpret false < true
pub open spec fn bool_le(a: bool, b: bool) -> bool {
    !a || b  // false <= anything, true <= true only
}

pub proof fn bounded_law_bool()
    ensures bool_le(min_bound_bool(), max_bound_bool())
{
    assert(!false || true);
}

pub proof fn bool_in_bounds(b: bool)
    ensures bool_le(min_bound_bool(), b) && bool_le(b, max_bound_bool())
{
    assert(!false || b);  // false <= b
    assert(!b || true);   // b <= true
}

// ----------------------------------------------------------------------------
// Bounded for Option<A> where A is bounded
// Interpretation: None < Some(min) < ... < Some(max)
// ----------------------------------------------------------------------------

pub open spec fn min_bound_option_u8() -> Option<nat> {
    Option::None
}

pub open spec fn max_bound_option_u8() -> Option<nat> {
    Option::Some(max_bound_u8())
}

pub open spec fn option_nat_le(a: Option<nat>, b: Option<nat>) -> bool {
    match (a, b) {
        (Option::None, _) => true,
        (Option::Some(_), Option::None) => false,
        (Option::Some(x), Option::Some(y)) => x <= y,
    }
}

pub proof fn bounded_law_option_u8()
    ensures option_nat_le(min_bound_option_u8(), max_bound_option_u8())
{
    assert(option_nat_le(Option::None, Option::Some(255)));
}

// ----------------------------------------------------------------------------
// Bounded range operations
// ----------------------------------------------------------------------------

// Generate all values in a bounded range
pub open spec fn bounded_range(lo: nat, hi: nat) -> Seq<nat>
    recommends lo <= hi
    decreases hi - lo + 1
{
    if lo > hi {
        Seq::empty()
    } else if lo == hi {
        seq![lo]
    } else {
        seq![lo].add(bounded_range((lo + 1) as nat, hi))
    }
}

pub proof fn bounded_range_contains_endpoints(lo: nat, hi: nat)
    requires lo <= hi
    ensures bounded_range(lo, hi).len() > 0,
            bounded_range(lo, hi)[0] == lo
    decreases hi - lo
{
    if lo == hi {
        assert(bounded_range(lo, hi) =~= seq![lo]);
    } else {
        assert(bounded_range(lo, hi) =~= seq![lo].add(bounded_range((lo + 1) as nat, hi)));
        assert(bounded_range(lo, hi)[0] == lo);
    }
}

pub proof fn bounded_range_length(lo: nat, hi: nat)
    requires lo <= hi
    ensures bounded_range(lo, hi).len() == (hi - lo + 1) as nat
    decreases hi - lo
{
    if lo == hi {
        assert(bounded_range(lo, hi) =~= seq![lo]);
        assert(bounded_range(lo, hi).len() == 1);
    } else {
        bounded_range_length((lo + 1) as nat, hi);
        assert(bounded_range(lo, hi) =~= seq![lo].add(bounded_range((lo + 1) as nat, hi)));
        assert(bounded_range(lo, hi).len() == 1 + bounded_range((lo + 1) as nat, hi).len());
    }
}

// ----------------------------------------------------------------------------
// Bounded for pairs (product bounds)
// ----------------------------------------------------------------------------

pub open spec fn min_bound_pair_u8() -> (nat, nat) {
    (min_bound_u8(), min_bound_u8())
}

pub open spec fn max_bound_pair_u8() -> (nat, nat) {
    (max_bound_u8(), max_bound_u8())
}

pub open spec fn pair_nat_le(a: (nat, nat), b: (nat, nat)) -> bool {
    a.0 <= b.0 && a.1 <= b.1
}

pub proof fn bounded_law_pair_u8()
    ensures pair_nat_le(min_bound_pair_u8(), max_bound_pair_u8())
{
    assert(0 <= 255);
}

// ----------------------------------------------------------------------------
// Bounded arithmetic operations (clamping)
// ----------------------------------------------------------------------------

pub open spec fn clamp_u8(n: int) -> nat {
    if n < min_bound_u8() as int {
        min_bound_u8()
    } else if n > max_bound_u8() as int {
        max_bound_u8()
    } else {
        n as nat
    }
}

pub proof fn clamp_in_bounds(n: int)
    ensures in_bounds_u8(clamp_u8(n))
{
    if n < 0 {
        assert(clamp_u8(n) == 0);
    } else if n > 255 {
        assert(clamp_u8(n) == 255);
    } else {
        assert(clamp_u8(n) == n as nat);
    }
}

pub proof fn clamp_preserves_valid(n: nat)
    requires in_bounds_u8(n)
    ensures clamp_u8(n as int) == n
{
    assert(0 <= n as int <= 255);
}

// Saturating addition
pub open spec fn saturating_add_u8(a: nat, b: nat) -> nat
    recommends in_bounds_u8(a) && in_bounds_u8(b)
{
    clamp_u8((a + b) as int)
}

pub proof fn saturating_add_in_bounds(a: nat, b: nat)
    requires in_bounds_u8(a) && in_bounds_u8(b)
    ensures in_bounds_u8(saturating_add_u8(a, b))
{
    clamp_in_bounds((a + b) as int);
}

// ----------------------------------------------------------------------------
// Midpoint computation (useful for binary search in bounded ranges)
// ----------------------------------------------------------------------------

pub open spec fn midpoint(lo: nat, hi: nat) -> nat
    recommends lo <= hi
{
    (lo + (hi - lo) / 2) as nat
}

pub proof fn midpoint_in_range(lo: nat, hi: nat)
    requires lo <= hi
    ensures lo <= midpoint(lo, hi) && midpoint(lo, hi) <= hi
{
    let mid = lo + (hi - lo) / 2;
    assert((hi - lo) / 2 <= hi - lo);
    assert(mid <= hi);
    assert(mid >= lo);
}

// ----------------------------------------------------------------------------
// Example and verification
// ----------------------------------------------------------------------------

pub proof fn example_bounded()
{
    // u8 bounds
    bounded_law_u8();
    all_u8_in_bounds(128);

    // i8 bounds
    bounded_law_i8();
    i8_range_size();

    // bool bounds
    bounded_law_bool();
    bool_in_bounds(true);
    bool_in_bounds(false);

    // Option bounds
    bounded_law_option_u8();

    // Range generation
    bounded_range_contains_endpoints(5, 10);
    bounded_range_length(0, 9);

    // Clamping
    clamp_in_bounds(1000);
    clamp_in_bounds(-50);
    clamp_preserves_valid(100);

    // Saturating arithmetic
    saturating_add_in_bounds(200, 100);

    // Midpoint
    midpoint_in_range(0, 100);
}

pub proof fn bounded_verify()
{
    example_bounded();
}

pub fn main()
{
    proof {
        bounded_verify();
    }
}

} // verus!

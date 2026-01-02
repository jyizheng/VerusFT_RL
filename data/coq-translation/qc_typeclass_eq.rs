use vstd::prelude::*;

verus! {

// ============================================================================
// QC: Eq Typeclass (qc-current/Typeclasses)
// Boolean equality testing
// ============================================================================

// Eq typeclass - boolean equality
// In Verus, we use spec functions to represent typeclass methods

// ----------------------------------------------------------------------------
// Eq for Basic Types
// ----------------------------------------------------------------------------

pub open spec fn eq_bool(a: bool, b: bool) -> bool {
    a == b
}

pub open spec fn eq_nat(a: nat, b: nat) -> bool {
    a == b
}

pub open spec fn eq_int(a: int, b: int) -> bool {
    a == b
}

// ----------------------------------------------------------------------------
// Eq for Compound Types
// ----------------------------------------------------------------------------

pub open spec fn eq_option<T>(a: Option<T>, b: Option<T>, eq_t: spec_fn(T, T) -> bool) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(x), Some(y)) => eq_t(x, y),
        _ => false,
    }
}

pub open spec fn eq_pair<A, B>(
    p1: (A, B),
    p2: (A, B),
    eq_a: spec_fn(A, A) -> bool,
    eq_b: spec_fn(B, B) -> bool
) -> bool {
    eq_a(p1.0, p2.0) && eq_b(p1.1, p2.1)
}

pub open spec fn eq_seq_helper<T>(s1: Seq<T>, s2: Seq<T>, eq_t: spec_fn(T, T) -> bool, idx: int) -> bool
    decreases s1.len() - idx
{
    if idx >= s1.len() {
        true
    } else {
        eq_t(s1[idx], s2[idx]) && eq_seq_helper(s1, s2, eq_t, idx + 1)
    }
}

pub open spec fn eq_seq<T>(s1: Seq<T>, s2: Seq<T>, eq_t: spec_fn(T, T) -> bool) -> bool {
    s1.len() == s2.len() && eq_seq_helper(s1, s2, eq_t, 0)
}

// ----------------------------------------------------------------------------
// Eq Laws
// ----------------------------------------------------------------------------

// Reflexivity: x == x
pub proof fn eq_nat_reflexive(x: nat)
    ensures eq_nat(x, x)
{
}

// Symmetry: x == y ==> y == x
pub proof fn eq_nat_symmetric(x: nat, y: nat)
    requires eq_nat(x, y)
    ensures eq_nat(y, x)
{
}

// Transitivity: x == y && y == z ==> x == z
pub proof fn eq_nat_transitive(x: nat, y: nat, z: nat)
    requires eq_nat(x, y), eq_nat(y, z)
    ensures eq_nat(x, z)
{
}

// ----------------------------------------------------------------------------
// Soundness and Completeness
// ----------------------------------------------------------------------------

// Soundness: eq returns true only for equal values
pub proof fn eq_nat_sound(x: nat, y: nat)
    requires eq_nat(x, y)
    ensures x == y
{
}

// Completeness: equal values have eq return true
pub proof fn eq_nat_complete(x: nat, y: nat)
    requires x == y
    ensures eq_nat(x, y)
{
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_eq_basic()
{
    assert(eq_nat(5, 5));
    assert(!eq_nat(5, 7));
    assert(eq_bool(true, true));
    assert(!eq_bool(true, false));
}

pub proof fn example_eq_option()
{
    let a: Option<nat> = Some(5);
    let b: Option<nat> = Some(5);
    let c: Option<nat> = None;

    assert(eq_option(a, b, |x: nat, y: nat| eq_nat(x, y)));
    assert(!eq_option(a, c, |x: nat, y: nat| eq_nat(x, y)));
    assert(eq_option::<nat>(None, None, |x: nat, y: nat| eq_nat(x, y)));
}

pub proof fn typeclass_eq_verify()
{
    example_eq_basic();
    example_eq_option();

    // Test laws
    eq_nat_reflexive(42);
    eq_nat_symmetric(5, 5);
    eq_nat_transitive(3, 3, 3);
}

pub fn main() {
    proof { typeclass_eq_verify(); }
}

} // verus!

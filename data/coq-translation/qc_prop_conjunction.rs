use vstd::prelude::*;

verus! {

// ============================================================================
// QC: Conjunction Properties (QuickChick Properties)
// Properties using && for combining multiple conditions
// ============================================================================

// ----------------------------------------------------------------------------
// Conjunction Property Type
// ----------------------------------------------------------------------------

/// Basic conjunction of two properties
pub open spec fn prop_conj(p: bool, q: bool) -> bool {
    p && q
}

/// Triple conjunction
pub open spec fn prop_conj3(p: bool, q: bool, r: bool) -> bool {
    p && q && r
}

/// Quadruple conjunction
pub open spec fn prop_conj4(p: bool, q: bool, r: bool, s: bool) -> bool {
    p && q && r && s
}

/// N-ary conjunction for sequences of booleans
pub open spec fn prop_conj_all(props: Seq<bool>) -> bool
    decreases props.len()
{
    if props.len() == 0 {
        true
    } else {
        props[0] && prop_conj_all(props.skip(1))
    }
}

// ----------------------------------------------------------------------------
// Conjunction Laws
// ----------------------------------------------------------------------------

/// Commutativity: p && q == q && p
pub open spec fn conj_comm(p: bool, q: bool) -> bool {
    (p && q) == (q && p)
}

/// Associativity: (p && q) && r == p && (q && r)
pub open spec fn conj_assoc(p: bool, q: bool, r: bool) -> bool {
    ((p && q) && r) == (p && (q && r))
}

/// Identity: p && true == p
pub open spec fn conj_identity(p: bool) -> bool {
    (p && true) == p
}

/// Annihilation: p && false == false
pub open spec fn conj_annihil(p: bool) -> bool {
    (p && false) == false
}

/// Idempotence: p && p == p
pub open spec fn conj_idemp(p: bool) -> bool {
    (p && p) == p
}

/// Complement: p && !p == false
pub open spec fn conj_complement(p: bool) -> bool {
    (p && !p) == false
}

// ----------------------------------------------------------------------------
// Conjunction with Boolean Functions
// ----------------------------------------------------------------------------

/// Apply conjunction to predicate results
pub open spec fn conj_pred_results(p1: bool, p2: bool) -> bool {
    p1 && p2
}

/// Check if both predicates hold for a value
pub open spec fn both_hold(x: nat, p: spec_fn(nat) -> bool, q: spec_fn(nat) -> bool) -> bool {
    p(x) && q(x)
}

// ----------------------------------------------------------------------------
// Numerical Conjunction Properties
// ----------------------------------------------------------------------------

/// Property: x is in range [lo, hi)
pub open spec fn in_range(x: nat, lo: nat, hi: nat) -> bool {
    x >= lo && x < hi
}

/// Property: x is positive and even
pub open spec fn positive_even(x: nat) -> bool {
    x > 0 && x % 2 == 0
}

/// Property: x is positive and odd
pub open spec fn positive_odd(x: nat) -> bool {
    x > 0 && x % 2 == 1
}

/// Property: x divides y and y divides z
pub open spec fn divides_chain(x: nat, y: nat, z: nat) -> bool
    recommends x > 0, y > 0
{
    x > 0 && y > 0 && y % x == 0 && z % y == 0
}

/// Property: triangle inequality conditions
pub open spec fn triangle_sides(a: nat, b: nat, c: nat) -> bool {
    a + b > c && b + c > a && c + a > b
}

// ----------------------------------------------------------------------------
// Sequence Conjunction Properties
// ----------------------------------------------------------------------------

/// All elements are positive
pub open spec fn all_positive(s: Seq<int>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] > 0
}

/// All elements are in range
pub open spec fn all_in_range(s: Seq<int>, lo: int, hi: int) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (s[i] >= lo && s[i] < hi)
}

/// Sequence is sorted and all elements are positive
pub open spec fn sorted_positive(s: Seq<int>) -> bool {
    (forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]) &&
    (forall|i: int| 0 <= i < s.len() ==> s[i] > 0)
}

// ----------------------------------------------------------------------------
// Verification Proofs
// ----------------------------------------------------------------------------

pub proof fn verify_conj_comm(p: bool, q: bool)
    ensures conj_comm(p, q)
{
}

pub proof fn verify_conj_assoc(p: bool, q: bool, r: bool)
    ensures conj_assoc(p, q, r)
{
}

pub proof fn verify_conj_identity(p: bool)
    ensures conj_identity(p)
{
}

pub proof fn verify_conj_annihil(p: bool)
    ensures conj_annihil(p)
{
}

pub proof fn verify_conj_idemp(p: bool)
    ensures conj_idemp(p)
{
}

pub proof fn verify_conj_complement(p: bool)
    ensures conj_complement(p)
{
}

// ----------------------------------------------------------------------------
// Conjunction Introduction and Elimination
// ----------------------------------------------------------------------------

/// Introduction: from p and q, derive p && q
pub proof fn conj_intro(p: bool, q: bool)
    requires p, q
    ensures p && q
{
}

/// Left elimination: from p && q, derive p
pub proof fn conj_elim_left(p: bool, q: bool)
    requires p && q
    ensures p
{
}

/// Right elimination: from p && q, derive q
pub proof fn conj_elim_right(p: bool, q: bool)
    requires p && q
    ensures q
{
}

/// Split: p && q implies p and q separately
pub proof fn conj_split(p: bool, q: bool)
    requires p && q
    ensures p, q
{
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_basic_conjunction()
{
    assert(prop_conj(true, true));
    assert(!prop_conj(true, false));
    assert(!prop_conj(false, true));
    assert(!prop_conj(false, false));

    assert(prop_conj3(true, true, true));
    assert(!prop_conj3(true, true, false));
}

pub proof fn example_conjunction_laws()
{
    // Verify laws for all combinations
    verify_conj_comm(true, false);
    assert(conj_comm(true, false));

    verify_conj_assoc(true, false, true);
    assert(conj_assoc(true, false, true));

    verify_conj_identity(true);
    verify_conj_identity(false);
    assert(conj_identity(true));
    assert(conj_identity(false));

    verify_conj_annihil(true);
    assert(conj_annihil(true));

    verify_conj_idemp(true);
    assert(conj_idemp(true));

    verify_conj_complement(true);
    assert(conj_complement(true));
}

pub proof fn example_numerical_conjunctions()
{
    // Range checking
    assert(in_range(5, 0, 10));
    assert(!in_range(10, 0, 10));

    // Positive even/odd
    assert(positive_even(4));
    assert(!positive_even(3));
    assert(positive_odd(5));
    assert(!positive_odd(4));

    // Triangle inequality
    assert(triangle_sides(3, 4, 5));
    assert(!triangle_sides(1, 1, 10));
}

pub proof fn example_introduction_elimination()
{
    // Introduction
    conj_intro(true, true);

    // Elimination
    conj_elim_left(true, true);
    conj_elim_right(true, true);

    // Split
    conj_split(true, true);
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_prop_conjunction_verify()
{
    example_basic_conjunction();
    example_conjunction_laws();
    example_numerical_conjunctions();
    example_introduction_elimination();

    // Verify all laws
    verify_conj_comm(true, true);
    verify_conj_assoc(true, true, true);
    verify_conj_identity(true);
    verify_conj_annihil(false);
    verify_conj_idemp(true);
    verify_conj_complement(false);
}

pub fn main() {
    proof {
        qc_prop_conjunction_verify();
    }
}

} // verus!

use vstd::prelude::*;

verus! {

// ============================================================================
// QC: Disjunction Properties (QuickChick Properties)
// Properties using || for alternative conditions
// ============================================================================

// ----------------------------------------------------------------------------
// Disjunction Property Type
// ----------------------------------------------------------------------------

/// Basic disjunction of two properties
pub open spec fn prop_disj(p: bool, q: bool) -> bool {
    p || q
}

/// Triple disjunction
pub open spec fn prop_disj3(p: bool, q: bool, r: bool) -> bool {
    p || q || r
}

/// Quadruple disjunction
pub open spec fn prop_disj4(p: bool, q: bool, r: bool, s: bool) -> bool {
    p || q || r || s
}

/// N-ary disjunction for sequences of booleans
pub open spec fn prop_disj_any(props: Seq<bool>) -> bool
    decreases props.len()
{
    if props.len() == 0 {
        false
    } else {
        props[0] || prop_disj_any(props.skip(1))
    }
}

// ----------------------------------------------------------------------------
// Disjunction Laws
// ----------------------------------------------------------------------------

/// Commutativity: p || q == q || p
pub open spec fn disj_comm(p: bool, q: bool) -> bool {
    (p || q) == (q || p)
}

/// Associativity: (p || q) || r == p || (q || r)
pub open spec fn disj_assoc(p: bool, q: bool, r: bool) -> bool {
    ((p || q) || r) == (p || (q || r))
}

/// Identity: p || false == p
pub open spec fn disj_identity(p: bool) -> bool {
    (p || false) == p
}

/// Annihilation: p || true == true
pub open spec fn disj_annihil(p: bool) -> bool {
    (p || true) == true
}

/// Idempotence: p || p == p
pub open spec fn disj_idemp(p: bool) -> bool {
    (p || p) == p
}

/// Complement: p || !p == true
pub open spec fn disj_complement(p: bool) -> bool {
    (p || !p) == true
}

// ----------------------------------------------------------------------------
// De Morgan's Laws
// ----------------------------------------------------------------------------

/// Not (p && q) == !p || !q
pub open spec fn de_morgan_and(p: bool, q: bool) -> bool {
    !(p && q) == (!p || !q)
}

/// Not (p || q) == !p && !q
pub open spec fn de_morgan_or(p: bool, q: bool) -> bool {
    !(p || q) == (!p && !q)
}

// ----------------------------------------------------------------------------
// Distributivity
// ----------------------------------------------------------------------------

/// Or distributes over and: p || (q && r) == (p || q) && (p || r)
pub open spec fn disj_over_conj(p: bool, q: bool, r: bool) -> bool {
    (p || (q && r)) == ((p || q) && (p || r))
}

/// And distributes over or: p && (q || r) == (p && q) || (p && r)
pub open spec fn conj_over_disj(p: bool, q: bool, r: bool) -> bool {
    (p && (q || r)) == ((p && q) || (p && r))
}

// ----------------------------------------------------------------------------
// Disjunction with Boolean Functions
// ----------------------------------------------------------------------------

/// Apply disjunction to predicate results
pub open spec fn disj_pred_results(p1: bool, p2: bool) -> bool {
    p1 || p2
}

/// Check if either predicate holds for a value
pub open spec fn either_holds(x: nat, p: spec_fn(nat) -> bool, q: spec_fn(nat) -> bool) -> bool {
    p(x) || q(x)
}

// ----------------------------------------------------------------------------
// Numerical Disjunction Properties
// ----------------------------------------------------------------------------

/// Property: x is at boundary (0 or max)
pub open spec fn at_boundary(x: nat, max: nat) -> bool {
    x == 0 || x == max
}

/// Property: x is even or divisible by 3
pub open spec fn even_or_div3(x: nat) -> bool {
    x % 2 == 0 || x % 3 == 0
}

/// Property: x is small (< 10) or large (> 100)
pub open spec fn small_or_large(x: nat) -> bool {
    x < 10 || x > 100
}

/// Property: comparison trichotomy
pub open spec fn trichotomy(x: nat, y: nat) -> bool {
    x < y || x == y || x > y
}

/// Property: parity (every number is even or odd)
pub open spec fn parity(x: nat) -> bool {
    x % 2 == 0 || x % 2 == 1
}

// ----------------------------------------------------------------------------
// Sequence Disjunction Properties
// ----------------------------------------------------------------------------

/// Some element is zero
pub open spec fn some_zero(s: Seq<int>) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == 0
}

/// Some element is positive
pub open spec fn some_positive(s: Seq<int>) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] > 0
}

/// Sequence is empty or has positive length
pub open spec fn empty_or_nonempty<T>(s: Seq<T>) -> bool {
    s.len() == 0 || s.len() > 0
}

// ----------------------------------------------------------------------------
// Verification Proofs
// ----------------------------------------------------------------------------

pub proof fn verify_disj_comm(p: bool, q: bool)
    ensures disj_comm(p, q)
{
}

pub proof fn verify_disj_assoc(p: bool, q: bool, r: bool)
    ensures disj_assoc(p, q, r)
{
}

pub proof fn verify_disj_identity(p: bool)
    ensures disj_identity(p)
{
}

pub proof fn verify_disj_annihil(p: bool)
    ensures disj_annihil(p)
{
}

pub proof fn verify_disj_idemp(p: bool)
    ensures disj_idemp(p)
{
}

pub proof fn verify_disj_complement(p: bool)
    ensures disj_complement(p)
{
}

pub proof fn verify_de_morgan_and(p: bool, q: bool)
    ensures de_morgan_and(p, q)
{
}

pub proof fn verify_de_morgan_or(p: bool, q: bool)
    ensures de_morgan_or(p, q)
{
}

pub proof fn verify_disj_over_conj(p: bool, q: bool, r: bool)
    ensures disj_over_conj(p, q, r)
{
}

pub proof fn verify_conj_over_disj(p: bool, q: bool, r: bool)
    ensures conj_over_disj(p, q, r)
{
}

pub proof fn verify_trichotomy(x: nat, y: nat)
    ensures trichotomy(x, y)
{
}

pub proof fn verify_parity(x: nat)
    ensures parity(x)
{
}

// ----------------------------------------------------------------------------
// Disjunction Introduction and Elimination
// ----------------------------------------------------------------------------

/// Left introduction: from p, derive p || q
pub proof fn disj_intro_left(p: bool, q: bool)
    requires p
    ensures p || q
{
}

/// Right introduction: from q, derive p || q
pub proof fn disj_intro_right(p: bool, q: bool)
    requires q
    ensures p || q
{
}

/// Elimination (case analysis)
pub proof fn disj_elim(p: bool, q: bool, r: bool)
    requires p || q, p ==> r, q ==> r
    ensures r
{
}

/// Disjunctive syllogism
pub proof fn disj_syllogism_left(p: bool, q: bool)
    requires p || q, !p
    ensures q
{
}

pub proof fn disj_syllogism_right(p: bool, q: bool)
    requires p || q, !q
    ensures p
{
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_basic_disjunction()
{
    assert(prop_disj(true, true));
    assert(prop_disj(true, false));
    assert(prop_disj(false, true));
    assert(!prop_disj(false, false));

    assert(prop_disj3(false, false, true));
    assert(!prop_disj3(false, false, false));
}

pub proof fn example_disjunction_laws()
{
    // Verify laws
    verify_disj_comm(true, false);
    assert(disj_comm(true, false));

    verify_disj_assoc(true, false, true);
    assert(disj_assoc(true, false, true));

    verify_disj_identity(true);
    assert(disj_identity(true));

    verify_disj_annihil(false);
    assert(disj_annihil(false));

    verify_disj_complement(true);
    assert(disj_complement(true));
}

pub proof fn example_de_morgan()
{
    verify_de_morgan_and(true, false);
    assert(de_morgan_and(true, false));

    verify_de_morgan_or(true, false);
    assert(de_morgan_or(true, false));
}

pub proof fn example_numerical_disjunctions()
{
    // Trichotomy
    assert(trichotomy(3, 5));
    assert(trichotomy(5, 5));
    assert(trichotomy(7, 5));

    // Parity
    assert(parity(0));
    assert(parity(1));
    assert(parity(42));

    // Boundaries
    assert(at_boundary(0, 100));
    assert(at_boundary(100, 100));
    assert(!at_boundary(50, 100));
}

pub proof fn example_case_analysis()
{
    // Using disjunction elimination
    let p = true;
    let q = false;
    let r = true;
    disj_elim(p, q, r);
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_prop_disjunction_verify()
{
    example_basic_disjunction();
    example_disjunction_laws();
    example_de_morgan();
    example_numerical_disjunctions();
    example_case_analysis();

    // Verify all laws
    verify_disj_comm(true, true);
    verify_disj_assoc(true, true, true);
    verify_trichotomy(10, 20);
    verify_parity(100);
}

pub fn main() {
    proof {
        qc_prop_disjunction_verify();
    }
}

} // verus!

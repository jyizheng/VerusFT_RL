use vstd::prelude::*;

verus! {

// ============================================================================
// QC: Negation Properties (QuickChick Properties)
// Properties using ! for negation and contradiction
// ============================================================================

// ----------------------------------------------------------------------------
// Negation Property Type
// ----------------------------------------------------------------------------

/// Basic negation of a property
pub open spec fn prop_neg(p: bool) -> bool {
    !p
}

/// Double negation
pub open spec fn prop_neg_neg(p: bool) -> bool {
    !!p
}

/// Negation of conjunction
pub open spec fn prop_neg_conj(p: bool, q: bool) -> bool {
    !(p && q)
}

/// Negation of disjunction
pub open spec fn prop_neg_disj(p: bool, q: bool) -> bool {
    !(p || q)
}

// ----------------------------------------------------------------------------
// Negation Laws
// ----------------------------------------------------------------------------

/// Double negation elimination: !!p == p
pub open spec fn neg_elim(p: bool) -> bool {
    !!p == p
}

/// Contradiction: p && !p == false
pub open spec fn contradiction(p: bool) -> bool {
    (p && !p) == false
}

/// Excluded middle: p || !p == true
pub open spec fn excluded_middle(p: bool) -> bool {
    (p || !p) == true
}

/// Negation of true is false
pub open spec fn neg_true() -> bool {
    !true == false
}

/// Negation of false is true
pub open spec fn neg_false() -> bool {
    !false == true
}

// ----------------------------------------------------------------------------
// De Morgan's Laws via Negation
// ----------------------------------------------------------------------------

/// !(p && q) == !p || !q
pub open spec fn de_morgan_neg_and(p: bool, q: bool) -> bool {
    !(p && q) == (!p || !q)
}

/// !(p || q) == !p && !q
pub open spec fn de_morgan_neg_or(p: bool, q: bool) -> bool {
    !(p || q) == (!p && !q)
}

// ----------------------------------------------------------------------------
// Negation with Implication
// ----------------------------------------------------------------------------

/// Contraposition: (p ==> q) == (!q ==> !p)
pub open spec fn contraposition(p: bool, q: bool) -> bool {
    (p ==> q) == (!q ==> !p)
}

/// Negation of implication: !(p ==> q) == p && !q
pub open spec fn neg_implies(p: bool, q: bool) -> bool {
    !(p ==> q) == (p && !q)
}

/// Modus tollens: !q && (p ==> q) ==> !p
pub open spec fn modus_tollens(p: bool, q: bool) -> bool {
    (!q && (p ==> q)) ==> !p
}

// ----------------------------------------------------------------------------
// Negation with Boolean Functions
// ----------------------------------------------------------------------------

/// Negate predicate result
pub open spec fn neg_pred_result(p: bool) -> bool {
    !p
}

/// Check if predicate does not hold for a value
pub open spec fn does_not_hold(x: nat, p: spec_fn(nat) -> bool) -> bool {
    !p(x)
}

// ----------------------------------------------------------------------------
// Numerical Negation Properties
// ----------------------------------------------------------------------------

/// Property: x is not zero
pub open spec fn not_zero(x: nat) -> bool {
    x != 0
}

/// Property: x is not equal to y
pub open spec fn not_equal(x: nat, y: nat) -> bool {
    x != y
}

/// Property: x is not in range [lo, hi)
pub open spec fn not_in_range(x: nat, lo: nat, hi: nat) -> bool {
    !(x >= lo && x < hi)
}

/// Property: not (x < y and y < x) - asymmetry
pub open spec fn not_both_less(x: nat, y: nat) -> bool {
    !(x < y && y < x)
}

/// Property: not all equal in a triple
pub open spec fn not_all_equal(x: nat, y: nat, z: nat) -> bool {
    !(x == y && y == z)
}

// ----------------------------------------------------------------------------
// Proof by Contradiction
// ----------------------------------------------------------------------------

/// From false, anything follows (ex falso quodlibet)
pub open spec fn ex_falso(p: bool) -> bool {
    false ==> p
}

/// Proof by contradiction pattern
pub open spec fn proof_by_contradiction(p: bool) -> bool {
    (!p ==> false) ==> p
}

/// Reductio ad absurdum
pub open spec fn reductio(p: bool, q: bool) -> bool {
    ((p ==> q) && (p ==> !q)) ==> !p
}

// ----------------------------------------------------------------------------
// Verification Proofs
// ----------------------------------------------------------------------------

pub proof fn verify_neg_elim(p: bool)
    ensures neg_elim(p)
{
}

pub proof fn verify_contradiction(p: bool)
    ensures contradiction(p)
{
}

pub proof fn verify_excluded_middle(p: bool)
    ensures excluded_middle(p)
{
}

pub proof fn verify_neg_true()
    ensures neg_true()
{
}

pub proof fn verify_neg_false()
    ensures neg_false()
{
}

pub proof fn verify_de_morgan_neg_and(p: bool, q: bool)
    ensures de_morgan_neg_and(p, q)
{
}

pub proof fn verify_de_morgan_neg_or(p: bool, q: bool)
    ensures de_morgan_neg_or(p, q)
{
}

pub proof fn verify_contraposition(p: bool, q: bool)
    ensures contraposition(p, q)
{
}

pub proof fn verify_neg_implies(p: bool, q: bool)
    ensures neg_implies(p, q)
{
}

pub proof fn verify_modus_tollens(p: bool, q: bool)
    ensures modus_tollens(p, q)
{
}

pub proof fn verify_ex_falso(p: bool)
    ensures ex_falso(p)
{
}

pub proof fn verify_proof_by_contradiction(p: bool)
    ensures proof_by_contradiction(p)
{
}

pub proof fn verify_reductio(p: bool, q: bool)
    ensures reductio(p, q)
{
}

pub proof fn verify_not_both_less(x: nat, y: nat)
    ensures not_both_less(x, y)
{
}

// ----------------------------------------------------------------------------
// Negation Introduction and Elimination
// ----------------------------------------------------------------------------

/// Negation introduction: if p leads to contradiction, then !p
pub proof fn neg_intro(p: bool)
    requires p ==> false
    ensures !p
{
}

/// Negation elimination: from p and !p, derive anything
pub proof fn neg_elim_contradiction(p: bool, q: bool)
    requires p, !p
    ensures q
{
}

/// Double negation introduction
pub proof fn double_neg_intro(p: bool)
    requires p
    ensures !!p
{
}

/// Double negation elimination
pub proof fn double_neg_elim(p: bool)
    requires !!p
    ensures p
{
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_basic_negation()
{
    assert(prop_neg(false));
    assert(!prop_neg(true));
    assert(prop_neg_neg(true) == true);
    assert(prop_neg_neg(false) == false);
}

pub proof fn example_negation_laws()
{
    verify_neg_elim(true);
    assert(neg_elim(true));

    verify_contradiction(true);
    assert(contradiction(true));

    verify_excluded_middle(false);
    assert(excluded_middle(false));

    verify_neg_true();
    assert(neg_true());

    verify_neg_false();
    assert(neg_false());
}

pub proof fn example_de_morgan_negation()
{
    verify_de_morgan_neg_and(true, false);
    assert(de_morgan_neg_and(true, false));

    verify_de_morgan_neg_or(true, false);
    assert(de_morgan_neg_or(true, false));
}

pub proof fn example_implication_negation()
{
    verify_contraposition(true, false);
    assert(contraposition(true, false));

    verify_neg_implies(true, false);
    assert(neg_implies(true, false));

    verify_modus_tollens(true, false);
    assert(modus_tollens(true, false));
}

pub proof fn example_numerical_negation()
{
    assert(not_zero(5));
    assert(!not_zero(0));

    assert(not_equal(3, 5));
    assert(!not_equal(5, 5));

    assert(not_in_range(15, 0, 10));
    assert(!not_in_range(5, 0, 10));

    assert(not_both_less(3, 5));
    assert(not_both_less(5, 3));
    assert(not_both_less(5, 5));
}

pub proof fn example_contradiction_proofs()
{
    verify_ex_falso(true);
    assert(ex_falso(true));

    verify_proof_by_contradiction(true);
    assert(proof_by_contradiction(true));

    verify_reductio(true, false);
    assert(reductio(true, false));
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_prop_negation_verify()
{
    example_basic_negation();
    example_negation_laws();
    example_de_morgan_negation();
    example_implication_negation();
    example_numerical_negation();
    example_contradiction_proofs();

    // Verify all fundamental laws
    verify_neg_elim(true);
    verify_contradiction(false);
    verify_excluded_middle(true);
    verify_contraposition(true, true);
}

pub fn main() {
    proof {
        qc_prop_negation_verify();
    }
}

} // verus!

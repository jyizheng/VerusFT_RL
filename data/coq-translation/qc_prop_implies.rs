use vstd::prelude::*;

verus! {

// ============================================================================
// QC: Implication Properties (QuickChick Properties)
// Properties using the ==> operator for conditional testing
// ============================================================================

// ----------------------------------------------------------------------------
// Implication Property Type
// ----------------------------------------------------------------------------

/// Implication: if precondition then property must hold
pub open spec fn prop_implies(precondition: bool, property: bool) -> bool {
    precondition ==> property
}

/// Double implication (if and only if)
pub open spec fn prop_iff(p: bool, q: bool) -> bool {
    (p ==> q) && (q ==> p)
}

/// Chained implication: p ==> q ==> r
pub open spec fn prop_implies_chain(p: bool, q: bool, r: bool) -> bool {
    p ==> (q ==> r)
}

// ----------------------------------------------------------------------------
// Conditional Properties for Naturals
// ----------------------------------------------------------------------------

/// If x > 0 then x + 1 > 1
pub open spec fn prop_positive_add(x: nat) -> bool {
    (x > 0) ==> (x + 1 > 1)
}

/// If x >= y then x - y >= 0 (for nats, always true when valid)
pub open spec fn prop_sub_non_neg(x: nat, y: nat) -> bool {
    (x >= y) ==> (x - y >= 0)
}

/// If x > 0 and y > 0 then x + y > x
pub open spec fn prop_add_increases(x: nat, y: nat) -> bool {
    (x > 0 && y > 0) ==> (x + y > x)
}

/// If x == 0 then x * y == 0
pub open spec fn prop_mul_zero(x: nat, y: nat) -> bool {
    (x == 0) ==> (x * y == 0)
}

/// If x < y and y < z then x < z
pub open spec fn prop_less_trans(x: nat, y: nat, z: nat) -> bool {
    (x < y && y < z) ==> (x < z)
}

// ----------------------------------------------------------------------------
// Conditional Properties for Sequences
// ----------------------------------------------------------------------------

/// If sequence is non-empty, it has a first element
pub open spec fn prop_nonempty_first<T>(s: Seq<T>) -> bool {
    (s.len() > 0) ==> (s.len() >= 1)
}

/// If two sequences are equal, they have the same length
pub open spec fn prop_eq_same_len<T>(s1: Seq<T>, s2: Seq<T>) -> bool {
    (s1 =~= s2) ==> (s1.len() == s2.len())
}

/// If index is valid, access is safe
pub open spec fn prop_valid_index<T>(s: Seq<T>, i: int) -> bool {
    (0 <= i && i < s.len()) ==> (i >= 0)
}

// ----------------------------------------------------------------------------
// Logical Implication Laws
// ----------------------------------------------------------------------------

/// Implication reflexivity: p ==> p
pub open spec fn prop_implies_refl(p: bool) -> bool {
    p ==> p
}

/// Vacuous truth: false ==> anything
pub open spec fn prop_vacuous(p: bool) -> bool {
    false ==> p
}

/// Consequent true: anything ==> true
pub open spec fn prop_true_consequent(p: bool) -> bool {
    p ==> true
}

/// Contraposition: (p ==> q) <==> (!q ==> !p)
pub open spec fn prop_contraposition(p: bool, q: bool) -> bool {
    (p ==> q) <==> (!q ==> !p)
}

/// Modus ponens: p && (p ==> q) ==> q
pub open spec fn prop_modus_ponens(p: bool, q: bool) -> bool {
    (p && (p ==> q)) ==> q
}

/// Modus tollens: !q && (p ==> q) ==> !p
pub open spec fn prop_modus_tollens(p: bool, q: bool) -> bool {
    (!q && (p ==> q)) ==> !p
}

// ----------------------------------------------------------------------------
// Verification Proofs
// ----------------------------------------------------------------------------

pub proof fn verify_implies_refl(p: bool)
    ensures prop_implies_refl(p)
{
}

pub proof fn verify_vacuous(p: bool)
    ensures prop_vacuous(p)
{
}

pub proof fn verify_true_consequent(p: bool)
    ensures prop_true_consequent(p)
{
}

pub proof fn verify_contraposition(p: bool, q: bool)
    ensures prop_contraposition(p, q)
{
}

pub proof fn verify_modus_ponens(p: bool, q: bool)
    ensures prop_modus_ponens(p, q)
{
}

pub proof fn verify_modus_tollens(p: bool, q: bool)
    ensures prop_modus_tollens(p, q)
{
}

pub proof fn verify_positive_add(x: nat)
    ensures prop_positive_add(x)
{
}

pub proof fn verify_sub_non_neg(x: nat, y: nat)
    ensures prop_sub_non_neg(x, y)
{
}

pub proof fn verify_add_increases(x: nat, y: nat)
    ensures prop_add_increases(x, y)
{
}

pub proof fn verify_mul_zero(x: nat, y: nat)
    ensures prop_mul_zero(x, y)
{
}

pub proof fn verify_less_trans(x: nat, y: nat, z: nat)
    ensures prop_less_trans(x, y, z)
{
}

// ----------------------------------------------------------------------------
// Hypothetical Syllogism
// ----------------------------------------------------------------------------

/// If (p ==> q) and (q ==> r) then (p ==> r)
pub proof fn hypothetical_syllogism(p: bool, q: bool, r: bool)
    requires p ==> q, q ==> r
    ensures p ==> r
{
}

/// Proof by cases using implication
pub proof fn proof_by_cases(p: bool, q: bool, r: bool)
    requires (p ==> r), (q ==> r)
    ensures (p || q) ==> r
{
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_basic_implication()
{
    // Reflexivity
    assert(prop_implies_refl(true));
    assert(prop_implies_refl(false));

    // Vacuous truth
    assert(prop_vacuous(true));
    assert(prop_vacuous(false));

    // True consequent
    assert(prop_true_consequent(true));
    assert(prop_true_consequent(false));
}

pub proof fn example_implication_laws()
{
    // Contraposition
    assert(prop_contraposition(true, true));
    assert(prop_contraposition(true, false));
    assert(prop_contraposition(false, true));
    assert(prop_contraposition(false, false));

    // Modus ponens
    assert(prop_modus_ponens(true, true));
    assert(prop_modus_ponens(false, true));

    // Modus tollens
    assert(prop_modus_tollens(true, false));
    assert(prop_modus_tollens(false, false));
}

pub proof fn example_conditional_nat()
{
    // Positive addition
    assert(prop_positive_add(0));
    assert(prop_positive_add(5));

    // Multiplication with zero
    assert(prop_mul_zero(0, 100));
    assert(prop_mul_zero(5, 0));

    // Transitivity
    assert(prop_less_trans(1, 2, 3));
    assert(prop_less_trans(0, 5, 10));
}

pub proof fn example_chained_implication()
{
    // p ==> (q ==> r) examples
    assert(prop_implies_chain(false, true, true));
    assert(prop_implies_chain(true, false, true));
    assert(prop_implies_chain(true, true, true));
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_prop_implies_verify()
{
    example_basic_implication();
    example_implication_laws();
    example_conditional_nat();
    example_chained_implication();

    // Verify laws
    verify_implies_refl(true);
    verify_vacuous(false);
    verify_contraposition(true, false);
    verify_modus_ponens(true, true);
    verify_positive_add(10);
    verify_less_trans(1, 5, 10);
}

pub fn main() {
    proof {
        qc_prop_implies_verify();
    }
}

} // verus!

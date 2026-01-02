use vstd::prelude::*;

verus! {

// ============================================================================
// QC: Boolean Properties (QuickChick Properties)
// Testable boolean properties for property-based testing
// ============================================================================

// ----------------------------------------------------------------------------
// Property Type (Boolean Propositions)
// ----------------------------------------------------------------------------

// A property is a spec function that returns bool
// In QuickChick, properties are testable propositions

/// A simple boolean property
pub open spec fn prop_bool(b: bool) -> bool {
    b
}

/// Property that always holds (True)
pub open spec fn prop_true() -> bool {
    true
}

/// Property that never holds (False)
pub open spec fn prop_false() -> bool {
    false
}

// ----------------------------------------------------------------------------
// Property Combinators
// ----------------------------------------------------------------------------

/// Combine two properties with AND
pub open spec fn prop_and(p: bool, q: bool) -> bool {
    p && q
}

/// Combine two properties with OR
pub open spec fn prop_or(p: bool, q: bool) -> bool {
    p || q
}

/// Negate a property
pub open spec fn prop_not(p: bool) -> bool {
    !p
}

/// Conditional property: if condition then property
pub open spec fn prop_when(condition: bool, property: bool) -> bool {
    condition ==> property
}

// ----------------------------------------------------------------------------
// Testable Functions for Naturals
// ----------------------------------------------------------------------------

/// Property: addition is commutative
pub open spec fn prop_add_comm(x: nat, y: nat) -> bool {
    x + y == y + x
}

/// Property: addition is associative
pub open spec fn prop_add_assoc(x: nat, y: nat, z: nat) -> bool {
    (x + y) + z == x + (y + z)
}

/// Property: zero is identity for addition
pub open spec fn prop_add_zero(x: nat) -> bool {
    x + 0 == x && 0 + x == x
}

/// Property: multiplication is commutative
pub open spec fn prop_mul_comm(x: nat, y: nat) -> bool {
    x * y == y * x
}

/// Property: zero annihilates multiplication
pub open spec fn prop_mul_zero(x: nat) -> bool {
    x * 0 == 0 && 0 * x == 0
}

// ----------------------------------------------------------------------------
// Testable Functions for Booleans
// ----------------------------------------------------------------------------

/// Property: && is commutative
pub open spec fn prop_bool_and_comm(a: bool, b: bool) -> bool {
    (a && b) == (b && a)
}

/// Property: || is commutative
pub open spec fn prop_bool_or_comm(a: bool, b: bool) -> bool {
    (a || b) == (b || a)
}

/// Property: De Morgan's law for AND
pub open spec fn prop_de_morgan_and(a: bool, b: bool) -> bool {
    !(a && b) == (!a || !b)
}

/// Property: De Morgan's law for OR
pub open spec fn prop_de_morgan_or(a: bool, b: bool) -> bool {
    !(a || b) == (!a && !b)
}

/// Property: double negation
pub open spec fn prop_double_neg(a: bool) -> bool {
    !!a == a
}

// ----------------------------------------------------------------------------
// Verification Proofs
// ----------------------------------------------------------------------------

pub proof fn verify_prop_true()
    ensures prop_true()
{
}

pub proof fn verify_prop_add_comm(x: nat, y: nat)
    ensures prop_add_comm(x, y)
{
}

pub proof fn verify_prop_add_assoc(x: nat, y: nat, z: nat)
    ensures prop_add_assoc(x, y, z)
{
}

pub proof fn verify_prop_add_zero(x: nat)
    ensures prop_add_zero(x)
{
}

pub proof fn verify_prop_mul_comm(x: nat, y: nat)
    ensures prop_mul_comm(x, y)
{
}

pub proof fn verify_prop_mul_zero(x: nat)
    ensures prop_mul_zero(x)
{
}

pub proof fn verify_prop_bool_and_comm(a: bool, b: bool)
    ensures prop_bool_and_comm(a, b)
{
}

pub proof fn verify_prop_de_morgan_and(a: bool, b: bool)
    ensures prop_de_morgan_and(a, b)
{
}

pub proof fn verify_prop_de_morgan_or(a: bool, b: bool)
    ensures prop_de_morgan_or(a, b)
{
}

pub proof fn verify_prop_double_neg(a: bool)
    ensures prop_double_neg(a)
{
}

// ----------------------------------------------------------------------------
// Property Composition Proofs
// ----------------------------------------------------------------------------

pub proof fn prop_and_both_true(p: bool, q: bool)
    requires p, q
    ensures prop_and(p, q)
{
}

pub proof fn prop_or_one_true(p: bool, q: bool)
    requires p || q
    ensures prop_or(p, q)
{
}

pub proof fn prop_when_trivial(p: bool)
    ensures prop_when(false, p)
{
}

pub proof fn prop_when_holds(p: bool)
    requires p
    ensures prop_when(true, p)
{
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_basic_properties()
{
    // Boolean properties
    assert(prop_true());
    assert(!prop_false());
    assert(prop_bool(true));
    assert(!prop_bool(false));
}

pub proof fn example_arithmetic_properties()
{
    // Verify specific instances
    assert(prop_add_comm(3, 5));
    assert(prop_add_assoc(1, 2, 3));
    assert(prop_add_zero(42));
    assert(prop_mul_comm(4, 7));
    assert(prop_mul_zero(5));
}

pub proof fn example_boolean_properties()
{
    // Boolean law properties
    assert(prop_bool_and_comm(true, false));
    assert(prop_bool_or_comm(true, false));
    assert(prop_de_morgan_and(true, true));
    assert(prop_de_morgan_or(false, false));
    assert(prop_double_neg(true));
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_prop_bool_verify()
{
    example_basic_properties();
    example_arithmetic_properties();
    example_boolean_properties();

    // Verify universal properties
    verify_prop_true();
    verify_prop_add_comm(10, 20);
    verify_prop_mul_comm(5, 6);
    verify_prop_de_morgan_and(true, false);
}

pub fn main() {
    proof {
        qc_prop_bool_verify();
    }
}

} // verus!

use vstd::prelude::*;

verus! {

// ============================================================================
// QC: Boolean Decidability with Reflect (QuickChick-style)
// Models decidable propositions for boolean values with reflection
// ============================================================================

// ----------------------------------------------------------------------------
// Boolean Reflection Core
// Connects boolean computation to logical propositions
// ----------------------------------------------------------------------------

/// Reflect: boolean value reflects a proposition
/// This is the core of decidability - a boolean that correctly mirrors a prop
pub open spec fn reflect(b: bool, p: bool) -> bool {
    b <==> p
}

/// Decidability result type
pub enum Dec {
    Yes,
    No,
}

/// Convert Dec to bool
pub open spec fn dec_to_bool(d: Dec) -> bool {
    match d {
        Dec::Yes => true,
        Dec::No => false,
    }
}

/// Convert bool to Dec
pub open spec fn bool_to_dec(b: bool) -> Dec {
    if b { Dec::Yes } else { Dec::No }
}

// ----------------------------------------------------------------------------
// Boolean Decidability Functions
// ----------------------------------------------------------------------------

/// Boolean identity is decidable
pub open spec fn dec_bool(b: bool) -> Dec {
    bool_to_dec(b)
}

/// Boolean negation is decidable
pub open spec fn dec_not_bool(b: bool) -> Dec {
    bool_to_dec(!b)
}

/// Boolean AND is decidable
pub open spec fn dec_and_bool(a: bool, b: bool) -> Dec {
    bool_to_dec(a && b)
}

/// Boolean OR is decidable
pub open spec fn dec_or_bool(a: bool, b: bool) -> Dec {
    bool_to_dec(a || b)
}

/// Boolean XOR is decidable
pub open spec fn dec_xor_bool(a: bool, b: bool) -> Dec {
    bool_to_dec(a != b)
}

/// Boolean implication is decidable
pub open spec fn dec_implies_bool(a: bool, b: bool) -> Dec {
    bool_to_dec(!a || b)
}

/// Boolean iff is decidable
pub open spec fn dec_iff_bool(a: bool, b: bool) -> Dec {
    bool_to_dec(a == b)
}

// ----------------------------------------------------------------------------
// Reflection Proofs
// ----------------------------------------------------------------------------

/// Reflect true: true reflects a true proposition
pub proof fn reflect_true(p: bool)
    requires p
    ensures reflect(true, p)
{
}

/// Reflect false: false reflects a false proposition
pub proof fn reflect_false(p: bool)
    requires !p
    ensures reflect(false, p)
{
}

/// Reflection is symmetric in its arguments
pub proof fn reflect_symmetric(b: bool, p: bool)
    ensures reflect(b, p) == reflect(p, b)
{
}

/// Reflect preserves conjunction
pub proof fn reflect_and(b1: bool, b2: bool, p1: bool, p2: bool)
    requires reflect(b1, p1), reflect(b2, p2)
    ensures reflect(b1 && b2, p1 && p2)
{
}

/// Reflect preserves disjunction
pub proof fn reflect_or(b1: bool, b2: bool, p1: bool, p2: bool)
    requires reflect(b1, p1), reflect(b2, p2)
    ensures reflect(b1 || b2, p1 || p2)
{
}

/// Reflect preserves negation
pub proof fn reflect_not(b: bool, p: bool)
    requires reflect(b, p)
    ensures reflect(!b, !p)
{
}

// ----------------------------------------------------------------------------
// Dec Soundness Proofs
// ----------------------------------------------------------------------------

/// dec_bool soundly reflects boolean value
pub proof fn dec_bool_sound(b: bool)
    ensures dec_to_bool(dec_bool(b)) == b
{
}

/// dec_not_bool soundly reflects negation
pub proof fn dec_not_bool_sound(b: bool)
    ensures dec_to_bool(dec_not_bool(b)) == !b
{
}

/// dec_and_bool soundly reflects conjunction
pub proof fn dec_and_bool_sound(a: bool, b: bool)
    ensures dec_to_bool(dec_and_bool(a, b)) == (a && b)
{
}

/// dec_or_bool soundly reflects disjunction
pub proof fn dec_or_bool_sound(a: bool, b: bool)
    ensures dec_to_bool(dec_or_bool(a, b)) == (a || b)
{
}

/// dec_implies_bool soundly reflects implication
pub proof fn dec_implies_bool_sound(a: bool, b: bool)
    ensures dec_to_bool(dec_implies_bool(a, b)) == (!a || b)
{
}

/// dec_iff_bool soundly reflects iff
pub proof fn dec_iff_bool_sound(a: bool, b: bool)
    ensures dec_to_bool(dec_iff_bool(a, b)) == (a == b)
{
}

// ----------------------------------------------------------------------------
// Dec Completeness Proofs
// ----------------------------------------------------------------------------

/// dec_to_bool and bool_to_dec are inverses
pub proof fn dec_bool_roundtrip(b: bool)
    ensures dec_to_bool(bool_to_dec(b)) == b
{
}

/// Decidability completeness: all bools are decidable
pub proof fn bool_is_decidable(b: bool)
    ensures exists|d: Dec| dec_to_bool(d) == b
{
    let d = bool_to_dec(b);
    assert(dec_to_bool(d) == b);
}

// ----------------------------------------------------------------------------
// Boolean Decidability Laws
// ----------------------------------------------------------------------------

/// Double negation elimination
pub proof fn dec_double_neg(b: bool)
    ensures dec_to_bool(dec_not_bool(dec_to_bool(dec_not_bool(b)))) == b
{
}

/// De Morgan's law for AND
pub proof fn dec_demorgan_and(a: bool, b: bool)
    ensures dec_to_bool(dec_not_bool(dec_to_bool(dec_and_bool(a, b)))) ==
            dec_to_bool(dec_or_bool(!a, !b))
{
}

/// De Morgan's law for OR
pub proof fn dec_demorgan_or(a: bool, b: bool)
    ensures dec_to_bool(dec_not_bool(dec_to_bool(dec_or_bool(a, b)))) ==
            dec_to_bool(dec_and_bool(!a, !b))
{
}

/// Implication is equivalent to OR with negation
pub proof fn dec_implies_or(a: bool, b: bool)
    ensures dec_to_bool(dec_implies_bool(a, b)) == dec_to_bool(dec_or_bool(!a, b))
{
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_dec_bool_basic()
{
    // true is decidable as Yes
    assert(dec_to_bool(dec_bool(true)));
    assert(!dec_to_bool(dec_bool(false)));

    // Negation works correctly
    assert(!dec_to_bool(dec_not_bool(true)));
    assert(dec_to_bool(dec_not_bool(false)));
}

pub proof fn example_dec_bool_and()
{
    assert(dec_to_bool(dec_and_bool(true, true)));
    assert(!dec_to_bool(dec_and_bool(true, false)));
    assert(!dec_to_bool(dec_and_bool(false, true)));
    assert(!dec_to_bool(dec_and_bool(false, false)));
}

pub proof fn example_dec_bool_or()
{
    assert(dec_to_bool(dec_or_bool(true, true)));
    assert(dec_to_bool(dec_or_bool(true, false)));
    assert(dec_to_bool(dec_or_bool(false, true)));
    assert(!dec_to_bool(dec_or_bool(false, false)));
}

pub proof fn example_dec_bool_implies()
{
    // false implies anything
    assert(dec_to_bool(dec_implies_bool(false, true)));
    assert(dec_to_bool(dec_implies_bool(false, false)));

    // true implies true
    assert(dec_to_bool(dec_implies_bool(true, true)));

    // true does not imply false
    assert(!dec_to_bool(dec_implies_bool(true, false)));
}

pub proof fn example_reflect()
{
    // Reflection examples
    reflect_true(true);
    assert(reflect(true, true));

    reflect_false(false);
    assert(reflect(false, false));

    // Compound reflections
    reflect_and(true, true, true, true);
    assert(reflect(true && true, true && true));
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_dec_bool_verify()
{
    example_dec_bool_basic();
    example_dec_bool_and();
    example_dec_bool_or();
    example_dec_bool_implies();
    example_reflect();

    // Verify laws
    dec_double_neg(true);
    dec_double_neg(false);
    dec_demorgan_and(true, false);
    dec_demorgan_or(true, false);
    dec_implies_or(true, false);

    // Verify roundtrip
    dec_bool_roundtrip(true);
    dec_bool_roundtrip(false);
}

pub fn main() {
    proof {
        qc_dec_bool_verify();
    }
}

} // verus!

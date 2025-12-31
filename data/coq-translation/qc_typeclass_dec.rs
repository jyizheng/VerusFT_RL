use vstd::prelude::*;

verus! {

// ============================================================================
// QC: Dec Typeclass (qc-current/Typeclasses)
// Decidable propositions
// ============================================================================

// A proposition is decidable if we can compute true or false
// Dec P wraps the proposition P with decidability evidence

// ----------------------------------------------------------------------------
// Decidability Representation
// ----------------------------------------------------------------------------

pub enum Decidable {
    Yes,  // Proposition holds
    No,   // Proposition does not hold
}

// Convert decidable to bool
pub open spec fn dec_to_bool(d: Decidable) -> bool {
    match d {
        Decidable::Yes => true,
        Decidable::No => false,
    }
}

// Convert bool to decidable
pub open spec fn bool_to_dec(b: bool) -> Decidable {
    if b { Decidable::Yes } else { Decidable::No }
}

// ----------------------------------------------------------------------------
// Dec for Basic Propositions
// ----------------------------------------------------------------------------

// Equality is decidable
pub open spec fn dec_eq_nat(a: nat, b: nat) -> Decidable {
    bool_to_dec(a == b)
}

pub open spec fn dec_eq_bool(a: bool, b: bool) -> Decidable {
    bool_to_dec(a == b)
}

// Ordering is decidable
pub open spec fn dec_lt_nat(a: nat, b: nat) -> Decidable {
    bool_to_dec(a < b)
}

pub open spec fn dec_le_nat(a: nat, b: nat) -> Decidable {
    bool_to_dec(a <= b)
}

// ----------------------------------------------------------------------------
// Dec Combinators
// ----------------------------------------------------------------------------

// Decidable conjunction
pub open spec fn dec_and(d1: Decidable, d2: Decidable) -> Decidable {
    match (d1, d2) {
        (Decidable::Yes, Decidable::Yes) => Decidable::Yes,
        _ => Decidable::No,
    }
}

// Decidable disjunction
pub open spec fn dec_or(d1: Decidable, d2: Decidable) -> Decidable {
    match (d1, d2) {
        (Decidable::No, Decidable::No) => Decidable::No,
        _ => Decidable::Yes,
    }
}

// Decidable negation
pub open spec fn dec_not(d: Decidable) -> Decidable {
    match d {
        Decidable::Yes => Decidable::No,
        Decidable::No => Decidable::Yes,
    }
}

// Decidable implication
pub open spec fn dec_implies(d1: Decidable, d2: Decidable) -> Decidable {
    dec_or(dec_not(d1), d2)
}

// Decidable iff
pub open spec fn dec_iff(d1: Decidable, d2: Decidable) -> Decidable {
    dec_and(dec_implies(d1, d2), dec_implies(d2, d1))
}

// ----------------------------------------------------------------------------
// Boolean Reflection
// ----------------------------------------------------------------------------

// Reflect: connect boolean computation to proposition
pub open spec fn reflect(b: bool, p: bool) -> bool {
    b <==> p
}

pub proof fn reflect_true(p: bool)
    requires p
    ensures reflect(true, p)
{
}

pub proof fn reflect_false(p: bool)
    requires !p
    ensures reflect(false, p)
{
}

// ----------------------------------------------------------------------------
// Dec Properties
// ----------------------------------------------------------------------------

pub proof fn dec_and_sound(d1: Decidable, d2: Decidable)
    ensures dec_to_bool(dec_and(d1, d2)) == (dec_to_bool(d1) && dec_to_bool(d2))
{
}

pub proof fn dec_or_sound(d1: Decidable, d2: Decidable)
    ensures dec_to_bool(dec_or(d1, d2)) == (dec_to_bool(d1) || dec_to_bool(d2))
{
}

pub proof fn dec_not_sound(d: Decidable)
    ensures dec_to_bool(dec_not(d)) == !dec_to_bool(d)
{
}

pub proof fn dec_roundtrip(b: bool)
    ensures dec_to_bool(bool_to_dec(b)) == b
{
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_dec_eq()
{
    assert(dec_to_bool(dec_eq_nat(5, 5)));
    assert(!dec_to_bool(dec_eq_nat(5, 7)));
}

pub proof fn example_dec_combinators()
{
    let d1 = dec_eq_nat(5, 5);  // Yes
    let d2 = dec_lt_nat(3, 7);  // Yes
    let d3 = dec_lt_nat(7, 3);  // No

    assert(dec_to_bool(dec_and(d1, d2)));
    assert(!dec_to_bool(dec_and(d1, d3)));
    assert(dec_to_bool(dec_or(d1, d3)));
    assert(dec_to_bool(dec_implies(d3, d1)));
}

pub proof fn typeclass_dec_verify()
{
    example_dec_eq();
    example_dec_combinators();
    dec_roundtrip(true);
    dec_roundtrip(false);
}

pub fn main() {
    proof { typeclass_dec_verify(); }
}

} // verus!

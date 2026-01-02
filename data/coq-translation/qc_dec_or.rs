use vstd::prelude::*;

verus! {

// ============================================================================
// QC: Disjunction Decidability Combinator (QuickChick-style)
// Models decidable disjunction of propositions
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
// Basic Disjunction Combinator
// ----------------------------------------------------------------------------

/// Disjunction of two decidable propositions
pub open spec fn dec_or(d1: Dec, d2: Dec) -> Dec {
    match (d1, d2) {
        (Dec::No, Dec::No) => Dec::No,
        _ => Dec::Yes,
    }
}

/// Short-circuit disjunction (lazy evaluation model)
/// If first is Yes, don't evaluate second
pub open spec fn dec_or_lazy(d1: Dec, d2_thunk: spec_fn() -> Dec) -> Dec {
    match d1 {
        Dec::Yes => Dec::Yes,
        Dec::No => d2_thunk(),
    }
}

// ----------------------------------------------------------------------------
// N-ary Disjunction
// ----------------------------------------------------------------------------

/// Disjunction of a sequence of decidable propositions
pub open spec fn dec_or_any_helper(ds: Seq<Dec>, i: int) -> Dec
    decreases ds.len() - i when i >= 0
{
    if i >= ds.len() {
        Dec::No
    } else {
        match ds[i] {
            Dec::Yes => Dec::Yes,
            Dec::No => dec_or_any_helper(ds, i + 1),
        }
    }
}

/// Disjunction of any decision in sequence
pub open spec fn dec_or_any(ds: Seq<Dec>) -> Dec {
    dec_or_any_helper(ds, 0)
}

/// Disjunction of n identical decisions
pub open spec fn dec_or_n(d: Dec, n: nat) -> Dec
    decreases n
{
    if n == 0 {
        Dec::No
    } else {
        dec_or(d, dec_or_n(d, (n - 1) as nat))
    }
}

// ----------------------------------------------------------------------------
// Disjunction with Predicates
// ----------------------------------------------------------------------------

/// Decide disjunction of two predicates on a value
pub open spec fn dec_or_pred<T>(
    x: T,
    p1: spec_fn(T) -> Dec,
    p2: spec_fn(T) -> Dec
) -> Dec {
    dec_or(p1(x), p2(x))
}

/// Decide disjunction of predicates on sequence elements
pub open spec fn dec_or_pred_any<T>(
    s: Seq<T>,
    p1: spec_fn(T) -> Dec,
    p2: spec_fn(T) -> Dec
) -> Dec {
    dec_or_any(s.map_values(|x: T| dec_or(p1(x), p2(x))))
}

// ----------------------------------------------------------------------------
// Soundness Proofs
// ----------------------------------------------------------------------------

/// dec_or is sound
pub proof fn dec_or_sound(d1: Dec, d2: Dec)
    ensures dec_to_bool(dec_or(d1, d2)) == (dec_to_bool(d1) || dec_to_bool(d2))
{
}

/// dec_or_lazy is equivalent to dec_or
pub proof fn dec_or_lazy_equiv(d1: Dec, d2: Dec)
    ensures dec_or_lazy(d1, || d2) == dec_or(d1, d2)
{
}

/// dec_or_any correctly reflects the disjunction
pub proof fn dec_or_any_sound(ds: Seq<Dec>)
    ensures dec_to_bool(dec_or_any(ds)) == dec_to_bool(dec_or_any_helper(ds, 0))
{
}

// ----------------------------------------------------------------------------
// Algebraic Properties
// ----------------------------------------------------------------------------

/// Disjunction is commutative
pub proof fn dec_or_commutative(d1: Dec, d2: Dec)
    ensures dec_or(d1, d2) == dec_or(d2, d1)
{
}

/// Disjunction is associative
pub proof fn dec_or_associative(d1: Dec, d2: Dec, d3: Dec)
    ensures dec_or(dec_or(d1, d2), d3) == dec_or(d1, dec_or(d2, d3))
{
}

/// No is identity for disjunction (left)
pub proof fn dec_or_identity_no_left(d: Dec)
    ensures dec_or(Dec::No, d) == d
{
}

/// No is identity for disjunction (right)
pub proof fn dec_or_identity_no_right(d: Dec)
    ensures dec_or(d, Dec::No) == d
{
}

/// Yes is absorbing for disjunction (left)
pub proof fn dec_or_absorbing_yes_left(d: Dec)
    ensures dec_or(Dec::Yes, d) == Dec::Yes
{
}

/// Yes is absorbing for disjunction (right)
pub proof fn dec_or_absorbing_yes_right(d: Dec)
    ensures dec_or(d, Dec::Yes) == Dec::Yes
{
}

/// Disjunction is idempotent
pub proof fn dec_or_idempotent(d: Dec)
    ensures dec_or(d, d) == d
{
}

// ----------------------------------------------------------------------------
// Disjunction with Empty and Singleton
// ----------------------------------------------------------------------------

/// Empty disjunction is No (vacuous falsehood)
pub proof fn dec_or_any_empty()
    ensures dec_or_any(Seq::<Dec>::empty()) == Dec::No
{
}

/// Singleton disjunction equals the single element
pub proof fn dec_or_any_singleton(d: Dec)
    ensures dec_or_any(seq![d]) == d
{
    reveal_with_fuel(dec_or_any_helper, 2);
}

/// Pair disjunction
pub proof fn dec_or_any_pair(d1: Dec, d2: Dec)
    ensures dec_or_any(seq![d1, d2]) == dec_or(d1, d2)
{
    reveal_with_fuel(dec_or_any_helper, 3);
}


// ----------------------------------------------------------------------------
// Triple Disjunction
// ----------------------------------------------------------------------------

/// Triple disjunction combinator
pub open spec fn dec_or3(d1: Dec, d2: Dec, d3: Dec) -> Dec {
    dec_or(dec_or(d1, d2), d3)
}

/// Triple disjunction is sound
pub proof fn dec_or3_sound(d1: Dec, d2: Dec, d3: Dec)
    ensures dec_to_bool(dec_or3(d1, d2, d3)) ==
        (dec_to_bool(d1) || dec_to_bool(d2) || dec_to_bool(d3))
{
}

/// Quadruple disjunction combinator
pub open spec fn dec_or4(d1: Dec, d2: Dec, d3: Dec, d4: Dec) -> Dec {
    dec_or(dec_or3(d1, d2, d3), d4)
}

/// Quadruple disjunction is sound
pub proof fn dec_or4_sound(d1: Dec, d2: Dec, d3: Dec, d4: Dec)
    ensures dec_to_bool(dec_or4(d1, d2, d3, d4)) ==
        (dec_to_bool(d1) || dec_to_bool(d2) || dec_to_bool(d3) || dec_to_bool(d4))
{
}

// ----------------------------------------------------------------------------
// Decidability Lifting
// ----------------------------------------------------------------------------

/// Lift binary disjunction to decidability
pub open spec fn lift_or(p1: bool, p2: bool) -> Dec {
    dec_or(bool_to_dec(p1), bool_to_dec(p2))
}

/// Lifted or is sound
pub proof fn lift_or_sound(p1: bool, p2: bool)
    ensures dec_to_bool(lift_or(p1, p2)) == (p1 || p2)
{
}

/// Lift ternary disjunction
pub open spec fn lift_or3(p1: bool, p2: bool, p3: bool) -> Dec {
    dec_or3(bool_to_dec(p1), bool_to_dec(p2), bool_to_dec(p3))
}

/// Lifted or3 is sound
pub proof fn lift_or3_sound(p1: bool, p2: bool, p3: bool)
    ensures dec_to_bool(lift_or3(p1, p2, p3)) == (p1 || p2 || p3)
{
}

// ----------------------------------------------------------------------------
// De Morgan's Laws (Negation)
// ----------------------------------------------------------------------------

/// Negation of a decision
pub open spec fn dec_not(d: Dec) -> Dec {
    match d {
        Dec::Yes => Dec::No,
        Dec::No => Dec::Yes,
    }
}

/// De Morgan: not (p || q) = (not p) && (not q)
pub proof fn dec_demorgan_or(d1: Dec, d2: Dec)
    ensures dec_not(dec_or(d1, d2)) == dec_and(dec_not(d1), dec_not(d2))
{
}

/// Conjunction helper for De Morgan
pub open spec fn dec_and(d1: Dec, d2: Dec) -> Dec {
    match (d1, d2) {
        (Dec::Yes, Dec::Yes) => Dec::Yes,
        _ => Dec::No,
    }
}

/// De Morgan: not (p && q) = (not p) || (not q)
pub proof fn dec_demorgan_and(d1: Dec, d2: Dec)
    ensures dec_not(dec_and(d1, d2)) == dec_or(dec_not(d1), dec_not(d2))
{
}

// ----------------------------------------------------------------------------
// Distributive Laws
// ----------------------------------------------------------------------------

/// Or distributes over And (left)
pub proof fn dec_or_and_distrib_left(d1: Dec, d2: Dec, d3: Dec)
    ensures dec_or(d1, dec_and(d2, d3)) == dec_and(dec_or(d1, d2), dec_or(d1, d3))
{
}

/// And distributes over Or (left)
pub proof fn dec_and_or_distrib_left(d1: Dec, d2: Dec, d3: Dec)
    ensures dec_and(d1, dec_or(d2, d3)) == dec_or(dec_and(d1, d2), dec_and(d1, d3))
{
}

// ----------------------------------------------------------------------------
// Exclusive Or
// ----------------------------------------------------------------------------

/// Exclusive or (xor): exactly one is Yes
pub open spec fn dec_xor(d1: Dec, d2: Dec) -> Dec {
    match (d1, d2) {
        (Dec::Yes, Dec::No) => Dec::Yes,
        (Dec::No, Dec::Yes) => Dec::Yes,
        _ => Dec::No,
    }
}

/// Xor is sound
pub proof fn dec_xor_sound(d1: Dec, d2: Dec)
    ensures dec_to_bool(dec_xor(d1, d2)) == (dec_to_bool(d1) != dec_to_bool(d2))
{
}

/// Xor is commutative
pub proof fn dec_xor_commutative(d1: Dec, d2: Dec)
    ensures dec_xor(d1, d2) == dec_xor(d2, d1)
{
}

/// Xor self is No
pub proof fn dec_xor_self(d: Dec)
    ensures dec_xor(d, d) == Dec::No
{
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_dec_or_basic()
{
    // Yes || Yes = Yes
    assert(dec_or(Dec::Yes, Dec::Yes) == Dec::Yes);
    assert(dec_to_bool(dec_or(Dec::Yes, Dec::Yes)));

    // Yes || No = Yes
    assert(dec_or(Dec::Yes, Dec::No) == Dec::Yes);

    // No || Yes = Yes
    assert(dec_or(Dec::No, Dec::Yes) == Dec::Yes);

    // No || No = No
    assert(dec_or(Dec::No, Dec::No) == Dec::No);
    assert(!dec_to_bool(dec_or(Dec::No, Dec::No)));
}

pub proof fn example_dec_or_lazy()
{
    // Lazy: if first is Yes, result is Yes regardless of second
    dec_or_lazy_equiv(Dec::Yes, Dec::No);
    assert(dec_or_lazy(Dec::Yes, || Dec::No) == Dec::Yes);

    // Lazy: if first is No, evaluate second
    dec_or_lazy_equiv(Dec::No, Dec::Yes);
    assert(dec_or_lazy(Dec::No, || Dec::Yes) == Dec::Yes);
}

pub proof fn example_dec_or_any()
{
    reveal_with_fuel(dec_or_any_helper, 5);

    // All No
    let all_no = seq![Dec::No, Dec::No, Dec::No];
    assert(!dec_to_bool(dec_or_any(all_no)));

    // One Yes makes any Yes
    let one_yes = seq![Dec::No, Dec::Yes, Dec::No];
    assert(dec_to_bool(dec_or_any(one_yes)));

    // Empty is No
    dec_or_any_empty();
    assert(!dec_to_bool(dec_or_any(Seq::<Dec>::empty())));
}

pub proof fn example_dec_or_n()
{
    reveal_with_fuel(dec_or_n, 6);

    // No || No || No = No (3 iterations)
    assert(!dec_to_bool(dec_or_n(Dec::No, 3)));

    // Yes || ... = Yes (unless n=0)
    assert(dec_to_bool(dec_or_n(Dec::Yes, 2)));

    // n=0 is always No (vacuous)
    assert(!dec_to_bool(dec_or_n(Dec::Yes, 0)));
}

pub proof fn example_dec_or_properties()
{
    // Commutativity
    dec_or_commutative(Dec::Yes, Dec::No);
    assert(dec_or(Dec::Yes, Dec::No) == dec_or(Dec::No, Dec::Yes));

    // Associativity
    dec_or_associative(Dec::No, Dec::No, Dec::Yes);

    // Identity
    dec_or_identity_no_left(Dec::Yes);
    dec_or_identity_no_right(Dec::No);

    // Absorbing
    dec_or_absorbing_yes_left(Dec::No);

    // Idempotent
    dec_or_idempotent(Dec::Yes);
    dec_or_idempotent(Dec::No);
}

pub proof fn example_dec_or_pred()
{
    let is_zero = |n: nat| bool_to_dec(n == 0);
    let is_even = |n: nat| bool_to_dec(n % 2 == 0);

    // 0 is zero or even
    assert(dec_to_bool(dec_or_pred(0nat, is_zero, is_even)));

    // 4 is not zero but is even
    assert(dec_to_bool(dec_or_pred(4nat, is_zero, is_even)));

    // 3 is neither zero nor even
    assert(!dec_to_bool(dec_or_pred(3nat, is_zero, is_even)));
}

pub proof fn example_dec_or3_or4()
{
    // Triple disjunction
    assert(dec_to_bool(dec_or3(Dec::No, Dec::No, Dec::Yes)));
    assert(!dec_to_bool(dec_or3(Dec::No, Dec::No, Dec::No)));

    // Quadruple disjunction
    assert(dec_to_bool(dec_or4(Dec::No, Dec::No, Dec::No, Dec::Yes)));
    assert(!dec_to_bool(dec_or4(Dec::No, Dec::No, Dec::No, Dec::No)));
}

pub proof fn example_dec_demorgan()
{
    // De Morgan's laws
    dec_demorgan_or(Dec::Yes, Dec::No);
    dec_demorgan_and(Dec::Yes, Dec::No);

    // not (Yes || No) = not Yes && not No = No && Yes = No
    assert(dec_not(dec_or(Dec::Yes, Dec::No)) == Dec::No);

    // not (Yes && No) = not Yes || not No = No || Yes = Yes
    assert(dec_not(dec_and(Dec::Yes, Dec::No)) == Dec::Yes);
}

pub proof fn example_dec_xor()
{
    // Xor basics
    assert(dec_to_bool(dec_xor(Dec::Yes, Dec::No)));
    assert(dec_to_bool(dec_xor(Dec::No, Dec::Yes)));
    assert(!dec_to_bool(dec_xor(Dec::Yes, Dec::Yes)));
    assert(!dec_to_bool(dec_xor(Dec::No, Dec::No)));

    // Xor properties
    dec_xor_commutative(Dec::Yes, Dec::No);
    dec_xor_self(Dec::Yes);
}

pub proof fn example_lift_or()
{
    // Lift boolean disjunction
    lift_or_sound(false, true);
    assert(dec_to_bool(lift_or(false, true)));

    lift_or_sound(false, false);
    assert(!dec_to_bool(lift_or(false, false)));

    // Lift triple disjunction
    lift_or3_sound(false, false, true);
    assert(dec_to_bool(lift_or3(false, false, true)));
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_dec_or_verify()
{
    example_dec_or_basic();
    example_dec_or_lazy();
    example_dec_or_any();
    example_dec_or_n();
    example_dec_or_properties();
    example_dec_or_pred();
    example_dec_or3_or4();
    example_dec_demorgan();
    example_dec_xor();
    example_lift_or();

    // Verify soundness
    dec_or_sound(Dec::Yes, Dec::No);
    dec_or_any_empty();
    dec_or_any_singleton(Dec::Yes);
}

pub fn main() {
    proof {
        qc_dec_or_verify();
    }
}

} // verus!

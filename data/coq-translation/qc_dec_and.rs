use vstd::prelude::*;

verus! {

// ============================================================================
// QC: Conjunction Decidability Combinator (QuickChick-style)
// Models decidable conjunction of propositions
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
// Basic Conjunction Combinator
// ----------------------------------------------------------------------------

/// Conjunction of two decidable propositions
pub open spec fn dec_and(d1: Dec, d2: Dec) -> Dec {
    match (d1, d2) {
        (Dec::Yes, Dec::Yes) => Dec::Yes,
        _ => Dec::No,
    }
}

/// Short-circuit conjunction (lazy evaluation model)
/// If first is No, don't evaluate second
pub open spec fn dec_and_lazy(d1: Dec, d2_thunk: spec_fn() -> Dec) -> Dec {
    match d1 {
        Dec::No => Dec::No,
        Dec::Yes => d2_thunk(),
    }
}

// ----------------------------------------------------------------------------
// N-ary Conjunction
// ----------------------------------------------------------------------------

/// Conjunction of a sequence of decidable propositions
pub open spec fn dec_and_all_helper(ds: Seq<Dec>, i: int) -> Dec
    decreases ds.len() - i when i >= 0
{
    if i >= ds.len() {
        Dec::Yes
    } else {
        match ds[i] {
            Dec::No => Dec::No,
            Dec::Yes => dec_and_all_helper(ds, i + 1),
        }
    }
}

/// Conjunction of all decisions in sequence
pub open spec fn dec_and_all(ds: Seq<Dec>) -> Dec {
    dec_and_all_helper(ds, 0)
}

/// Conjunction of n identical decisions
pub open spec fn dec_and_n(d: Dec, n: nat) -> Dec
    decreases n
{
    if n == 0 {
        Dec::Yes
    } else {
        dec_and(d, dec_and_n(d, (n - 1) as nat))
    }
}

// ----------------------------------------------------------------------------
// Conjunction with Predicates
// ----------------------------------------------------------------------------

/// Decide conjunction of two predicates on a value
pub open spec fn dec_and_pred<T>(
    x: T,
    p1: spec_fn(T) -> Dec,
    p2: spec_fn(T) -> Dec
) -> Dec {
    dec_and(p1(x), p2(x))
}

/// Decide conjunction of predicates on sequence elements
pub open spec fn dec_and_pred_all<T>(
    s: Seq<T>,
    p1: spec_fn(T) -> Dec,
    p2: spec_fn(T) -> Dec
) -> Dec {
    dec_and_all(s.map_values(|x: T| dec_and(p1(x), p2(x))))
}

// ----------------------------------------------------------------------------
// Soundness Proofs
// ----------------------------------------------------------------------------

/// dec_and is sound
pub proof fn dec_and_sound(d1: Dec, d2: Dec)
    ensures dec_to_bool(dec_and(d1, d2)) == (dec_to_bool(d1) && dec_to_bool(d2))
{
}

/// dec_and_lazy is equivalent to dec_and
pub proof fn dec_and_lazy_equiv(d1: Dec, d2: Dec)
    ensures dec_and_lazy(d1, || d2) == dec_and(d1, d2)
{
}

/// dec_and_all correctly reflects the conjunction
pub proof fn dec_and_all_sound(ds: Seq<Dec>)
    ensures dec_to_bool(dec_and_all(ds)) == dec_to_bool(dec_and_all_helper(ds, 0))
{
}

// ----------------------------------------------------------------------------
// Algebraic Properties
// ----------------------------------------------------------------------------

/// Conjunction is commutative
pub proof fn dec_and_commutative(d1: Dec, d2: Dec)
    ensures dec_and(d1, d2) == dec_and(d2, d1)
{
}

/// Conjunction is associative
pub proof fn dec_and_associative(d1: Dec, d2: Dec, d3: Dec)
    ensures dec_and(dec_and(d1, d2), d3) == dec_and(d1, dec_and(d2, d3))
{
}

/// Yes is identity for conjunction (left)
pub proof fn dec_and_identity_yes_left(d: Dec)
    ensures dec_and(Dec::Yes, d) == d
{
}

/// Yes is identity for conjunction (right)
pub proof fn dec_and_identity_yes_right(d: Dec)
    ensures dec_and(d, Dec::Yes) == d
{
}

/// No is absorbing for conjunction (left)
pub proof fn dec_and_absorbing_no_left(d: Dec)
    ensures dec_and(Dec::No, d) == Dec::No
{
}

/// No is absorbing for conjunction (right)
pub proof fn dec_and_absorbing_no_right(d: Dec)
    ensures dec_and(d, Dec::No) == Dec::No
{
}

/// Conjunction is idempotent
pub proof fn dec_and_idempotent(d: Dec)
    ensures dec_and(d, d) == d
{
}

// ----------------------------------------------------------------------------
// Conjunction with Empty and Singleton
// ----------------------------------------------------------------------------

/// Empty conjunction is Yes (vacuous truth)
pub proof fn dec_and_all_empty()
    ensures dec_and_all(Seq::<Dec>::empty()) == Dec::Yes
{
}

/// Singleton conjunction equals the single element
pub proof fn dec_and_all_singleton(d: Dec)
    ensures dec_and_all(seq![d]) == d
{
    reveal_with_fuel(dec_and_all_helper, 2);
}

/// Pair conjunction
pub proof fn dec_and_all_pair(d1: Dec, d2: Dec)
    ensures dec_and_all(seq![d1, d2]) == dec_and(d1, d2)
{
    reveal_with_fuel(dec_and_all_helper, 3);
}


// ----------------------------------------------------------------------------
// Triple Conjunction
// ----------------------------------------------------------------------------

/// Triple conjunction combinator
pub open spec fn dec_and3(d1: Dec, d2: Dec, d3: Dec) -> Dec {
    dec_and(dec_and(d1, d2), d3)
}

/// Triple conjunction is sound
pub proof fn dec_and3_sound(d1: Dec, d2: Dec, d3: Dec)
    ensures dec_to_bool(dec_and3(d1, d2, d3)) ==
        (dec_to_bool(d1) && dec_to_bool(d2) && dec_to_bool(d3))
{
}

/// Quadruple conjunction combinator
pub open spec fn dec_and4(d1: Dec, d2: Dec, d3: Dec, d4: Dec) -> Dec {
    dec_and(dec_and3(d1, d2, d3), d4)
}

/// Quadruple conjunction is sound
pub proof fn dec_and4_sound(d1: Dec, d2: Dec, d3: Dec, d4: Dec)
    ensures dec_to_bool(dec_and4(d1, d2, d3, d4)) ==
        (dec_to_bool(d1) && dec_to_bool(d2) && dec_to_bool(d3) && dec_to_bool(d4))
{
}

// ----------------------------------------------------------------------------
// Decidability Lifting
// ----------------------------------------------------------------------------

/// Lift binary conjunction to decidability
pub open spec fn lift_and(p1: bool, p2: bool) -> Dec {
    dec_and(bool_to_dec(p1), bool_to_dec(p2))
}

/// Lifted and is sound
pub proof fn lift_and_sound(p1: bool, p2: bool)
    ensures dec_to_bool(lift_and(p1, p2)) == (p1 && p2)
{
}

/// Lift ternary conjunction
pub open spec fn lift_and3(p1: bool, p2: bool, p3: bool) -> Dec {
    dec_and3(bool_to_dec(p1), bool_to_dec(p2), bool_to_dec(p3))
}

/// Lifted and3 is sound
pub proof fn lift_and3_sound(p1: bool, p2: bool, p3: bool)
    ensures dec_to_bool(lift_and3(p1, p2, p3)) == (p1 && p2 && p3)
{
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_dec_and_basic()
{
    // Yes && Yes = Yes
    assert(dec_and(Dec::Yes, Dec::Yes) == Dec::Yes);
    assert(dec_to_bool(dec_and(Dec::Yes, Dec::Yes)));

    // Yes && No = No
    assert(dec_and(Dec::Yes, Dec::No) == Dec::No);
    assert(!dec_to_bool(dec_and(Dec::Yes, Dec::No)));

    // No && Yes = No
    assert(dec_and(Dec::No, Dec::Yes) == Dec::No);

    // No && No = No
    assert(dec_and(Dec::No, Dec::No) == Dec::No);
}

pub proof fn example_dec_and_lazy()
{
    // Lazy: if first is No, result is No regardless of second
    dec_and_lazy_equiv(Dec::No, Dec::Yes);
    assert(dec_and_lazy(Dec::No, || Dec::Yes) == Dec::No);

    // Lazy: if first is Yes, evaluate second
    dec_and_lazy_equiv(Dec::Yes, Dec::No);
    assert(dec_and_lazy(Dec::Yes, || Dec::No) == Dec::No);
}

pub proof fn example_dec_and_all()
{
    reveal_with_fuel(dec_and_all_helper, 5);

    // All Yes
    let all_yes = seq![Dec::Yes, Dec::Yes, Dec::Yes];
    assert(dec_to_bool(dec_and_all(all_yes)));

    // One No makes all No
    let one_no = seq![Dec::Yes, Dec::No, Dec::Yes];
    assert(!dec_to_bool(dec_and_all(one_no)));

    // Empty is Yes
    dec_and_all_empty();
    assert(dec_to_bool(dec_and_all(Seq::<Dec>::empty())));
}

pub proof fn example_dec_and_n()
{
    reveal_with_fuel(dec_and_n, 6);

    // Yes && Yes && Yes = Yes (3 iterations)
    assert(dec_to_bool(dec_and_n(Dec::Yes, 3)));

    // No && ... = No (unless n=0)
    assert(!dec_to_bool(dec_and_n(Dec::No, 2)));

    // n=0 is always Yes (vacuous)
    assert(dec_to_bool(dec_and_n(Dec::No, 0)));
}

pub proof fn example_dec_and_properties()
{
    // Commutativity
    dec_and_commutative(Dec::Yes, Dec::No);
    assert(dec_and(Dec::Yes, Dec::No) == dec_and(Dec::No, Dec::Yes));

    // Associativity
    dec_and_associative(Dec::Yes, Dec::Yes, Dec::No);

    // Identity
    dec_and_identity_yes_left(Dec::Yes);
    dec_and_identity_yes_right(Dec::No);

    // Absorbing
    dec_and_absorbing_no_left(Dec::Yes);

    // Idempotent
    dec_and_idempotent(Dec::Yes);
    dec_and_idempotent(Dec::No);
}

pub proof fn example_dec_and_pred()
{
    let is_positive = |n: nat| bool_to_dec(n > 0);
    let is_even = |n: nat| bool_to_dec(n % 2 == 0);

    // 4 is positive and even
    assert(dec_to_bool(dec_and_pred(4nat, is_positive, is_even)));

    // 3 is positive but not even
    assert(!dec_to_bool(dec_and_pred(3nat, is_positive, is_even)));

    // 0 is even but not positive
    assert(!dec_to_bool(dec_and_pred(0nat, is_positive, is_even)));
}

pub proof fn example_dec_and3_and4()
{
    // Triple conjunction
    assert(dec_to_bool(dec_and3(Dec::Yes, Dec::Yes, Dec::Yes)));
    assert(!dec_to_bool(dec_and3(Dec::Yes, Dec::No, Dec::Yes)));

    // Quadruple conjunction
    assert(dec_to_bool(dec_and4(Dec::Yes, Dec::Yes, Dec::Yes, Dec::Yes)));
    assert(!dec_to_bool(dec_and4(Dec::Yes, Dec::Yes, Dec::No, Dec::Yes)));
}

pub proof fn example_lift_and()
{
    // Lift boolean conjunction
    lift_and_sound(true, true);
    assert(dec_to_bool(lift_and(true, true)));

    lift_and_sound(true, false);
    assert(!dec_to_bool(lift_and(true, false)));

    // Lift triple conjunction
    lift_and3_sound(true, true, true);
    assert(dec_to_bool(lift_and3(true, true, true)));

    lift_and3_sound(true, false, true);
    assert(!dec_to_bool(lift_and3(true, false, true)));
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_dec_and_verify()
{
    example_dec_and_basic();
    example_dec_and_lazy();
    example_dec_and_all();
    example_dec_and_n();
    example_dec_and_properties();
    example_dec_and_pred();
    example_dec_and3_and4();
    example_lift_and();

    // Verify soundness
    dec_and_sound(Dec::Yes, Dec::No);
    dec_and_all_empty();
    dec_and_all_singleton(Dec::Yes);
}

pub fn main() {
    proof {
        qc_dec_and_verify();
    }
}

} // verus!

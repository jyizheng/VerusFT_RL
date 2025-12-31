use vstd::prelude::*;

verus! {

// ============================================================================
// QC: Equality Decidability (QuickChick-style)
// Models decidable equality for various types
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
// Equality Decidability for Basic Types
// ----------------------------------------------------------------------------

/// Boolean equality is decidable
pub open spec fn dec_eq_bool(a: bool, b: bool) -> Dec {
    bool_to_dec(a == b)
}

/// Natural number equality is decidable
pub open spec fn dec_eq_nat(a: nat, b: nat) -> Dec {
    bool_to_dec(a == b)
}

/// Integer equality is decidable
pub open spec fn dec_eq_int(a: int, b: int) -> Dec {
    bool_to_dec(a == b)
}

// ----------------------------------------------------------------------------
// Equality Decidability for Option Types
// ----------------------------------------------------------------------------

/// Option equality is decidable given decidable element equality
pub open spec fn dec_eq_option<T>(
    a: Option<T>,
    b: Option<T>,
    dec_eq_t: spec_fn(T, T) -> Dec
) -> Dec {
    match (a, b) {
        (Option::None, Option::None) => Dec::Yes,
        (Option::Some(x), Option::Some(y)) => dec_eq_t(x, y),
        _ => Dec::No,
    }
}

/// Option<nat> equality is decidable
pub open spec fn dec_eq_option_nat(a: Option<nat>, b: Option<nat>) -> Dec {
    dec_eq_option(a, b, |x: nat, y: nat| dec_eq_nat(x, y))
}

// ----------------------------------------------------------------------------
// Equality Decidability for Pairs
// ----------------------------------------------------------------------------

/// Pair equality is decidable given decidable component equality
pub open spec fn dec_eq_pair<A, B>(
    p1: (A, B),
    p2: (A, B),
    dec_eq_a: spec_fn(A, A) -> Dec,
    dec_eq_b: spec_fn(B, B) -> Dec
) -> Dec {
    match (dec_eq_a(p1.0, p2.0), dec_eq_b(p1.1, p2.1)) {
        (Dec::Yes, Dec::Yes) => Dec::Yes,
        _ => Dec::No,
    }
}

/// Pair<nat, nat> equality is decidable
pub open spec fn dec_eq_pair_nat(p1: (nat, nat), p2: (nat, nat)) -> Dec {
    dec_eq_pair(p1, p2, |x: nat, y: nat| dec_eq_nat(x, y), |x: nat, y: nat| dec_eq_nat(x, y))
}

// ----------------------------------------------------------------------------
// Equality Decidability for Sequences
// ----------------------------------------------------------------------------

/// Helper: Check equality of sequences from index i
pub open spec fn dec_eq_seq_helper<T>(
    s1: Seq<T>,
    s2: Seq<T>,
    dec_eq_t: spec_fn(T, T) -> Dec,
    i: int
) -> Dec
    decreases s1.len() - i when i >= 0
{
    if i >= s1.len() {
        Dec::Yes
    } else {
        match dec_eq_t(s1[i], s2[i]) {
            Dec::No => Dec::No,
            Dec::Yes => dec_eq_seq_helper(s1, s2, dec_eq_t, i + 1),
        }
    }
}

/// Sequence equality is decidable given decidable element equality
pub open spec fn dec_eq_seq<T>(
    s1: Seq<T>,
    s2: Seq<T>,
    dec_eq_t: spec_fn(T, T) -> Dec
) -> Dec {
    if s1.len() != s2.len() {
        Dec::No
    } else {
        dec_eq_seq_helper(s1, s2, dec_eq_t, 0)
    }
}

/// Seq<nat> equality is decidable
pub open spec fn dec_eq_seq_nat(s1: Seq<nat>, s2: Seq<nat>) -> Dec {
    dec_eq_seq(s1, s2, |x: nat, y: nat| dec_eq_nat(x, y))
}

// ----------------------------------------------------------------------------
// Soundness Proofs
// ----------------------------------------------------------------------------

/// dec_eq_bool is sound
pub proof fn dec_eq_bool_sound(a: bool, b: bool)
    ensures dec_to_bool(dec_eq_bool(a, b)) <==> (a == b)
{
}

/// dec_eq_nat is sound
pub proof fn dec_eq_nat_sound(a: nat, b: nat)
    ensures dec_to_bool(dec_eq_nat(a, b)) <==> (a == b)
{
}

/// dec_eq_int is sound
pub proof fn dec_eq_int_sound(a: int, b: int)
    ensures dec_to_bool(dec_eq_int(a, b)) <==> (a == b)
{
}

/// dec_eq_option is sound given sound element equality
pub proof fn dec_eq_option_sound<T>(
    a: Option<T>,
    b: Option<T>,
    dec_eq_t: spec_fn(T, T) -> Dec,
    eq_t: spec_fn(T, T) -> bool
)
    requires
        forall|x: T, y: T| #[trigger] dec_to_bool(dec_eq_t(x, y)) <==> eq_t(x, y),
        forall|x: T, y: T| #[trigger] eq_t(x, y) <==> (x == y),
    ensures
        dec_to_bool(dec_eq_option(a, b, dec_eq_t)) <==> (a == b)
{
}

/// dec_eq_pair is sound given sound component equality
pub proof fn dec_eq_pair_sound<A, B>(
    p1: (A, B),
    p2: (A, B),
    dec_eq_a: spec_fn(A, A) -> Dec,
    dec_eq_b: spec_fn(B, B) -> Dec
)
    requires
        forall|x: A, y: A| #[trigger] dec_to_bool(dec_eq_a(x, y)) <==> (x == y),
        forall|x: B, y: B| #[trigger] dec_to_bool(dec_eq_b(x, y)) <==> (x == y),
    ensures
        dec_to_bool(dec_eq_pair(p1, p2, dec_eq_a, dec_eq_b)) <==> (p1 == p2)
{
}

// ----------------------------------------------------------------------------
// Reflexivity, Symmetry, Transitivity
// ----------------------------------------------------------------------------

/// Equality decidability is reflexive
pub proof fn dec_eq_nat_reflexive(x: nat)
    ensures dec_to_bool(dec_eq_nat(x, x))
{
}

/// Equality decidability is symmetric
pub proof fn dec_eq_nat_symmetric(x: nat, y: nat)
    ensures dec_to_bool(dec_eq_nat(x, y)) == dec_to_bool(dec_eq_nat(y, x))
{
}

/// Equality decidability is transitive
pub proof fn dec_eq_nat_transitive(x: nat, y: nat, z: nat)
    requires dec_to_bool(dec_eq_nat(x, y)), dec_to_bool(dec_eq_nat(y, z))
    ensures dec_to_bool(dec_eq_nat(x, z))
{
}

// ----------------------------------------------------------------------------
// Inequality Decidability
// ----------------------------------------------------------------------------

/// Not-equal is decidable
pub open spec fn dec_neq_nat(a: nat, b: nat) -> Dec {
    bool_to_dec(a != b)
}

/// Decidable inequality is sound
pub proof fn dec_neq_nat_sound(a: nat, b: nat)
    ensures dec_to_bool(dec_neq_nat(a, b)) <==> (a != b)
{
}

/// Inequality is negation of equality
pub proof fn dec_neq_is_not_eq(a: nat, b: nat)
    ensures dec_to_bool(dec_neq_nat(a, b)) == !dec_to_bool(dec_eq_nat(a, b))
{
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_dec_eq_basic()
{
    // Equal values
    assert(dec_to_bool(dec_eq_nat(5, 5)));
    assert(dec_to_bool(dec_eq_bool(true, true)));
    assert(dec_to_bool(dec_eq_int(-3, -3)));

    // Unequal values
    assert(!dec_to_bool(dec_eq_nat(5, 7)));
    assert(!dec_to_bool(dec_eq_bool(true, false)));
    assert(!dec_to_bool(dec_eq_int(3, -3)));
}

pub proof fn example_dec_eq_option()
{
    let a: Option<nat> = Option::Some(5);
    let b: Option<nat> = Option::Some(5);
    let c: Option<nat> = Option::Some(7);
    let n: Option<nat> = Option::None;

    assert(dec_to_bool(dec_eq_option_nat(a, b)));
    assert(!dec_to_bool(dec_eq_option_nat(a, c)));
    assert(!dec_to_bool(dec_eq_option_nat(a, n)));
    assert(dec_to_bool(dec_eq_option_nat(n, n)));
}

pub proof fn example_dec_eq_pair()
{
    let p1: (nat, nat) = (1, 2);
    let p2: (nat, nat) = (1, 2);
    let p3: (nat, nat) = (1, 3);
    let p4: (nat, nat) = (2, 2);

    assert(dec_to_bool(dec_eq_pair_nat(p1, p2)));
    assert(!dec_to_bool(dec_eq_pair_nat(p1, p3)));
    assert(!dec_to_bool(dec_eq_pair_nat(p1, p4)));
}

pub proof fn example_dec_eq_seq()
{
    reveal_with_fuel(dec_eq_seq_helper, 4);

    let s1 = seq![1nat, 2, 3];
    let s2 = seq![1nat, 2, 3];
    let s3 = seq![1nat, 2, 4];
    let s4 = seq![1nat, 2];

    assert(dec_to_bool(dec_eq_seq_nat(s1, s2)));
    assert(!dec_to_bool(dec_eq_seq_nat(s1, s3)));
    assert(!dec_to_bool(dec_eq_seq_nat(s1, s4)));
}

pub proof fn example_dec_neq()
{
    assert(dec_to_bool(dec_neq_nat(5, 7)));
    assert(!dec_to_bool(dec_neq_nat(5, 5)));

    dec_neq_is_not_eq(5, 7);
    dec_neq_is_not_eq(5, 5);
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_dec_eq_verify()
{
    example_dec_eq_basic();
    example_dec_eq_option();
    example_dec_eq_pair();
    example_dec_eq_seq();
    example_dec_neq();

    // Verify properties
    dec_eq_nat_reflexive(42);
    dec_eq_nat_symmetric(5, 7);
    dec_eq_nat_transitive(3, 3, 3);

    // Verify soundness
    dec_eq_bool_sound(true, false);
    dec_eq_nat_sound(5, 5);
    dec_eq_int_sound(-1, -1);
}

pub fn main() {
    proof {
        qc_dec_eq_verify();
    }
}

} // verus!

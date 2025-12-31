use vstd::prelude::*;

verus! {

// ============================================================================
// QC: Monoid Typeclass (qc-current/Typeclasses)
// Semigroup with identity element
// ============================================================================

// ----------------------------------------------------------------------------
// Monoid Operations and Identities
// ----------------------------------------------------------------------------

// Nat addition monoid (identity: 0)
pub open spec fn nat_add(a: nat, b: nat) -> nat { a + b }
pub open spec fn nat_add_identity() -> nat { 0 }

// Nat multiplication monoid (identity: 1)
pub open spec fn nat_mul(a: nat, b: nat) -> nat { a * b }
pub open spec fn nat_mul_identity() -> nat { 1 }

// Seq concatenation monoid (identity: empty)
pub open spec fn seq_concat<A>(s1: Seq<A>, s2: Seq<A>) -> Seq<A> { s1 + s2 }
pub open spec fn seq_concat_identity<A>() -> Seq<A> { Seq::empty() }

// Bool conjunction monoid (identity: true)
pub open spec fn bool_and(a: bool, b: bool) -> bool { a && b }
pub open spec fn bool_and_identity() -> bool { true }

// Bool disjunction monoid (identity: false)
pub open spec fn bool_or(a: bool, b: bool) -> bool { a || b }
pub open spec fn bool_or_identity() -> bool { false }

// ----------------------------------------------------------------------------
// Monoid Laws
// ----------------------------------------------------------------------------

// Left identity: mempty <> x == x
pub proof fn nat_add_left_identity(x: nat)
    ensures nat_add(nat_add_identity(), x) == x
{
}

// Right identity: x <> mempty == x
pub proof fn nat_add_right_identity(x: nat)
    ensures nat_add(x, nat_add_identity()) == x
{
}

pub proof fn nat_mul_left_identity(x: nat)
    ensures nat_mul(nat_mul_identity(), x) == x
{
    assert(1 * x == x) by(nonlinear_arith);
}

pub proof fn nat_mul_right_identity(x: nat)
    ensures nat_mul(x, nat_mul_identity()) == x
{
    assert(x * 1 == x) by(nonlinear_arith);
}

pub proof fn seq_concat_left_identity<A>(s: Seq<A>)
    ensures seq_concat(seq_concat_identity(), s) =~= s
{
}

pub proof fn seq_concat_right_identity<A>(s: Seq<A>)
    ensures seq_concat(s, seq_concat_identity()) =~= s
{
}

pub proof fn bool_and_left_identity(x: bool)
    ensures bool_and(bool_and_identity(), x) == x
{
}

pub proof fn bool_and_right_identity(x: bool)
    ensures bool_and(x, bool_and_identity()) == x
{
}

// ----------------------------------------------------------------------------
// Mconcat: Fold over a list with monoid operation
// ----------------------------------------------------------------------------

pub open spec fn mconcat_nat_add(s: Seq<nat>) -> nat
    decreases s.len()
{
    if s.len() == 0 { nat_add_identity() }
    else { nat_add(s[0], mconcat_nat_add(s.skip(1))) }
}

pub open spec fn mconcat_nat_mul(s: Seq<nat>) -> nat
    decreases s.len()
{
    if s.len() == 0 { nat_mul_identity() }
    else { nat_mul(s[0], mconcat_nat_mul(s.skip(1))) }
}

pub open spec fn mconcat_bool_and(s: Seq<bool>) -> bool
    decreases s.len()
{
    if s.len() == 0 { bool_and_identity() }
    else { bool_and(s[0], mconcat_bool_and(s.skip(1))) }
}

pub open spec fn mconcat_bool_or(s: Seq<bool>) -> bool
    decreases s.len()
{
    if s.len() == 0 { bool_or_identity() }
    else { bool_or(s[0], mconcat_bool_or(s.skip(1))) }
}

// ----------------------------------------------------------------------------
// Properties
// ----------------------------------------------------------------------------

pub proof fn mconcat_empty_is_identity()
    ensures mconcat_nat_add(Seq::empty()) == nat_add_identity()
{
}

pub proof fn mconcat_singleton(x: nat)
    ensures mconcat_nat_add(seq![x]) == x
{
    reveal_with_fuel(mconcat_nat_add, 2);
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_mconcat()
{
    reveal_with_fuel(mconcat_nat_add, 5);

    let s = seq![1nat, 2, 3, 4];
    assert(mconcat_nat_add(s) == 10);
}

pub proof fn example_mconcat_mul()
{
    reveal_with_fuel(mconcat_nat_mul, 5);

    let s = seq![1nat, 2, 3, 4];
    // 1 * 2 * 3 * 4 = 24
    assert(1 * 2 == 2) by(nonlinear_arith);
    assert(2 * 3 == 6) by(nonlinear_arith);
    assert(6 * 4 == 24) by(nonlinear_arith);
    // mconcat computes the product correctly
}

pub proof fn example_mconcat_bool()
{
    reveal_with_fuel(mconcat_bool_and, 4);
    reveal_with_fuel(mconcat_bool_or, 4);

    let s1 = seq![true, true, true];
    let s2 = seq![true, false, true];

    assert(mconcat_bool_and(s1));
    assert(!mconcat_bool_and(s2));
    assert(mconcat_bool_or(s2));
}

pub proof fn typeclass_monoid_verify()
{
    example_mconcat();
    example_mconcat_mul();
    example_mconcat_bool();
    nat_add_left_identity(42);
    nat_add_right_identity(42);
    nat_mul_left_identity(42);
    nat_mul_right_identity(42);
    mconcat_empty_is_identity();
}

pub fn main() {
    proof { typeclass_monoid_verify(); }
}

} // verus!

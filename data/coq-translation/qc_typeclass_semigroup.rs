use vstd::prelude::*;

verus! {

// ============================================================================
// QC: Semigroup Typeclass (qc-current/Typeclasses)
// Types with associative binary operation
// ============================================================================

// ----------------------------------------------------------------------------
// Semigroup Operations
// ----------------------------------------------------------------------------

// Nat addition semigroup
pub open spec fn nat_add(a: nat, b: nat) -> nat { a + b }

// Nat multiplication semigroup
pub open spec fn nat_mul(a: nat, b: nat) -> nat { a * b }

// Nat max semigroup
pub open spec fn nat_max(a: nat, b: nat) -> nat { if a >= b { a } else { b } }

// Nat min semigroup (on positive nats)
pub open spec fn nat_min(a: nat, b: nat) -> nat { if a <= b { a } else { b } }

// Seq concatenation semigroup
pub open spec fn seq_concat<A>(s1: Seq<A>, s2: Seq<A>) -> Seq<A> { s1 + s2 }

// Bool conjunction semigroup
pub open spec fn bool_and(a: bool, b: bool) -> bool { a && b }

// Bool disjunction semigroup
pub open spec fn bool_or(a: bool, b: bool) -> bool { a || b }

// ----------------------------------------------------------------------------
// Semigroup Law: Associativity
// ----------------------------------------------------------------------------

pub proof fn nat_add_assoc(a: nat, b: nat, c: nat)
    ensures nat_add(nat_add(a, b), c) == nat_add(a, nat_add(b, c))
{
}

pub proof fn nat_mul_assoc(a: nat, b: nat, c: nat)
    ensures nat_mul(nat_mul(a, b), c) == nat_mul(a, nat_mul(b, c))
{
    assert(nat_mul(nat_mul(a, b), c) == nat_mul(a, nat_mul(b, c))) by (nonlinear_arith);
}

pub proof fn nat_max_assoc(a: nat, b: nat, c: nat)
    ensures nat_max(nat_max(a, b), c) == nat_max(a, nat_max(b, c))
{
}

pub proof fn nat_min_assoc(a: nat, b: nat, c: nat)
    ensures nat_min(nat_min(a, b), c) == nat_min(a, nat_min(b, c))
{
}

pub proof fn seq_concat_assoc<A>(s1: Seq<A>, s2: Seq<A>, s3: Seq<A>)
    ensures seq_concat(seq_concat(s1, s2), s3) =~= seq_concat(s1, seq_concat(s2, s3))
{
}

pub proof fn bool_and_assoc(a: bool, b: bool, c: bool)
    ensures bool_and(bool_and(a, b), c) == bool_and(a, bool_and(b, c))
{
}

pub proof fn bool_or_assoc(a: bool, b: bool, c: bool)
    ensures bool_or(bool_or(a, b), c) == bool_or(a, bool_or(b, c))
{
}

// ----------------------------------------------------------------------------
// Sconcat: Fold with semigroup operation
// ----------------------------------------------------------------------------

pub open spec fn sconcat_nat_add(s: Seq<nat>) -> nat
    decreases s.len()
{
    if s.len() == 0 { 0 }
    else if s.len() == 1 { s[0] }
    else { nat_add(s[0], sconcat_nat_add(s.skip(1))) }
}

pub open spec fn sconcat_nat_mul(s: Seq<nat>) -> nat
    decreases s.len()
{
    if s.len() == 0 { 1 }
    else if s.len() == 1 { s[0] }
    else { nat_mul(s[0], sconcat_nat_mul(s.skip(1))) }
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_semigroup()
{
    assert(nat_add(2, 3) == 5);
    assert(nat_mul(2, 3) == 6);
    assert(nat_max(2, 3) == 3);
    assert(nat_min(2, 3) == 2);
}

pub proof fn example_sconcat()
{
    reveal_with_fuel(sconcat_nat_add, 4);
    let s = seq![1nat, 2, 3];
    assert(sconcat_nat_add(s) == 6);
}

pub proof fn typeclass_semigroup_verify()
{
    example_semigroup();
    example_sconcat();
    nat_add_assoc(1, 2, 3);
    nat_max_assoc(1, 5, 3);
    bool_and_assoc(true, false, true);
}

pub fn main() {
    proof { typeclass_semigroup_verify(); }
}

} // verus!

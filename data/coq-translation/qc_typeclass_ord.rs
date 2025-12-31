use vstd::prelude::*;

verus! {

// ============================================================================
// QC: Ord Typeclass (qc-current/Typeclasses)
// Ordering with superclass constraint on Eq
// ============================================================================

// Ordering result
#[derive(PartialEq, Eq)]
pub enum Ordering {
    Lt,
    Eq,
    Gt,
}

// ----------------------------------------------------------------------------
// Ord for Basic Types
// ----------------------------------------------------------------------------

pub open spec fn cmp_nat(a: nat, b: nat) -> Ordering {
    if a < b { Ordering::Lt }
    else if a == b { Ordering::Eq }
    else { Ordering::Gt }
}

pub open spec fn le_nat(a: nat, b: nat) -> bool { a <= b }
pub open spec fn lt_nat(a: nat, b: nat) -> bool { a < b }
pub open spec fn ge_nat(a: nat, b: nat) -> bool { a >= b }
pub open spec fn gt_nat(a: nat, b: nat) -> bool { a > b }

pub open spec fn cmp_int(a: int, b: int) -> Ordering {
    if a < b { Ordering::Lt }
    else if a == b { Ordering::Eq }
    else { Ordering::Gt }
}

pub open spec fn cmp_bool(a: bool, b: bool) -> Ordering {
    match (a, b) {
        (false, false) => Ordering::Eq,
        (false, true) => Ordering::Lt,
        (true, false) => Ordering::Gt,
        (true, true) => Ordering::Eq,
    }
}

// ----------------------------------------------------------------------------
// Ord for Compound Types
// ----------------------------------------------------------------------------

// Lexicographic ordering for pairs
pub open spec fn cmp_pair<A, B>(
    p1: (A, B), p2: (A, B),
    cmp_a: spec_fn(A, A) -> Ordering,
    cmp_b: spec_fn(B, B) -> Ordering
) -> Ordering {
    match cmp_a(p1.0, p2.0) {
        Ordering::Lt => Ordering::Lt,
        Ordering::Gt => Ordering::Gt,
        Ordering::Eq => cmp_b(p1.1, p2.1),
    }
}

// Lexicographic ordering for sequences
pub open spec fn cmp_seq_helper(s1: Seq<nat>, s2: Seq<nat>, idx: int) -> Ordering
    decreases s1.len() - idx
{
    if idx >= s1.len() && idx >= s2.len() {
        Ordering::Eq
    } else if idx >= s1.len() {
        Ordering::Lt
    } else if idx >= s2.len() {
        Ordering::Gt
    } else {
        match cmp_nat(s1[idx], s2[idx]) {
            Ordering::Lt => Ordering::Lt,
            Ordering::Gt => Ordering::Gt,
            Ordering::Eq => cmp_seq_helper(s1, s2, idx + 1),
        }
    }
}

pub open spec fn cmp_seq(s1: Seq<nat>, s2: Seq<nat>) -> Ordering {
    cmp_seq_helper(s1, s2, 0)
}

// ----------------------------------------------------------------------------
// Ord Laws
// ----------------------------------------------------------------------------

// Reflexivity: cmp(x, x) == Eq
pub proof fn cmp_nat_reflexive(x: nat)
    ensures cmp_nat(x, x) == Ordering::Eq
{
}

// Antisymmetry
pub proof fn cmp_nat_antisymmetric(x: nat, y: nat)
    ensures cmp_nat(x, y) == Ordering::Lt <==> cmp_nat(y, x) == Ordering::Gt
{
}

// Transitivity
pub proof fn cmp_nat_transitive(x: nat, y: nat, z: nat)
    requires cmp_nat(x, y) == Ordering::Lt, cmp_nat(y, z) == Ordering::Lt
    ensures cmp_nat(x, z) == Ordering::Lt
{
}

// Consistency with Eq
pub proof fn cmp_nat_eq_consistent(x: nat, y: nat)
    ensures (cmp_nat(x, y) == Ordering::Eq) <==> (x == y)
{
}

// ----------------------------------------------------------------------------
// Min and Max
// ----------------------------------------------------------------------------

pub open spec fn min_nat(a: nat, b: nat) -> nat {
    if a <= b { a } else { b }
}

pub open spec fn max_nat(a: nat, b: nat) -> nat {
    if a >= b { a } else { b }
}

pub proof fn min_le_both(a: nat, b: nat)
    ensures min_nat(a, b) <= a && min_nat(a, b) <= b
{
}

pub proof fn max_ge_both(a: nat, b: nat)
    ensures max_nat(a, b) >= a && max_nat(a, b) >= b
{
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_cmp_nat()
{
    assert(cmp_nat(3, 5) == Ordering::Lt);
    assert(cmp_nat(5, 5) == Ordering::Eq);
    assert(cmp_nat(7, 5) == Ordering::Gt);
}

pub proof fn example_cmp_seq()
{
    reveal_with_fuel(cmp_seq_helper, 3);
    let s1 = seq![1nat, 2, 3];
    let s2 = seq![1nat, 2, 4];
    assert(cmp_seq(s1, s2) == Ordering::Lt);
}

pub proof fn typeclass_ord_verify()
{
    example_cmp_nat();
    example_cmp_seq();
    cmp_nat_reflexive(10);
    min_le_both(3, 7);
    max_ge_both(3, 7);
}

pub fn main() {
    proof { typeclass_ord_verify(); }
}

} // verus!

use vstd::prelude::*;

verus! {

// ============================================================================
// QC: Order Decidability (QuickChick-style)
// Models decidable ordering predicates (lt, le, gt, ge)
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
// Order Decidability for Natural Numbers
// ----------------------------------------------------------------------------

/// Less than is decidable
pub open spec fn dec_lt_nat(a: nat, b: nat) -> Dec {
    bool_to_dec(a < b)
}

/// Less than or equal is decidable
pub open spec fn dec_le_nat(a: nat, b: nat) -> Dec {
    bool_to_dec(a <= b)
}

/// Greater than is decidable
pub open spec fn dec_gt_nat(a: nat, b: nat) -> Dec {
    bool_to_dec(a > b)
}

/// Greater than or equal is decidable
pub open spec fn dec_ge_nat(a: nat, b: nat) -> Dec {
    bool_to_dec(a >= b)
}

// ----------------------------------------------------------------------------
// Order Decidability for Integers
// ----------------------------------------------------------------------------

/// Integer less than is decidable
pub open spec fn dec_lt_int(a: int, b: int) -> Dec {
    bool_to_dec(a < b)
}

/// Integer less than or equal is decidable
pub open spec fn dec_le_int(a: int, b: int) -> Dec {
    bool_to_dec(a <= b)
}

/// Integer greater than is decidable
pub open spec fn dec_gt_int(a: int, b: int) -> Dec {
    bool_to_dec(a > b)
}

/// Integer greater than or equal is decidable
pub open spec fn dec_ge_int(a: int, b: int) -> Dec {
    bool_to_dec(a >= b)
}

// ----------------------------------------------------------------------------
// Soundness Proofs
// ----------------------------------------------------------------------------

pub proof fn dec_lt_nat_sound(a: nat, b: nat)
    ensures dec_to_bool(dec_lt_nat(a, b)) <==> (a < b)
{
}

pub proof fn dec_le_nat_sound(a: nat, b: nat)
    ensures dec_to_bool(dec_le_nat(a, b)) <==> (a <= b)
{
}

pub proof fn dec_gt_nat_sound(a: nat, b: nat)
    ensures dec_to_bool(dec_gt_nat(a, b)) <==> (a > b)
{
}

pub proof fn dec_ge_nat_sound(a: nat, b: nat)
    ensures dec_to_bool(dec_ge_nat(a, b)) <==> (a >= b)
{
}

// ----------------------------------------------------------------------------
// Order Relationship Proofs
// ----------------------------------------------------------------------------

/// lt and ge are complements
pub proof fn dec_lt_ge_complement(a: nat, b: nat)
    ensures dec_to_bool(dec_lt_nat(a, b)) == !dec_to_bool(dec_ge_nat(a, b))
{
}

/// le and gt are complements
pub proof fn dec_le_gt_complement(a: nat, b: nat)
    ensures dec_to_bool(dec_le_nat(a, b)) == !dec_to_bool(dec_gt_nat(a, b))
{
}

/// lt is antisymmetric to gt
pub proof fn dec_lt_gt_antisymmetric(a: nat, b: nat)
    ensures dec_to_bool(dec_lt_nat(a, b)) == dec_to_bool(dec_gt_nat(b, a))
{
}

/// le is antisymmetric to ge
pub proof fn dec_le_ge_antisymmetric(a: nat, b: nat)
    ensures dec_to_bool(dec_le_nat(a, b)) == dec_to_bool(dec_ge_nat(b, a))
{
}

/// Trichotomy: exactly one of <, =, > holds
pub proof fn dec_trichotomy_nat(a: nat, b: nat)
    ensures
        (dec_to_bool(dec_lt_nat(a, b)) && !(a == b) && !dec_to_bool(dec_gt_nat(a, b))) ||
        (!dec_to_bool(dec_lt_nat(a, b)) && (a == b) && !dec_to_bool(dec_gt_nat(a, b))) ||
        (!dec_to_bool(dec_lt_nat(a, b)) && !(a == b) && dec_to_bool(dec_gt_nat(a, b)))
{
}

// ----------------------------------------------------------------------------
// Transitivity Proofs
// ----------------------------------------------------------------------------

/// Less than is transitive
pub proof fn dec_lt_nat_transitive(a: nat, b: nat, c: nat)
    requires dec_to_bool(dec_lt_nat(a, b)), dec_to_bool(dec_lt_nat(b, c))
    ensures dec_to_bool(dec_lt_nat(a, c))
{
}

/// Less than or equal is transitive
pub proof fn dec_le_nat_transitive(a: nat, b: nat, c: nat)
    requires dec_to_bool(dec_le_nat(a, b)), dec_to_bool(dec_le_nat(b, c))
    ensures dec_to_bool(dec_le_nat(a, c))
{
}

/// Greater than is transitive
pub proof fn dec_gt_nat_transitive(a: nat, b: nat, c: nat)
    requires dec_to_bool(dec_gt_nat(a, b)), dec_to_bool(dec_gt_nat(b, c))
    ensures dec_to_bool(dec_gt_nat(a, c))
{
}

/// Greater than or equal is transitive
pub proof fn dec_ge_nat_transitive(a: nat, b: nat, c: nat)
    requires dec_to_bool(dec_ge_nat(a, b)), dec_to_bool(dec_ge_nat(b, c))
    ensures dec_to_bool(dec_ge_nat(a, c))
{
}

// ----------------------------------------------------------------------------
// Reflexivity Proofs
// ----------------------------------------------------------------------------

/// Less than is irreflexive
pub proof fn dec_lt_nat_irreflexive(a: nat)
    ensures !dec_to_bool(dec_lt_nat(a, a))
{
}

/// Less than or equal is reflexive
pub proof fn dec_le_nat_reflexive(a: nat)
    ensures dec_to_bool(dec_le_nat(a, a))
{
}

/// Greater than is irreflexive
pub proof fn dec_gt_nat_irreflexive(a: nat)
    ensures !dec_to_bool(dec_gt_nat(a, a))
{
}

/// Greater than or equal is reflexive
pub proof fn dec_ge_nat_reflexive(a: nat)
    ensures dec_to_bool(dec_ge_nat(a, a))
{
}

// ----------------------------------------------------------------------------
// Combined Ordering Decidability
// ----------------------------------------------------------------------------

/// Ordering result type
pub enum Ordering {
    Lt,
    Eq,
    Gt,
}

/// Full ordering comparison is decidable
pub open spec fn dec_cmp_nat(a: nat, b: nat) -> Ordering {
    if a < b { Ordering::Lt }
    else if a == b { Ordering::Eq }
    else { Ordering::Gt }
}

/// dec_cmp is consistent with individual comparisons
pub proof fn dec_cmp_consistent_lt(a: nat, b: nat)
    ensures (dec_cmp_nat(a, b) == Ordering::Lt) <==> dec_to_bool(dec_lt_nat(a, b))
{
}

pub proof fn dec_cmp_consistent_eq(a: nat, b: nat)
    ensures (dec_cmp_nat(a, b) == Ordering::Eq) <==> (a == b)
{
}

pub proof fn dec_cmp_consistent_gt(a: nat, b: nat)
    ensures (dec_cmp_nat(a, b) == Ordering::Gt) <==> dec_to_bool(dec_gt_nat(a, b))
{
}

// ----------------------------------------------------------------------------
// Range Decidability
// ----------------------------------------------------------------------------

/// In range [lo, hi) is decidable
pub open spec fn dec_in_range(x: nat, lo: nat, hi: nat) -> Dec {
    bool_to_dec(lo <= x && x < hi)
}

/// In range [lo, hi] (inclusive) is decidable
pub open spec fn dec_in_range_inclusive(x: nat, lo: nat, hi: nat) -> Dec {
    bool_to_dec(lo <= x && x <= hi)
}

/// Range decidability is sound
pub proof fn dec_in_range_sound(x: nat, lo: nat, hi: nat)
    ensures dec_to_bool(dec_in_range(x, lo, hi)) <==> (lo <= x && x < hi)
{
}

pub proof fn dec_in_range_inclusive_sound(x: nat, lo: nat, hi: nat)
    ensures dec_to_bool(dec_in_range_inclusive(x, lo, hi)) <==> (lo <= x && x <= hi)
{
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_dec_lt()
{
    assert(dec_to_bool(dec_lt_nat(3, 5)));
    assert(!dec_to_bool(dec_lt_nat(5, 5)));
    assert(!dec_to_bool(dec_lt_nat(7, 5)));
}

pub proof fn example_dec_le()
{
    assert(dec_to_bool(dec_le_nat(3, 5)));
    assert(dec_to_bool(dec_le_nat(5, 5)));
    assert(!dec_to_bool(dec_le_nat(7, 5)));
}

pub proof fn example_dec_gt()
{
    assert(!dec_to_bool(dec_gt_nat(3, 5)));
    assert(!dec_to_bool(dec_gt_nat(5, 5)));
    assert(dec_to_bool(dec_gt_nat(7, 5)));
}

pub proof fn example_dec_ge()
{
    assert(!dec_to_bool(dec_ge_nat(3, 5)));
    assert(dec_to_bool(dec_ge_nat(5, 5)));
    assert(dec_to_bool(dec_ge_nat(7, 5)));
}

pub proof fn example_dec_int_ordering()
{
    assert(dec_to_bool(dec_lt_int(-5, 3)));
    assert(dec_to_bool(dec_le_int(-5, -5)));
    assert(dec_to_bool(dec_gt_int(3, -5)));
    assert(dec_to_bool(dec_ge_int(-5, -5)));
}

pub proof fn example_dec_cmp()
{
    assert(dec_cmp_nat(3, 5) == Ordering::Lt);
    assert(dec_cmp_nat(5, 5) == Ordering::Eq);
    assert(dec_cmp_nat(7, 5) == Ordering::Gt);
}

pub proof fn example_dec_range()
{
    // In range [2, 5)
    assert(!dec_to_bool(dec_in_range(1, 2, 5)));
    assert(dec_to_bool(dec_in_range(2, 2, 5)));
    assert(dec_to_bool(dec_in_range(4, 2, 5)));
    assert(!dec_to_bool(dec_in_range(5, 2, 5)));

    // In range [2, 5]
    assert(!dec_to_bool(dec_in_range_inclusive(1, 2, 5)));
    assert(dec_to_bool(dec_in_range_inclusive(2, 2, 5)));
    assert(dec_to_bool(dec_in_range_inclusive(5, 2, 5)));
    assert(!dec_to_bool(dec_in_range_inclusive(6, 2, 5)));
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_dec_ord_verify()
{
    example_dec_lt();
    example_dec_le();
    example_dec_gt();
    example_dec_ge();
    example_dec_int_ordering();
    example_dec_cmp();
    example_dec_range();

    // Verify properties
    dec_lt_ge_complement(3, 5);
    dec_le_gt_complement(3, 5);
    dec_lt_gt_antisymmetric(3, 5);
    dec_le_ge_antisymmetric(3, 5);

    // Verify transitivity
    dec_lt_nat_transitive(1, 3, 5);
    dec_le_nat_transitive(1, 3, 5);

    // Verify reflexivity/irreflexivity
    dec_lt_nat_irreflexive(5);
    dec_le_nat_reflexive(5);

    // Verify soundness
    dec_lt_nat_sound(3, 5);
    dec_le_nat_sound(3, 5);
    dec_gt_nat_sound(3, 5);
    dec_ge_nat_sound(3, 5);
}

pub fn main() {
    proof {
        qc_dec_ord_verify();
    }
}

} // verus!

use vstd::prelude::*;

verus! {

// ============================================================================
// QC: Integer Generators (QuickChick-style)
// Specification functions modeling integer generation for property testing
// ============================================================================

// ----------------------------------------------------------------------------
// Core Generator Model
// An int generator is modeled as the set of integers it can produce
// ----------------------------------------------------------------------------

/// Range specification: [lo, hi)
pub open spec fn in_int_range(n: int, lo: int, hi: int) -> bool {
    lo <= n && n < hi
}

/// choose_int(lo, hi) generates integers in [lo, hi)
pub open spec fn choose_int_outputs(lo: int, hi: int) -> Set<int> {
    Set::new(|n: int| in_int_range(n, lo, hi))
}

/// Arbitrary int in [-bound, bound]
pub open spec fn gen_int_bound_outputs(bound: nat) -> Set<int> {
    choose_int_outputs(-(bound as int), (bound as int) + 1)
}

/// Small int generator (-10 to 10)
pub open spec fn gen_small_int_outputs() -> Set<int> {
    choose_int_outputs(-10, 11)
}

/// Positive int generator (1 to bound)
pub open spec fn gen_pos_int_outputs(bound: nat) -> Set<int> {
    choose_int_outputs(1, (bound as int) + 1)
}

/// Non-negative int generator (0 to bound)
pub open spec fn gen_nonneg_int_outputs(bound: nat) -> Set<int> {
    choose_int_outputs(0, (bound as int) + 1)
}

/// Negative int generator (-bound to -1)
pub open spec fn gen_neg_int_outputs(bound: nat) -> Set<int> {
    choose_int_outputs(-(bound as int), 0)
}

// ----------------------------------------------------------------------------
// Choose Function Properties
// ----------------------------------------------------------------------------

/// Choose with valid range is non-empty
pub proof fn choose_int_nonempty(lo: int, hi: int)
    requires lo < hi
    ensures choose_int_outputs(lo, hi).contains(lo)
{
}

/// Choose contains all values in range
pub proof fn choose_int_complete(lo: int, hi: int, n: int)
    requires lo <= n && n < hi
    ensures choose_int_outputs(lo, hi).contains(n)
{
}

/// Choose excludes values outside range
pub proof fn choose_int_bounded(lo: int, hi: int, n: int)
    requires choose_int_outputs(lo, hi).contains(n)
    ensures lo <= n && n < hi
{
}

/// Choose from singleton range produces single value
pub proof fn choose_int_singleton(n: int)
    ensures
        choose_int_outputs(n, n + 1).contains(n),
        forall|m: int| #[trigger] choose_int_outputs(n, n + 1).contains(m) ==> m == n,
{
}

// ----------------------------------------------------------------------------
// Generator Combinators for Int
// ----------------------------------------------------------------------------

/// Map a function over generator outputs
pub open spec fn gen_int_map(outputs: Set<int>, f: spec_fn(int) -> int) -> Set<int> {
    Set::new(|n: int| exists|m: int| outputs.contains(m) && f(m) == n)
}

/// Filter generator outputs by predicate
pub open spec fn gen_int_filter(outputs: Set<int>, p: spec_fn(int) -> bool) -> Set<int> {
    Set::new(|n: int| outputs.contains(n) && p(n))
}

/// Add constant to all outputs
pub open spec fn gen_int_add(outputs: Set<int>, k: int) -> Set<int> {
    gen_int_map(outputs, |n: int| n + k)
}

/// Negate all outputs
pub open spec fn gen_int_negate(outputs: Set<int>) -> Set<int> {
    gen_int_map(outputs, |n: int| -n)
}

/// Absolute value of all outputs
pub open spec fn gen_int_abs(outputs: Set<int>) -> Set<int> {
    gen_int_map(outputs, |n: int| if n >= 0 { n } else { -n })
}

/// Multiply all outputs by constant
pub open spec fn gen_int_mul(outputs: Set<int>, k: int) -> Set<int> {
    gen_int_map(outputs, |n: int| n * k)
}

// ----------------------------------------------------------------------------
// Combinator Properties
// ----------------------------------------------------------------------------

/// Map preserves membership
pub proof fn gen_int_map_membership(outputs: Set<int>, f: spec_fn(int) -> int, n: int)
    requires outputs.contains(n)
    ensures gen_int_map(outputs, f).contains(f(n))
{
}

/// Filter restricts membership
pub proof fn gen_int_filter_restriction(outputs: Set<int>, p: spec_fn(int) -> bool, n: int)
    requires gen_int_filter(outputs, p).contains(n)
    ensures outputs.contains(n) && p(n)
{
}

/// Negation is involutive
pub proof fn gen_int_negate_involutive(outputs: Set<int>)
    ensures gen_int_negate(gen_int_negate(outputs)) =~= outputs
{
    assert forall|n: int| gen_int_negate(gen_int_negate(outputs)).contains(n) <==>
        outputs.contains(n) by {
        if gen_int_negate(gen_int_negate(outputs)).contains(n) {
            let m = choose|m: int| gen_int_negate(outputs).contains(m) && -m == n;
            let k = choose|k: int| outputs.contains(k) && -k == m;
            assert(k == n);
        }
        if outputs.contains(n) {
            assert(gen_int_negate(outputs).contains(-n));
            assert(gen_int_negate(gen_int_negate(outputs)).contains(n));
        }
    }
}

/// Adding shifts range
pub proof fn gen_int_add_shifts(lo: int, hi: int, k: int)
    ensures
        forall|n: int| gen_int_add(choose_int_outputs(lo, hi), k).contains(n) <==>
            in_int_range(n, lo + k, hi + k)
{
    assert forall|n: int| gen_int_add(choose_int_outputs(lo, hi), k).contains(n) <==>
        in_int_range(n, lo + k, hi + k) by {
        if gen_int_add(choose_int_outputs(lo, hi), k).contains(n) {
            let m = choose|m: int| choose_int_outputs(lo, hi).contains(m) && m + k == n;
            assert(in_int_range(m, lo, hi));
            assert(n == m + k);
        }
        if in_int_range(n, lo + k, hi + k) {
            let m = n - k;
            assert(choose_int_outputs(lo, hi).contains(m));
        }
    }
}

// ----------------------------------------------------------------------------
// Sign-based Generators
// ----------------------------------------------------------------------------

/// Generate strictly positive integers
pub open spec fn gen_positive_outputs(bound: nat) -> Set<int> {
    gen_int_filter(gen_int_bound_outputs(bound), |n: int| n > 0)
}

/// Generate strictly negative integers
pub open spec fn gen_negative_outputs(bound: nat) -> Set<int> {
    gen_int_filter(gen_int_bound_outputs(bound), |n: int| n < 0)
}

/// Generate non-zero integers
pub open spec fn gen_nonzero_outputs(bound: nat) -> Set<int> {
    gen_int_filter(gen_int_bound_outputs(bound), |n: int| n != 0)
}

/// Positive generator is correct
pub proof fn gen_positive_correct(bound: nat, n: int)
    requires gen_positive_outputs(bound).contains(n)
    ensures n > 0
{
    gen_int_filter_restriction(gen_int_bound_outputs(bound), |m: int| m > 0, n);
}

/// Negative generator is correct
pub proof fn gen_negative_correct(bound: nat, n: int)
    requires gen_negative_outputs(bound).contains(n)
    ensures n < 0
{
    gen_int_filter_restriction(gen_int_bound_outputs(bound), |m: int| m < 0, n);
}

/// Nonzero generator is correct
pub proof fn gen_nonzero_correct(bound: nat, n: int)
    requires gen_nonzero_outputs(bound).contains(n)
    ensures n != 0
{
    gen_int_filter_restriction(gen_int_bound_outputs(bound), |m: int| m != 0, n);
}

// ----------------------------------------------------------------------------
// Union and Intersection
// ----------------------------------------------------------------------------

/// Union of two generators
pub open spec fn gen_int_union(out1: Set<int>, out2: Set<int>) -> Set<int> {
    out1.union(out2)
}

/// Intersection of two generators
pub open spec fn gen_int_intersect(out1: Set<int>, out2: Set<int>) -> Set<int> {
    out1.intersect(out2)
}

/// Union contains both
pub proof fn gen_int_union_contains(out1: Set<int>, out2: Set<int>, n: int)
    requires out1.contains(n) || out2.contains(n)
    ensures gen_int_union(out1, out2).contains(n)
{
}

/// Positive and negative are disjoint
pub proof fn positive_negative_disjoint(bound: nat)
    ensures gen_int_intersect(gen_positive_outputs(bound), gen_negative_outputs(bound)) =~= Set::empty()
{
    assert forall|n: int| !gen_int_intersect(gen_positive_outputs(bound), gen_negative_outputs(bound)).contains(n) by {
        if gen_positive_outputs(bound).contains(n) {
            gen_positive_correct(bound, n);
            assert(n > 0);
        }
        if gen_negative_outputs(bound).contains(n) {
            gen_negative_correct(bound, n);
            assert(n < 0);
        }
    }
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_choose_int_basic()
{
    choose_int_nonempty(-5int, 5int);
    assert(choose_int_outputs(-5int, 5int).contains(-5int));

    choose_int_complete(-5int, 5int, 0int);
    assert(choose_int_outputs(-5int, 5int).contains(0int));

    choose_int_complete(-5int, 5int, 4int);
    assert(choose_int_outputs(-5int, 5int).contains(4int));

    // 5 is not in [-5, 5)
    assert(!choose_int_outputs(-5int, 5int).contains(5int));
}

pub proof fn example_small_int()
{
    assert(gen_small_int_outputs().contains(-10int));
    assert(gen_small_int_outputs().contains(0int));
    assert(gen_small_int_outputs().contains(10int));
    assert(!gen_small_int_outputs().contains(-11int));
    assert(!gen_small_int_outputs().contains(11int));
}

pub proof fn example_signed_generators()
{
    // Positive
    assert(gen_pos_int_outputs(10nat).contains(1int));
    assert(gen_pos_int_outputs(10nat).contains(10int));
    assert(!gen_pos_int_outputs(10nat).contains(0int));
    assert(!gen_pos_int_outputs(10nat).contains(-1int));

    // Negative
    assert(gen_neg_int_outputs(10nat).contains(-1int));
    assert(gen_neg_int_outputs(10nat).contains(-10int));
    assert(!gen_neg_int_outputs(10nat).contains(0int));
}

pub proof fn example_negation()
{
    let pos = gen_pos_int_outputs(10nat);
    let neg = gen_int_negate(pos);

    // Negating positive gives negative
    // Show 1 is in pos, so -1 is in neg
    assert(pos.contains(1int));
    gen_int_map_membership(pos, |n: int| -n, 1int);
    assert(neg.contains(-1int));

    assert(pos.contains(10int));
    gen_int_map_membership(pos, |n: int| -n, 10int);
    assert(neg.contains(-10int));

    // Double negation
    gen_int_negate_involutive(pos);
}

pub proof fn example_abs()
{
    let both = gen_int_bound_outputs(5nat);
    let abs_fn = |n: int| if n >= 0 { n } else { -n };
    let abs_vals = gen_int_abs(both);

    // Absolute values are non-negative
    // 0 maps to 0
    assert(both.contains(0int));
    gen_int_map_membership(both, abs_fn, 0int);
    assert(abs_vals.contains(0int));

    // 5 maps to 5
    assert(both.contains(5int));
    gen_int_map_membership(both, abs_fn, 5int);
    assert(abs_vals.contains(5int));

    // Both 5 and -5 map to 5
    gen_int_map_membership(both, abs_fn, 5int);
    gen_int_map_membership(both, abs_fn, -5int);
}

pub proof fn example_disjoint()
{
    positive_negative_disjoint(10nat);
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_gen_int_verify()
{
    example_choose_int_basic();
    example_small_int();
    example_signed_generators();
    example_negation();
    example_abs();
    example_disjoint();

    // Additional properties
    choose_int_singleton(42int);
}

pub fn main() {
    proof {
        qc_gen_int_verify();
    }
}

} // verus!

use vstd::prelude::*;

verus! {

// ============================================================================
// QC: Natural Number Generators (QuickChick-style)
// Specification functions modeling natural number generation for property testing
// ============================================================================

// ----------------------------------------------------------------------------
// Core Generator Model
// A nat generator is modeled as the set of natural numbers it can produce
// ----------------------------------------------------------------------------

/// Range specification: [lo, hi)
pub open spec fn in_range(n: nat, lo: nat, hi: nat) -> bool {
    lo <= n && n < hi
}

/// choose(lo, hi) generates natural numbers in [lo, hi)
pub open spec fn choose_outputs(lo: nat, hi: nat) -> Set<nat> {
    Set::new(|n: nat| in_range(n, lo, hi))
}

/// Arbitrary nat up to a bound
pub open spec fn gen_nat_bound_outputs(bound: nat) -> Set<nat> {
    choose_outputs(0, bound + 1)
}

/// Small nat generator (0 to 10)
pub open spec fn gen_small_nat_outputs() -> Set<nat> {
    choose_outputs(0, 11)
}

// ----------------------------------------------------------------------------
// Choose Function Properties
// ----------------------------------------------------------------------------

/// Choose with valid range is non-empty
pub proof fn choose_nonempty(lo: nat, hi: nat)
    requires lo < hi
    ensures choose_outputs(lo, hi).contains(lo)
{
}

/// Choose contains all values in range
pub proof fn choose_complete(lo: nat, hi: nat, n: nat)
    requires lo <= n && n < hi
    ensures choose_outputs(lo, hi).contains(n)
{
}

/// Choose excludes values outside range
pub proof fn choose_bounded(lo: nat, hi: nat, n: nat)
    requires choose_outputs(lo, hi).contains(n)
    ensures lo <= n && n < hi
{
}

/// Choose from singleton range produces single value
pub proof fn choose_singleton(n: nat)
    ensures
        choose_outputs(n, n + 1).contains(n),
        forall|m: nat| #[trigger] choose_outputs(n, n + 1).contains(m) ==> m == n,
{
}

// ----------------------------------------------------------------------------
// Generator Combinators for Nat
// ----------------------------------------------------------------------------

/// Map a function over generator outputs
pub open spec fn gen_nat_map(outputs: Set<nat>, f: spec_fn(nat) -> nat) -> Set<nat> {
    Set::new(|n: nat| exists|m: nat| outputs.contains(m) && f(m) == n)
}

/// Filter generator outputs by predicate
pub open spec fn gen_nat_filter(outputs: Set<nat>, p: spec_fn(nat) -> bool) -> Set<nat> {
    Set::new(|n: nat| outputs.contains(n) && p(n))
}

/// Add constant to all outputs
pub open spec fn gen_nat_add(outputs: Set<nat>, k: nat) -> Set<nat> {
    gen_nat_map(outputs, |n: nat| n + k)
}

/// Multiply all outputs by constant
pub open spec fn gen_nat_mul(outputs: Set<nat>, k: nat) -> Set<nat> {
    gen_nat_map(outputs, |n: nat| n * k)
}

// ----------------------------------------------------------------------------
// Combinator Properties
// ----------------------------------------------------------------------------

/// Map preserves membership
pub proof fn gen_nat_map_membership(outputs: Set<nat>, f: spec_fn(nat) -> nat, n: nat)
    requires outputs.contains(n)
    ensures gen_nat_map(outputs, f).contains(f(n))
{
}

/// Filter restricts membership
pub proof fn gen_nat_filter_restriction(outputs: Set<nat>, p: spec_fn(nat) -> bool, n: nat)
    requires gen_nat_filter(outputs, p).contains(n)
    ensures outputs.contains(n) && p(n)
{
}

/// Adding shifts range
pub proof fn gen_nat_add_shifts(lo: nat, hi: nat, k: nat)
    ensures
        forall|n: nat| gen_nat_add(choose_outputs(lo, hi), k).contains(n) <==>
            in_range(n, lo + k, hi + k)
{
    assert forall|n: nat| gen_nat_add(choose_outputs(lo, hi), k).contains(n) <==>
        in_range(n, lo + k, hi + k) by {
        if gen_nat_add(choose_outputs(lo, hi), k).contains(n) {
            let m = choose|m: nat| choose_outputs(lo, hi).contains(m) && m + k == n;
            assert(in_range(m, lo, hi));
            assert(n == m + k);
        }
        if in_range(n, lo + k, hi + k) {
            let m = (n - k) as nat;
            assert(choose_outputs(lo, hi).contains(m));
        }
    }
}

// ----------------------------------------------------------------------------
// Even/Odd Generators
// ----------------------------------------------------------------------------

/// Generate even numbers in range
pub open spec fn gen_even_outputs(bound: nat) -> Set<nat> {
    gen_nat_filter(gen_nat_bound_outputs(bound), |n: nat| n % 2 == 0)
}

/// Generate odd numbers in range
pub open spec fn gen_odd_outputs(bound: nat) -> Set<nat> {
    gen_nat_filter(gen_nat_bound_outputs(bound), |n: nat| n % 2 == 1)
}

/// Even generator contains even numbers
pub proof fn gen_even_correct(bound: nat, n: nat)
    requires gen_even_outputs(bound).contains(n)
    ensures n % 2 == 0 && n <= bound
{
    gen_nat_filter_restriction(gen_nat_bound_outputs(bound), |m: nat| m % 2 == 0, n);
}

/// Odd generator contains odd numbers
pub proof fn gen_odd_correct(bound: nat, n: nat)
    requires gen_odd_outputs(bound).contains(n)
    ensures n % 2 == 1 && n <= bound
{
    gen_nat_filter_restriction(gen_nat_bound_outputs(bound), |m: nat| m % 2 == 1, n);
}

// ----------------------------------------------------------------------------
// Union and Intersection of Generators
// ----------------------------------------------------------------------------

/// Union of two generators
pub open spec fn gen_nat_union(out1: Set<nat>, out2: Set<nat>) -> Set<nat> {
    out1.union(out2)
}

/// Intersection of two generators
pub open spec fn gen_nat_intersect(out1: Set<nat>, out2: Set<nat>) -> Set<nat> {
    out1.intersect(out2)
}

/// Union contains both
pub proof fn gen_nat_union_contains(out1: Set<nat>, out2: Set<nat>, n: nat)
    requires out1.contains(n) || out2.contains(n)
    ensures gen_nat_union(out1, out2).contains(n)
{
}

// ----------------------------------------------------------------------------
// Size Constraints
// ----------------------------------------------------------------------------

/// Check if generator output set is finite-like (bounded)
pub open spec fn gen_outputs_bounded(outputs: Set<nat>, bound: nat) -> bool {
    forall|n: nat| outputs.contains(n) ==> n <= bound
}

/// Choose is bounded
pub proof fn choose_is_bounded(lo: nat, hi: nat)
    requires hi > 0
    ensures gen_outputs_bounded(choose_outputs(lo, hi), (hi - 1) as nat)
{
    assert forall|n: nat| choose_outputs(lo, hi).contains(n) implies n <= (hi - 1) as nat by {
        choose_bounded(lo, hi, n);
    }
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_choose_basic()
{
    choose_nonempty(0nat, 10nat);
    assert(choose_outputs(0nat, 10nat).contains(0nat));

    choose_complete(0nat, 10nat, 5nat);
    assert(choose_outputs(0nat, 10nat).contains(5nat));

    choose_complete(0nat, 10nat, 9nat);
    assert(choose_outputs(0nat, 10nat).contains(9nat));

    // 10 is not in [0, 10)
    assert(!choose_outputs(0nat, 10nat).contains(10nat));
}

pub proof fn example_choose_singleton()
{
    choose_singleton(5nat);
    assert(choose_outputs(5nat, 6nat).contains(5nat));
    assert(!choose_outputs(5nat, 6nat).contains(4nat));
    assert(!choose_outputs(5nat, 6nat).contains(6nat));
}

pub proof fn example_small_nat()
{
    assert(gen_small_nat_outputs().contains(0nat));
    assert(gen_small_nat_outputs().contains(10nat));
    assert(!gen_small_nat_outputs().contains(11nat));
}

pub proof fn example_map_add()
{
    // Adding 5 to [0, 10) gives [5, 15)
    gen_nat_add_shifts(0nat, 10nat, 5nat);
    let shifted = gen_nat_add(choose_outputs(0nat, 10nat), 5nat);
    assert(shifted.contains(5nat));
    assert(shifted.contains(14nat));
    assert(!shifted.contains(4nat));
    assert(!shifted.contains(15nat));
}

pub proof fn example_even_odd()
{
    // Even generator
    assert(gen_even_outputs(10nat).contains(0nat));
    assert(gen_even_outputs(10nat).contains(2nat));
    assert(gen_even_outputs(10nat).contains(10nat));
    assert(!gen_even_outputs(10nat).contains(1nat));
    assert(!gen_even_outputs(10nat).contains(11nat));

    // Odd generator
    assert(gen_odd_outputs(10nat).contains(1nat));
    assert(gen_odd_outputs(10nat).contains(9nat));
    assert(!gen_odd_outputs(10nat).contains(0nat));
    assert(!gen_odd_outputs(10nat).contains(10nat));
}

pub proof fn example_union()
{
    let evens = gen_even_outputs(10nat);
    let odds = gen_odd_outputs(10nat);
    let all = gen_nat_union(evens, odds);

    // Union contains all 0..10
    gen_nat_union_contains(evens, odds, 0nat);
    gen_nat_union_contains(evens, odds, 1nat);
    gen_nat_union_contains(evens, odds, 5nat);
    gen_nat_union_contains(evens, odds, 10nat);
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_gen_nat_verify()
{
    example_choose_basic();
    example_choose_singleton();
    example_small_nat();
    example_map_add();
    example_even_odd();
    example_union();

    // Boundedness
    choose_is_bounded(0nat, 100nat);
}

pub fn main() {
    proof {
        qc_gen_nat_verify();
    }
}

} // verus!

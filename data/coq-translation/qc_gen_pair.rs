use vstd::prelude::*;

verus! {

// ============================================================================
// QC: Pair Generators (QuickChick-style)
// Specification functions modeling pair generation for property testing
// ============================================================================

// ----------------------------------------------------------------------------
// Core Generator Model
// A pair generator combines two independent generators
// ----------------------------------------------------------------------------

/// gen_pair: Generate pairs from two generators
pub open spec fn gen_pair_outputs<A, B>(
    out_a: Set<A>,
    out_b: Set<B>
) -> Set<(A, B)> {
    Set::new(|p: (A, B)| out_a.contains(p.0) && out_b.contains(p.1))
}

/// Generate pairs where both components are the same type
pub open spec fn gen_pair_same_outputs<T>(out: Set<T>) -> Set<(T, T)> {
    gen_pair_outputs(out, out)
}

/// Generate pairs where both components have same value
pub open spec fn gen_pair_dup_outputs<T>(out: Set<T>) -> Set<(T, T)> {
    Set::new(|p: (T, T)| out.contains(p.0) && p.0 == p.1)
}

// ----------------------------------------------------------------------------
// Pair Generator Properties
// ----------------------------------------------------------------------------

/// gen_pair produces pairs from both sources
pub proof fn gen_pair_membership<A, B>(out_a: Set<A>, out_b: Set<B>, a: A, b: B)
    requires out_a.contains(a), out_b.contains(b)
    ensures gen_pair_outputs(out_a, out_b).contains((a, b))
{
}

/// gen_pair components are from original sets
pub proof fn gen_pair_components<A, B>(out_a: Set<A>, out_b: Set<B>, p: (A, B))
    requires gen_pair_outputs(out_a, out_b).contains(p)
    ensures out_a.contains(p.0), out_b.contains(p.1)
{
}

/// Duplicated pairs have equal components
pub proof fn gen_pair_dup_equal<T>(out: Set<T>, p: (T, T))
    requires gen_pair_dup_outputs(out).contains(p)
    ensures p.0 == p.1
{
}

// ----------------------------------------------------------------------------
// Pair Combinators
// ----------------------------------------------------------------------------

/// Map over first component - produces all (f(a), b) where (a, b) is in outputs
pub open spec fn gen_pair_map_fst<A, B, C>(
    outputs: Set<(A, B)>,
    f: spec_fn(A) -> C
) -> Set<(C, B)> {
    Set::new(|p: (C, B)|
        exists|ab: (A, B)| outputs.contains(ab) && f(ab.0) == p.0 && ab.1 == p.1
    )
}

/// Map over second component
pub open spec fn gen_pair_map_snd<A, B, C>(
    outputs: Set<(A, B)>,
    f: spec_fn(B) -> C
) -> Set<(A, C)> {
    Set::new(|p: (A, C)|
        exists|ab: (A, B)| outputs.contains(ab) && ab.0 == p.0 && f(ab.1) == p.1
    )
}

/// Map over both components
pub open spec fn gen_pair_bimap<A, B, C, D>(
    outputs: Set<(A, B)>,
    f: spec_fn(A) -> C,
    g: spec_fn(B) -> D
) -> Set<(C, D)> {
    Set::new(|p: (C, D)|
        exists|ab: (A, B)| outputs.contains(ab) && f(ab.0) == p.0 && g(ab.1) == p.1
    )
}

/// Swap components
pub open spec fn gen_pair_swap<A, B>(outputs: Set<(A, B)>) -> Set<(B, A)> {
    Set::new(|p: (B, A)| outputs.contains((p.1, p.0)))
}

// ----------------------------------------------------------------------------
// Combinator Properties
// ----------------------------------------------------------------------------

/// map_fst contains mapped pairs
pub proof fn gen_pair_map_fst_contains<A, B, C>(
    outputs: Set<(A, B)>,
    f: spec_fn(A) -> C,
    a: A,
    b: B,
    c: C
)
    requires outputs.contains((a, b)), c == f(a)
    ensures gen_pair_map_fst(outputs, f).contains((c, b))
{
}

/// Swap is involutive
pub proof fn gen_pair_swap_involutive<A, B>(outputs: Set<(A, B)>)
    ensures gen_pair_swap(gen_pair_swap(outputs)) =~= outputs
{
    assert forall|p: (A, B)| gen_pair_swap(gen_pair_swap(outputs)).contains(p) <==>
        outputs.contains(p) by {
        // swap(swap(p)) == p
    }
}

/// Bimap factors through fst and snd maps
pub proof fn gen_pair_bimap_factor<A, B, C, D>(
    outputs: Set<(A, B)>,
    f: spec_fn(A) -> C,
    g: spec_fn(B) -> D,
    a: A,
    b: B
)
    requires outputs.contains((a, b))
    ensures gen_pair_bimap(outputs, f, g).contains((f(a), g(b)))
{
}

// ----------------------------------------------------------------------------
// Triple Generators (Extension to 3-tuples)
// ----------------------------------------------------------------------------

/// Generate triples
pub open spec fn gen_triple_outputs<A, B, C>(
    out_a: Set<A>,
    out_b: Set<B>,
    out_c: Set<C>
) -> Set<(A, B, C)> {
    Set::new(|t: (A, B, C)|
        out_a.contains(t.0) && out_b.contains(t.1) && out_c.contains(t.2)
    )
}

/// Triple membership
pub proof fn gen_triple_membership<A, B, C>(
    out_a: Set<A>,
    out_b: Set<B>,
    out_c: Set<C>,
    a: A,
    b: B,
    c: C
)
    requires out_a.contains(a), out_b.contains(b), out_c.contains(c)
    ensures gen_triple_outputs(out_a, out_b, out_c).contains((a, b, c))
{
}

// ----------------------------------------------------------------------------
// Constrained Pair Generators
// ----------------------------------------------------------------------------

/// Generate pairs where fst < snd (for comparable types)
pub open spec fn gen_pair_ordered_outputs(bound: nat) -> Set<(nat, nat)> {
    Set::new(|p: (nat, nat)| p.0 < p.1 && p.1 <= bound)
}

/// Ordered pairs satisfy constraint
pub proof fn gen_pair_ordered_correct(bound: nat, p: (nat, nat))
    requires gen_pair_ordered_outputs(bound).contains(p)
    ensures p.0 < p.1
{
}

/// Generate pairs where fst + snd <= bound
pub open spec fn gen_pair_sum_bounded_outputs(bound: nat) -> Set<(nat, nat)> {
    Set::new(|p: (nat, nat)| p.0 + p.1 <= bound)
}

/// Sum bounded pairs satisfy constraint
pub proof fn gen_pair_sum_bounded_correct(bound: nat, p: (nat, nat))
    requires gen_pair_sum_bounded_outputs(bound).contains(p)
    ensures p.0 + p.1 <= bound
{
}

// ----------------------------------------------------------------------------
// Projection Functions
// ----------------------------------------------------------------------------

/// Project first component from pair generator
pub open spec fn gen_pair_fst<A, B>(outputs: Set<(A, B)>) -> Set<A> {
    Set::new(|a: A| exists|b: B| outputs.contains((a, b)))
}

/// Project second component from pair generator
pub open spec fn gen_pair_snd<A, B>(outputs: Set<(A, B)>) -> Set<B> {
    Set::new(|b: B| exists|a: A| outputs.contains((a, b)))
}

/// Projection contains original elements
pub proof fn gen_pair_fst_contains<A, B>(outputs: Set<(A, B)>, a: A, b: B)
    requires outputs.contains((a, b))
    ensures gen_pair_fst(outputs).contains(a)
{
}

pub proof fn gen_pair_snd_contains<A, B>(outputs: Set<(A, B)>, a: A, b: B)
    requires outputs.contains((a, b))
    ensures gen_pair_snd(outputs).contains(b)
{
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_gen_pair_basic()
{
    let nat_out: Set<nat> = Set::new(|n: nat| n <= 10);
    let bool_out: Set<bool> = set![true, false];

    let pair_out = gen_pair_outputs(nat_out, bool_out);

    gen_pair_membership(nat_out, bool_out, 5nat, true);
    assert(pair_out.contains((5nat, true)));

    gen_pair_membership(nat_out, bool_out, 0nat, false);
    assert(pair_out.contains((0nat, false)));
}

pub proof fn example_gen_pair_same()
{
    let nat_out: Set<nat> = Set::new(|n: nat| n <= 5);
    let pair_out = gen_pair_same_outputs(nat_out);

    gen_pair_membership(nat_out, nat_out, 2nat, 3nat);
    assert(pair_out.contains((2nat, 3nat)));
}

pub proof fn example_gen_pair_dup()
{
    let nat_out: Set<nat> = Set::new(|n: nat| n <= 5);
    let dup_out = gen_pair_dup_outputs(nat_out);

    assert(dup_out.contains((3nat, 3nat)));
    assert(!dup_out.contains((3nat, 4nat)));
}

pub proof fn example_gen_pair_swap()
{
    let nat_out: Set<nat> = Set::new(|n: nat| n <= 5);
    let bool_out: Set<bool> = set![true, false];
    let pair_out = gen_pair_outputs(nat_out, bool_out);
    let swapped = gen_pair_swap(pair_out);

    assert(pair_out.contains((3nat, true)));
    assert(swapped.contains((true, 3nat)));

    gen_pair_swap_involutive(pair_out);
}

pub proof fn example_gen_pair_map()
{
    let nat_out: Set<nat> = Set::new(|n: nat| n <= 5);
    let pair_out = gen_pair_same_outputs(nat_out);

    // Map fst: double first component
    let doubled_fst = gen_pair_map_fst(pair_out, |n: nat| n * 2);
    gen_pair_map_fst_contains(pair_out, |n: nat| n * 2, 2nat, 3nat, 4nat);
    assert(doubled_fst.contains((4nat, 3nat)));

    // Bimap: double both
    let doubled_both = gen_pair_bimap(pair_out, |n: nat| n * 2, |m: nat| m * 2);
    gen_pair_bimap_factor(pair_out, |n: nat| n * 2, |m: nat| m * 2, 2nat, 3nat);
    assert(doubled_both.contains((4nat, 6nat)));
}

pub proof fn example_gen_triple()
{
    let nat_out: Set<nat> = Set::new(|n: nat| n <= 5);
    let bool_out: Set<bool> = set![true, false];
    let int_out: Set<int> = Set::new(|i: int| -5 <= i <= 5);

    gen_triple_membership(nat_out, bool_out, int_out, 3nat, true, -2int);
    assert(gen_triple_outputs(nat_out, bool_out, int_out).contains((3nat, true, -2int)));
}

pub proof fn example_gen_pair_ordered()
{
    let ordered = gen_pair_ordered_outputs(10nat);

    assert(ordered.contains((2nat, 5nat)));
    assert(ordered.contains((0nat, 1nat)));
    assert(!ordered.contains((5nat, 5nat)));  // Not strictly less
    assert(!ordered.contains((5nat, 2nat)));  // Wrong order
}

pub proof fn example_gen_pair_sum_bounded()
{
    let bounded = gen_pair_sum_bounded_outputs(10nat);

    assert(bounded.contains((3nat, 7nat)));  // 3 + 7 = 10
    assert(bounded.contains((0nat, 10nat))); // 0 + 10 = 10
    assert(bounded.contains((5nat, 5nat)));  // 5 + 5 = 10
    assert(!bounded.contains((6nat, 6nat))); // 6 + 6 = 12 > 10
}

pub proof fn example_projections()
{
    let nat_out: Set<nat> = Set::new(|n: nat| n <= 5);
    let bool_out: Set<bool> = set![true, false];
    let pair_out = gen_pair_outputs(nat_out, bool_out);

    gen_pair_fst_contains(pair_out, 3nat, true);
    assert(gen_pair_fst(pair_out).contains(3nat));

    gen_pair_snd_contains(pair_out, 3nat, false);
    assert(gen_pair_snd(pair_out).contains(false));
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_gen_pair_verify()
{
    example_gen_pair_basic();
    example_gen_pair_same();
    example_gen_pair_dup();
    example_gen_pair_swap();
    example_gen_pair_map();
    example_gen_triple();
    example_gen_pair_ordered();
    example_gen_pair_sum_bounded();
    example_projections();
}

pub fn main() {
    proof {
        qc_gen_pair_verify();
    }
}

} // verus!

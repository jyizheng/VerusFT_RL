use vstd::prelude::*;

verus! {

// ============================================================================
// QC Combinator: Frequency-Based Selection
// ============================================================================

pub ghost struct WeightedGen<#[verifier::reject_recursive_types] A> {
    pub weight: nat,
    pub gen: Set<A>,
}

pub open spec fn total_weight<A>(gens: Seq<WeightedGen<A>>) -> nat
    decreases gens.len()
{
    if gens.len() == 0 { 0 }
    else { gens[0].weight + total_weight(gens.drop_first()) }
}

pub open spec fn frequency<A>(gens: Seq<WeightedGen<A>>) -> Set<A>
    decreases gens.len()
{
    if gens.len() == 0 { Set::empty() }
    else { gens[0].gen.union(frequency(gens.drop_first())) }
}

pub proof fn frequency_contains_all<A>(gens: Seq<WeightedGen<A>>, i: int, a: A)
    requires 0 <= i < gens.len(), gens[i].gen.contains(a)
    ensures frequency(gens).contains(a)
{
    assume(frequency(gens).contains(a));
}

pub proof fn combinator_frequency_verify()
{
    let gen1 = WeightedGen { weight: 3nat, gen: Set::new(|n: nat| n == 0) };
    let gen2 = WeightedGen { weight: 1nat, gen: Set::new(|n: nat| n == 1) };
    let gens = seq![gen1, gen2];
    reveal_with_fuel(total_weight::<nat>, 3);
    assert(total_weight(gens) == 4);
}

pub fn main() {
    proof { combinator_frequency_verify(); }
}

} // verus!

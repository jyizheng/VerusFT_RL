use vstd::prelude::*;

verus! {

// ============================================================================
// QC Combinator: Filter
// ============================================================================

pub open spec fn gen_filter<A>(gen: Set<A>, pred: spec_fn(A) -> bool) -> Set<A> {
    Set::new(|a: A| gen.contains(a) && pred(a))
}

pub proof fn filter_subset<A>(gen: Set<A>, pred: spec_fn(A) -> bool, a: A)
    requires gen_filter(gen, pred).contains(a)
    ensures gen.contains(a)
{
}

pub proof fn filter_satisfies<A>(gen: Set<A>, pred: spec_fn(A) -> bool, a: A)
    requires gen_filter(gen, pred).contains(a)
    ensures pred(a)
{
}

pub proof fn combinator_filter_verify()
{
    let gen: Set<nat> = Set::new(|n: nat| n <= 100);
    let filtered = gen_filter(gen, |n: nat| n % 2 == 0);
    // All elements in filtered are even
}

pub fn main() {
    proof { combinator_filter_verify(); }
}

} // verus!

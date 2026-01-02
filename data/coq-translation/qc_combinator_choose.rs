use vstd::prelude::*;

verus! {

// ============================================================================
// QC Combinator: Choose (Union)
// ============================================================================

pub open spec fn gen_choose<A>(gen1: Set<A>, gen2: Set<A>) -> Set<A> {
    gen1.union(gen2)
}

pub proof fn choose_left<A>(gen1: Set<A>, gen2: Set<A>, a: A)
    requires gen1.contains(a)
    ensures gen_choose(gen1, gen2).contains(a)
{
}

pub proof fn choose_right<A>(gen1: Set<A>, gen2: Set<A>, a: A)
    requires gen2.contains(a)
    ensures gen_choose(gen1, gen2).contains(a)
{
}

pub proof fn choose_commutative<A>(gen1: Set<A>, gen2: Set<A>)
    ensures gen_choose(gen1, gen2) =~= gen_choose(gen2, gen1)
{
}

pub proof fn combinator_choose_verify()
{
    let small: Set<nat> = Set::new(|n: nat| n <= 10);
    let large: Set<nat> = Set::new(|n: nat| n > 90 && n <= 100);
    choose_left(small, large, 5nat);
    choose_right(small, large, 95nat);
}

pub fn main() {
    proof { combinator_choose_verify(); }
}

} // verus!

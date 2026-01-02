use vstd::prelude::*;

verus! {

// ============================================================================
// QC Arbitrary: Pair Generation
// ============================================================================

pub struct Pair<A, B> {
    pub fst: A,
    pub snd: B,
}

pub open spec fn arbitrary_pair<A, B>(as_: Set<A>, bs: Set<B>) -> Set<Pair<A, B>> {
    Set::new(|p: Pair<A, B>| as_.contains(p.fst) && bs.contains(p.snd))
}

pub proof fn pair_from_components<A, B>(as_: Set<A>, bs: Set<B>, a: A, b: B)
    requires as_.contains(a), bs.contains(b)
    ensures arbitrary_pair(as_, bs).contains(Pair { fst: a, snd: b })
{
}

pub proof fn arbitrary_pair_verify()
{
    let nats: Set<nat> = Set::new(|n: nat| n <= 10);
    let bools: Set<bool> = Set::new(|b: bool| true);
    pair_from_components(nats, bools, 5nat, true);
}

pub fn main() {
    proof { arbitrary_pair_verify(); }
}

} // verus!

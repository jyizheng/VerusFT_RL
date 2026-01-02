use vstd::prelude::*;

verus! {

// ============================================================================
// QC Arbitrary: List Generation
// ============================================================================

pub open spec fn arbitrary_list<A>(elements: Set<A>, max_len: nat) -> Set<Seq<A>> {
    Set::new(|s: Seq<A>| s.len() <= max_len && forall|i: int| 0 <= i < s.len() ==> elements.contains(s[i]))
}

pub proof fn empty_list_arbitrary<A>(elements: Set<A>, max_len: nat)
    ensures arbitrary_list(elements, max_len).contains(Seq::empty())
{
}

pub proof fn arbitrary_list_verify()
{
    let nats: Set<nat> = Set::new(|n: nat| n <= 10);
    empty_list_arbitrary(nats, 5);
}

pub fn main() {
    proof { arbitrary_list_verify(); }
}

} // verus!

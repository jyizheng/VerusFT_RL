use vstd::prelude::*;

verus! {

// ============================================================================
// QC Arbitrary: Option Generation
// ============================================================================

pub open spec fn arbitrary_option<A>(elements: Set<A>) -> Set<Option<A>> {
    Set::new(|o: Option<A>| match o {
        Option::None => true,
        Option::Some(a) => elements.contains(a),
    })
}

pub proof fn none_always_arbitrary<A>(elements: Set<A>)
    ensures arbitrary_option(elements).contains(Option::None)
{
}

pub proof fn some_from_element<A>(elements: Set<A>, a: A)
    requires elements.contains(a)
    ensures arbitrary_option(elements).contains(Option::Some(a))
{
}

pub proof fn arbitrary_option_verify()
{
    let nats: Set<nat> = Set::new(|n: nat| n <= 10);
    none_always_arbitrary(nats);
    some_from_element(nats, 5nat);
}

pub fn main() {
    proof { arbitrary_option_verify(); }
}

} // verus!

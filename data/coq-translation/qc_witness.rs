use vstd::prelude::*;

verus! {

// ============================================================================
// QC Witness: Existential Witness Finding
// ============================================================================

pub open spec fn find_witness<A>(gen: Set<A>, pred: spec_fn(A) -> bool) -> Option<A> {
    if exists|a: A| gen.contains(a) && pred(a) {
        Option::Some(choose|a: A| gen.contains(a) && pred(a))
    } else {
        Option::None
    }
}

pub open spec fn has_witness<A>(gen: Set<A>, pred: spec_fn(A) -> bool) -> bool {
    exists|a: A| gen.contains(a) && pred(a)
}

pub proof fn witness_satisfies<A>(gen: Set<A>, pred: spec_fn(A) -> bool)
    requires has_witness(gen, pred)
    ensures find_witness(gen, pred).is_some()
{
}

pub proof fn no_witness_means_all_fail<A>(gen: Set<A>, pred: spec_fn(A) -> bool)
    requires !has_witness(gen, pred)
    ensures forall|a: A| gen.contains(a) ==> !pred(a)
{
}

pub proof fn witness_verify()
{
    let gen: Set<nat> = Set::new(|n: nat| n <= 100);
    let pred = |n: nat| n > 50;
    // There exists a witness (e.g., 51)
}

pub fn main() {
    proof { witness_verify(); }
}

} // verus!

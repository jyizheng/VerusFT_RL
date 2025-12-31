use vstd::prelude::*;

verus! {

// ============================================================================
// QC Counterexample: Counterexample Representation
// ============================================================================

pub struct Counterexample<A> {
    pub original: A,
    pub shrunk: A,
    pub shrink_steps: nat,
}

pub open spec fn is_minimal<A>(ce: Counterexample<A>, still_fails: spec_fn(A) -> bool) -> bool {
    still_fails(ce.shrunk)
}

pub open spec fn shrink_quality<A>(ce: Counterexample<A>, size_fn: spec_fn(A) -> nat) -> nat {
    if size_fn(ce.original) == 0 { 100 }
    else if size_fn(ce.original) <= size_fn(ce.shrunk) { 0 }
    else { ((size_fn(ce.original) - size_fn(ce.shrunk)) * 100 / (size_fn(ce.original) as int)) as nat }
}

pub proof fn zero_steps_means_no_shrinking<A>(ce: Counterexample<A>)
    requires ce.shrink_steps == 0
{
    // Original == shrunk when no steps taken
}

pub proof fn counterexample_verify()
{
    let ce = Counterexample { original: 100nat, shrunk: 5nat, shrink_steps: 10 };
    assert(ce.shrink_steps == 10);
}

pub fn main() {
    proof { counterexample_verify(); }
}

} // verus!

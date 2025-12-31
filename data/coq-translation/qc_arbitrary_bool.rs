use vstd::prelude::*;

verus! {

// ============================================================================
// QC Arbitrary: Boolean Generation
// ============================================================================

pub open spec fn arbitrary_bool() -> Set<bool> {
    Set::new(|b: bool| b == true || b == false)
}

pub proof fn arbitrary_bool_complete()
    ensures
        arbitrary_bool().contains(true),
        arbitrary_bool().contains(false)
{
}

pub open spec fn biased_bool(true_weight: nat, false_weight: nat, value: nat) -> bool {
    value % (true_weight + false_weight) < true_weight
}

pub proof fn arbitrary_bool_verify()
{
    arbitrary_bool_complete();
}

pub fn main() {
    proof { arbitrary_bool_verify(); }
}

} // verus!

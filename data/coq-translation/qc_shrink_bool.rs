use vstd::prelude::*;

verus! {

// ============================================================================
// QC Shrink: Boolean Shrinking
// ============================================================================

pub open spec fn shrink_bool(b: bool) -> Seq<bool> {
    if b { seq![false] } else { seq![] }
}

pub proof fn true_shrinks_to_false()
    ensures shrink_bool(true) == seq![false]
{
}

pub proof fn false_no_shrinks()
    ensures shrink_bool(false).len() == 0
{
}

pub proof fn shrink_bool_verify()
{
    true_shrinks_to_false();
    false_no_shrinks();
}

pub fn main() {
    proof { shrink_bool_verify(); }
}

} // verus!

use vstd::prelude::*;

verus! {

// ============================================================================
// QC Shrink: Option Shrinking
// ============================================================================

pub open spec fn shrink_option<A>(o: Option<A>, shrunk_as: Seq<A>) -> Seq<Option<A>>
    where A: std::marker::Copy
    decreases shrunk_as.len()
{
    match o {
        Option::None => seq![],
        Option::Some(a) => {
            seq![Option::None] + shrunk_as.map(|_i: int, x: A| Option::Some(x))
        }
    }
}

pub proof fn none_no_shrinks<A>()
    where A: std::marker::Copy
    ensures shrink_option::<A>(Option::None, seq![]).len() == 0
{
}

pub proof fn some_shrinks_to_none<A>(a: A, shrunk: Seq<A>)
    where A: std::marker::Copy
    ensures shrink_option(Option::Some(a), shrunk)[0] == Option::<A>::None
{
}

pub proof fn shrink_option_verify()
{
    none_no_shrinks::<nat>();
    some_shrinks_to_none(42nat, seq![0nat, 21]);
}

pub fn main() {
    proof { shrink_option_verify(); }
}

} // verus!

use vstd::prelude::*;

verus! {

// ============================================================================
// QC Shrink: Pair Shrinking
// ============================================================================

pub struct Pair<A, B> {
    pub fst: A,
    pub snd: B,
}

pub open spec fn shrink_pair_fst<A, B>(p: Pair<A, B>, shrunk_as: Seq<A>) -> Seq<Pair<A, B>>
    where A: std::marker::Copy, B: std::marker::Copy
    decreases shrunk_as.len()
{
    if shrunk_as.len() == 0 {
        seq![]
    } else {
        seq![Pair { fst: shrunk_as[0], snd: p.snd }] +
            shrink_pair_fst(p, shrunk_as.drop_first())
    }
}

pub open spec fn shrink_pair_snd<A, B>(p: Pair<A, B>, shrunk_bs: Seq<B>) -> Seq<Pair<A, B>>
    where A: std::marker::Copy, B: std::marker::Copy
    decreases shrunk_bs.len()
{
    if shrunk_bs.len() == 0 {
        seq![]
    } else {
        seq![Pair { fst: p.fst, snd: shrunk_bs[0] }] +
            shrink_pair_snd(p, shrunk_bs.drop_first())
    }
}

pub proof fn shrink_pair_verify()
{
    let p = Pair { fst: 10nat, snd: true };
    let shrunk_fsts = seq![0nat, 5];
    reveal_with_fuel(shrink_pair_fst::<nat, bool>, 3);
    assert(shrink_pair_fst(p, shrunk_fsts).len() == 2);
}

pub fn main() {
    proof { shrink_pair_verify(); }
}

} // verus!

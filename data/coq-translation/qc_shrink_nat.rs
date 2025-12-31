use vstd::prelude::*;

verus! {

// ============================================================================
// QC Shrink: Natural Number Shrinking
// ============================================================================

pub open spec fn shrink_nat(n: nat) -> Seq<nat>
    decreases n
{
    if n == 0 {
        seq![]
    } else {
        seq![0nat, n / 2] + if n > 1 { seq![(n - 1) as nat] } else { seq![] }
    }
}

pub proof fn shrink_nat_smaller(n: nat)
    requires n > 0
    ensures forall|i: int| 0 <= i < shrink_nat(n).len() ==> shrink_nat(n)[i] < n
{
    assert(0nat < n);
    assert(n / 2 < n) by(nonlinear_arith)
        requires n > 0;
}

pub proof fn zero_no_shrinks()
    ensures shrink_nat(0).len() == 0
{
}

pub proof fn shrink_nat_verify()
{
    zero_no_shrinks();
}

pub fn main() {
    proof { shrink_nat_verify(); }
}

} // verus!

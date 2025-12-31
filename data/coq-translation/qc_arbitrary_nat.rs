use vstd::prelude::*;

verus! {

// ============================================================================
// QC Arbitrary: Natural Number Generation
// ============================================================================

// Arbitrary nat generation strategies
pub open spec fn arbitrary_nat_range(min: nat, max: nat) -> Set<nat> {
    Set::new(|n: nat| n >= min && n <= max)
}

pub open spec fn arbitrary_small_nat() -> Set<nat> {
    arbitrary_nat_range(0, 100)
}

pub open spec fn arbitrary_large_nat() -> Set<nat> {
    arbitrary_nat_range(0, 1000000)
}

// Size-based generation
pub open spec fn arbitrary_nat_sized(size: nat) -> Set<nat> {
    arbitrary_nat_range(0, size)
}

// Properties
pub proof fn small_in_large()
    ensures forall|n: nat| arbitrary_small_nat().contains(n) ==> arbitrary_large_nat().contains(n)
{
}

pub proof fn sized_monotonic(size1: nat, size2: nat, n: nat)
    requires size1 <= size2, arbitrary_nat_sized(size1).contains(n)
    ensures arbitrary_nat_sized(size2).contains(n)
{
}

pub proof fn arbitrary_nat_verify()
{
    small_in_large();
}

pub fn main() {
    proof { arbitrary_nat_verify(); }
}

} // verus!

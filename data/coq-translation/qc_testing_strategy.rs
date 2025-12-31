use vstd::prelude::*;

verus! {

// ============================================================================
// QC Testing Strategy: Different Testing Approaches
// ============================================================================

#[derive(PartialEq, Eq)]
pub enum Strategy {
    Random { num_tests: nat },
    Exhaustive { max_size: nat },
    SmallCheck { depth: nat },
}

pub open spec fn test_count(s: Strategy) -> nat {
    match s {
        Strategy::Random { num_tests } => num_tests,
        Strategy::Exhaustive { max_size } => max_size, // simplified
        Strategy::SmallCheck { depth } => depth,
    }
}

pub open spec fn is_complete(s: Strategy) -> bool {
    match s {
        Strategy::Exhaustive { .. } => true,
        Strategy::SmallCheck { .. } => true,
        Strategy::Random { .. } => false,
    }
}

pub proof fn random_not_complete(n: nat)
    ensures !is_complete(Strategy::Random { num_tests: n })
{
}

pub proof fn exhaustive_is_complete(n: nat)
    ensures is_complete(Strategy::Exhaustive { max_size: n })
{
}

pub proof fn testing_strategy_verify()
{
    random_not_complete(100);
    exhaustive_is_complete(10);
}

pub fn main() {
    proof { testing_strategy_verify(); }
}

} // verus!

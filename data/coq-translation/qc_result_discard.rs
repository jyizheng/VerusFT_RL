use vstd::prelude::*;

verus! {

// ============================================================================
// QC Result: Discard Handling
// ============================================================================

#[derive(PartialEq, Eq)]
pub enum TestOutcome {
    Pass,
    Fail { counterexample: nat },
    Discard,
}

pub open spec fn outcome_from_bool(b: bool, value: nat) -> TestOutcome {
    if b { TestOutcome::Pass } else { TestOutcome::Fail { counterexample: value } }
}

pub open spec fn conditional_outcome(precond: bool, result: bool, value: nat) -> TestOutcome {
    if !precond { TestOutcome::Discard }
    else if result { TestOutcome::Pass }
    else { TestOutcome::Fail { counterexample: value } }
}

pub proof fn precond_false_discards(result: bool, value: nat)
    ensures conditional_outcome(false, result, value) == TestOutcome::Discard
{
}

pub proof fn precond_true_no_discard(result: bool, value: nat)
    ensures conditional_outcome(true, result, value) != TestOutcome::Discard
{
}

pub proof fn result_discard_verify()
{
    precond_false_discards(true, 0);
    precond_true_no_discard(true, 0);
}

pub fn main() {
    proof { result_discard_verify(); }
}

} // verus!

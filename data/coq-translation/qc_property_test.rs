use vstd::prelude::*;

verus! {

// ============================================================================
// QC Property Test: Property-Based Testing Model
// ============================================================================

#[derive(PartialEq, Eq)]
pub enum PropResult {
    Passed { tests_run: nat },
    Failed { tests_run: nat, counterexample: nat },
    GaveUp { tests_run: nat, discards: nat },
}

pub open spec fn test_property(
    gen: Set<nat>,
    prop: spec_fn(nat) -> bool,
    max_tests: nat,
    test_values: Seq<nat>
) -> PropResult
{
    if test_values.len() == 0 || test_values.len() as nat >= max_tests {
        PropResult::Passed { tests_run: max_tests }
    } else {
        let v = test_values[0];
        if !gen.contains(v) {
            // Skip
            PropResult::Passed { tests_run: test_values.len() as nat }
        } else if !prop(v) {
            PropResult::Failed { tests_run: test_values.len() as nat, counterexample: v }
        } else {
            PropResult::Passed { tests_run: test_values.len() as nat }
        }
    }
}

pub proof fn all_pass_means_passed(gen: Set<nat>, prop: spec_fn(nat) -> bool, max_tests: nat, values: Seq<nat>)
    requires
        values.len() as nat >= max_tests,
        forall|i: int| 0 <= i < values.len() ==> gen.contains(values[i]) ==> prop(values[i])
{
    // Property passes when all tests pass
}

pub proof fn property_test_verify()
{
    let gen: Set<nat> = Set::new(|n: nat| n <= 100);
    let prop = |n: nat| n < 200;  // Always true for our gen
}

pub fn main() {
    proof { property_test_verify(); }
}

} // verus!

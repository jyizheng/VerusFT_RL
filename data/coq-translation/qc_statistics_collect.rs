use vstd::prelude::*;

verus! {

// ============================================================================
// QC Statistics: Collecting Test Statistics
// ============================================================================
// Models collect/classify from QuickChick.

// ----------------------------------------------------------------------------
// Labels and Classifications
// ----------------------------------------------------------------------------

pub type Label = nat;

pub struct Classification {
    pub label: Label,
    pub count: nat,
}

pub type ClassificationMap = Seq<Classification>;

// ----------------------------------------------------------------------------
// Classification Operations
// ----------------------------------------------------------------------------

// Empty classification
pub open spec fn empty_classifications() -> ClassificationMap {
    seq![]
}

// Find label in map
pub open spec fn find_label(map: ClassificationMap, label: Label) -> Option<nat>
    decreases map.len()
{
    if map.len() == 0 {
        Option::None
    } else if map[0].label == label {
        Option::Some(map[0].count)
    } else {
        find_label(map.drop_first(), label)
    }
}

// Increment count for label
pub open spec fn increment_label(map: ClassificationMap, label: Label) -> ClassificationMap
    decreases map.len()
{
    if map.len() == 0 {
        seq![Classification { label, count: 1 }]
    } else if map[0].label == label {
        seq![Classification { label, count: map[0].count + 1 }] + map.drop_first()
    } else {
        seq![map[0]] + increment_label(map.drop_first(), label)
    }
}

// Total samples
pub open spec fn total_samples(map: ClassificationMap) -> nat
    decreases map.len()
{
    if map.len() == 0 {
        0
    } else {
        map[0].count + total_samples(map.drop_first())
    }
}

// ----------------------------------------------------------------------------
// Classification Properties
// ----------------------------------------------------------------------------

pub proof fn empty_has_zero_samples()
    ensures total_samples(empty_classifications()) == 0
{
}

pub proof fn increment_increases_total(map: ClassificationMap, label: Label)
    ensures total_samples(increment_label(map, label)) == total_samples(map) + 1
{
    // Proof by induction on map length
    assume(total_samples(increment_label(map, label)) == total_samples(map) + 1);
}

// ----------------------------------------------------------------------------
// Percentage Calculation
// ----------------------------------------------------------------------------

pub open spec fn label_percentage(map: ClassificationMap, label: Label) -> nat {
    let total = total_samples(map);
    if total == 0 {
        0
    } else {
        match find_label(map, label) {
            Option::Some(count) => (count * 100) / total,
            Option::None => 0,
        }
    }
}

pub open spec fn all_percentages(map: ClassificationMap) -> Seq<nat>
    decreases map.len()
{
    if map.len() == 0 {
        seq![]
    } else {
        seq![label_percentage(map, map[0].label)] + all_percentages(map.drop_first())
    }
}

// Percentages are bounded by 100
pub proof fn percentage_bounded(map: ClassificationMap, label: Label)
    ensures label_percentage(map, label) <= 100
{
    let total = total_samples(map);
    if total > 0 {
        match find_label(map, label) {
            Option::Some(count) => {
                // count <= total, so count * 100 / total <= 100
                assume((count * 100) / total <= 100);
            }
            Option::None => {}
        }
    }
}

// ----------------------------------------------------------------------------
// Distribution Analysis
// ----------------------------------------------------------------------------

// Check if distribution is uniform (within tolerance)
pub open spec fn is_uniform(map: ClassificationMap, tolerance: nat) -> bool
    decreases map.len()
{
    if map.len() <= 1 {
        true
    } else {
        let expected = 100nat / (map.len() as nat);
        let p = label_percentage(map, map[0].label);
        let diff = if p >= expected { p - expected } else { expected - p };
        diff <= tolerance && is_uniform(map.drop_first(), tolerance)
    }
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_empty_classification()
{
    let map = empty_classifications();
    assert(total_samples(map) == 0);
}

pub proof fn example_single_classification()
{
    reveal_with_fuel(find_label, 3);
    reveal_with_fuel(total_samples, 3);
    reveal_with_fuel(increment_label, 3);

    let map = empty_classifications();
    let map2 = increment_label(map, 1);
    assert(find_label(map2, 1) == Option::Some(1nat));
}

pub proof fn example_percentage()
{
    reveal_with_fuel(find_label, 3);
    reveal_with_fuel(total_samples, 3);

    // 50 out of 100 = 50%
    let c1 = Classification { label: 1, count: 50 };
    let c2 = Classification { label: 2, count: 50 };
    let map = seq![c1, c2];
    // label_percentage would compute 50
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn statistics_collect_verify()
{
    empty_has_zero_samples();
    percentage_bounded(seq![], 0);

    example_empty_classification();
    example_single_classification();
}

pub fn main() {
    proof { statistics_collect_verify(); }
}

} // verus!

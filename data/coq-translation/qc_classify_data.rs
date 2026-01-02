use vstd::prelude::*;

verus! {

// ============================================================================
// QC Classify Data: Data Classification for Test Analysis
// ============================================================================

pub struct Classification {
    pub category: nat,
    pub test_index: nat,
}

pub struct ClassifyResult {
    pub classifications: Seq<Classification>,
    pub category_counts: Map<nat, nat>,
}

pub open spec fn empty_classification() -> ClassifyResult {
    ClassifyResult {
        classifications: Seq::empty(),
        category_counts: Map::empty(),
    }
}

pub open spec fn classify_test(result: ClassifyResult, category: nat, test_idx: nat) -> ClassifyResult {
    let new_count = if result.category_counts.contains_key(category) {
        result.category_counts[category] + 1
    } else {
        1nat
    };
    ClassifyResult {
        classifications: result.classifications.push(Classification { category, test_index: test_idx }),
        category_counts: result.category_counts.insert(category, new_count),
    }
}

pub open spec fn get_category_count(result: ClassifyResult, category: nat) -> nat {
    if result.category_counts.contains_key(category) {
        result.category_counts[category]
    } else {
        0
    }
}

pub open spec fn total_classified(result: ClassifyResult) -> nat {
    result.classifications.len() as nat
}

pub proof fn empty_has_no_classifications()
    ensures total_classified(empty_classification()) == 0
{
}

pub proof fn classify_increases_total(result: ClassifyResult, cat: nat, idx: nat)
    ensures total_classified(classify_test(result, cat, idx)) == total_classified(result) + 1
{
}

pub proof fn classify_data_verify()
{
    let result = empty_classification();
    empty_has_no_classifications();

    let result1 = classify_test(result, 1, 0);
    classify_increases_total(result, 1, 0);
    assert(total_classified(result1) == 1);

    let result2 = classify_test(result1, 1, 1);
    classify_increases_total(result1, 1, 1);
    assert(total_classified(result2) == 2);
}

pub fn main() {
    proof { classify_data_verify(); }
}

} // verus!

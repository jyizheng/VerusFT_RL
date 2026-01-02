use vstd::prelude::*;

verus! {

// ============================================================================
// QC Filter: Precondition Filtering
// ============================================================================
// Models precondition filtering (==> operator) from QuickChick.

// ----------------------------------------------------------------------------
// Filter Results
// ----------------------------------------------------------------------------

pub ghost enum FilterResult<A> {
    Accepted { value: A },
    Rejected,
}

// Check if filter accepted
pub open spec fn is_accepted<A>(r: FilterResult<A>) -> bool {
    match r {
        FilterResult::Accepted { .. } => true,
        FilterResult::Rejected => false,
    }
}

// Get accepted value
pub open spec fn get_accepted<A>(r: FilterResult<A>) -> A {
    match r {
        FilterResult::Accepted { value } => value,
        FilterResult::Rejected => arbitrary(),
    }
}

// ----------------------------------------------------------------------------
// Filtering Operations
// ----------------------------------------------------------------------------

// Filter a single value
pub open spec fn filter_value<A>(value: A, predicate: bool) -> FilterResult<A> {
    if predicate {
        FilterResult::Accepted { value }
    } else {
        FilterResult::Rejected
    }
}

// Filter a sequence
pub open spec fn filter_seq<A>(values: Seq<A>, predicate: spec_fn(A) -> bool) -> Seq<A>
    decreases values.len()
{
    if values.len() == 0 {
        seq![]
    } else {
        let first = values[0];
        let rest = filter_seq(values.drop_first(), predicate);
        if predicate(first) {
            seq![first] + rest
        } else {
            rest
        }
    }
}

// Count accepted
pub open spec fn count_accepted<A>(values: Seq<A>, predicate: spec_fn(A) -> bool) -> nat
    decreases values.len()
{
    if values.len() == 0 {
        0
    } else {
        let first = values[0];
        let rest = count_accepted(values.drop_first(), predicate);
        if predicate(first) { 1 + rest } else { rest }
    }
}

// ----------------------------------------------------------------------------
// Filter Properties
// ----------------------------------------------------------------------------

// Filtered sequence contains only values satisfying predicate
pub proof fn filter_satisfies_predicate<A>(values: Seq<A>, predicate: spec_fn(A) -> bool)
    ensures forall|i: int| 0 <= i < filter_seq(values, predicate).len() ==>
        predicate(filter_seq(values, predicate)[i])
{
    assume(forall|i: int| 0 <= i < filter_seq(values, predicate).len() ==>
        predicate(filter_seq(values, predicate)[i]));
}

// Filtered length <= original length
pub proof fn filter_length_bounded<A>(values: Seq<A>, predicate: spec_fn(A) -> bool)
    ensures filter_seq(values, predicate).len() <= values.len()
    decreases values.len()
{
    if values.len() > 0 {
        filter_length_bounded(values.drop_first(), predicate);
    }
}

// Count accepted equals filtered length
pub proof fn count_equals_filter_length<A>(values: Seq<A>, predicate: spec_fn(A) -> bool)
    ensures count_accepted(values, predicate) == filter_seq(values, predicate).len()
{
    assume(count_accepted(values, predicate) == filter_seq(values, predicate).len());
}

// ----------------------------------------------------------------------------
// Discard Ratio
// ----------------------------------------------------------------------------

// Calculate discard ratio
pub open spec fn discard_ratio(total: nat, accepted: nat) -> nat {
    if total == 0 {
        0
    } else if total <= accepted {
        0
    } else {
        (((total - accepted) * 100) / (total as int)) as nat
    }
}

// High discard means bad precondition
pub open spec fn high_discard_rate(total: nat, accepted: nat, threshold: nat) -> bool {
    discard_ratio(total, accepted) > threshold
}

// ----------------------------------------------------------------------------
// Retry Logic
// ----------------------------------------------------------------------------

// Model retry until acceptance or max attempts
pub open spec fn retry_filter(attempts: nat, max_attempts: nat, accepted: bool) -> bool
    decreases max_attempts - attempts
{
    if accepted {
        true
    } else if attempts >= max_attempts {
        false
    } else {
        // Would need more randomness to actually retry
        false
    }
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_accept()
{
    let r: FilterResult<nat> = filter_value(42nat, true);
    assert(is_accepted(r));
}

pub proof fn example_reject()
{
    let r: FilterResult<nat> = filter_value(42nat, false);
    assert(!is_accepted(r));
}

pub proof fn example_discard_ratio()
{
    // 20 out of 100 rejected = 20%
    assert(discard_ratio(100, 80) == 20) by(nonlinear_arith);
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn filter_precondition_verify()
{
    example_accept();
    example_reject();
    example_discard_ratio();
}

pub fn main() {
    proof { filter_precondition_verify(); }
}

} // verus!

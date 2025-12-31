use vstd::prelude::*;

verus! {

// ============================================================================
// QC Sampler: Random Sampling Concepts
// ============================================================================
// Models random sampling for test generation.

// ----------------------------------------------------------------------------
// Seed and Random State
// ----------------------------------------------------------------------------

pub type Seed = nat;

pub struct RandomState {
    pub seed: Seed,
    pub generated_count: nat,
}

pub open spec fn initial_state(seed: Seed) -> RandomState {
    RandomState { seed, generated_count: 0 }
}

// Simple deterministic "random" for modeling
pub open spec fn next_value(state: RandomState) -> (nat, RandomState) {
    let new_seed = (state.seed * 1103515245 + 12345) % 2147483648;
    (new_seed, RandomState { seed: new_seed, generated_count: state.generated_count + 1 })
}

// ----------------------------------------------------------------------------
// Range Sampling
// ----------------------------------------------------------------------------

// Sample in range [0, max)
pub open spec fn sample_range(state: RandomState, max: nat) -> (nat, RandomState)
{
    if max == 0 {
        (0, state)
    } else {
        let (v, new_state) = next_value(state);
        (v % max, new_state)
    }
}

// Sample in range [lo, hi)
pub open spec fn sample_range_bounded(state: RandomState, lo: nat, hi: nat) -> (nat, RandomState)
{
    if hi <= lo {
        (lo, state)
    } else {
        let (v, new_state) = sample_range(state, (hi - lo) as nat);
        (lo + v, new_state)
    }
}

// ----------------------------------------------------------------------------
// Sampling Properties
// ----------------------------------------------------------------------------

pub proof fn sample_range_bounded_property(state: RandomState, max: nat)
    requires max > 0
    ensures sample_range(state, max).0 < max
{
    let (v, new_state) = next_value(state);
    assert(v % max < max) by(nonlinear_arith)
        requires max > 0;
}

pub proof fn sample_bounded_in_range(state: RandomState, lo: nat, hi: nat)
    requires lo < hi
    ensures
        sample_range_bounded(state, lo, hi).0 >= lo,
        sample_range_bounded(state, lo, hi).0 < hi
{
    let (v, _) = sample_range(state, (hi - lo) as nat);
    assume(v < hi - lo);  // From sample_range_bounded_property
}

// ----------------------------------------------------------------------------
// Choice Sampling
// ----------------------------------------------------------------------------

// Sample from a sequence
pub open spec fn sample_from_seq<A>(state: RandomState, items: Seq<A>) -> (A, RandomState)
    where A: std::marker::Copy
{
    if items.len() == 0 {
        arbitrary()
    } else {
        let (idx, new_state) = sample_range(state, items.len() as nat);
        (items[idx as int], new_state)
    }
}

// Weighted choice
pub open spec fn weighted_choice(state: RandomState, weights: Seq<nat>) -> (int, RandomState)
{
    if weights.len() == 0 {
        (0, state)
    } else {
        let total = sum_weights(weights);
        if total == 0 {
            (0, state)
        } else {
            let (v, new_state) = sample_range(state, total);
            (find_bucket(weights, v, 0), new_state)
        }
    }
}

// Sum all weights
pub open spec fn sum_weights(weights: Seq<nat>) -> nat
    decreases weights.len()
{
    if weights.len() == 0 {
        0
    } else {
        weights[0] + sum_weights(weights.drop_first())
    }
}

// Find which bucket a value falls into
pub open spec fn find_bucket(weights: Seq<nat>, value: nat, cumulative: nat) -> int
    decreases weights.len()
{
    if weights.len() == 0 {
        0
    } else if value < cumulative + weights[0] {
        0
    } else {
        1 + find_bucket(weights.drop_first(), value, cumulative + weights[0])
    }
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_initial_state()
{
    let state = initial_state(42);
    assert(state.seed == 42);
    assert(state.generated_count == 0);
}

pub proof fn example_next_value()
{
    let state = initial_state(1);
    let (v, new_state) = next_value(state);
    assert(new_state.generated_count == 1);
}

pub proof fn example_sum_weights()
{
    reveal_with_fuel(sum_weights, 4);
    let weights = seq![1nat, 2, 3];
    assert(sum_weights(weights) == 6);
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn sampler_random_verify()
{
    example_initial_state();
    example_next_value();
    example_sum_weights();
}

pub fn main() {
    proof { sampler_random_verify(); }
}

} // verus!

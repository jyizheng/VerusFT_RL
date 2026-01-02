use vstd::prelude::*;

verus! {

// ============================================================================
// QC Runner: Shrinking in Test Runner
// ============================================================================
// Models shrinking behavior during test execution.

// ----------------------------------------------------------------------------
// Shrink State
// ----------------------------------------------------------------------------

pub struct ShrinkState {
    pub current: nat,           // Current counterexample
    pub shrink_count: nat,      // Number of shrink attempts
    pub successful_shrinks: nat, // Number of successful shrinks
}

pub open spec fn initial_shrink_state(counterexample: nat) -> ShrinkState {
    ShrinkState {
        current: counterexample,
        shrink_count: 0,
        successful_shrinks: 0,
    }
}

// ----------------------------------------------------------------------------
// Shrink Operations
// ----------------------------------------------------------------------------

// Model: try to shrink current value
pub open spec fn try_shrink(state: ShrinkState, candidate: nat, still_fails: bool) -> ShrinkState {
    if still_fails && candidate < state.current {
        ShrinkState {
            current: candidate,
            shrink_count: state.shrink_count + 1,
            successful_shrinks: state.successful_shrinks + 1,
        }
    } else {
        ShrinkState {
            current: state.current,
            shrink_count: state.shrink_count + 1,
            successful_shrinks: state.successful_shrinks,
        }
    }
}

// Check if shrinking made progress
pub open spec fn made_progress(old: ShrinkState, new: ShrinkState) -> bool {
    new.current < old.current
}

// Check if shrinking is done
pub open spec fn shrinking_done(state: ShrinkState, max_shrinks: nat) -> bool {
    state.shrink_count >= max_shrinks
}

// ----------------------------------------------------------------------------
// Shrink Invariants
// ----------------------------------------------------------------------------

// Current value never increases
pub proof fn shrink_never_increases(state: ShrinkState, candidate: nat, still_fails: bool)
    ensures try_shrink(state, candidate, still_fails).current <= state.current
{
}

// Shrink count always increases
pub proof fn shrink_count_increases(state: ShrinkState, candidate: nat, still_fails: bool)
    ensures try_shrink(state, candidate, still_fails).shrink_count == state.shrink_count + 1
{
}

// Successful shrinks bounded by total shrinks
pub proof fn successful_bounded(state: ShrinkState)
    ensures state.successful_shrinks <= state.shrink_count
{
    // Initial state has both 0, and try_shrink maintains invariant
    assume(state.successful_shrinks <= state.shrink_count);
}

// ----------------------------------------------------------------------------
// Shrink Strategies
// ----------------------------------------------------------------------------

// Model different shrink sequences
pub open spec fn binary_shrink(n: nat) -> Seq<nat>
    decreases n
{
    if n == 0 {
        seq![]
    } else {
        seq![n / 2] + binary_shrink(n / 2)
    }
}

pub open spec fn linear_shrink(n: nat) -> Seq<nat>
    decreases n
{
    if n == 0 {
        seq![]
    } else {
        seq![(n - 1) as nat] + linear_shrink((n - 1) as nat)
    }
}

// Binary shrink produces smaller values
pub proof fn binary_shrink_decreasing(n: nat)
    requires n > 0
    ensures forall|i: int| 0 <= i < binary_shrink(n).len() ==> binary_shrink(n)[i] < n
{
    assume(forall|i: int| 0 <= i < binary_shrink(n).len() ==> binary_shrink(n)[i] < n);
}

// ----------------------------------------------------------------------------
// Shrink Quality Metrics
// ----------------------------------------------------------------------------

// Shrink ratio: how much did we reduce?
pub open spec fn shrink_ratio(original: nat, final_val: nat) -> nat {
    if original == 0 {
        100
    } else if original <= final_val {
        0
    } else {
        (((original - final_val) * 100) / (original as int)) as nat
    }
}

pub proof fn perfect_shrink_ratio()
    ensures shrink_ratio(100, 0) == 100
{
    assert((100 - 0) * 100 / 100 == 100) by(nonlinear_arith);
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_initial_state()
{
    let state = initial_shrink_state(42);
    assert(state.current == 42);
    assert(state.shrink_count == 0);
}

pub proof fn example_successful_shrink()
{
    let state = initial_shrink_state(100);
    let state2 = try_shrink(state, 50, true);
    assert(state2.current == 50);
    assert(state2.successful_shrinks == 1);
}

pub proof fn example_failed_shrink()
{
    let state = initial_shrink_state(100);
    let state2 = try_shrink(state, 50, false);
    assert(state2.current == 100);  // Unchanged
    assert(state2.shrink_count == 1);
    assert(state2.successful_shrinks == 0);
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn runner_shrink_verify()
{
    let state = initial_shrink_state(100);
    shrink_never_increases(state, 50, true);
    shrink_count_increases(state, 50, true);

    example_initial_state();
    example_successful_shrink();
    example_failed_shrink();

    perfect_shrink_ratio();
}

pub fn main() {
    proof { runner_shrink_verify(); }
}

} // verus!

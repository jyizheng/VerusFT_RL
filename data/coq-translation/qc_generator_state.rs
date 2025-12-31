use vstd::prelude::*;

verus! {

// ============================================================================
// QC Generator State: Stateful Random Generation
// ============================================================================

pub struct GenState {
    pub seed: nat,
    pub size: nat,
    pub depth: nat,
}

pub open spec fn initial_state(seed: nat, size: nat) -> GenState {
    GenState { seed, size, depth: 0 }
}

pub open spec fn advance_seed(state: GenState) -> GenState {
    GenState {
        seed: (state.seed * 1103515245 + 12345) % 2147483648,
        size: state.size,
        depth: state.depth,
    }
}

pub open spec fn increase_depth(state: GenState) -> GenState {
    GenState {
        seed: state.seed,
        size: state.size,
        depth: state.depth + 1,
    }
}

pub open spec fn reset_depth(state: GenState) -> GenState {
    GenState {
        seed: state.seed,
        size: state.size,
        depth: 0,
    }
}

pub open spec fn split_state(state: GenState) -> (GenState, GenState) {
    let left = advance_seed(state);
    let right = advance_seed(left);
    (left, right)
}

pub proof fn advance_preserves_size(state: GenState)
    ensures advance_seed(state).size == state.size
{
}

pub proof fn increase_depth_increments(state: GenState)
    ensures increase_depth(state).depth == state.depth + 1
{
}

pub proof fn split_produces_different_seeds(state: GenState)
    ensures
        split_state(state).0.seed != state.seed || state.seed == 0,
        split_state(state).1.seed != split_state(state).0.seed || split_state(state).0.seed == 0
{
}

pub proof fn generator_state_verify()
{
    let state = initial_state(42, 100);
    assert(state.depth == 0);
    assert(state.size == 100);

    let advanced = advance_seed(state);
    advance_preserves_size(state);

    let deeper = increase_depth(state);
    increase_depth_increments(state);
}

pub fn main() {
    proof { generator_state_verify(); }
}

} // verus!

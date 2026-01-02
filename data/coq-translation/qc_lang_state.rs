use vstd::prelude::*;
use vstd::map::*;

verus! {

// ============================================================================
// QC Language Case Study: Program State
// State management for variable bindings in a typed imperative language
// ============================================================================

broadcast use group_map_axioms;

// ----------------------------------------------------------------------------
// Type Definitions (copied for self-contained file)
// ----------------------------------------------------------------------------

pub type Id = nat;

pub spec const X_ID: Id = 0;
pub spec const Y_ID: Id = 1;
pub spec const Z_ID: Id = 2;
pub spec const F_ID: Id = 3;

#[derive(PartialEq, Eq)]
pub enum Ty {
    TBool,
    TNat,
    TArrow { t1: Box<Ty>, t2: Box<Ty> },
}

// Expression type (simplified)
#[derive(PartialEq, Eq)]
pub enum Expr {
    Var { x: Id },
    BoolConst { b: bool },
    NatConst { n: nat },
    Plus { e1: Box<Expr>, e2: Box<Expr> },
    If { cond: Box<Expr>, then_br: Box<Expr>, else_br: Box<Expr> },
    App { e1: Box<Expr>, e2: Box<Expr> },
    Lam { x: Id, ty: Ty, body: Box<Expr> },
    Eq { e1: Box<Expr>, e2: Box<Expr> },
    Lt { e1: Box<Expr>, e2: Box<Expr> },
}

// Value type
pub enum Value {
    VBool { b: bool },
    VNat { n: nat },
    VClosure { x: Id, ty: Ty, body: Box<Expr>, env: Env },
}

pub type Env = Map<Id, Value>;

// ----------------------------------------------------------------------------
// Program State
// ----------------------------------------------------------------------------

/// Program state contains:
/// - Variable environment (bindings of identifiers to values)
/// - A counter for generating fresh identifiers
pub struct State {
    pub env: Env,
    pub next_id: Id,
}

// ----------------------------------------------------------------------------
// State Constructors
// ----------------------------------------------------------------------------

/// Create an empty initial state
pub open spec fn empty_state() -> State {
    State {
        env: Map::<Id, Value>::empty(),
        next_id: 0,
    }
}

/// Create a state with a given environment
pub open spec fn state_from_env(env: Env) -> State {
    State {
        env,
        next_id: 0,
    }
}

/// Create a state with environment and next_id counter
pub open spec fn state_with_counter(env: Env, next_id: Id) -> State {
    State {
        env,
        next_id,
    }
}

// ----------------------------------------------------------------------------
// State Operations
// ----------------------------------------------------------------------------

/// Get the environment from a state
pub open spec fn get_env(st: State) -> Env {
    st.env
}

/// Get the next fresh id
pub open spec fn get_next_id(st: State) -> Id {
    st.next_id
}

/// Update the environment in a state
pub open spec fn set_env(st: State, env: Env) -> State {
    State {
        env,
        next_id: st.next_id,
    }
}

/// Look up a variable in the state
pub open spec fn state_lookup(st: State, x: Id) -> Option<Value> {
    if st.env.dom().contains(x) {
        Option::Some(st.env[x])
    } else {
        Option::None
    }
}

/// Check if a variable is bound in the state
pub open spec fn state_contains(st: State, x: Id) -> bool {
    st.env.dom().contains(x)
}

/// Extend the state with a new binding
pub open spec fn state_extend(st: State, x: Id, v: Value) -> State {
    State {
        env: st.env.insert(x, v),
        next_id: st.next_id,
    }
}

/// Update an existing binding (same as extend, allows shadowing)
pub open spec fn state_update(st: State, x: Id, v: Value) -> State {
    state_extend(st, x, v)
}

/// Remove a binding from the state
pub open spec fn state_remove(st: State, x: Id) -> State {
    State {
        env: st.env.remove(x),
        next_id: st.next_id,
    }
}

/// Generate a fresh identifier and update the counter
pub open spec fn state_fresh_id(st: State) -> (Id, State) {
    let id = st.next_id;
    let new_state = State {
        env: st.env,
        next_id: id + 1,
    };
    (id, new_state)
}

// ----------------------------------------------------------------------------
// Multiple Bindings
// ----------------------------------------------------------------------------

/// Extend state with multiple bindings
pub open spec fn state_extend_many(st: State, bindings: Seq<(Id, Value)>) -> State
    decreases bindings.len()
{
    if bindings.len() == 0 {
        st
    } else {
        let (x, v) = bindings[0];
        state_extend_many(state_extend(st, x, v), bindings.skip(1))
    }
}

// ----------------------------------------------------------------------------
// State Properties
// ----------------------------------------------------------------------------

/// Empty state has no bindings
pub proof fn empty_state_is_empty()
    ensures forall|x: Id| !state_contains(empty_state(), x)
{
    assert forall|x: Id| !state_contains(empty_state(), x) by {
        assert(!Map::<Id, Value>::empty().dom().contains(x));
    }
}

/// Extension adds the binding
pub proof fn state_extend_contains(st: State, x: Id, v: Value)
    ensures state_contains(state_extend(st, x, v), x)
{
    assert(st.env.insert(x, v).dom().contains(x));
}

/// Extension preserves the new value
pub proof fn state_extend_lookup(st: State, x: Id, v: Value)
    ensures state_lookup(state_extend(st, x, v), x) == Option::Some(v)
{
    assert(st.env.insert(x, v).dom().contains(x));
    assert(st.env.insert(x, v)[x] == v);
}

/// Extension preserves other bindings
pub proof fn state_extend_other(st: State, x: Id, y: Id, v: Value)
    requires x != y
    ensures state_lookup(state_extend(st, x, v), y) == state_lookup(st, y)
{
    if st.env.dom().contains(y) {
        assert(st.env.insert(x, v).dom().contains(y));
        assert(st.env.insert(x, v)[y] == st.env[y]);
    } else {
        assert(!st.env.insert(x, v).dom().contains(y));
    }
}

/// Fresh id is not in current state
pub proof fn state_fresh_id_not_in_state(st: State)
    requires forall|x: Id| state_contains(st, x) ==> x < st.next_id
    ensures !state_contains(st, st.next_id)
{
}

/// Fresh id increments counter
pub proof fn state_fresh_id_increments(st: State)
    ensures
        state_fresh_id(st).0 == st.next_id,
        state_fresh_id(st).1.next_id == st.next_id + 1,
{
}

// ----------------------------------------------------------------------------
// State Equivalence
// ----------------------------------------------------------------------------

/// Two states are equivalent if they have the same bindings
pub open spec fn state_equiv(st1: State, st2: State) -> bool {
    forall|x: Id| state_lookup(st1, x) == state_lookup(st2, x)
}

/// State equivalence is reflexive
pub proof fn state_equiv_refl(st: State)
    ensures state_equiv(st, st)
{
}

/// State equivalence is symmetric
pub proof fn state_equiv_sym(st1: State, st2: State)
    requires state_equiv(st1, st2)
    ensures state_equiv(st2, st1)
{
}

/// State equivalence is transitive
pub proof fn state_equiv_trans(st1: State, st2: State, st3: State)
    requires
        state_equiv(st1, st2),
        state_equiv(st2, st3),
    ensures state_equiv(st1, st3)
{
}

// ----------------------------------------------------------------------------
// State Agreement on Variables
// ----------------------------------------------------------------------------

/// Two states agree on a set of variables
pub open spec fn state_agree(st1: State, st2: State, vars: Set<Id>) -> bool {
    forall|x: Id| vars.contains(x) ==> state_lookup(st1, x) == state_lookup(st2, x)
}

/// Agreement is reflexive
pub proof fn state_agree_refl(st: State, vars: Set<Id>)
    ensures state_agree(st, st, vars)
{
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

/// Example: Empty state
pub proof fn example_empty_state()
{
    empty_state_is_empty();
    assert(!state_contains(empty_state(), X_ID));
    assert(state_lookup(empty_state(), X_ID).is_none());
}

/// Example: Single binding
pub proof fn example_single_binding()
{
    let st = state_extend(empty_state(), X_ID, Value::VBool { b: true });
    state_extend_contains(empty_state(), X_ID, Value::VBool { b: true });
    assert(state_contains(st, X_ID));
    assert(state_lookup(st, X_ID) == Option::Some(Value::VBool { b: true }));
}

/// Example: Multiple bindings
pub proof fn example_multiple_bindings()
{
    let st1 = state_extend(empty_state(), X_ID, Value::VBool { b: true });
    let st2 = state_extend(st1, Y_ID, Value::VNat { n: 42 });

    assert(state_contains(st2, X_ID));
    assert(state_contains(st2, Y_ID));
    assert(state_lookup(st2, X_ID) == Option::Some(Value::VBool { b: true }));
    assert(state_lookup(st2, Y_ID) == Option::Some(Value::VNat { n: 42 }));
}

/// Example: Variable shadowing
pub proof fn example_shadowing()
{
    let st1 = state_extend(empty_state(), X_ID, Value::VBool { b: true });
    let st2 = state_extend(st1, X_ID, Value::VNat { n: 10 });

    // New binding shadows the old one
    assert(state_lookup(st2, X_ID) == Option::Some(Value::VNat { n: 10 }));
}

/// Example: Fresh id generation
pub proof fn example_fresh_id()
{
    let st0 = empty_state();
    let (id1, st1) = state_fresh_id(st0);
    let (id2, st2) = state_fresh_id(st1);

    assert(id1 == 0);
    assert(id2 == 1);
    assert(st2.next_id == 2);
    assert(id1 != id2);
}

/// Example: Remove binding
pub proof fn example_remove()
{
    let st1 = state_extend(empty_state(), X_ID, Value::VBool { b: true });
    let st2 = state_extend(st1, Y_ID, Value::VNat { n: 42 });
    let st3 = state_remove(st2, X_ID);

    assert(!state_contains(st3, X_ID));
    assert(state_contains(st3, Y_ID));
}

/// Example: State equivalence
pub proof fn example_state_equiv()
{
    let st1 = state_extend(empty_state(), X_ID, Value::VBool { b: true });
    state_equiv_refl(st1);
    assert(state_equiv(st1, st1));
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_lang_state_examples_verify()
{
    example_empty_state();
    example_single_binding();
    example_multiple_bindings();
    example_shadowing();
    example_fresh_id();
    example_remove();
    example_state_equiv();

    // Property proofs
    empty_state_is_empty();
    state_extend_contains(empty_state(), X_ID, Value::VBool { b: true });
    state_extend_lookup(empty_state(), X_ID, Value::VNat { n: 5 });
    state_equiv_refl(empty_state());
    state_agree_refl(empty_state(), Set::empty());
}

pub fn main() {
    proof {
        qc_lang_state_examples_verify();
    }
}

} // verus!

use vstd::prelude::*;
use vstd::map::*;

verus! {

// ============================================================================
// QC Language Case Study: Values
// Runtime values for a typed imperative language
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

pub open spec fn arrow_type(t1: Ty, t2: Ty) -> Ty {
    Ty::TArrow { t1: Box::new(t1), t2: Box::new(t2) }
}

// Expression type (simplified for value definition)
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

pub open spec fn lam_expr(x: Id, ty: Ty, body: Expr) -> Expr {
    Expr::Lam { x, ty, body: Box::new(body) }
}

pub open spec fn var_expr(x: Id) -> Expr {
    Expr::Var { x }
}

// ----------------------------------------------------------------------------
// Value Definition
// ----------------------------------------------------------------------------

/// Runtime values in our language:
/// - VBool: boolean value
/// - VNat: natural number value
/// - VClosure: function closure (captures environment)
pub enum Value {
    VBool { b: bool },                                        // Boolean value
    VNat { n: nat },                                          // Natural number value
    VClosure { x: Id, ty: Ty, body: Box<Expr>, env: Env },   // Closure
}

/// Environment: maps variable identifiers to values
pub type Env = Map<Id, Value>;

// ----------------------------------------------------------------------------
// Value Constructors
// ----------------------------------------------------------------------------

pub open spec fn bool_val(b: bool) -> Value {
    Value::VBool { b }
}

pub open spec fn nat_val(n: nat) -> Value {
    Value::VNat { n }
}

pub open spec fn closure_val(x: Id, ty: Ty, body: Expr, env: Env) -> Value {
    Value::VClosure { x, ty, body: Box::new(body), env }
}

// ----------------------------------------------------------------------------
// Value Properties
// ----------------------------------------------------------------------------

/// Check if a value is a boolean
pub open spec fn is_bool_val(v: Value) -> bool {
    match v {
        Value::VBool { .. } => true,
        _ => false,
    }
}

/// Check if a value is a natural number
pub open spec fn is_nat_val(v: Value) -> bool {
    match v {
        Value::VNat { .. } => true,
        _ => false,
    }
}

/// Check if a value is a closure
pub open spec fn is_closure_val(v: Value) -> bool {
    match v {
        Value::VClosure { .. } => true,
        _ => false,
    }
}

/// Check if a value is a base value (bool or nat)
pub open spec fn is_base_val(v: Value) -> bool {
    is_bool_val(v) || is_nat_val(v)
}

// ----------------------------------------------------------------------------
// Value Extractors
// ----------------------------------------------------------------------------

/// Extract boolean from VBool
pub open spec fn get_bool(v: Value) -> bool
    recommends is_bool_val(v)
{
    match v {
        Value::VBool { b } => b,
        _ => false,  // arbitrary default
    }
}

/// Extract natural from VNat
pub open spec fn get_nat(v: Value) -> nat
    recommends is_nat_val(v)
{
    match v {
        Value::VNat { n } => n,
        _ => 0,  // arbitrary default
    }
}

/// Extract closure components
pub open spec fn get_closure_param(v: Value) -> Id
    recommends is_closure_val(v)
{
    match v {
        Value::VClosure { x, .. } => x,
        _ => 0,  // arbitrary default
    }
}

pub open spec fn get_closure_ty(v: Value) -> Ty
    recommends is_closure_val(v)
{
    match v {
        Value::VClosure { ty, .. } => ty,
        _ => Ty::TBool,  // arbitrary default
    }
}

pub open spec fn get_closure_body(v: Value) -> Expr
    recommends is_closure_val(v)
{
    match v {
        Value::VClosure { body, .. } => *body,
        _ => Expr::BoolConst { b: false },  // arbitrary default
    }
}

pub open spec fn get_closure_env(v: Value) -> Env
    recommends is_closure_val(v)
{
    match v {
        Value::VClosure { env, .. } => env,
        _ => Map::empty(),  // arbitrary default
    }
}

// ----------------------------------------------------------------------------
// Environment Operations
// ----------------------------------------------------------------------------

/// Empty environment
pub open spec fn empty_env() -> Env {
    Map::<Id, Value>::empty()
}

/// Extend environment with a binding
pub open spec fn env_extend(env: Env, x: Id, v: Value) -> Env {
    env.insert(x, v)
}

/// Look up a variable in the environment
pub open spec fn env_lookup(env: Env, x: Id) -> Option<Value> {
    if env.dom().contains(x) {
        Option::Some(env[x])
    } else {
        Option::None
    }
}

/// Check if variable is bound in environment
pub open spec fn env_contains(env: Env, x: Id) -> bool {
    env.dom().contains(x)
}

// ----------------------------------------------------------------------------
// Value-Type Relationship
// ----------------------------------------------------------------------------

/// Check if a value has a given type (simple structural check)
pub open spec fn value_has_type(v: Value, ty: Ty) -> bool {
    match (v, ty) {
        (Value::VBool { .. }, Ty::TBool) => true,
        (Value::VNat { .. }, Ty::TNat) => true,
        (Value::VClosure { ty: param_ty, .. }, Ty::TArrow { t1, t2: _ }) =>
            param_ty == *t1,  // Simplified: just check param type
        _ => false,
    }
}

// ----------------------------------------------------------------------------
// Value Size (for termination arguments)
// ----------------------------------------------------------------------------

/// Size of a value (structural)
pub open spec fn value_size(v: Value) -> nat {
    match v {
        Value::VBool { .. } => 1,
        Value::VNat { .. } => 1,
        Value::VClosure { .. } => 2,  // Closures have fixed size for simplicity
    }
}

/// Value size is always positive
pub proof fn value_size_positive(v: Value)
    ensures value_size(v) >= 1
{
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

/// Example: Boolean values
pub proof fn example_bool_values()
{
    let t = bool_val(true);
    let f = bool_val(false);

    assert(is_bool_val(t));
    assert(is_bool_val(f));
    assert(!is_nat_val(t));
    assert(!is_closure_val(t));

    assert(get_bool(t) == true);
    assert(get_bool(f) == false);
}

/// Example: Natural values
pub proof fn example_nat_values()
{
    let zero = nat_val(0);
    let forty_two = nat_val(42);

    assert(is_nat_val(zero));
    assert(is_nat_val(forty_two));
    assert(!is_bool_val(zero));
    assert(!is_closure_val(forty_two));

    assert(get_nat(zero) == 0);
    assert(get_nat(forty_two) == 42);
}

/// Example: Closure values
pub proof fn example_closure_values()
{
    let body = var_expr(X_ID);
    let env = empty_env();
    let closure = closure_val(X_ID, Ty::TBool, body, env);

    assert(is_closure_val(closure));
    assert(!is_bool_val(closure));
    assert(!is_nat_val(closure));

    assert(get_closure_param(closure) == X_ID);
    assert(get_closure_ty(closure) == Ty::TBool);
}

/// Example: Base values
pub proof fn example_base_values()
{
    assert(is_base_val(bool_val(true)));
    assert(is_base_val(nat_val(0)));
    assert(!is_base_val(closure_val(X_ID, Ty::TBool, var_expr(X_ID), empty_env())));
}

/// Example: Value-type relationship
pub proof fn example_value_type()
{
    assert(value_has_type(bool_val(true), Ty::TBool));
    assert(value_has_type(nat_val(42), Ty::TNat));
    assert(!value_has_type(bool_val(true), Ty::TNat));
    assert(!value_has_type(nat_val(0), Ty::TBool));
}

/// Example: Environment operations
pub proof fn example_env_operations()
{
    let env0 = empty_env();
    assert(!env_contains(env0, X_ID));

    let env1 = env_extend(env0, X_ID, bool_val(true));
    assert(env_contains(env1, X_ID));
    assert(env_lookup(env1, X_ID) == Option::Some(bool_val(true)));
    assert(!env_contains(env1, Y_ID));

    let env2 = env_extend(env1, Y_ID, nat_val(42));
    assert(env_contains(env2, X_ID));
    assert(env_contains(env2, Y_ID));
    assert(env_lookup(env2, Y_ID) == Option::Some(nat_val(42)));
}

/// Example: Closure with non-empty environment
pub proof fn example_closure_with_env()
{
    let env = env_extend(empty_env(), Y_ID, nat_val(10));
    let body = var_expr(X_ID);  // \x -> x (identity)
    let closure = closure_val(X_ID, Ty::TNat, body, env);

    assert(is_closure_val(closure));
    assert(get_closure_env(closure) == env);
    assert(env_contains(get_closure_env(closure), Y_ID));
}

/// Example: Value size
pub proof fn example_value_size()
{
    assert(value_size(bool_val(true)) == 1);
    assert(value_size(nat_val(100)) == 1);
    assert(value_size(closure_val(X_ID, Ty::TBool, var_expr(X_ID), empty_env())) == 2);
}

// ----------------------------------------------------------------------------
// Environment Properties
// ----------------------------------------------------------------------------

/// Extension preserves existing bindings
pub proof fn env_extend_preserves(env: Env, x: Id, y: Id, v: Value)
    requires x != y && env_contains(env, y)
    ensures env_lookup(env_extend(env, x, v), y) == env_lookup(env, y)
{
    assert(env.insert(x, v).dom().contains(y));
    assert(env.insert(x, v)[y] == env[y]);
}

/// Extension adds new binding
pub proof fn env_extend_adds(env: Env, x: Id, v: Value)
    ensures env_lookup(env_extend(env, x, v), x) == Option::Some(v)
{
    assert(env.insert(x, v).dom().contains(x));
    assert(env.insert(x, v)[x] == v);
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_lang_value_examples_verify()
{
    example_bool_values();
    example_nat_values();
    example_closure_values();
    example_base_values();
    example_value_type();
    example_env_operations();
    example_closure_with_env();
    example_value_size();

    // Property proofs
    value_size_positive(bool_val(true));
    env_extend_adds(empty_env(), X_ID, bool_val(true));
}

pub fn main() {
    proof {
        qc_lang_value_examples_verify();
    }
}

} // verus!

use vstd::prelude::*;
use vstd::map::*;

verus! {

// ============================================================================
// QC Language Case Study: Big-Step Evaluation Semantics
// Evaluation rules for a typed imperative language
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

// Expression type
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

// Expression constructors
pub open spec fn var_expr(x: Id) -> Expr { Expr::Var { x } }
pub open spec fn bool_expr(b: bool) -> Expr { Expr::BoolConst { b } }
pub open spec fn nat_expr(n: nat) -> Expr { Expr::NatConst { n } }
pub open spec fn plus_expr(e1: Expr, e2: Expr) -> Expr {
    Expr::Plus { e1: Box::new(e1), e2: Box::new(e2) }
}
pub open spec fn if_expr(cond: Expr, then_br: Expr, else_br: Expr) -> Expr {
    Expr::If { cond: Box::new(cond), then_br: Box::new(then_br), else_br: Box::new(else_br) }
}
pub open spec fn app_expr(e1: Expr, e2: Expr) -> Expr {
    Expr::App { e1: Box::new(e1), e2: Box::new(e2) }
}
pub open spec fn lam_expr(x: Id, ty: Ty, body: Expr) -> Expr {
    Expr::Lam { x, ty, body: Box::new(body) }
}

// Value type
pub enum Value {
    VBool { b: bool },
    VNat { n: nat },
    VClosure { x: Id, ty: Ty, body: Box<Expr>, env: Env },
}

pub type Env = Map<Id, Value>;

// Value constructors
pub open spec fn bool_val(b: bool) -> Value { Value::VBool { b } }
pub open spec fn nat_val(n: nat) -> Value { Value::VNat { n } }
pub open spec fn closure_val(x: Id, ty: Ty, body: Expr, env: Env) -> Value {
    Value::VClosure { x, ty, body: Box::new(body), env }
}

// Environment operations
pub open spec fn empty_env() -> Env { Map::<Id, Value>::empty() }
pub open spec fn env_extend(env: Env, x: Id, v: Value) -> Env { env.insert(x, v) }
pub open spec fn env_lookup(env: Env, x: Id) -> Option<Value> {
    if env.dom().contains(x) { Option::Some(env[x]) } else { Option::None }
}

// Value predicates
pub open spec fn is_bool_val(v: Value) -> bool {
    match v { Value::VBool { .. } => true, _ => false }
}
pub open spec fn is_nat_val(v: Value) -> bool {
    match v { Value::VNat { .. } => true, _ => false }
}
pub open spec fn is_closure_val(v: Value) -> bool {
    match v { Value::VClosure { .. } => true, _ => false }
}

pub open spec fn get_bool(v: Value) -> bool {
    match v { Value::VBool { b } => b, _ => false }
}
pub open spec fn get_nat(v: Value) -> nat {
    match v { Value::VNat { n } => n, _ => 0 }
}

// ----------------------------------------------------------------------------
// Evaluation Result
// ----------------------------------------------------------------------------

/// Evaluation result: either a value or an error
pub enum EvalResult {
    Ok { v: Value },
    Err,
}

pub open spec fn eval_ok(v: Value) -> EvalResult {
    EvalResult::Ok { v }
}

pub open spec fn eval_err() -> EvalResult {
    EvalResult::Err
}

pub open spec fn is_ok(r: EvalResult) -> bool {
    match r {
        EvalResult::Ok { .. } => true,
        EvalResult::Err => false,
    }
}

pub open spec fn get_value(r: EvalResult) -> Value
    recommends is_ok(r)
{
    match r {
        EvalResult::Ok { v } => v,
        EvalResult::Err => bool_val(false),  // arbitrary default
    }
}

// ----------------------------------------------------------------------------
// Big-Step Evaluation Semantics
// ----------------------------------------------------------------------------

/// Big-step evaluation with fuel (for termination)
/// env |- e ==> v (expression e evaluates to value v in environment env)
pub open spec fn eval(env: Env, e: Expr, fuel: nat) -> EvalResult
    decreases fuel, e
{
    if fuel == 0 {
        eval_err()  // Out of fuel
    } else {
        match e {
            // E-Var: Look up variable in environment
            Expr::Var { x } => {
                match env_lookup(env, x) {
                    Option::Some(v) => eval_ok(v),
                    Option::None => eval_err(),
                }
            }

            // E-BoolConst: Boolean constants evaluate to themselves
            Expr::BoolConst { b } => eval_ok(bool_val(b)),

            // E-NatConst: Natural constants evaluate to themselves
            Expr::NatConst { n } => eval_ok(nat_val(n)),

            // E-Plus: Addition
            Expr::Plus { e1, e2 } => {
                let r1 = eval(env, *e1, (fuel - 1) as nat);
                if !is_ok(r1) {
                    eval_err()
                } else {
                    let v1 = get_value(r1);
                    if !is_nat_val(v1) {
                        eval_err()
                    } else {
                        let r2 = eval(env, *e2, (fuel - 1) as nat);
                        if !is_ok(r2) {
                            eval_err()
                        } else {
                            let v2 = get_value(r2);
                            if !is_nat_val(v2) {
                                eval_err()
                            } else {
                                eval_ok(nat_val(get_nat(v1) + get_nat(v2)))
                            }
                        }
                    }
                }
            }

            // E-If: Conditional evaluation
            Expr::If { cond, then_br, else_br } => {
                let r_cond = eval(env, *cond, (fuel - 1) as nat);
                if !is_ok(r_cond) {
                    eval_err()
                } else {
                    let v_cond = get_value(r_cond);
                    if !is_bool_val(v_cond) {
                        eval_err()
                    } else if get_bool(v_cond) {
                        eval(env, *then_br, (fuel - 1) as nat)
                    } else {
                        eval(env, *else_br, (fuel - 1) as nat)
                    }
                }
            }

            // E-Lam: Lambda abstractions evaluate to closures
            Expr::Lam { x, ty, body } => {
                eval_ok(closure_val(x, ty, *body, env))
            }

            // E-App: Function application
            Expr::App { e1, e2 } => {
                let r1 = eval(env, *e1, (fuel - 1) as nat);
                if !is_ok(r1) {
                    eval_err()
                } else {
                    let v1 = get_value(r1);
                    if !is_closure_val(v1) {
                        eval_err()
                    } else {
                        let r2 = eval(env, *e2, (fuel - 1) as nat);
                        if !is_ok(r2) {
                            eval_err()
                        } else {
                            let v2 = get_value(r2);
                            match v1 {
                                Value::VClosure { x, ty: _, body, env: closure_env } => {
                                    let new_env = env_extend(closure_env, x, v2);
                                    eval(new_env, *body, (fuel - 1) as nat)
                                }
                                _ => eval_err(),  // Unreachable
                            }
                        }
                    }
                }
            }

            // E-Eq: Equality comparison (only for nats)
            Expr::Eq { e1, e2 } => {
                let r1 = eval(env, *e1, (fuel - 1) as nat);
                if !is_ok(r1) {
                    eval_err()
                } else {
                    let v1 = get_value(r1);
                    if !is_nat_val(v1) {
                        eval_err()
                    } else {
                        let r2 = eval(env, *e2, (fuel - 1) as nat);
                        if !is_ok(r2) {
                            eval_err()
                        } else {
                            let v2 = get_value(r2);
                            if !is_nat_val(v2) {
                                eval_err()
                            } else {
                                eval_ok(bool_val(get_nat(v1) == get_nat(v2)))
                            }
                        }
                    }
                }
            }

            // E-Lt: Less-than comparison
            Expr::Lt { e1, e2 } => {
                let r1 = eval(env, *e1, (fuel - 1) as nat);
                if !is_ok(r1) {
                    eval_err()
                } else {
                    let v1 = get_value(r1);
                    if !is_nat_val(v1) {
                        eval_err()
                    } else {
                        let r2 = eval(env, *e2, (fuel - 1) as nat);
                        if !is_ok(r2) {
                            eval_err()
                        } else {
                            let v2 = get_value(r2);
                            if !is_nat_val(v2) {
                                eval_err()
                            } else {
                                eval_ok(bool_val(get_nat(v1) < get_nat(v2)))
                            }
                        }
                    }
                }
            }
        }
    }
}

// ----------------------------------------------------------------------------
// Evaluation Properties
// ----------------------------------------------------------------------------

/// Constants always evaluate successfully (with sufficient fuel)
pub proof fn const_eval_ok(env: Env, fuel: nat)
    requires fuel >= 1
    ensures
        is_ok(eval(env, bool_expr(true), fuel)),
        is_ok(eval(env, bool_expr(false), fuel)),
        is_ok(eval(env, nat_expr(42), fuel)),
{
}

/// Lambda always evaluates to a closure
pub proof fn lam_eval_closure(env: Env, x: Id, ty: Ty, body: Expr, fuel: nat)
    requires fuel >= 1
    ensures
        is_ok(eval(env, lam_expr(x, ty, body), fuel)),
        is_closure_val(get_value(eval(env, lam_expr(x, ty, body), fuel))),
{
}

/// Variable lookup succeeds if in environment
pub proof fn var_eval_ok(env: Env, x: Id, v: Value, fuel: nat)
    requires
        fuel >= 1,
        env_lookup(env, x) == Option::Some(v),
    ensures
        is_ok(eval(env, var_expr(x), fuel)),
        get_value(eval(env, var_expr(x), fuel)) == v,
{
    assert(env.dom().contains(x));
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

/// Example: Evaluating constants
pub proof fn example_eval_constants()
{
    let env = empty_env();
    reveal_with_fuel(eval, 2);

    let r_true = eval(env, bool_expr(true), 1);
    assert(is_ok(r_true));
    assert(get_value(r_true) == bool_val(true));

    let r_nat = eval(env, nat_expr(42), 1);
    assert(is_ok(r_nat));
    assert(get_value(r_nat) == nat_val(42));
}

/// Example: Evaluating variable
pub proof fn example_eval_var()
{
    let env = env_extend(empty_env(), X_ID, nat_val(10));
    reveal_with_fuel(eval, 2);

    let r = eval(env, var_expr(X_ID), 1);
    assert(is_ok(r));
    assert(get_value(r) == nat_val(10));
}

/// Example: Evaluating addition
pub proof fn example_eval_plus()
{
    let env = empty_env();
    reveal_with_fuel(eval, 3);

    let e = plus_expr(nat_expr(2), nat_expr(3));
    let r = eval(env, e, 2);
    assert(is_ok(r));
    assert(get_value(r) == nat_val(5));
}

/// Example: Evaluating if-then-else (true branch)
pub proof fn example_eval_if_true()
{
    let env = empty_env();
    reveal_with_fuel(eval, 3);

    let e = if_expr(bool_expr(true), nat_expr(1), nat_expr(2));
    let r = eval(env, e, 2);
    assert(is_ok(r));
    assert(get_value(r) == nat_val(1));
}

/// Example: Evaluating if-then-else (false branch)
pub proof fn example_eval_if_false()
{
    let env = empty_env();
    reveal_with_fuel(eval, 3);

    let e = if_expr(bool_expr(false), nat_expr(1), nat_expr(2));
    let r = eval(env, e, 2);
    assert(is_ok(r));
    assert(get_value(r) == nat_val(2));
}

/// Example: Evaluating lambda (creates closure)
pub proof fn example_eval_lambda()
{
    let env = empty_env();
    reveal_with_fuel(eval, 2);

    let id_fn = lam_expr(X_ID, Ty::TNat, var_expr(X_ID));
    let r = eval(env, id_fn, 1);
    assert(is_ok(r));
    assert(is_closure_val(get_value(r)));
}

/// Example: Evaluating function application
pub proof fn example_eval_app()
{
    let env = empty_env();
    reveal_with_fuel(eval, 5);

    // (\x:Nat. x) 5 => 5
    let id_fn = lam_expr(X_ID, Ty::TNat, var_expr(X_ID));
    let e = app_expr(id_fn, nat_expr(5));
    let r = eval(env, e, 4);
    assert(is_ok(r));
    assert(get_value(r) == nat_val(5));
}

/// Example: Evaluating equality
pub proof fn example_eval_eq()
{
    let env = empty_env();
    reveal_with_fuel(eval, 3);

    let e1 = Expr::Eq { e1: Box::new(nat_expr(5)), e2: Box::new(nat_expr(5)) };
    let r1 = eval(env, e1, 2);
    assert(is_ok(r1));
    assert(get_value(r1) == bool_val(true));

    let e2 = Expr::Eq { e1: Box::new(nat_expr(5)), e2: Box::new(nat_expr(3)) };
    let r2 = eval(env, e2, 2);
    assert(is_ok(r2));
    assert(get_value(r2) == bool_val(false));
}

/// Example: Evaluating less-than
pub proof fn example_eval_lt()
{
    let env = empty_env();
    reveal_with_fuel(eval, 3);

    let e1 = Expr::Lt { e1: Box::new(nat_expr(3)), e2: Box::new(nat_expr(5)) };
    let r1 = eval(env, e1, 2);
    assert(is_ok(r1));
    assert(get_value(r1) == bool_val(true));

    let e2 = Expr::Lt { e1: Box::new(nat_expr(5)), e2: Box::new(nat_expr(3)) };
    let r2 = eval(env, e2, 2);
    assert(is_ok(r2));
    assert(get_value(r2) == bool_val(false));
}

/// Example: Evaluation error (unbound variable)
pub proof fn example_eval_error()
{
    let env = empty_env();
    reveal_with_fuel(eval, 2);

    let r = eval(env, var_expr(X_ID), 1);
    assert(!is_ok(r));
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_lang_eval_examples_verify()
{
    example_eval_constants();
    example_eval_var();
    example_eval_plus();
    example_eval_if_true();
    example_eval_if_false();
    example_eval_lambda();
    example_eval_app();
    example_eval_eq();
    example_eval_lt();
    example_eval_error();

    // Property proofs
    const_eval_ok(empty_env(), 5nat);
    lam_eval_closure(empty_env(), X_ID, Ty::TBool, var_expr(X_ID), 5nat);
}

pub fn main() {
    proof {
        qc_lang_eval_examples_verify();
    }
}

} // verus!

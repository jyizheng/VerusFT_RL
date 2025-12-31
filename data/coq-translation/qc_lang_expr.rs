use vstd::prelude::*;

verus! {

// ============================================================================
// QC Language Case Study: Expressions
// Expression syntax for a typed imperative language
// ============================================================================

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

// ----------------------------------------------------------------------------
// Expression Definition
// ----------------------------------------------------------------------------

/// Expressions in our typed imperative language:
/// - Var: variable reference
/// - BoolConst: boolean constant (true/false)
/// - NatConst: natural number constant
/// - Plus: addition of two expressions
/// - If: conditional expression
/// - App: function application
/// - Lam: lambda abstraction (anonymous function)
/// - Eq: equality comparison
/// - Lt: less than comparison
#[derive(PartialEq, Eq)]
pub enum Expr {
    Var { x: Id },                                              // Variable
    BoolConst { b: bool },                                      // Boolean constant
    NatConst { n: nat },                                        // Natural constant
    Plus { e1: Box<Expr>, e2: Box<Expr> },                     // Addition
    If { cond: Box<Expr>, then_br: Box<Expr>, else_br: Box<Expr> }, // Conditional
    App { e1: Box<Expr>, e2: Box<Expr> },                      // Application
    Lam { x: Id, ty: Ty, body: Box<Expr> },                    // Lambda abstraction
    Eq { e1: Box<Expr>, e2: Box<Expr> },                       // Equality
    Lt { e1: Box<Expr>, e2: Box<Expr> },                       // Less than
}

// ----------------------------------------------------------------------------
// Expression Constructors (as spec functions)
// ----------------------------------------------------------------------------

pub open spec fn var_expr(x: Id) -> Expr {
    Expr::Var { x }
}

pub open spec fn bool_expr(b: bool) -> Expr {
    Expr::BoolConst { b }
}

pub open spec fn nat_expr(n: nat) -> Expr {
    Expr::NatConst { n }
}

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

pub open spec fn eq_expr(e1: Expr, e2: Expr) -> Expr {
    Expr::Eq { e1: Box::new(e1), e2: Box::new(e2) }
}

pub open spec fn lt_expr(e1: Expr, e2: Expr) -> Expr {
    Expr::Lt { e1: Box::new(e1), e2: Box::new(e2) }
}

// ----------------------------------------------------------------------------
// Expression Properties
// ----------------------------------------------------------------------------

/// Check if an expression is a value (can't be reduced further)
pub open spec fn is_value(e: Expr) -> bool {
    match e {
        Expr::BoolConst { .. } => true,
        Expr::NatConst { .. } => true,
        Expr::Lam { .. } => true,
        _ => false,
    }
}

/// Check if an expression is a constant
pub open spec fn is_const(e: Expr) -> bool {
    match e {
        Expr::BoolConst { .. } => true,
        Expr::NatConst { .. } => true,
        _ => false,
    }
}

/// Check if an expression is an atomic expression (var or const)
pub open spec fn is_atomic(e: Expr) -> bool {
    match e {
        Expr::Var { .. } => true,
        Expr::BoolConst { .. } => true,
        Expr::NatConst { .. } => true,
        _ => false,
    }
}

// ----------------------------------------------------------------------------
// Expression Size (for termination proofs)
// ----------------------------------------------------------------------------

/// Size of an expression (structural)
pub open spec fn expr_size(e: Expr) -> nat
    decreases e
{
    match e {
        Expr::Var { .. } => 1,
        Expr::BoolConst { .. } => 1,
        Expr::NatConst { .. } => 1,
        Expr::Plus { e1, e2 } => 1 + expr_size(*e1) + expr_size(*e2),
        Expr::If { cond, then_br, else_br } =>
            1 + expr_size(*cond) + expr_size(*then_br) + expr_size(*else_br),
        Expr::App { e1, e2 } => 1 + expr_size(*e1) + expr_size(*e2),
        Expr::Lam { x: _, ty: _, body } => 1 + expr_size(*body),
        Expr::Eq { e1, e2 } => 1 + expr_size(*e1) + expr_size(*e2),
        Expr::Lt { e1, e2 } => 1 + expr_size(*e1) + expr_size(*e2),
    }
}

/// Expression size is always positive
pub proof fn expr_size_positive(e: Expr)
    ensures expr_size(e) >= 1
    decreases e
{
    match e {
        Expr::Var { .. } => {}
        Expr::BoolConst { .. } => {}
        Expr::NatConst { .. } => {}
        Expr::Plus { e1, e2 } => {
            expr_size_positive(*e1);
            expr_size_positive(*e2);
        }
        Expr::If { cond, then_br, else_br } => {
            expr_size_positive(*cond);
            expr_size_positive(*then_br);
            expr_size_positive(*else_br);
        }
        Expr::App { e1, e2 } => {
            expr_size_positive(*e1);
            expr_size_positive(*e2);
        }
        Expr::Lam { x: _, ty: _, body } => {
            expr_size_positive(*body);
        }
        Expr::Eq { e1, e2 } => {
            expr_size_positive(*e1);
            expr_size_positive(*e2);
        }
        Expr::Lt { e1, e2 } => {
            expr_size_positive(*e1);
            expr_size_positive(*e2);
        }
    }
}

// ----------------------------------------------------------------------------
// Free Variables
// ----------------------------------------------------------------------------

/// Check if a variable x is free in expression e
pub open spec fn free_in(x: Id, e: Expr) -> bool
    decreases e
{
    match e {
        Expr::Var { x: y } => x == y,
        Expr::BoolConst { .. } => false,
        Expr::NatConst { .. } => false,
        Expr::Plus { e1, e2 } => free_in(x, *e1) || free_in(x, *e2),
        Expr::If { cond, then_br, else_br } =>
            free_in(x, *cond) || free_in(x, *then_br) || free_in(x, *else_br),
        Expr::App { e1, e2 } => free_in(x, *e1) || free_in(x, *e2),
        Expr::Lam { x: y, ty: _, body } => x != y && free_in(x, *body),
        Expr::Eq { e1, e2 } => free_in(x, *e1) || free_in(x, *e2),
        Expr::Lt { e1, e2 } => free_in(x, *e1) || free_in(x, *e2),
    }
}

/// An expression is closed if it has no free variables
pub open spec fn closed(e: Expr) -> bool {
    forall|x: Id| !free_in(x, e)
}

// ----------------------------------------------------------------------------
// Substitution [x := s]e
// ----------------------------------------------------------------------------

/// Capture-avoiding substitution: replace free occurrences of x with s in e
pub open spec fn subst(x: Id, s: Expr, e: Expr) -> Expr
    decreases e
{
    match e {
        Expr::Var { x: y } => if x == y { s } else { e },
        Expr::BoolConst { .. } => e,
        Expr::NatConst { .. } => e,
        Expr::Plus { e1, e2 } =>
            plus_expr(subst(x, s, *e1), subst(x, s, *e2)),
        Expr::If { cond, then_br, else_br } =>
            if_expr(subst(x, s, *cond), subst(x, s, *then_br), subst(x, s, *else_br)),
        Expr::App { e1, e2 } =>
            app_expr(subst(x, s, *e1), subst(x, s, *e2)),
        Expr::Lam { x: y, ty, body } =>
            if x == y {
                e  // x is bound, no substitution
            } else {
                lam_expr(y, ty, subst(x, s, *body))
            },
        Expr::Eq { e1, e2 } =>
            eq_expr(subst(x, s, *e1), subst(x, s, *e2)),
        Expr::Lt { e1, e2 } =>
            lt_expr(subst(x, s, *e1), subst(x, s, *e2)),
    }
}

// ----------------------------------------------------------------------------
// Substitution Properties
// ----------------------------------------------------------------------------

/// Substitution with the same variable is identity
pub proof fn subst_var_same(x: Id, s: Expr)
    ensures subst(x, s, var_expr(x)) == s
{
}

/// Substitution with different variable is identity
pub proof fn subst_var_diff(x: Id, y: Id, s: Expr)
    requires x != y
    ensures subst(x, s, var_expr(y)) == var_expr(y)
{
}

/// Substitution doesn't affect non-free variables
pub proof fn subst_not_free(x: Id, s: Expr, e: Expr)
    requires !free_in(x, e)
    ensures subst(x, s, e) == e
    decreases e
{
    match e {
        Expr::Var { x: y } => {
            assert(x != y);
        }
        Expr::BoolConst { .. } => {}
        Expr::NatConst { .. } => {}
        Expr::Plus { e1, e2 } => {
            subst_not_free(x, s, *e1);
            subst_not_free(x, s, *e2);
        }
        Expr::If { cond, then_br, else_br } => {
            subst_not_free(x, s, *cond);
            subst_not_free(x, s, *then_br);
            subst_not_free(x, s, *else_br);
        }
        Expr::App { e1, e2 } => {
            subst_not_free(x, s, *e1);
            subst_not_free(x, s, *e2);
        }
        Expr::Lam { x: y, ty: _, body } => {
            if x == y {
                // Already handled by the match
            } else {
                subst_not_free(x, s, *body);
            }
        }
        Expr::Eq { e1, e2 } => {
            subst_not_free(x, s, *e1);
            subst_not_free(x, s, *e2);
        }
        Expr::Lt { e1, e2 } => {
            subst_not_free(x, s, *e1);
            subst_not_free(x, s, *e2);
        }
    }
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

/// Example: Values
pub proof fn example_values()
{
    assert(is_value(bool_expr(true)));
    assert(is_value(nat_expr(42)));
    assert(is_value(lam_expr(X_ID, Ty::TBool, var_expr(X_ID))));
    assert(!is_value(var_expr(X_ID)));
    assert(!is_value(plus_expr(nat_expr(1), nat_expr(2))));
}

/// Example: Constants
pub proof fn example_constants()
{
    assert(is_const(bool_expr(true)));
    assert(is_const(bool_expr(false)));
    assert(is_const(nat_expr(0)));
    assert(!is_const(var_expr(X_ID)));
}

/// Example: Expression size
pub proof fn example_expr_size()
{
    assert(expr_size(var_expr(X_ID)) == 1);
    assert(expr_size(bool_expr(true)) == 1);
    assert(expr_size(nat_expr(42)) == 1);
    reveal_with_fuel(expr_size, 3);
    assert(expr_size(plus_expr(nat_expr(1), nat_expr(2))) == 3);
}

/// Example: Free variables
pub proof fn example_free_vars()
{
    assert(free_in(X_ID, var_expr(X_ID)));
    assert(!free_in(Y_ID, var_expr(X_ID)));
    assert(!free_in(X_ID, bool_expr(true)));
    assert(!free_in(X_ID, lam_expr(X_ID, Ty::TBool, var_expr(X_ID))));
    assert(free_in(X_ID, lam_expr(Y_ID, Ty::TBool, var_expr(X_ID))));
}

/// Example: Closed expressions
pub proof fn example_closed()
{
    assert(closed(bool_expr(true)));
    assert(closed(nat_expr(42)));
    // var_expr is not closed
    assert(free_in(X_ID, var_expr(X_ID)));
}

/// Example: Substitution
pub proof fn example_substitution()
{
    // [x := true](x) = true
    assert(subst(X_ID, bool_expr(true), var_expr(X_ID)) == bool_expr(true));

    // [x := true](y) = y
    assert(subst(X_ID, bool_expr(true), var_expr(Y_ID)) == var_expr(Y_ID));

    // [x := 1](x + 2) = 1 + 2
    let e = plus_expr(var_expr(X_ID), nat_expr(2));
    reveal_with_fuel(subst, 3);
    let result = subst(X_ID, nat_expr(1), e);
    assert(result == plus_expr(nat_expr(1), nat_expr(2)));
}

/// Example: Lambda shadowing
pub proof fn example_lambda_shadowing()
{
    // [x := true](\x:Bool. x) = \x:Bool. x (no change, x is bound)
    let lam = lam_expr(X_ID, Ty::TBool, var_expr(X_ID));
    assert(subst(X_ID, bool_expr(true), lam) == lam);

    // [x := true](\y:Bool. x) = \y:Bool. true (x is free in body)
    let lam2 = lam_expr(Y_ID, Ty::TBool, var_expr(X_ID));
    reveal_with_fuel(subst, 3);
    let result = subst(X_ID, bool_expr(true), lam2);
    assert(result == lam_expr(Y_ID, Ty::TBool, bool_expr(true)));
}

/// Example: Identity function
pub proof fn example_identity()
{
    let id_bool = lam_expr(X_ID, Ty::TBool, var_expr(X_ID));
    assert(is_value(id_bool));
}

/// Example: Factorial pattern (just structure, not evaluation)
pub proof fn example_complex_expr()
{
    // if x == 0 then 1 else x * f(x - 1)
    // Simplified: if (x == 0) then 1 else x
    let body = if_expr(
        eq_expr(var_expr(X_ID), nat_expr(0)),
        nat_expr(1),
        var_expr(X_ID)
    );

    assert(expr_size(body) >= 1);
    reveal_with_fuel(free_in, 5);
    assert(free_in(X_ID, body));
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_lang_expr_examples_verify()
{
    example_values();
    example_constants();
    example_expr_size();
    example_free_vars();
    example_closed();
    example_substitution();
    example_lambda_shadowing();
    example_identity();
    example_complex_expr();

    // Property proofs
    expr_size_positive(var_expr(X_ID));
    subst_var_same(X_ID, bool_expr(true));
    subst_var_diff(X_ID, Y_ID, bool_expr(true));
    subst_not_free(X_ID, bool_expr(true), nat_expr(42));
}

pub fn main() {
    proof {
        qc_lang_expr_examples_verify();
    }
}

} // verus!

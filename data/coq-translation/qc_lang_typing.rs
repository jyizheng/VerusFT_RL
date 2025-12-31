use vstd::prelude::*;
use vstd::map::*;

verus! {

// ============================================================================
// QC Language Case Study: Type Checking
// Type inference rules for a typed imperative language
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

pub open spec fn is_arrow_type(ty: Ty) -> bool {
    match ty { Ty::TArrow { .. } => true, _ => false }
}

pub open spec fn arrow_domain(ty: Ty) -> Ty {
    match ty { Ty::TArrow { t1, .. } => *t1, _ => Ty::TBool }
}

pub open spec fn arrow_codomain(ty: Ty) -> Ty {
    match ty { Ty::TArrow { t1: _, t2 } => *t2, _ => Ty::TBool }
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
pub open spec fn eq_expr(e1: Expr, e2: Expr) -> Expr {
    Expr::Eq { e1: Box::new(e1), e2: Box::new(e2) }
}
pub open spec fn lt_expr(e1: Expr, e2: Expr) -> Expr {
    Expr::Lt { e1: Box::new(e1), e2: Box::new(e2) }
}

// Typing context
pub type Context = Map<Id, Ty>;

pub open spec fn empty_ctx() -> Context {
    Map::<Id, Ty>::empty()
}

pub open spec fn ctx_extend(ctx: Context, x: Id, ty: Ty) -> Context {
    ctx.insert(x, ty)
}

pub open spec fn ctx_lookup(ctx: Context, x: Id) -> Option<Ty> {
    if ctx.dom().contains(x) {
        Option::Some(ctx[x])
    } else {
        Option::None
    }
}

// ----------------------------------------------------------------------------
// Typing Relation: ctx |- e : ty
// ----------------------------------------------------------------------------

/// Check if expression e has type ty in context ctx
pub open spec fn has_type(ctx: Context, e: Expr, ty: Ty) -> bool
    decreases e
{
    match e {
        // T-Var: Variables have their type from the context
        Expr::Var { x } => {
            ctx.dom().contains(x) && ctx[x] == ty
        }

        // T-BoolConst: Boolean constants have type Bool
        Expr::BoolConst { .. } => {
            ty == Ty::TBool
        }

        // T-NatConst: Natural constants have type Nat
        Expr::NatConst { .. } => {
            ty == Ty::TNat
        }

        // T-Plus: Both operands must be Nat, result is Nat
        Expr::Plus { e1, e2 } => {
            ty == Ty::TNat &&
            has_type(ctx, *e1, Ty::TNat) &&
            has_type(ctx, *e2, Ty::TNat)
        }

        // T-If: Condition is Bool, branches have same type
        Expr::If { cond, then_br, else_br } => {
            has_type(ctx, *cond, Ty::TBool) &&
            has_type(ctx, *then_br, ty) &&
            has_type(ctx, *else_br, ty)
        }

        // T-Lam: Lambda abstraction
        Expr::Lam { x, ty: ty_param, body } => {
            match ty {
                Ty::TArrow { t1, t2 } =>
                    *t1 == ty_param &&
                    has_type(ctx_extend(ctx, x, ty_param), *body, *t2),
                _ => false,
            }
        }

        // T-App: Function application
        Expr::App { e1, e2 } => {
            exists|ty_arg: Ty|
                has_type(ctx, *e1, arrow_type(ty_arg, ty)) &&
                has_type(ctx, *e2, ty_arg)
        }

        // T-Eq: Equality comparison on nats produces bool
        Expr::Eq { e1, e2 } => {
            ty == Ty::TBool &&
            has_type(ctx, *e1, Ty::TNat) &&
            has_type(ctx, *e2, Ty::TNat)
        }

        // T-Lt: Less-than comparison on nats produces bool
        Expr::Lt { e1, e2 } => {
            ty == Ty::TBool &&
            has_type(ctx, *e1, Ty::TNat) &&
            has_type(ctx, *e2, Ty::TNat)
        }
    }
}

// ----------------------------------------------------------------------------
// Type Inference (returns Option<Ty>)
// ----------------------------------------------------------------------------

/// Infer the type of expression e in context ctx
pub open spec fn infer_type(ctx: Context, e: Expr) -> Option<Ty>
    decreases e
{
    match e {
        Expr::Var { x } => ctx_lookup(ctx, x),

        Expr::BoolConst { .. } => Option::Some(Ty::TBool),

        Expr::NatConst { .. } => Option::Some(Ty::TNat),

        Expr::Plus { e1, e2 } => {
            match (infer_type(ctx, *e1), infer_type(ctx, *e2)) {
                (Option::Some(Ty::TNat), Option::Some(Ty::TNat)) =>
                    Option::Some(Ty::TNat),
                _ => Option::None,
            }
        }

        Expr::If { cond, then_br, else_br } => {
            match (infer_type(ctx, *cond), infer_type(ctx, *then_br), infer_type(ctx, *else_br)) {
                (Option::Some(Ty::TBool), Option::Some(ty1), Option::Some(ty2)) =>
                    if ty1 == ty2 { Option::Some(ty1) } else { Option::None },
                _ => Option::None,
            }
        }

        Expr::Lam { x, ty: ty_param, body } => {
            match infer_type(ctx_extend(ctx, x, ty_param), *body) {
                Option::Some(ty_body) =>
                    Option::Some(arrow_type(ty_param, ty_body)),
                Option::None => Option::None,
            }
        }

        Expr::App { e1, e2 } => {
            match (infer_type(ctx, *e1), infer_type(ctx, *e2)) {
                (Option::Some(Ty::TArrow { t1, t2 }), Option::Some(ty_arg)) =>
                    if *t1 == ty_arg { Option::Some(*t2) } else { Option::None },
                _ => Option::None,
            }
        }

        Expr::Eq { e1, e2 } => {
            match (infer_type(ctx, *e1), infer_type(ctx, *e2)) {
                (Option::Some(Ty::TNat), Option::Some(Ty::TNat)) =>
                    Option::Some(Ty::TBool),
                _ => Option::None,
            }
        }

        Expr::Lt { e1, e2 } => {
            match (infer_type(ctx, *e1), infer_type(ctx, *e2)) {
                (Option::Some(Ty::TNat), Option::Some(Ty::TNat)) =>
                    Option::Some(Ty::TBool),
                _ => Option::None,
            }
        }
    }
}

// ----------------------------------------------------------------------------
// Type Checking (returns bool)
// ----------------------------------------------------------------------------

/// Check if expression e has type ty in context ctx
pub open spec fn check_type(ctx: Context, e: Expr, ty: Ty) -> bool {
    match infer_type(ctx, e) {
        Option::Some(inferred) => inferred == ty,
        Option::None => false,
    }
}

// ----------------------------------------------------------------------------
// Well-Typed Expressions
// ----------------------------------------------------------------------------

/// An expression is well-typed if it has some type
pub open spec fn well_typed(ctx: Context, e: Expr) -> bool {
    infer_type(ctx, e).is_some()
}

/// Closed well-typed expression
pub open spec fn closed_well_typed(e: Expr) -> bool {
    well_typed(empty_ctx(), e)
}

// ----------------------------------------------------------------------------
// Typing Properties
// ----------------------------------------------------------------------------

/// Inference implies has_type (for specific simple cases)
pub proof fn inference_implies_has_type_const(ctx: Context, b: bool)
    ensures has_type(ctx, bool_expr(b), Ty::TBool)
{
}

pub proof fn inference_implies_has_type_nat(ctx: Context, n: nat)
    ensures has_type(ctx, nat_expr(n), Ty::TNat)
{
}

pub proof fn inference_implies_has_type_var(ctx: Context, x: Id, ty: Ty)
    requires ctx.dom().contains(x) && ctx[x] == ty
    ensures has_type(ctx, var_expr(x), ty)
{
}

/// Type uniqueness: if e has type ty1 and ty2, then ty1 == ty2
pub proof fn type_uniqueness(ctx: Context, e: Expr, ty1: Ty, ty2: Ty)
    requires
        infer_type(ctx, e) == Option::Some(ty1),
        infer_type(ctx, e) == Option::Some(ty2),
    ensures ty1 == ty2
{
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

/// Example: Boolean constant typing
pub proof fn example_bool_typing()
{
    let e = bool_expr(true);
    assert(infer_type(empty_ctx(), e) == Option::Some(Ty::TBool));
    assert(has_type(empty_ctx(), e, Ty::TBool));
}

/// Example: Natural constant typing
pub proof fn example_nat_typing()
{
    let e = nat_expr(42);
    assert(infer_type(empty_ctx(), e) == Option::Some(Ty::TNat));
    assert(has_type(empty_ctx(), e, Ty::TNat));
}

/// Example: Variable typing
pub proof fn example_var_typing()
{
    let ctx = ctx_extend(empty_ctx(), X_ID, Ty::TNat);
    let e = var_expr(X_ID);
    assert(infer_type(ctx, e) == Option::Some(Ty::TNat));
    assert(has_type(ctx, e, Ty::TNat));
}

/// Example: Plus typing
pub proof fn example_plus_typing()
{
    let e = plus_expr(nat_expr(1), nat_expr(2));
    reveal_with_fuel(infer_type, 3);
    assert(infer_type(empty_ctx(), e) == Option::Some(Ty::TNat));
}

/// Example: If-then-else typing
pub proof fn example_if_typing()
{
    let e = if_expr(bool_expr(true), nat_expr(1), nat_expr(2));
    reveal_with_fuel(infer_type, 3);
    assert(infer_type(empty_ctx(), e) == Option::Some(Ty::TNat));
}

/// Example: Lambda typing
pub proof fn example_lambda_typing()
{
    // \x:Nat. x : Nat -> Nat
    let e = lam_expr(X_ID, Ty::TNat, var_expr(X_ID));
    reveal_with_fuel(infer_type, 3);
    assert(infer_type(empty_ctx(), e) == Option::Some(arrow_type(Ty::TNat, Ty::TNat)));
}

/// Example: Application typing
pub proof fn example_app_typing()
{
    // (\x:Nat. x) 5 : Nat
    let id_fn = lam_expr(X_ID, Ty::TNat, var_expr(X_ID));
    let e = app_expr(id_fn, nat_expr(5));
    reveal_with_fuel(infer_type, 5);
    assert(infer_type(empty_ctx(), e) == Option::Some(Ty::TNat));
}

/// Example: Equality typing
pub proof fn example_eq_typing()
{
    let e = eq_expr(nat_expr(5), nat_expr(5));
    reveal_with_fuel(infer_type, 3);
    assert(infer_type(empty_ctx(), e) == Option::Some(Ty::TBool));
}

/// Example: Less-than typing
pub proof fn example_lt_typing()
{
    let e = lt_expr(nat_expr(3), nat_expr(5));
    reveal_with_fuel(infer_type, 3);
    assert(infer_type(empty_ctx(), e) == Option::Some(Ty::TBool));
}

/// Example: Type error (unbound variable)
pub proof fn example_type_error_var()
{
    let e = var_expr(X_ID);
    assert(infer_type(empty_ctx(), e) == Option::<Ty>::None);
}

/// Example: Type error (adding booleans)
pub proof fn example_type_error_plus()
{
    let e = plus_expr(bool_expr(true), nat_expr(1));
    reveal_with_fuel(infer_type, 3);
    assert(infer_type(empty_ctx(), e) == Option::<Ty>::None);
}

/// Example: Well-typed expression
pub proof fn example_well_typed()
{
    let e = nat_expr(42);
    assert(well_typed(empty_ctx(), e));
    assert(closed_well_typed(e));
}

/// Example: Ill-typed expression
pub proof fn example_ill_typed()
{
    let e = var_expr(X_ID);
    assert(!well_typed(empty_ctx(), e));
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_lang_typing_examples_verify()
{
    example_bool_typing();
    example_nat_typing();
    example_var_typing();
    example_plus_typing();
    example_if_typing();
    example_lambda_typing();
    example_app_typing();
    example_eq_typing();
    example_lt_typing();
    example_type_error_var();
    example_type_error_plus();
    example_well_typed();
    example_ill_typed();

    // Property proofs
    inference_implies_has_type_const(empty_ctx(), true);
    inference_implies_has_type_nat(empty_ctx(), 42);
    type_uniqueness(empty_ctx(), nat_expr(42), Ty::TNat, Ty::TNat);
}

pub fn main() {
    proof {
        qc_lang_typing_examples_verify();
    }
}

} // verus!

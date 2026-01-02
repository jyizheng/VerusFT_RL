use vstd::prelude::*;

verus! {

// ============================================================================
// QC Lang: Well-Typed Expression Generation
// ============================================================================
// Models generation of expressions that are guaranteed to be well-typed.
// This is type-directed generation where the target type guides construction.

// ----------------------------------------------------------------------------
// Types
// ----------------------------------------------------------------------------

#[derive(PartialEq, Eq)]
pub enum Ty {
    TBool,
    TNat,
    TArrow { t1: Box<Ty>, t2: Box<Ty> },
}

pub open spec fn ty_size(t: Ty) -> nat
    decreases t
{
    match t {
        Ty::TBool => 1,
        Ty::TNat => 1,
        Ty::TArrow { t1, t2 } => 1 + ty_size(*t1) + ty_size(*t2),
    }
}

// ----------------------------------------------------------------------------
// Expressions
// ----------------------------------------------------------------------------

pub type Var = nat;

#[derive(PartialEq, Eq)]
pub enum Expr {
    Var { x: Var },
    Lam { x: Var, ty: Ty, body: Box<Expr> },
    App { e1: Box<Expr>, e2: Box<Expr> },
    Tru,
    Fls,
    If { cond: Box<Expr>, then_br: Box<Expr>, else_br: Box<Expr> },
    Zero,
    Succ { e: Box<Expr> },
    Pred { e: Box<Expr> },
    IsZero { e: Box<Expr> },
}

// ----------------------------------------------------------------------------
// Typing Context
// ----------------------------------------------------------------------------

pub type Context = Map<Var, Ty>;

pub open spec fn empty_ctx() -> Context {
    Map::<Var, Ty>::empty()
}

pub open spec fn ctx_extend(ctx: Context, x: Var, ty: Ty) -> Context {
    ctx.insert(x, ty)
}

pub open spec fn ctx_lookup(ctx: Context, x: Var) -> Option<Ty> {
    if ctx.dom().contains(x) {
        Option::Some(ctx[x])
    } else {
        Option::None
    }
}

// ----------------------------------------------------------------------------
// Typing Relation
// ----------------------------------------------------------------------------

pub open spec fn has_type(ctx: Context, e: Expr, ty: Ty) -> bool
    decreases e
{
    match e {
        Expr::Var { x } => ctx_lookup(ctx, x) == Option::Some(ty),

        Expr::Lam { x, ty: ty_param, body } => {
            match ty {
                Ty::TArrow { t1, t2 } =>
                    *t1 == ty_param &&
                    has_type(ctx_extend(ctx, x, ty_param), *body, *t2),
                _ => false,
            }
        }

        Expr::App { e1, e2 } => {
            exists|ty_arg: Ty|
                has_type(ctx, *e1, Ty::TArrow { t1: Box::new(ty_arg), t2: Box::new(ty) }) &&
                has_type(ctx, *e2, ty_arg)
        }

        Expr::Tru => ty == Ty::TBool,
        Expr::Fls => ty == Ty::TBool,

        Expr::If { cond, then_br, else_br } => {
            has_type(ctx, *cond, Ty::TBool) &&
            has_type(ctx, *then_br, ty) &&
            has_type(ctx, *else_br, ty)
        }

        Expr::Zero => ty == Ty::TNat,
        Expr::Succ { e } => ty == Ty::TNat && has_type(ctx, *e, Ty::TNat),
        Expr::Pred { e } => ty == Ty::TNat && has_type(ctx, *e, Ty::TNat),
        Expr::IsZero { e } => ty == Ty::TBool && has_type(ctx, *e, Ty::TNat),
    }
}

// ----------------------------------------------------------------------------
// Type-Directed Generation
// ----------------------------------------------------------------------------

// Generate expressions of a specific type with size bound
pub open spec fn gen_typed(ctx: Context, ty: Ty, size: nat) -> Set<Expr> {
    Set::new(|e: Expr| has_type(ctx, e, ty) && expr_size(e) <= size)
}

// Expression size helper
pub open spec fn expr_size(e: Expr) -> nat
    decreases e
{
    match e {
        Expr::Var { .. } => 1,
        Expr::Lam { body, .. } => 1 + expr_size(*body),
        Expr::App { e1, e2 } => 1 + expr_size(*e1) + expr_size(*e2),
        Expr::Tru => 1,
        Expr::Fls => 1,
        Expr::If { cond, then_br, else_br } =>
            1 + expr_size(*cond) + expr_size(*then_br) + expr_size(*else_br),
        Expr::Zero => 1,
        Expr::Succ { e } => 1 + expr_size(*e),
        Expr::Pred { e } => 1 + expr_size(*e),
        Expr::IsZero { e } => 1 + expr_size(*e),
    }
}

// ----------------------------------------------------------------------------
// Generators for Specific Types
// ----------------------------------------------------------------------------

// Generate Bool-typed expressions
pub open spec fn gen_bool(ctx: Context, size: nat) -> Set<Expr> {
    gen_typed(ctx, Ty::TBool, size)
}

// Generate Nat-typed expressions
pub open spec fn gen_nat(ctx: Context, size: nat) -> Set<Expr> {
    gen_typed(ctx, Ty::TNat, size)
}

// Generate function-typed expressions
pub open spec fn gen_arrow(ctx: Context, t1: Ty, t2: Ty, size: nat) -> Set<Expr> {
    gen_typed(ctx, Ty::TArrow { t1: Box::new(t1), t2: Box::new(t2) }, size)
}

// ----------------------------------------------------------------------------
// Base Generators
// ----------------------------------------------------------------------------

// Bool literals
pub open spec fn gen_bool_lit() -> Set<Expr> {
    Set::new(|e: Expr| e == Expr::Tru || e == Expr::Fls)
}

// Nat zero
pub open spec fn gen_nat_zero() -> Set<Expr> {
    Set::new(|e: Expr| e == Expr::Zero)
}

// Variables of type T from context
pub open spec fn gen_var_of_type(ctx: Context, ty: Ty) -> Set<Expr> {
    Set::new(|e: Expr|
        exists|x: Var| ctx_lookup(ctx, x) == Option::Some(ty) && e == Expr::Var { x }
    )
}

// ----------------------------------------------------------------------------
// Compound Generators
// ----------------------------------------------------------------------------

// Generate Succ expressions (produces Nat)
pub open spec fn gen_succ_expr(ctx: Context, size: nat) -> Set<Expr> {
    if size <= 1 {
        Set::empty()
    } else {
        Set::new(|e: Expr|
            exists|inner: Expr|
                gen_nat(ctx, (size - 1) as nat).contains(inner) &&
                e == Expr::Succ { e: Box::new(inner) }
        )
    }
}

// Generate Pred expressions (produces Nat)
pub open spec fn gen_pred_expr(ctx: Context, size: nat) -> Set<Expr> {
    if size <= 1 {
        Set::empty()
    } else {
        Set::new(|e: Expr|
            exists|inner: Expr|
                gen_nat(ctx, (size - 1) as nat).contains(inner) &&
                e == Expr::Pred { e: Box::new(inner) }
        )
    }
}

// Generate IsZero expressions (produces Bool)
pub open spec fn gen_iszero_expr(ctx: Context, size: nat) -> Set<Expr> {
    if size <= 1 {
        Set::empty()
    } else {
        Set::new(|e: Expr|
            exists|inner: Expr|
                gen_nat(ctx, (size - 1) as nat).contains(inner) &&
                e == Expr::IsZero { e: Box::new(inner) }
        )
    }
}

// Generate If expressions of type T
pub open spec fn gen_if_expr(ctx: Context, ty: Ty, size: nat) -> Set<Expr> {
    if size <= 3 {
        Set::empty()
    } else {
        Set::new(|e: Expr|
            exists|c: Expr, t: Expr, f: Expr, s1: nat, s2: nat, s3: nat|
                s1 + s2 + s3 + 1 <= size &&
                gen_bool(ctx, s1).contains(c) &&
                gen_typed(ctx, ty, s2).contains(t) &&
                gen_typed(ctx, ty, s3).contains(f) &&
                e == Expr::If { cond: Box::new(c), then_br: Box::new(t), else_br: Box::new(f) }
        )
    }
}

// Generate Lambda expressions
pub open spec fn gen_lam_expr(ctx: Context, t1: Ty, t2: Ty, size: nat, fresh: Var) -> Set<Expr> {
    if size <= 1 {
        Set::empty()
    } else {
        let extended_ctx = ctx_extend(ctx, fresh, t1);
        Set::new(|e: Expr|
            !ctx.dom().contains(fresh) &&
            exists|body: Expr|
                gen_typed(extended_ctx, t2, (size - 1) as nat).contains(body) &&
                e == Expr::Lam { x: fresh, ty: t1, body: Box::new(body) }
        )
    }
}

// Generate Application expressions
pub open spec fn gen_app_expr(ctx: Context, ty: Ty, size: nat) -> Set<Expr> {
    if size <= 2 {
        Set::empty()
    } else {
        Set::new(|e: Expr|
            exists|e1: Expr, e2: Expr, ty_arg: Ty, s1: nat, s2: nat|
                s1 + s2 + 1 <= size &&
                gen_arrow(ctx, ty_arg, ty, s1).contains(e1) &&
                gen_typed(ctx, ty_arg, s2).contains(e2) &&
                e == Expr::App { e1: Box::new(e1), e2: Box::new(e2) }
        )
    }
}

// ----------------------------------------------------------------------------
// Generator Properties
// ----------------------------------------------------------------------------

// Bool literals have type Bool
pub proof fn bool_lit_has_type_bool(ctx: Context)
    ensures
        has_type(ctx, Expr::Tru, Ty::TBool),
        has_type(ctx, Expr::Fls, Ty::TBool),
{
}

// Zero has type Nat
pub proof fn zero_has_type_nat(ctx: Context)
    ensures has_type(ctx, Expr::Zero, Ty::TNat)
{
}

// Generated expressions are well-typed
pub proof fn gen_typed_correct(ctx: Context, ty: Ty, size: nat, e: Expr)
    requires gen_typed(ctx, ty, size).contains(e)
    ensures has_type(ctx, e, ty)
{
    // By definition of gen_typed
}

// Succ preserves Nat type
pub proof fn succ_has_type_nat(ctx: Context, e: Expr)
    requires has_type(ctx, e, Ty::TNat)
    ensures has_type(ctx, Expr::Succ { e: Box::new(e) }, Ty::TNat)
{
}

// Pred preserves Nat type
pub proof fn pred_has_type_nat(ctx: Context, e: Expr)
    requires has_type(ctx, e, Ty::TNat)
    ensures has_type(ctx, Expr::Pred { e: Box::new(e) }, Ty::TNat)
{
}

// IsZero produces Bool
pub proof fn iszero_has_type_bool(ctx: Context, e: Expr)
    requires has_type(ctx, e, Ty::TNat)
    ensures has_type(ctx, Expr::IsZero { e: Box::new(e) }, Ty::TBool)
{
}

// ----------------------------------------------------------------------------
// Completeness: Sufficient Generators Exist
// ----------------------------------------------------------------------------

// Non-empty generator for Bool at size >= 1
pub proof fn gen_bool_nonempty(ctx: Context, size: nat)
    requires size >= 1
    ensures
        gen_bool(ctx, size).contains(Expr::Tru),
        gen_bool(ctx, size).contains(Expr::Fls),
{
    bool_lit_has_type_bool(ctx);
    assert(expr_size(Expr::Tru) == 1);
    assert(expr_size(Expr::Fls) == 1);
}

// Non-empty generator for Nat at size >= 1
pub proof fn gen_nat_nonempty(ctx: Context, size: nat)
    requires size >= 1
    ensures gen_nat(ctx, size).contains(Expr::Zero)
{
    zero_has_type_nat(ctx);
    assert(expr_size(Expr::Zero) == 1);
}

// ----------------------------------------------------------------------------
// Type-Directed Generation Strategy
// ----------------------------------------------------------------------------

// Strategy: generate by target type
pub open spec fn generation_strategy(ty: Ty) -> nat {
    match ty {
        Ty::TBool => 1,  // Use: true, false, iszero, if
        Ty::TNat => 2,   // Use: 0, succ, pred, if
        Ty::TArrow { .. } => 3,  // Use: lambda, if
    }
}

// Count possible base forms for a type
pub open spec fn base_forms_count(ty: Ty) -> nat {
    match ty {
        Ty::TBool => 2,  // true, false
        Ty::TNat => 1,   // zero
        Ty::TArrow { .. } => 0,  // No base forms
    }
}

// Types with base forms can be generated at size 1
pub proof fn base_forms_sufficient(ctx: Context, ty: Ty)
    requires base_forms_count(ty) > 0
    ensures !gen_typed(ctx, ty, 1).is_empty()
{
    match ty {
        Ty::TBool => {
            assert(gen_typed(ctx, Ty::TBool, 1).contains(Expr::Tru));
        }
        Ty::TNat => {
            assert(gen_typed(ctx, Ty::TNat, 1).contains(Expr::Zero));
        }
        Ty::TArrow { .. } => {
            // Vacuously true since requires is false
        }
    }
}

// ----------------------------------------------------------------------------
// Size Distribution for Compound Expressions
// ----------------------------------------------------------------------------

// Distribute size between subexpressions
pub open spec fn valid_size_split(total: nat, s1: nat, s2: nat) -> bool {
    s1 + s2 + 1 <= total && s1 >= 1 && s2 >= 1
}

// For if expressions (3 subexpressions)
pub open spec fn valid_size_split_3(total: nat, s1: nat, s2: nat, s3: nat) -> bool {
    s1 + s2 + s3 + 1 <= total && s1 >= 1 && s2 >= 1 && s3 >= 1
}

pub proof fn size_split_exists(total: nat)
    requires total >= 3
    ensures valid_size_split(total, 1, 1)
{
    assert(1 + 1 + 1 == 3);
    assert(3 <= total);
}

pub proof fn size_split_3_exists(total: nat)
    requires total >= 4
    ensures valid_size_split_3(total, 1, 1, 1)
{
    assert(1 + 1 + 1 + 1 == 4);
    assert(4 <= total);
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_gen_bool()
{
    let ctx = empty_ctx();

    // Size 1: literals
    gen_bool_nonempty(ctx, 1);
    assert(gen_bool(ctx, 1).contains(Expr::Tru));
    assert(gen_bool(ctx, 1).contains(Expr::Fls));

    // Size 2: iszero(zero)
    let iszero_zero = Expr::IsZero { e: Box::new(Expr::Zero) };
    iszero_has_type_bool(ctx, Expr::Zero);
    assert(has_type(ctx, iszero_zero, Ty::TBool));
}

pub proof fn example_gen_nat()
{
    let ctx = empty_ctx();

    // Size 1: zero
    gen_nat_nonempty(ctx, 1);
    assert(gen_nat(ctx, 1).contains(Expr::Zero));

    // Size 2: succ(zero)
    let succ_zero = Expr::Succ { e: Box::new(Expr::Zero) };
    succ_has_type_nat(ctx, Expr::Zero);
    assert(has_type(ctx, succ_zero, Ty::TNat));
    assert(expr_size(succ_zero) == 2);
}

pub proof fn example_gen_arrow()
{
    let ctx = empty_ctx();

    // Identity function: \x:Bool. x
    let id_bool = Expr::Lam {
        x: 0,
        ty: Ty::TBool,
        body: Box::new(Expr::Var { x: 0 })
    };

    // Check it has type Bool -> Bool
    let extended = ctx_extend(ctx, 0, Ty::TBool);
    assert(ctx_lookup(extended, 0) == Option::Some(Ty::TBool));
    assert(has_type(extended, Expr::Var { x: 0 }, Ty::TBool));
    assert(has_type(ctx, id_bool, Ty::TArrow {
        t1: Box::new(Ty::TBool),
        t2: Box::new(Ty::TBool)
    }));
}

pub proof fn example_gen_with_context()
{
    // Context with x : Nat
    let ctx = ctx_extend(empty_ctx(), 0, Ty::TNat);

    // Can generate: x, 0, succ(x), succ(0), etc.
    assert(ctx_lookup(ctx, 0) == Option::Some(Ty::TNat));
    assert(has_type(ctx, Expr::Var { x: 0 }, Ty::TNat));

    // Variable is in generator
    assert(gen_var_of_type(ctx, Ty::TNat).contains(Expr::Var { x: 0 }));
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn gen_welltyped_verify()
{
    let ctx = empty_ctx();

    bool_lit_has_type_bool(ctx);
    zero_has_type_nat(ctx);

    gen_bool_nonempty(ctx, 1);
    gen_nat_nonempty(ctx, 1);

    size_split_exists(5);
    size_split_3_exists(5);

    example_gen_bool();
    example_gen_nat();
    example_gen_arrow();
    example_gen_with_context();
}

pub fn main() {
    proof {
        gen_welltyped_verify();
    }
}

} // verus!

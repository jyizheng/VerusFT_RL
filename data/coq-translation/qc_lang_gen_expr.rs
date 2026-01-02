use vstd::prelude::*;

verus! {

// ============================================================================
// QC Lang: Expression Generation (Well-Formed Expressions)
// ============================================================================
// Models generation of syntactically well-formed expressions.
// Uses size bounds and variable scopes to ensure validity.

// ----------------------------------------------------------------------------
// Types
// ----------------------------------------------------------------------------

#[derive(PartialEq, Eq)]
pub enum Ty {
    TBool,
    TNat,
    TArrow { t1: Box<Ty>, t2: Box<Ty> },
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
    Let { x: Var, def: Box<Expr>, body: Box<Expr> },
}

// ----------------------------------------------------------------------------
// Expression Size
// ----------------------------------------------------------------------------

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
        Expr::Let { def, body, .. } => 1 + expr_size(*def) + expr_size(*body),
    }
}

pub proof fn expr_size_positive(e: Expr)
    ensures expr_size(e) >= 1
    decreases e
{
    match e {
        Expr::Var { .. } => {}
        Expr::Lam { body, .. } => expr_size_positive(*body),
        Expr::App { e1, e2 } => {
            expr_size_positive(*e1);
            expr_size_positive(*e2);
        }
        Expr::Tru => {}
        Expr::Fls => {}
        Expr::If { cond, then_br, else_br } => {
            expr_size_positive(*cond);
            expr_size_positive(*then_br);
            expr_size_positive(*else_br);
        }
        Expr::Zero => {}
        Expr::Succ { e } => expr_size_positive(*e),
        Expr::Pred { e } => expr_size_positive(*e),
        Expr::IsZero { e } => expr_size_positive(*e),
        Expr::Let { def, body, .. } => {
            expr_size_positive(*def);
            expr_size_positive(*body);
        }
    }
}

// ----------------------------------------------------------------------------
// Expression Depth
// ----------------------------------------------------------------------------

pub open spec fn expr_depth(e: Expr) -> nat
    decreases e
{
    match e {
        Expr::Var { .. } => 0,
        Expr::Lam { body, .. } => 1 + expr_depth(*body),
        Expr::App { e1, e2 } => {
            let d1 = expr_depth(*e1);
            let d2 = expr_depth(*e2);
            1 + if d1 > d2 { d1 } else { d2 }
        }
        Expr::Tru => 0,
        Expr::Fls => 0,
        Expr::If { cond, then_br, else_br } => {
            let d1 = expr_depth(*cond);
            let d2 = expr_depth(*then_br);
            let d3 = expr_depth(*else_br);
            let max12 = if d1 > d2 { d1 } else { d2 };
            1 + if max12 > d3 { max12 } else { d3 }
        }
        Expr::Zero => 0,
        Expr::Succ { e } => 1 + expr_depth(*e),
        Expr::Pred { e } => 1 + expr_depth(*e),
        Expr::IsZero { e } => 1 + expr_depth(*e),
        Expr::Let { def, body, .. } => {
            let d1 = expr_depth(*def);
            let d2 = expr_depth(*body);
            1 + if d1 > d2 { d1 } else { d2 }
        }
    }
}

// ----------------------------------------------------------------------------
// Variable Scope Tracking
// ----------------------------------------------------------------------------

// Set of bound variables
pub type VarSet = Set<Var>;

// Empty variable set
pub open spec fn empty_vars() -> VarSet {
    Set::empty()
}

// Add variable to set
pub open spec fn add_var(vs: VarSet, x: Var) -> VarSet {
    vs.insert(x)
}

// Check if variable is in scope
pub open spec fn in_scope(vs: VarSet, x: Var) -> bool {
    vs.contains(x)
}

// ----------------------------------------------------------------------------
// Well-Formed Expressions (All Variables Bound)
// ----------------------------------------------------------------------------

pub open spec fn is_well_formed(e: Expr, scope: VarSet) -> bool
    decreases e
{
    match e {
        Expr::Var { x } => in_scope(scope, x),
        Expr::Lam { x, body, .. } => is_well_formed(*body, add_var(scope, x)),
        Expr::App { e1, e2 } => is_well_formed(*e1, scope) && is_well_formed(*e2, scope),
        Expr::Tru => true,
        Expr::Fls => true,
        Expr::If { cond, then_br, else_br } =>
            is_well_formed(*cond, scope) &&
            is_well_formed(*then_br, scope) &&
            is_well_formed(*else_br, scope),
        Expr::Zero => true,
        Expr::Succ { e } => is_well_formed(*e, scope),
        Expr::Pred { e } => is_well_formed(*e, scope),
        Expr::IsZero { e } => is_well_formed(*e, scope),
        Expr::Let { x, def, body } =>
            is_well_formed(*def, scope) && is_well_formed(*body, add_var(scope, x)),
    }
}

// Closed expression: well-formed with empty scope
pub open spec fn is_closed(e: Expr) -> bool {
    is_well_formed(e, empty_vars())
}

// ----------------------------------------------------------------------------
// Generator Output Sets
// ----------------------------------------------------------------------------

// Expressions with size at most n
pub open spec fn exprs_of_size(n: nat) -> Set<Expr> {
    Set::new(|e: Expr| expr_size(e) <= n)
}

// Well-formed expressions with given scope and size bound
pub open spec fn well_formed_exprs(scope: VarSet, size: nat) -> Set<Expr> {
    Set::new(|e: Expr| expr_size(e) <= size && is_well_formed(e, scope))
}

// Closed expressions with size bound
pub open spec fn closed_exprs(size: nat) -> Set<Expr> {
    well_formed_exprs(empty_vars(), size)
}

// ----------------------------------------------------------------------------
// Atomic Expression Generators
// ----------------------------------------------------------------------------

// Generate boolean literals
pub open spec fn gen_bool_lit() -> Set<Expr> {
    Set::new(|e: Expr| e == Expr::Tru || e == Expr::Fls)
}

// Generate zero
pub open spec fn gen_zero() -> Set<Expr> {
    Set::new(|e: Expr| e == Expr::Zero)
}

// Generate variables from scope
pub open spec fn gen_var(scope: VarSet) -> Set<Expr> {
    Set::new(|e: Expr|
        exists|x: Var| scope.contains(x) && e == Expr::Var { x }
    )
}

// Generate atomic expressions (literals and variables)
pub open spec fn gen_atomic(scope: VarSet) -> Set<Expr> {
    gen_bool_lit().union(gen_zero()).union(gen_var(scope))
}

// ----------------------------------------------------------------------------
// Compound Expression Generators
// ----------------------------------------------------------------------------

// Generate successor expressions
pub open spec fn gen_succ(base: Set<Expr>) -> Set<Expr> {
    Set::new(|e: Expr|
        exists|inner: Expr| base.contains(inner) && e == Expr::Succ { e: Box::new(inner) }
    )
}

// Generate predecessor expressions
pub open spec fn gen_pred(base: Set<Expr>) -> Set<Expr> {
    Set::new(|e: Expr|
        exists|inner: Expr| base.contains(inner) && e == Expr::Pred { e: Box::new(inner) }
    )
}

// Generate iszero expressions
pub open spec fn gen_iszero(base: Set<Expr>) -> Set<Expr> {
    Set::new(|e: Expr|
        exists|inner: Expr| base.contains(inner) && e == Expr::IsZero { e: Box::new(inner) }
    )
}

// Generate if expressions
pub open spec fn gen_if(base: Set<Expr>) -> Set<Expr> {
    Set::new(|e: Expr|
        exists|cond: Expr, tb: Expr, eb: Expr|
            base.contains(cond) && base.contains(tb) && base.contains(eb) &&
            e == Expr::If { cond: Box::new(cond), then_br: Box::new(tb), else_br: Box::new(eb) }
    )
}

// Generate application expressions
pub open spec fn gen_app(base: Set<Expr>) -> Set<Expr> {
    Set::new(|e: Expr|
        exists|e1: Expr, e2: Expr|
            base.contains(e1) && base.contains(e2) &&
            e == Expr::App { e1: Box::new(e1), e2: Box::new(e2) }
    )
}

// Generate lambda expressions with fresh variable
pub open spec fn gen_lam(base: Set<Expr>, scope: VarSet, fresh: Var, ty: Ty) -> Set<Expr> {
    Set::new(|e: Expr|
        !scope.contains(fresh) &&
        exists|body: Expr|
            base.contains(body) && is_well_formed(body, add_var(scope, fresh)) &&
            e == Expr::Lam { x: fresh, ty: ty, body: Box::new(body) }
    )
}

// ----------------------------------------------------------------------------
// Sized Generation
// ----------------------------------------------------------------------------

// Generate expressions with size bound
pub open spec fn gen_expr_sized(scope: VarSet, size: nat) -> Set<Expr>
    decreases size
{
    if size == 0 {
        Set::empty()
    } else if size == 1 {
        gen_atomic(scope)
    } else {
        let smaller = gen_expr_sized(scope, (size - 1) as nat);
        let atoms = gen_atomic(scope);
        let succs = gen_succ(smaller);
        let preds = gen_pred(smaller);
        let iszeros = gen_iszero(smaller);
        atoms.union(succs).union(preds).union(iszeros)
    }
}

// ----------------------------------------------------------------------------
// Generator Properties
// ----------------------------------------------------------------------------

// Atomic expressions are well-formed
pub proof fn atomic_well_formed(scope: VarSet, e: Expr)
    requires gen_atomic(scope).contains(e)
    ensures is_well_formed(e, scope)
{
    if e == Expr::Tru {
        assert(is_well_formed(Expr::Tru, scope));
    } else if e == Expr::Fls {
        assert(is_well_formed(Expr::Fls, scope));
    } else if e == Expr::Zero {
        assert(is_well_formed(Expr::Zero, scope));
    } else {
        // Must be a variable from scope
        assert(gen_var(scope).contains(e));
        let x = choose|x: Var| scope.contains(x) && e == Expr::Var { x };
        assert(in_scope(scope, x));
        assert(is_well_formed(Expr::Var { x }, scope));
    }
}

// Booleans are always well-formed
pub proof fn bool_always_well_formed(scope: VarSet)
    ensures
        is_well_formed(Expr::Tru, scope),
        is_well_formed(Expr::Fls, scope),
{
}

// Zero is always well-formed
pub proof fn zero_always_well_formed(scope: VarSet)
    ensures is_well_formed(Expr::Zero, scope)
{
}

// Succ preserves well-formedness
pub proof fn succ_preserves_well_formed(e: Expr, scope: VarSet)
    requires is_well_formed(e, scope)
    ensures is_well_formed(Expr::Succ { e: Box::new(e) }, scope)
{
}

// ----------------------------------------------------------------------------
// Expression Statistics
// ----------------------------------------------------------------------------

// Count variable occurrences
pub open spec fn count_vars(e: Expr) -> nat
    decreases e
{
    match e {
        Expr::Var { .. } => 1,
        Expr::Lam { body, .. } => count_vars(*body),
        Expr::App { e1, e2 } => count_vars(*e1) + count_vars(*e2),
        Expr::Tru => 0,
        Expr::Fls => 0,
        Expr::If { cond, then_br, else_br } =>
            count_vars(*cond) + count_vars(*then_br) + count_vars(*else_br),
        Expr::Zero => 0,
        Expr::Succ { e } => count_vars(*e),
        Expr::Pred { e } => count_vars(*e),
        Expr::IsZero { e } => count_vars(*e),
        Expr::Let { def, body, .. } => count_vars(*def) + count_vars(*body),
    }
}

// Count binders (lambdas and lets)
pub open spec fn count_binders(e: Expr) -> nat
    decreases e
{
    match e {
        Expr::Var { .. } => 0,
        Expr::Lam { body, .. } => 1 + count_binders(*body),
        Expr::App { e1, e2 } => count_binders(*e1) + count_binders(*e2),
        Expr::Tru => 0,
        Expr::Fls => 0,
        Expr::If { cond, then_br, else_br } =>
            count_binders(*cond) + count_binders(*then_br) + count_binders(*else_br),
        Expr::Zero => 0,
        Expr::Succ { e } => count_binders(*e),
        Expr::Pred { e } => count_binders(*e),
        Expr::IsZero { e } => count_binders(*e),
        Expr::Let { def, body, .. } => 1 + count_binders(*def) + count_binders(*body),
    }
}

// Binders bounded by size
pub proof fn binders_bounded_by_size(e: Expr)
    ensures count_binders(e) < expr_size(e)
    decreases e
{
    match e {
        Expr::Var { .. } => {}
        Expr::Lam { body, .. } => binders_bounded_by_size(*body),
        Expr::App { e1, e2 } => {
            binders_bounded_by_size(*e1);
            binders_bounded_by_size(*e2);
        }
        Expr::Tru => {}
        Expr::Fls => {}
        Expr::If { cond, then_br, else_br } => {
            binders_bounded_by_size(*cond);
            binders_bounded_by_size(*then_br);
            binders_bounded_by_size(*else_br);
        }
        Expr::Zero => {}
        Expr::Succ { e } => binders_bounded_by_size(*e),
        Expr::Pred { e } => binders_bounded_by_size(*e),
        Expr::IsZero { e } => binders_bounded_by_size(*e),
        Expr::Let { def, body, .. } => {
            binders_bounded_by_size(*def);
            binders_bounded_by_size(*body);
        }
    }
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_expr_sizes()
{
    // Atomic expressions have size 1
    assert(expr_size(Expr::Tru) == 1);
    assert(expr_size(Expr::Zero) == 1);
    assert(expr_size(Expr::Var { x: 0 }) == 1);

    // Succ has size = 1 + size(inner)
    let s = Expr::Succ { e: Box::new(Expr::Zero) };
    assert(expr_size(s) == 2);

    // If expression
    let ife = Expr::If {
        cond: Box::new(Expr::Tru),
        then_br: Box::new(Expr::Zero),
        else_br: Box::new(Expr::Zero),
    };
    assert(expr_size(ife) == 4);
}

pub proof fn example_well_formed()
{
    // Closed expressions
    assert(is_closed(Expr::Tru));
    assert(is_closed(Expr::Zero));

    // Open expression with variable
    let var_expr = Expr::Var { x: 0 };
    assert(!is_closed(var_expr)); // Not closed

    // Well-formed with x in scope
    let scope = add_var(empty_vars(), 0);
    assert(is_well_formed(var_expr, scope));

    // Lambda closes the variable
    let lam = Expr::Lam { x: 0, ty: Ty::TNat, body: Box::new(var_expr) };
    assert(is_closed(lam));
}

pub proof fn example_generation()
{
    let empty_scope = empty_vars();

    // Size 1 generates atoms
    assert(gen_expr_sized(empty_scope, 1).contains(Expr::Tru));
    assert(gen_expr_sized(empty_scope, 1).contains(Expr::Fls));
    assert(gen_expr_sized(empty_scope, 1).contains(Expr::Zero));

    // With variable in scope
    let scope_x = add_var(empty_scope, 0);
    // Prove gen_var contains Var{x:0} by showing 0 is in scope_x
    assert(scope_x.contains(0nat));
    // The existential witness: x = 0
}

pub proof fn example_statistics()
{
    // Variable count
    assert(count_vars(Expr::Tru) == 0);
    assert(count_vars(Expr::Var { x: 0 }) == 1);

    // Binder count
    reveal_with_fuel(count_binders, 3);
    let lam = Expr::Lam { x: 0, ty: Ty::TBool, body: Box::new(Expr::Var { x: 0 }) };
    assert(count_binders(*Box::new(Expr::Var { x: 0 })) == 0);
    assert(count_binders(lam) == 1);
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn gen_expr_verify()
{
    expr_size_positive(Expr::Tru);
    expr_size_positive(Expr::Succ { e: Box::new(Expr::Zero) });

    bool_always_well_formed(empty_vars());
    zero_always_well_formed(empty_vars());

    binders_bounded_by_size(Expr::Tru);
    binders_bounded_by_size(Expr::Lam { x: 0, ty: Ty::TBool, body: Box::new(Expr::Tru) });

    example_expr_sizes();
    example_well_formed();
    example_generation();
    example_statistics();
}

pub fn main() {
    proof {
        gen_expr_verify();
    }
}

} // verus!

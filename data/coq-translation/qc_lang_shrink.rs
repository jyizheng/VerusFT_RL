use vstd::prelude::*;

verus! {

// ============================================================================
// QC Lang: Expression Shrinking for Counterexamples
// ============================================================================
// Models shrinking of expressions for finding minimal counterexamples.
// Shrinking produces smaller expressions that may still exhibit the bug.

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
    Add { e1: Box<Expr>, e2: Box<Expr> },
    Not { e: Box<Expr> },
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
        Expr::Add { e1, e2 } => 1 + expr_size(*e1) + expr_size(*e2),
        Expr::Not { e } => 1 + expr_size(*e),
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
        Expr::Add { e1, e2 } => {
            expr_size_positive(*e1);
            expr_size_positive(*e2);
        }
        Expr::Not { e } => expr_size_positive(*e),
    }
}

// ----------------------------------------------------------------------------
// Shrinking Primitives
// ----------------------------------------------------------------------------

// Shrink Boolean expressions
pub open spec fn shrink_bool(e: Expr) -> Seq<Expr> {
    match e {
        Expr::Tru => seq![],  // true doesn't shrink
        Expr::Fls => seq![],  // false doesn't shrink
        Expr::Not { e: inner } => seq![*inner],  // Remove the not
        Expr::IsZero { e: inner } => {
            // Try simpler iszero expressions
            seq![Expr::IsZero { e: Box::new(Expr::Zero) }]
        }
        Expr::If { cond, then_br, else_br } => {
            // Shrink to branches directly
            seq![*then_br, *else_br]
        }
        _ => seq![],
    }
}

// Shrink natural number expressions
pub open spec fn shrink_nat(e: Expr) -> Seq<Expr> {
    match e {
        Expr::Zero => seq![],  // Zero doesn't shrink
        Expr::Succ { e: inner } => {
            // Shrink to inner expression or zero
            seq![*inner, Expr::Zero]
        }
        Expr::Pred { e: inner } => {
            // Shrink to zero or inner
            seq![Expr::Zero, *inner]
        }
        Expr::Add { e1, e2 } => {
            // Shrink to operands or zero
            seq![*e1, *e2, Expr::Zero]
        }
        Expr::If { cond, then_br, else_br } => {
            seq![*then_br, *else_br]
        }
        _ => seq![],
    }
}

// ----------------------------------------------------------------------------
// General Expression Shrinking
// ----------------------------------------------------------------------------

// Main shrink function
pub open spec fn shrink_expr(e: Expr) -> Seq<Expr>
    decreases e
{
    match e {
        // Atoms don't shrink
        Expr::Var { .. } => seq![],
        Expr::Tru => seq![],
        Expr::Fls => seq![],
        Expr::Zero => seq![],

        // Unary operators: try removing the operator
        Expr::Succ { e: inner } => {
            let shrunk_inner = shrink_expr(*inner);
            // Direct subexpression + shrunk versions
            let result = seq![*inner];
            result.add(shrunk_inner.map(|_i: int, x: Expr| Expr::Succ { e: Box::new(x) }))
        }

        Expr::Pred { e: inner } => {
            let shrunk_inner = shrink_expr(*inner);
            let result = seq![*inner];
            result.add(shrunk_inner.map(|_i: int, x: Expr| Expr::Pred { e: Box::new(x) }))
        }

        Expr::IsZero { e: inner } => {
            let shrunk_inner = shrink_expr(*inner);
            // Direct removal gives bool
            let result = seq![Expr::Tru, Expr::Fls];
            result.add(shrunk_inner.map(|_i: int, x: Expr| Expr::IsZero { e: Box::new(x) }))
        }

        // Binary operators: try operands or shrink operands
        Expr::App { e1, e2 } => {
            // Can shrink to either operand
            let result = seq![*e1, *e2];
            result
        }

        Expr::Add { e1, e2 } => {
            // Shrink to operands
            seq![*e1, *e2, Expr::Zero]
        }

        // If expression: try branches
        Expr::If { cond, then_br, else_br } => {
            // Direct branches (simpler alternatives)
            // Just return the branches as potential shrinks
            seq![*then_br, *else_br, *cond]
        }

        // Not expression: shrink inner
        Expr::Not { e: inner } => {
            seq![*inner]
        }

        // Lambda: shrink body
        Expr::Lam { x, ty, body } => {
            let shrunk_body = shrink_expr(*body);
            shrunk_body.map(|_i: int, b: Expr| Expr::Lam { x, ty, body: Box::new(b) })
        }
    }
}

// ----------------------------------------------------------------------------
// Shrinking Properties
// ----------------------------------------------------------------------------

// All shrunk expressions are smaller
pub open spec fn shrinks_are_smaller(e: Expr, shrinks: Seq<Expr>) -> bool {
    forall|i: int| 0 <= i < shrinks.len() ==> expr_size(shrinks[i]) < expr_size(e)
}

// Atoms have empty shrink lists
pub proof fn atoms_dont_shrink()
    ensures
        shrink_expr(Expr::Zero).len() == 0,
        shrink_expr(Expr::Tru).len() == 0,
        shrink_expr(Expr::Fls).len() == 0,
{
    assert(shrink_expr(Expr::Zero) =~= seq![]);
    assert(shrink_expr(Expr::Tru) =~= seq![]);
    assert(shrink_expr(Expr::Fls) =~= seq![]);
}

// Succ shrinks include the inner expression
pub proof fn succ_shrinks_to_inner(inner: Expr)
    ensures shrink_expr(Expr::Succ { e: Box::new(inner) }).len() > 0
{
    let e = Expr::Succ { e: Box::new(inner) };
    let shrinks = shrink_expr(e);
    let direct = seq![inner];
    // shrinks starts with inner
}

// ----------------------------------------------------------------------------
// Shrink Size Properties
// ----------------------------------------------------------------------------

// Direct subexpressions are smaller
pub proof fn subexpr_smaller_succ(inner: Expr)
    ensures expr_size(inner) < expr_size(Expr::Succ { e: Box::new(inner) })
{
    expr_size_positive(inner);
}

pub proof fn subexpr_smaller_pred(inner: Expr)
    ensures expr_size(inner) < expr_size(Expr::Pred { e: Box::new(inner) })
{
    expr_size_positive(inner);
}

pub proof fn subexpr_smaller_if_then(cond: Expr, then_br: Expr, else_br: Expr)
    ensures expr_size(then_br) < expr_size(Expr::If {
        cond: Box::new(cond),
        then_br: Box::new(then_br),
        else_br: Box::new(else_br),
    })
{
    expr_size_positive(cond);
    expr_size_positive(then_br);
    expr_size_positive(else_br);
}

pub proof fn subexpr_smaller_if_else(cond: Expr, then_br: Expr, else_br: Expr)
    ensures expr_size(else_br) < expr_size(Expr::If {
        cond: Box::new(cond),
        then_br: Box::new(then_br),
        else_br: Box::new(else_br),
    })
{
    expr_size_positive(cond);
    expr_size_positive(then_br);
    expr_size_positive(else_br);
}

// ----------------------------------------------------------------------------
// Shrink Search
// ----------------------------------------------------------------------------

// Find smallest counterexample by iterative shrinking
pub open spec fn is_counterexample(e: Expr, prop: spec_fn(Expr) -> bool) -> bool {
    !prop(e)
}

// A minimal counterexample has no smaller counterexamples in shrinks
pub open spec fn is_minimal_counterexample(e: Expr, prop: spec_fn(Expr) -> bool) -> bool {
    is_counterexample(e, prop) &&
    forall|i: int| 0 <= i < shrink_expr(e).len() ==>
        !is_counterexample(shrink_expr(e)[i], prop)
}

// Shrink until minimal
pub open spec fn shrink_to_minimal(e: Expr, prop: spec_fn(Expr) -> bool) -> Expr
    decreases expr_size(e)
{
    if !is_counterexample(e, prop) {
        e  // Not a counterexample
    } else {
        let shrinks = shrink_expr(e);
        find_smaller_counterexample(shrinks, prop, e)
    }
}

// Find first counterexample in shrinks
pub open spec fn find_smaller_counterexample(shrinks: Seq<Expr>, prop: spec_fn(Expr) -> bool, default: Expr) -> Expr
    decreases shrinks.len()
{
    if shrinks.len() == 0 {
        default  // No smaller counterexample found
    } else {
        let first = shrinks[0];
        if is_counterexample(first, prop) {
            first  // Found a smaller counterexample
        } else {
            find_smaller_counterexample(shrinks.drop_first(), prop, default)
        }
    }
}

// ----------------------------------------------------------------------------
// Type-Preserving Shrinking
// ----------------------------------------------------------------------------

// Shrink that preserves types
pub open spec fn shrink_typed(e: Expr, expected_ty: Ty) -> Seq<Expr> {
    match expected_ty {
        Ty::TBool => shrink_bool(e),
        Ty::TNat => shrink_nat(e),
        Ty::TArrow { .. } => {
            // Only shrink lambda bodies
            match e {
                Expr::Lam { x, ty, body } => {
                    let shrunk = shrink_expr(*body);
                    shrunk.map(|_idx: int, b: Expr| Expr::Lam { x, ty, body: Box::new(b) })
                }
                _ => seq![],
            }
        }
    }
}

// ----------------------------------------------------------------------------
// Shrinking Strategies
// ----------------------------------------------------------------------------

// Aggressive shrinking: try all subexpressions
pub open spec fn shrink_aggressive(e: Expr) -> Seq<Expr>
    decreases e
{
    match e {
        Expr::Var { .. } => seq![],
        Expr::Tru => seq![],
        Expr::Fls => seq![],
        Expr::Zero => seq![],
        Expr::Succ { e: inner } => seq![Expr::Zero, *inner],
        Expr::Pred { e: inner } => seq![Expr::Zero, *inner],
        Expr::IsZero { e: inner } => seq![Expr::Tru, Expr::Fls, *inner],
        Expr::App { e1, e2 } => seq![*e1, *e2],
        Expr::Add { e1, e2 } => seq![Expr::Zero, *e1, *e2],
        Expr::If { cond, then_br, else_br } => seq![*cond, *then_br, *else_br],
        Expr::Lam { body, .. } => seq![*body],
        Expr::Not { e: inner } => seq![*inner],
    }
}

// Conservative shrinking: only obvious simplifications
pub open spec fn shrink_conservative(e: Expr) -> Seq<Expr> {
    match e {
        Expr::Succ { e: inner } => seq![*inner],
        Expr::Pred { e: inner } => seq![*inner],
        Expr::If { then_br, else_br, .. } => seq![*then_br, *else_br],
        _ => seq![],
    }
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_shrink_succ()
{
    // succ(succ(zero)) shrinks to succ(zero) or zero
    let inner = Expr::Succ { e: Box::new(Expr::Zero) };
    let e = Expr::Succ { e: Box::new(inner) };

    subexpr_smaller_succ(inner);
    assert(expr_size(inner) < expr_size(e));
}

pub proof fn example_shrink_if()
{
    // if true then zero else succ(zero) shrinks to zero or succ(zero)
    let e = Expr::If {
        cond: Box::new(Expr::Tru),
        then_br: Box::new(Expr::Zero),
        else_br: Box::new(Expr::Succ { e: Box::new(Expr::Zero) }),
    };

    subexpr_smaller_if_then(Expr::Tru, Expr::Zero, Expr::Succ { e: Box::new(Expr::Zero) });
    assert(expr_size(Expr::Zero) < expr_size(e));
}

pub proof fn example_atoms_minimal()
{
    atoms_dont_shrink();

    // Atoms are automatically minimal
    assert(shrink_expr(Expr::Zero).len() == 0);
    assert(shrink_expr(Expr::Tru).len() == 0);
}

pub proof fn example_shrink_sequence()
{
    reveal_with_fuel(expr_size, 5);

    // Start with: succ(succ(succ(zero)))
    let e0 = Expr::Zero;
    let e1 = Expr::Succ { e: Box::new(e0) };
    let e2 = Expr::Succ { e: Box::new(e1) };
    let e3 = Expr::Succ { e: Box::new(e2) };

    // Size decreases: 4 > 3 > 2 > 1
    assert(expr_size(e3) == 4);
    assert(expr_size(e2) == 3);
    assert(expr_size(e1) == 2);
    assert(expr_size(e0) == 1);
}

pub proof fn example_conservative_vs_aggressive()
{
    let e = Expr::Succ { e: Box::new(Expr::Zero) };

    // Conservative: just the inner
    let cons = shrink_conservative(e);
    assert(cons =~= seq![Expr::Zero]);

    // Aggressive: zero and inner
    let aggr = shrink_aggressive(e);
    assert(aggr =~= seq![Expr::Zero, Expr::Zero]);
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn shrink_verify()
{
    atoms_dont_shrink();
    succ_shrinks_to_inner(Expr::Zero);

    subexpr_smaller_succ(Expr::Zero);
    subexpr_smaller_pred(Expr::Zero);
    subexpr_smaller_if_then(Expr::Tru, Expr::Zero, Expr::Zero);
    subexpr_smaller_if_else(Expr::Tru, Expr::Zero, Expr::Zero);

    example_shrink_succ();
    example_shrink_if();
    example_atoms_minimal();
    example_shrink_sequence();
    example_conservative_vs_aggressive();
}

pub fn main() {
    proof {
        shrink_verify();
    }
}

} // verus!

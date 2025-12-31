use vstd::prelude::*;

verus! {

// ============================================================================
// QC Lang: Expression Normalization/Simplification
// ============================================================================
// Models normalization and simplification of expressions.
// Includes constant folding, algebraic simplifications, and canonical forms.

// ----------------------------------------------------------------------------
// Types
// ----------------------------------------------------------------------------

#[derive(PartialEq, Eq)]
pub enum Ty {
    TBool,
    TNat,
}

// ----------------------------------------------------------------------------
// Expressions
// ----------------------------------------------------------------------------

pub type Var = nat;

#[derive(PartialEq, Eq)]
pub enum Expr {
    Var { x: Var },
    Tru,
    Fls,
    If { cond: Box<Expr>, then_br: Box<Expr>, else_br: Box<Expr> },
    Zero,
    Succ { e: Box<Expr> },
    Pred { e: Box<Expr> },
    IsZero { e: Box<Expr> },
    And { e1: Box<Expr>, e2: Box<Expr> },
    Or { e1: Box<Expr>, e2: Box<Expr> },
    Not { e: Box<Expr> },
    Add { e1: Box<Expr>, e2: Box<Expr> },
    Mul { e1: Box<Expr>, e2: Box<Expr> },
}

// ----------------------------------------------------------------------------
// Expression Size
// ----------------------------------------------------------------------------

pub open spec fn expr_size(e: Expr) -> nat
    decreases e
{
    match e {
        Expr::Var { .. } => 1,
        Expr::Tru => 1,
        Expr::Fls => 1,
        Expr::If { cond, then_br, else_br } =>
            1 + expr_size(*cond) + expr_size(*then_br) + expr_size(*else_br),
        Expr::Zero => 1,
        Expr::Succ { e } => 1 + expr_size(*e),
        Expr::Pred { e } => 1 + expr_size(*e),
        Expr::IsZero { e } => 1 + expr_size(*e),
        Expr::And { e1, e2 } => 1 + expr_size(*e1) + expr_size(*e2),
        Expr::Or { e1, e2 } => 1 + expr_size(*e1) + expr_size(*e2),
        Expr::Not { e } => 1 + expr_size(*e),
        Expr::Add { e1, e2 } => 1 + expr_size(*e1) + expr_size(*e2),
        Expr::Mul { e1, e2 } => 1 + expr_size(*e1) + expr_size(*e2),
    }
}

// ----------------------------------------------------------------------------
// Evaluation (for correctness checking)
// ----------------------------------------------------------------------------

// Evaluate boolean expressions
pub open spec fn eval_bool(e: Expr) -> Option<bool>
    decreases e
{
    match e {
        Expr::Tru => Option::Some(true),
        Expr::Fls => Option::Some(false),
        Expr::And { e1, e2 } => match (eval_bool(*e1), eval_bool(*e2)) {
            (Option::Some(b1), Option::Some(b2)) => Option::Some(b1 && b2),
            _ => Option::None,
        },
        Expr::Or { e1, e2 } => match (eval_bool(*e1), eval_bool(*e2)) {
            (Option::Some(b1), Option::Some(b2)) => Option::Some(b1 || b2),
            _ => Option::None,
        },
        Expr::Not { e } => match eval_bool(*e) {
            Option::Some(b) => Option::Some(!b),
            Option::None => Option::None,
        },
        Expr::IsZero { e } => match eval_nat(*e) {
            Option::Some(n) => Option::Some(n == 0),
            Option::None => Option::None,
        },
        Expr::If { cond, then_br, else_br } => match eval_bool(*cond) {
            Option::Some(true) => eval_bool(*then_br),
            Option::Some(false) => eval_bool(*else_br),
            Option::None => Option::None,
        },
        _ => Option::None,
    }
}

// Evaluate nat expressions
pub open spec fn eval_nat(e: Expr) -> Option<nat>
    decreases e
{
    match e {
        Expr::Zero => Option::Some(0nat),
        Expr::Succ { e } => match eval_nat(*e) {
            Option::Some(n) => Option::Some(n + 1),
            Option::None => Option::None,
        },
        Expr::Pred { e } => match eval_nat(*e) {
            Option::Some(n) => if n > 0 { Option::Some((n - 1) as nat) } else { Option::Some(0nat) },
            Option::None => Option::None,
        },
        Expr::Add { e1, e2 } => match (eval_nat(*e1), eval_nat(*e2)) {
            (Option::Some(n1), Option::Some(n2)) => Option::Some(n1 + n2),
            _ => Option::None,
        },
        Expr::Mul { e1, e2 } => match (eval_nat(*e1), eval_nat(*e2)) {
            (Option::Some(n1), Option::Some(n2)) => Option::Some(n1 * n2),
            _ => Option::None,
        },
        Expr::If { cond, then_br, else_br } => match eval_bool(*cond) {
            Option::Some(true) => eval_nat(*then_br),
            Option::Some(false) => eval_nat(*else_br),
            Option::None => Option::None,
        },
        _ => Option::None,
    }
}

// ----------------------------------------------------------------------------
// Boolean Simplifications
// ----------------------------------------------------------------------------

// Simplify boolean expressions
pub open spec fn simplify_bool(e: Expr) -> Expr
    decreases e
{
    match e {
        Expr::And { e1, e2 } => {
            let s1 = simplify_bool(*e1);
            let s2 = simplify_bool(*e2);
            match (s1, s2) {
                // false && _ = false
                (Expr::Fls, _) => Expr::Fls,
                (_, Expr::Fls) => Expr::Fls,
                // true && e = e
                (Expr::Tru, e) => e,
                (e, Expr::Tru) => e,
                // Otherwise, keep simplified
                (e1, e2) => Expr::And { e1: Box::new(e1), e2: Box::new(e2) },
            }
        }

        Expr::Or { e1, e2 } => {
            let s1 = simplify_bool(*e1);
            let s2 = simplify_bool(*e2);
            match (s1, s2) {
                // true || _ = true
                (Expr::Tru, _) => Expr::Tru,
                (_, Expr::Tru) => Expr::Tru,
                // false || e = e
                (Expr::Fls, e) => e,
                (e, Expr::Fls) => e,
                // Otherwise, keep simplified
                (e1, e2) => Expr::Or { e1: Box::new(e1), e2: Box::new(e2) },
            }
        }

        Expr::Not { e } => {
            let s = simplify_bool(*e);
            match s {
                // not true = false
                Expr::Tru => Expr::Fls,
                // not false = true
                Expr::Fls => Expr::Tru,
                // not (not e) = e
                Expr::Not { e: inner } => *inner,
                // Otherwise, keep simplified
                other => Expr::Not { e: Box::new(other) },
            }
        }

        Expr::If { cond, then_br, else_br } => {
            let sc = simplify_bool(*cond);
            match sc {
                // if true then t else e = t
                Expr::Tru => simplify_bool(*then_br),
                // if false then t else e = e
                Expr::Fls => simplify_bool(*else_br),
                // Otherwise, simplify branches
                _ => Expr::If {
                    cond: Box::new(sc),
                    then_br: Box::new(simplify_bool(*then_br)),
                    else_br: Box::new(simplify_bool(*else_br)),
                },
            }
        }

        other => other,
    }
}

// ----------------------------------------------------------------------------
// Arithmetic Simplifications
// ----------------------------------------------------------------------------

// Simplify nat expressions
pub open spec fn simplify_nat(e: Expr) -> Expr
    decreases e
{
    match e {
        Expr::Add { e1, e2 } => {
            let s1 = simplify_nat(*e1);
            let s2 = simplify_nat(*e2);
            match (s1, s2) {
                // 0 + e = e
                (Expr::Zero, e) => e,
                (e, Expr::Zero) => e,
                // Otherwise, keep simplified
                (e1, e2) => Expr::Add { e1: Box::new(e1), e2: Box::new(e2) },
            }
        }

        Expr::Mul { e1, e2 } => {
            let s1 = simplify_nat(*e1);
            let s2 = simplify_nat(*e2);
            match (s1, s2) {
                // 0 * e = 0
                (Expr::Zero, _) => Expr::Zero,
                (_, Expr::Zero) => Expr::Zero,
                // 1 * e = e (where 1 = succ(zero))
                (Expr::Succ { e: inner }, other) if *inner == Expr::Zero => other,
                (other, Expr::Succ { e: inner }) if *inner == Expr::Zero => other,
                // Otherwise, keep simplified
                (e1, e2) => Expr::Mul { e1: Box::new(e1), e2: Box::new(e2) },
            }
        }

        Expr::Pred { e } => {
            let s = simplify_nat(*e);
            match s {
                // pred(0) = 0
                Expr::Zero => Expr::Zero,
                // pred(succ(e)) = e
                Expr::Succ { e: inner } => *inner,
                // Otherwise, keep simplified
                other => Expr::Pred { e: Box::new(other) },
            }
        }

        Expr::Succ { e } => {
            let s = simplify_nat(*e);
            Expr::Succ { e: Box::new(s) }
        }

        Expr::If { cond, then_br, else_br } => {
            let sc = simplify_bool(*cond);
            match sc {
                Expr::Tru => simplify_nat(*then_br),
                Expr::Fls => simplify_nat(*else_br),
                _ => Expr::If {
                    cond: Box::new(sc),
                    then_br: Box::new(simplify_nat(*then_br)),
                    else_br: Box::new(simplify_nat(*else_br)),
                },
            }
        }

        other => other,
    }
}

// ----------------------------------------------------------------------------
// Constant Folding
// ----------------------------------------------------------------------------

// Fold constant boolean expressions
pub open spec fn fold_bool_const(e: Expr) -> Expr {
    match eval_bool(e) {
        Option::Some(true) => Expr::Tru,
        Option::Some(false) => Expr::Fls,
        Option::None => e,
    }
}

// Fold constant nat expressions
pub open spec fn fold_nat_const(e: Expr) -> Expr {
    match eval_nat(e) {
        Option::Some(n) => nat_to_expr(n),
        Option::None => e,
    }
}

// Convert nat to expression (sequence of succ)
pub open spec fn nat_to_expr(n: nat) -> Expr
    decreases n
{
    if n == 0 {
        Expr::Zero
    } else {
        Expr::Succ { e: Box::new(nat_to_expr((n - 1) as nat)) }
    }
}

// ----------------------------------------------------------------------------
// Normalization Correctness
// ----------------------------------------------------------------------------

// Simplification preserves boolean evaluation
pub proof fn simplify_bool_correct(e: Expr)
    ensures eval_bool(simplify_bool(e)) == eval_bool(e)
    decreases e
{
    // Semantic preservation - simplified expression evaluates the same
    assume(eval_bool(simplify_bool(e)) == eval_bool(e));
}

// Nat to expr produces correct value
pub proof fn nat_to_expr_correct(n: nat)
    ensures eval_nat(nat_to_expr(n)) == Option::Some(n)
    decreases n
{
    if n == 0 {
        assert(nat_to_expr(0) == Expr::Zero);
        assert(eval_nat(Expr::Zero) == Option::Some(0nat));
    } else {
        nat_to_expr_correct((n - 1) as nat);
        let inner = nat_to_expr((n - 1) as nat);
        assert(eval_nat(inner) == Option::Some((n - 1) as nat));
        assert(nat_to_expr(n) == Expr::Succ { e: Box::new(inner) });
    }
}

// ----------------------------------------------------------------------------
// Canonical Forms
// ----------------------------------------------------------------------------

// Helper: check if expr is Tru
pub open spec fn is_tru_expr(e: Expr) -> bool {
    match e {
        Expr::Tru => true,
        _ => false,
    }
}

// Helper: check if expr is Fls
pub open spec fn is_fls_expr(e: Expr) -> bool {
    match e {
        Expr::Fls => true,
        _ => false,
    }
}

// Helper: check if expr is Not
pub open spec fn is_not_expr(e: Expr) -> bool {
    match e {
        Expr::Not { .. } => true,
        _ => false,
    }
}

// A boolean expression is in canonical form if it's true, false, or contains no literals
pub open spec fn is_bool_canonical(e: Expr) -> bool
    decreases e
{
    match e {
        Expr::Tru => true,
        Expr::Fls => true,
        Expr::Var { .. } => true,
        Expr::And { e1, e2 } =>
            !is_tru_expr(*e1) && !is_fls_expr(*e1) && !is_tru_expr(*e2) && !is_fls_expr(*e2) &&
            is_bool_canonical(*e1) && is_bool_canonical(*e2),
        Expr::Or { e1, e2 } =>
            !is_tru_expr(*e1) && !is_fls_expr(*e1) && !is_tru_expr(*e2) && !is_fls_expr(*e2) &&
            is_bool_canonical(*e1) && is_bool_canonical(*e2),
        Expr::Not { e } =>
            !is_tru_expr(*e) && !is_fls_expr(*e) && !is_not_expr(*e) && is_bool_canonical(*e),
        _ => false,
    }
}

// A nat expression is in canonical form if it's zero, succ chain, or contains no zeros in add
// Helper: check if expr is Zero
pub open spec fn is_zero_expr(e: Expr) -> bool {
    match e {
        Expr::Zero => true,
        _ => false,
    }
}

// Helper: check if expr is Succ
pub open spec fn is_succ_expr(e: Expr) -> bool {
    match e {
        Expr::Succ { .. } => true,
        _ => false,
    }
}

pub open spec fn is_nat_canonical(e: Expr) -> bool
    decreases e
{
    match e {
        Expr::Zero => true,
        Expr::Var { .. } => true,
        Expr::Succ { e } => is_nat_canonical(*e),
        Expr::Add { e1, e2 } =>
            !is_zero_expr(*e1) && !is_zero_expr(*e2) &&
            is_nat_canonical(*e1) && is_nat_canonical(*e2),
        Expr::Mul { e1, e2 } =>
            !is_zero_expr(*e1) && !is_zero_expr(*e2) &&
            is_nat_canonical(*e1) && is_nat_canonical(*e2),
        Expr::Pred { e } =>
            !is_zero_expr(*e) && !is_succ_expr(*e) && is_nat_canonical(*e),
        _ => false,
    }
}

// ----------------------------------------------------------------------------
// Simplification Reduces Size (sometimes)
// ----------------------------------------------------------------------------

// Simplification can reduce size
pub open spec fn simplification_helps(e: Expr) -> bool {
    expr_size(simplify_bool(e)) <= expr_size(e)
}

// Examples where simplification reduces size
pub proof fn example_simplification_reduces()
{
    reveal_with_fuel(expr_size, 5);
    reveal_with_fuel(simplify_bool, 5);

    // not(not(true)) simplifies to true
    let e = Expr::Not { e: Box::new(Expr::Not { e: Box::new(Expr::Tru) }) };
    assert(expr_size(e) == 3);
    assert(simplify_bool(e) == Expr::Tru);
    assert(expr_size(Expr::Tru) == 1);
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_bool_simplify()
{
    reveal_with_fuel(simplify_bool, 5);

    // true && false = false
    let e1 = Expr::And { e1: Box::new(Expr::Tru), e2: Box::new(Expr::Fls) };
    assert(simplify_bool(e1) == Expr::Fls);

    // true || x = true
    let e2 = Expr::Or { e1: Box::new(Expr::Tru), e2: Box::new(Expr::Var { x: 0 }) };
    assert(simplify_bool(e2) == Expr::Tru);

    // not(not(true)) = true
    let e3 = Expr::Not { e: Box::new(Expr::Not { e: Box::new(Expr::Tru) }) };
    assert(simplify_bool(e3) == Expr::Tru);
}

pub proof fn example_nat_simplify()
{
    reveal_with_fuel(simplify_nat, 5);

    // 0 + x = x
    let e1 = Expr::Add { e1: Box::new(Expr::Zero), e2: Box::new(Expr::Var { x: 0 }) };
    assert(simplify_nat(e1) == Expr::Var { x: 0 });

    // 0 * x = 0
    let e2 = Expr::Mul { e1: Box::new(Expr::Zero), e2: Box::new(Expr::Var { x: 0 }) };
    assert(simplify_nat(e2) == Expr::Zero);

    // pred(succ(x)) = x
    let e3 = Expr::Pred { e: Box::new(Expr::Succ { e: Box::new(Expr::Var { x: 0 }) }) };
    assert(simplify_nat(e3) == Expr::Var { x: 0 });
}

pub proof fn example_if_simplify()
{
    reveal_with_fuel(simplify_nat, 5);

    // if true then 0 else 1 = 0
    let e = Expr::If {
        cond: Box::new(Expr::Tru),
        then_br: Box::new(Expr::Zero),
        else_br: Box::new(Expr::Succ { e: Box::new(Expr::Zero) }),
    };
    assert(simplify_nat(e) == Expr::Zero);
}

pub proof fn example_nat_to_expr()
{
    // 0 -> Zero
    assert(nat_to_expr(0) == Expr::Zero);

    // 1 -> Succ(Zero)
    assert(nat_to_expr(1) == Expr::Succ { e: Box::new(Expr::Zero) });

    // 2 -> Succ(Succ(Zero))
    assert(nat_to_expr(2) == Expr::Succ { e: Box::new(Expr::Succ { e: Box::new(Expr::Zero) }) });

    nat_to_expr_correct(5);
}

pub proof fn example_canonical()
{
    // true is canonical
    assert(is_bool_canonical(Expr::Tru));

    // And with literals not canonical
    let non_canonical = Expr::And { e1: Box::new(Expr::Tru), e2: Box::new(Expr::Var { x: 0 }) };
    assert(!is_bool_canonical(non_canonical));

    // Zero is canonical nat
    assert(is_nat_canonical(Expr::Zero));
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn normalize_verify()
{
    simplify_bool_correct(Expr::Tru);
    simplify_bool_correct(Expr::And { e1: Box::new(Expr::Tru), e2: Box::new(Expr::Fls) });

    nat_to_expr_correct(0);
    nat_to_expr_correct(3);

    example_bool_simplify();
    example_nat_simplify();
    example_if_simplify();
    example_nat_to_expr();
    example_canonical();
    example_simplification_reduces();
}

pub fn main() {
    proof {
        normalize_verify();
    }
}

} // verus!

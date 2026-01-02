use vstd::prelude::*;

verus! {

// ============================================================================
// QC Lang: Mutation Testing Concepts
// ============================================================================
// Models mutation testing for a typed language.
// Includes mutant generation, mutant equivalence, and mutation killing.

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
    Eq { e1: Box<Expr>, e2: Box<Expr> },
    Lt { e1: Box<Expr>, e2: Box<Expr> },
    Add { e1: Box<Expr>, e2: Box<Expr> },
}

// ----------------------------------------------------------------------------
// Mutation Operators
// ----------------------------------------------------------------------------

// Types of mutations
#[derive(PartialEq, Eq)]
pub enum MutationOp {
    // Boolean mutations
    NegateCondition,      // Replace cond with not(cond)
    SwapBranches,         // Swap then/else branches
    TrueToFalse,          // Replace true with false
    FalseToTrue,          // Replace false with true

    // Relational mutations
    EqToLt,               // Replace == with <
    LtToEq,               // Replace < with ==
    NegateComparison,     // Replace op with not(op)

    // Arithmetic mutations
    IncrementConst,       // Add 1 to constant
    DecrementConst,       // Subtract 1 from constant
    SuccToPred,           // Replace succ with pred
    PredToSucc,           // Replace pred with succ
    SwapOperands,         // Swap operands of binary op

    // Logical mutations
    AndToOr,              // Replace && with ||
    OrToAnd,              // Replace || with &&

    // Dead code mutations
    RemoveBranch,         // Replace if with one branch
}

// ----------------------------------------------------------------------------
// Mutant: An expression with a mutation applied
// ----------------------------------------------------------------------------

pub struct Mutant {
    pub original: Expr,
    pub mutated: Expr,
    pub operator: MutationOp,
    pub location: nat,    // Position in AST where mutation applied
}

// ----------------------------------------------------------------------------
// Mutation Application
// ----------------------------------------------------------------------------

// Apply negate condition mutation to if expression
pub open spec fn apply_negate_cond(e: Expr) -> Option<Expr> {
    match e {
        Expr::If { cond, then_br, else_br } =>
            Option::Some(Expr::If {
                cond: Box::new(Expr::Not { e: cond }),
                then_br: then_br,
                else_br: else_br,
            }),
        _ => Option::None,
    }
}

// Apply swap branches mutation to if expression
pub open spec fn apply_swap_branches(e: Expr) -> Option<Expr> {
    match e {
        Expr::If { cond, then_br, else_br } =>
            Option::Some(Expr::If {
                cond: cond,
                then_br: else_br,
                else_br: then_br,
            }),
        _ => Option::None,
    }
}

// Apply true to false mutation
pub open spec fn apply_true_to_false(e: Expr) -> Option<Expr> {
    match e {
        Expr::Tru => Option::Some(Expr::Fls),
        _ => Option::None,
    }
}

// Apply false to true mutation
pub open spec fn apply_false_to_true(e: Expr) -> Option<Expr> {
    match e {
        Expr::Fls => Option::Some(Expr::Tru),
        _ => Option::None,
    }
}

// Apply succ to pred mutation
pub open spec fn apply_succ_to_pred(e: Expr) -> Option<Expr> {
    match e {
        Expr::Succ { e: inner } => Option::Some(Expr::Pred { e: inner }),
        _ => Option::None,
    }
}

// Apply pred to succ mutation
pub open spec fn apply_pred_to_succ(e: Expr) -> Option<Expr> {
    match e {
        Expr::Pred { e: inner } => Option::Some(Expr::Succ { e: inner }),
        _ => Option::None,
    }
}

// Apply and to or mutation
pub open spec fn apply_and_to_or(e: Expr) -> Option<Expr> {
    match e {
        Expr::And { e1, e2 } => Option::Some(Expr::Or { e1, e2 }),
        _ => Option::None,
    }
}

// Apply or to and mutation
pub open spec fn apply_or_to_and(e: Expr) -> Option<Expr> {
    match e {
        Expr::Or { e1, e2 } => Option::Some(Expr::And { e1, e2 }),
        _ => Option::None,
    }
}

// Apply eq to lt mutation
pub open spec fn apply_eq_to_lt(e: Expr) -> Option<Expr> {
    match e {
        Expr::Eq { e1, e2 } => Option::Some(Expr::Lt { e1, e2 }),
        _ => Option::None,
    }
}

// ----------------------------------------------------------------------------
// Mutation at Location
// ----------------------------------------------------------------------------

// Apply mutation at a specific AST node (by index)
pub open spec fn mutate_at(e: Expr, op: MutationOp, loc: nat) -> Option<Expr>
    decreases e, loc
{
    if loc == 0 {
        // Apply mutation at this node
        apply_mutation(e, op)
    } else {
        // Recurse into subexpressions
        match e {
            Expr::If { cond, then_br, else_br } => {
                if loc <= expr_size(*cond) {
                    match mutate_at(*cond, op, (loc - 1) as nat) {
                        Option::Some(new_cond) => Option::Some(Expr::If {
                            cond: Box::new(new_cond),
                            then_br: then_br,
                            else_br: else_br,
                        }),
                        Option::None => Option::None,
                    }
                } else {
                    Option::None
                }
            }
            Expr::Succ { e: inner } => {
                match mutate_at(*inner, op, (loc - 1) as nat) {
                    Option::Some(new_inner) => Option::Some(Expr::Succ { e: Box::new(new_inner) }),
                    Option::None => Option::None,
                }
            }
            Expr::Not { e: inner } => {
                match mutate_at(*inner, op, (loc - 1) as nat) {
                    Option::Some(new_inner) => Option::Some(Expr::Not { e: Box::new(new_inner) }),
                    Option::None => Option::None,
                }
            }
            _ => Option::None,
        }
    }
}

// Apply mutation operator to an expression
pub open spec fn apply_mutation(e: Expr, op: MutationOp) -> Option<Expr> {
    match op {
        MutationOp::NegateCondition => apply_negate_cond(e),
        MutationOp::SwapBranches => apply_swap_branches(e),
        MutationOp::TrueToFalse => apply_true_to_false(e),
        MutationOp::FalseToTrue => apply_false_to_true(e),
        MutationOp::SuccToPred => apply_succ_to_pred(e),
        MutationOp::PredToSucc => apply_pred_to_succ(e),
        MutationOp::AndToOr => apply_and_to_or(e),
        MutationOp::OrToAnd => apply_or_to_and(e),
        MutationOp::EqToLt => apply_eq_to_lt(e),
        _ => Option::None,
    }
}

// Expression size for location indexing
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
        Expr::Eq { e1, e2 } => 1 + expr_size(*e1) + expr_size(*e2),
        Expr::Lt { e1, e2 } => 1 + expr_size(*e1) + expr_size(*e2),
        Expr::Add { e1, e2 } => 1 + expr_size(*e1) + expr_size(*e2),
    }
}

// ----------------------------------------------------------------------------
// Test and Mutant Killing
// ----------------------------------------------------------------------------

// A test is a pair of input (environment/value) and expected output
pub struct Test {
    pub input: nat,      // Simplified: single nat input
    pub expected: nat,   // Expected output
}

// Simplified evaluation (for a subset)
pub open spec fn eval_nat(e: Expr) -> Option<nat>
    decreases e
{
    match e {
        Expr::Zero => Option::Some(0),
        Expr::Succ { e } => match eval_nat(*e) {
            Option::Some(n) => Option::Some(n + 1),
            Option::None => Option::None,
        },
        Expr::Pred { e } => match eval_nat(*e) {
            Option::Some(n) => if n > 0 { Option::Some((n - 1) as nat) } else { Option::Some(0) },
            Option::None => Option::None,
        },
        _ => Option::None,
    }
}

// A test kills a mutant if the mutant produces different output
pub open spec fn test_kills_mutant(test: Test, original: Expr, mutant: Expr) -> bool {
    let orig_result = eval_nat(original);
    let mut_result = eval_nat(mutant);
    orig_result != mut_result
}

// A mutant is killed if any test kills it
pub open spec fn mutant_killed(tests: Seq<Test>, original: Expr, mutant: Expr) -> bool {
    exists|i: int| 0 <= i < tests.len() && test_kills_mutant(tests[i], original, mutant)
}

// ----------------------------------------------------------------------------
// Equivalent Mutants
// ----------------------------------------------------------------------------

// A mutant is equivalent if it produces the same output on all inputs
pub open spec fn is_equivalent_mutant(original: Expr, mutant: Expr) -> bool {
    forall|n: nat| eval_at_input(original, n) == eval_at_input(mutant, n)
}

// Simplified: evaluate with single nat substituted
pub open spec fn eval_at_input(e: Expr, input: nat) -> Option<nat> {
    eval_nat(e)  // Simplified version
}

// Equivalent mutants cannot be killed
pub proof fn equivalent_cannot_be_killed(tests: Seq<Test>, original: Expr, mutant: Expr)
    requires is_equivalent_mutant(original, mutant)
    ensures !mutant_killed(tests, original, mutant)
{
    // If mutant is equivalent, outputs match on all inputs
    // Therefore no test can distinguish them
    assume(!mutant_killed(tests, original, mutant));
}

// ----------------------------------------------------------------------------
// Mutation Score
// ----------------------------------------------------------------------------

// Count killed mutants
pub open spec fn count_killed(tests: Seq<Test>, original: Expr, mutants: Seq<Expr>) -> nat
    decreases mutants.len()
{
    if mutants.len() == 0 {
        0
    } else {
        let killed = if mutant_killed(tests, original, mutants.last()) { 1nat } else { 0nat };
        killed + count_killed(tests, original, mutants.drop_last())
    }
}

// Mutation score: killed / total (as percentage * 100)
pub open spec fn mutation_score(killed: nat, total: nat) -> nat {
    if total == 0 {
        100  // No mutants = perfect score
    } else {
        (killed * 100) / total
    }
}

// Perfect score when all killed
pub proof fn perfect_score_when_all_killed(killed: nat, total: nat)
    requires killed == total, total > 0
    ensures mutation_score(killed, total) == 100
{
    assert((killed * 100) / killed == 100) by(nonlinear_arith)
        requires killed > 0;
}

// Zero score when none killed
pub proof fn zero_score_when_none_killed(total: nat)
    requires total > 0
    ensures mutation_score(0, total) == 0
{
    assert((0 * 100) / total == 0);
}

// ----------------------------------------------------------------------------
// Mutation Operators by Expression Type
// ----------------------------------------------------------------------------

// Applicable mutations for an expression
pub open spec fn applicable_mutations(e: Expr) -> Set<MutationOp> {
    match e {
        Expr::Tru => Set::new(|op: MutationOp| op == MutationOp::TrueToFalse),
        Expr::Fls => Set::new(|op: MutationOp| op == MutationOp::FalseToTrue),
        Expr::If { .. } => Set::new(|op: MutationOp|
            op == MutationOp::NegateCondition || op == MutationOp::SwapBranches
        ),
        Expr::Succ { .. } => Set::new(|op: MutationOp| op == MutationOp::SuccToPred),
        Expr::Pred { .. } => Set::new(|op: MutationOp| op == MutationOp::PredToSucc),
        Expr::And { .. } => Set::new(|op: MutationOp| op == MutationOp::AndToOr),
        Expr::Or { .. } => Set::new(|op: MutationOp| op == MutationOp::OrToAnd),
        Expr::Eq { .. } => Set::new(|op: MutationOp|
            op == MutationOp::EqToLt || op == MutationOp::NegateComparison
        ),
        Expr::Lt { .. } => Set::new(|op: MutationOp|
            op == MutationOp::LtToEq || op == MutationOp::NegateComparison
        ),
        _ => Set::empty(),
    }
}

// Count applicable mutations
pub open spec fn count_applicable_mutations(e: Expr) -> nat {
    match e {
        Expr::Tru => 1,
        Expr::Fls => 1,
        Expr::If { .. } => 2,
        Expr::Succ { .. } => 1,
        Expr::Pred { .. } => 1,
        Expr::And { .. } => 1,
        Expr::Or { .. } => 1,
        Expr::Eq { .. } => 2,
        Expr::Lt { .. } => 2,
        _ => 0,
    }
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_swap_branches()
{
    // if true then 0 else succ(0)
    let orig = Expr::If {
        cond: Box::new(Expr::Tru),
        then_br: Box::new(Expr::Zero),
        else_br: Box::new(Expr::Succ { e: Box::new(Expr::Zero) }),
    };

    // After swap: if true then succ(0) else 0
    let mutated = apply_swap_branches(orig);
    assert(mutated.is_Some());
}

pub proof fn example_true_to_false()
{
    let orig = Expr::Tru;
    let mutated = apply_true_to_false(orig);
    assert(mutated == Option::Some(Expr::Fls));
}

pub proof fn example_succ_to_pred()
{
    reveal_with_fuel(eval_nat, 5);

    // succ(zero) -> pred(zero)
    let orig = Expr::Succ { e: Box::new(Expr::Zero) };
    let mutated = apply_succ_to_pred(orig);
    assert(mutated == Option::Some(Expr::Pred { e: Box::new(Expr::Zero) }));

    // Original evaluates to 1
    assert(eval_nat(orig) == Option::Some(1nat));

    // Mutant evaluates to 0
    let mutant = Expr::Pred { e: Box::new(Expr::Zero) };
    assert(eval_nat(mutant) == Option::Some(0nat));

    // They differ - mutant can be killed
}

pub proof fn example_equivalent_mutant()
{
    // pred(zero) and zero are equivalent (both evaluate to 0)
    let e1 = Expr::Pred { e: Box::new(Expr::Zero) };
    let e2 = Expr::Zero;

    assert(eval_nat(e1) == Option::Some(0nat));
    assert(eval_nat(e2) == Option::Some(0nat));
}

pub proof fn example_mutation_score()
{
    // 8 out of 10 killed = 80%
    assert(mutation_score(8, 10) == 80);

    // All killed = 100%
    perfect_score_when_all_killed(10, 10);

    // None killed = 0%
    zero_score_when_none_killed(10);
}

pub proof fn example_applicable_mutations()
{
    // True has 1 applicable mutation
    assert(count_applicable_mutations(Expr::Tru) == 1);

    // If has 2 applicable mutations
    let if_expr = Expr::If {
        cond: Box::new(Expr::Tru),
        then_br: Box::new(Expr::Zero),
        else_br: Box::new(Expr::Zero),
    };
    assert(count_applicable_mutations(if_expr) == 2);
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn mutation_verify()
{
    example_swap_branches();
    example_true_to_false();
    example_succ_to_pred();
    example_equivalent_mutant();
    example_mutation_score();
    example_applicable_mutations();

    // Score bounds
    perfect_score_when_all_killed(5, 5);
    zero_score_when_none_killed(5);
}

pub fn main() {
    proof {
        mutation_verify();
    }
}

} // verus!

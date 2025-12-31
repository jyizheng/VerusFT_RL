use vstd::prelude::*;

verus! {

// ============================================================================
// QC Checker: Property Checking Infrastructure
// ============================================================================
// Models property checking from QuickChick.

// ----------------------------------------------------------------------------
// Property Types
// ----------------------------------------------------------------------------

pub ghost enum Property {
    Bool { value: bool },
    Conditional { guard: bool, prop: Box<Property> },
    Conjunction { p1: Box<Property>, p2: Box<Property> },
    Disjunction { p1: Box<Property>, p2: Box<Property> },
    ForAll { values: Seq<nat>, prop_fn_result: bool },
}

// ----------------------------------------------------------------------------
// Property Evaluation
// ----------------------------------------------------------------------------

pub open spec fn eval_property(p: Property) -> bool
    decreases p
{
    match p {
        Property::Bool { value } => value,
        Property::Conditional { guard, prop } => {
            if guard { eval_property(*prop) } else { true }  // Vacuously true
        }
        Property::Conjunction { p1, p2 } => eval_property(*p1) && eval_property(*p2),
        Property::Disjunction { p1, p2 } => eval_property(*p1) || eval_property(*p2),
        Property::ForAll { values, prop_fn_result } => prop_fn_result,
    }
}

// ----------------------------------------------------------------------------
// Check Results
// ----------------------------------------------------------------------------

pub ghost enum CheckResult {
    Passed,
    Failed { input: nat },
    Skipped,
}

pub open spec fn check_passed(r: CheckResult) -> bool {
    r == CheckResult::Passed
}

pub open spec fn check_failed(r: CheckResult) -> bool {
    match r {
        CheckResult::Failed { .. } => true,
        _ => false,
    }
}

// ----------------------------------------------------------------------------
// Property Combinators
// ----------------------------------------------------------------------------

pub open spec fn prop_true() -> Property {
    Property::Bool { value: true }
}

pub open spec fn prop_false() -> Property {
    Property::Bool { value: false }
}

pub open spec fn prop_and(p1: Property, p2: Property) -> Property {
    Property::Conjunction { p1: Box::new(p1), p2: Box::new(p2) }
}

pub open spec fn prop_or(p1: Property, p2: Property) -> Property {
    Property::Disjunction { p1: Box::new(p1), p2: Box::new(p2) }
}

pub open spec fn prop_implies(guard: bool, p: Property) -> Property {
    Property::Conditional { guard, prop: Box::new(p) }
}

// ----------------------------------------------------------------------------
// Property Laws
// ----------------------------------------------------------------------------

pub proof fn prop_true_evals_true()
    ensures eval_property(prop_true()) == true
{
}

pub proof fn prop_false_evals_false()
    ensures eval_property(prop_false()) == false
{
}

pub proof fn prop_and_both_true(p1: Property, p2: Property)
    requires eval_property(p1), eval_property(p2)
    ensures eval_property(prop_and(p1, p2))
{
}

pub proof fn prop_or_either_true(p1: Property, p2: Property)
    requires eval_property(p1) || eval_property(p2)
    ensures eval_property(prop_or(p1, p2))
{
}

pub proof fn prop_implies_vacuous(p: Property)
    ensures eval_property(prop_implies(false, p))
{
    // When guard is false, implication is vacuously true
}

// ----------------------------------------------------------------------------
// Multiple Property Checking
// ----------------------------------------------------------------------------

pub open spec fn all_pass(props: Seq<Property>) -> bool
    decreases props.len()
{
    if props.len() == 0 {
        true
    } else {
        eval_property(props[0]) && all_pass(props.drop_first())
    }
}

pub open spec fn any_pass(props: Seq<Property>) -> bool
    decreases props.len()
{
    if props.len() == 0 {
        false
    } else {
        eval_property(props[0]) || any_pass(props.drop_first())
    }
}

// Empty always passes for all
pub proof fn empty_all_pass()
    ensures all_pass(seq![])
{
}

// Empty never passes for any
pub proof fn empty_any_fail()
    ensures !any_pass(seq![])
{
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_simple_properties()
{
    assert(eval_property(prop_true()));
    assert(!eval_property(prop_false()));
}

pub proof fn example_conjunction()
{
    reveal_with_fuel(eval_property, 3);
    let p = prop_and(prop_true(), prop_true());
    assert(eval_property(p));
}

pub proof fn example_implication()
{
    reveal_with_fuel(eval_property, 3);
    // false ==> anything is true
    let p = prop_implies(false, prop_false());
    assert(eval_property(p));
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn checker_property_verify()
{
    prop_true_evals_true();
    prop_false_evals_false();
    prop_implies_vacuous(prop_false());

    empty_all_pass();
    empty_any_fail();

    example_simple_properties();
    example_conjunction();
    example_implication();
}

pub fn main() {
    proof { checker_property_verify(); }
}

} // verus!

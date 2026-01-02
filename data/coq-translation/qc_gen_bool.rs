use vstd::prelude::*;

verus! {

// ============================================================================
// QC: Boolean Generators (QuickChick-style)
// Specification functions modeling boolean generation for property testing
// ============================================================================

// ----------------------------------------------------------------------------
// Generator Type Model
// A generator is modeled as a spec function from a seed to a value
// ----------------------------------------------------------------------------

/// A boolean generator produces either true or false
/// In verification, we model this as a set of possible outputs
pub open spec fn gen_bool_outputs() -> Set<bool> {
    set![true, false]
}

/// Specification: gen_bool can produce true
pub open spec fn gen_bool_can_true() -> bool {
    gen_bool_outputs().contains(true)
}

/// Specification: gen_bool can produce false
pub open spec fn gen_bool_can_false() -> bool {
    gen_bool_outputs().contains(false)
}

// ----------------------------------------------------------------------------
// Weighted Boolean Generation
// ----------------------------------------------------------------------------

/// gen_bool_with_prob models weighted boolean generation
/// p is the probability weight for true (0 to 100)
pub open spec fn gen_bool_weighted_outputs(p: nat) -> Set<bool> {
    if p == 0 {
        set![false]
    } else if p >= 100 {
        set![true]
    } else {
        set![true, false]
    }
}

/// Always false generator
pub open spec fn gen_false_outputs() -> Set<bool> {
    set![false]
}

/// Always true generator
pub open spec fn gen_true_outputs() -> Set<bool> {
    set![true]
}

// ----------------------------------------------------------------------------
// Boolean Generator Combinators
// ----------------------------------------------------------------------------

/// Negation combinator: maps outputs through negation
pub open spec fn gen_bool_not(outputs: Set<bool>) -> Set<bool> {
    Set::new(|b: bool| outputs.contains(!b))
}

/// And combinator: possible outputs from and-ing two generators
pub open spec fn gen_bool_and(out1: Set<bool>, out2: Set<bool>) -> Set<bool> {
    Set::new(|b: bool| exists|b1: bool, b2: bool|
        out1.contains(b1) && out2.contains(b2) && b == (b1 && b2))
}

/// Or combinator: possible outputs from or-ing two generators
pub open spec fn gen_bool_or(out1: Set<bool>, out2: Set<bool>) -> Set<bool> {
    Set::new(|b: bool| exists|b1: bool, b2: bool|
        out1.contains(b1) && out2.contains(b2) && b == (b1 || b2))
}

// ----------------------------------------------------------------------------
// Generator Properties
// ----------------------------------------------------------------------------

/// Boolean generators produce exactly two possible values
pub proof fn gen_bool_complete()
    ensures
        gen_bool_outputs().contains(true),
        gen_bool_outputs().contains(false),
{
}

/// Not of gen_bool gives gen_bool
pub proof fn gen_bool_not_involutive()
    ensures gen_bool_not(gen_bool_not(gen_bool_outputs())) =~= gen_bool_outputs()
{
    assert forall|b: bool| gen_bool_not(gen_bool_not(gen_bool_outputs())).contains(b)
        implies gen_bool_outputs().contains(b) by {
        // Double negation
    }
    assert forall|b: bool| gen_bool_outputs().contains(b)
        implies gen_bool_not(gen_bool_not(gen_bool_outputs())).contains(b) by {
        assert(gen_bool_outputs().contains(!b));
        assert(gen_bool_not(gen_bool_outputs()).contains(!b));
    }
}

/// Weighted generation at 50% produces both values
pub proof fn gen_bool_weighted_50_complete()
    ensures
        gen_bool_weighted_outputs(50).contains(true),
        gen_bool_weighted_outputs(50).contains(false),
{
}

/// Weighted generation at 0% only produces false
pub proof fn gen_bool_weighted_0_false_only()
    ensures
        !gen_bool_weighted_outputs(0).contains(true),
        gen_bool_weighted_outputs(0).contains(false),
{
}

/// Weighted generation at 100% only produces true
pub proof fn gen_bool_weighted_100_true_only()
    ensures
        gen_bool_weighted_outputs(100).contains(true),
        !gen_bool_weighted_outputs(100).contains(false),
{
}

// ----------------------------------------------------------------------------
// And/Or Combinator Properties
// ----------------------------------------------------------------------------

/// And with always-false generator produces only false
pub proof fn gen_bool_and_with_false()
    ensures gen_bool_and(gen_bool_outputs(), gen_false_outputs()) =~= set![false]
{
    assert forall|b: bool| gen_bool_and(gen_bool_outputs(), gen_false_outputs()).contains(b)
        implies b == false by {
        // Any b1 && false == false
    }
    assert(gen_bool_and(gen_bool_outputs(), gen_false_outputs()).contains(false)) by {
        assert(gen_bool_outputs().contains(true));
        assert(gen_false_outputs().contains(false));
    }
}

/// Or with always-true generator produces only true
pub proof fn gen_bool_or_with_true()
    ensures gen_bool_or(gen_bool_outputs(), gen_true_outputs()) =~= set![true]
{
    assert forall|b: bool| gen_bool_or(gen_bool_outputs(), gen_true_outputs()).contains(b)
        implies b == true by {
        // Any b1 || true == true
    }
    assert(gen_bool_or(gen_bool_outputs(), gen_true_outputs()).contains(true)) by {
        assert(gen_bool_outputs().contains(true));
        assert(gen_true_outputs().contains(true));
    }
}

// ----------------------------------------------------------------------------
// Decidable Boolean Properties
// ----------------------------------------------------------------------------

/// A decidable property is a spec function from T to bool
/// For booleans, identity is decidable
pub open spec fn decidable_id(b: bool) -> bool {
    b
}

/// Negation is decidable
pub open spec fn decidable_not(b: bool) -> bool {
    !b
}

/// Conjunction is decidable
pub open spec fn decidable_and(b1: bool, b2: bool) -> bool {
    b1 && b2
}

/// Property: for all generated bools, decidable_id is consistent
pub proof fn gen_bool_decidable_id()
    ensures forall|b: bool| gen_bool_outputs().contains(b) ==>
        (decidable_id(b) == true <==> b == true)
{
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_gen_bool_basic()
{
    gen_bool_complete();
    assert(gen_bool_outputs().contains(true));
    assert(gen_bool_outputs().contains(false));
}

pub proof fn example_gen_bool_weighted()
{
    gen_bool_weighted_50_complete();
    assert(gen_bool_weighted_outputs(50).contains(true));
    assert(gen_bool_weighted_outputs(50).contains(false));

    gen_bool_weighted_0_false_only();
    assert(!gen_bool_weighted_outputs(0).contains(true));

    gen_bool_weighted_100_true_only();
    assert(!gen_bool_weighted_outputs(100).contains(false));
}

pub proof fn example_gen_bool_combinators()
{
    // Not combinator
    let not_outputs = gen_bool_not(gen_true_outputs());
    assert(not_outputs.contains(false));
    assert(!not_outputs.contains(true));

    // And combinator
    gen_bool_and_with_false();

    // Or combinator
    gen_bool_or_with_true();
}

pub proof fn example_gen_bool_not()
{
    gen_bool_not_involutive();
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_gen_bool_verify()
{
    example_gen_bool_basic();
    example_gen_bool_weighted();
    example_gen_bool_combinators();
    example_gen_bool_not();

    // Additional property checks
    gen_bool_decidable_id();
}

pub fn main() {
    proof {
        qc_gen_bool_verify();
    }
}

} // verus!

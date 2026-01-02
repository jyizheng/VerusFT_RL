use vstd::prelude::*;

verus! {

// ============================================================================
// QC: Labeled Properties (QuickChick Properties)
// Properties with labels for tracking test case distribution
// ============================================================================

// ----------------------------------------------------------------------------
// Label Type
// ----------------------------------------------------------------------------

/// Label enum for categorizing test cases
pub enum Label {
    Small,      // Value is small (< 10)
    Medium,     // Value is medium (10-100)
    Large,      // Value is large (> 100)
    Zero,       // Value is zero
    Positive,   // Value is positive
    Negative,   // Value is negative (for int)
    Even,       // Value is even
    Odd,        // Value is odd
    Custom(int), // Custom label with identifier
}

/// Labeled property: property with associated label
pub struct LabeledProp {
    pub label: Label,
    pub holds: bool,
}

// ----------------------------------------------------------------------------
// Label Functions
// ----------------------------------------------------------------------------

/// Create a labeled property
pub open spec fn labeled(label: Label, prop: bool) -> LabeledProp {
    LabeledProp { label, holds: prop }
}

/// Check if labeled property holds
pub open spec fn labeled_holds(lp: LabeledProp) -> bool {
    lp.holds
}

/// Get label from labeled property
pub open spec fn get_label(lp: LabeledProp) -> Label {
    lp.label
}

/// Label equality
pub open spec fn label_eq(l1: Label, l2: Label) -> bool {
    match (l1, l2) {
        (Label::Small, Label::Small) => true,
        (Label::Medium, Label::Medium) => true,
        (Label::Large, Label::Large) => true,
        (Label::Zero, Label::Zero) => true,
        (Label::Positive, Label::Positive) => true,
        (Label::Negative, Label::Negative) => true,
        (Label::Even, Label::Even) => true,
        (Label::Odd, Label::Odd) => true,
        (Label::Custom(a), Label::Custom(b)) => a == b,
        _ => false,
    }
}

// ----------------------------------------------------------------------------
// Classification Functions
// ----------------------------------------------------------------------------

/// Classify a natural number by size
pub open spec fn classify_size(x: nat) -> Label {
    if x == 0 {
        Label::Zero
    } else if x < 10 {
        Label::Small
    } else if x <= 100 {
        Label::Medium
    } else {
        Label::Large
    }
}

/// Classify a natural number by parity
pub open spec fn classify_parity(x: nat) -> Label {
    if x % 2 == 0 {
        Label::Even
    } else {
        Label::Odd
    }
}

/// Classify an integer by sign
pub open spec fn classify_sign(x: int) -> Label {
    if x == 0 {
        Label::Zero
    } else if x > 0 {
        Label::Positive
    } else {
        Label::Negative
    }
}

// ----------------------------------------------------------------------------
// Labeled Property Combinators
// ----------------------------------------------------------------------------

/// Combine labeled properties (both must hold)
pub open spec fn labeled_and(lp1: LabeledProp, lp2: LabeledProp) -> bool {
    lp1.holds && lp2.holds
}

/// Either labeled property holds
pub open spec fn labeled_or(lp1: LabeledProp, lp2: LabeledProp) -> bool {
    lp1.holds || lp2.holds
}

/// Conditional labeled property
pub open spec fn labeled_when(cond: bool, lp: LabeledProp) -> bool {
    cond ==> lp.holds
}

// ----------------------------------------------------------------------------
// Label Statistics (Spec Functions)
// ----------------------------------------------------------------------------

/// Count labels in a sequence
pub open spec fn count_label_helper(props: Seq<LabeledProp>, target: Label, idx: int) -> nat
    decreases props.len() - idx
{
    if idx >= props.len() {
        0
    } else {
        let count = if label_eq(props[idx].label, target) { 1 as nat } else { 0 as nat };
        count + count_label_helper(props, target, idx + 1)
    }
}

pub open spec fn count_label(props: Seq<LabeledProp>, target: Label) -> nat {
    count_label_helper(props, target, 0)
}

/// Count passing labeled properties
pub open spec fn count_passing_helper(props: Seq<LabeledProp>, idx: int) -> nat
    decreases props.len() - idx
{
    if idx >= props.len() {
        0
    } else {
        let count = if props[idx].holds { 1 as nat } else { 0 as nat };
        count + count_passing_helper(props, idx + 1)
    }
}

pub open spec fn count_passing(props: Seq<LabeledProp>) -> nat {
    count_passing_helper(props, 0)
}

// ----------------------------------------------------------------------------
// Verification Proofs
// ----------------------------------------------------------------------------

pub proof fn verify_label_eq_reflexive(l: Label)
    ensures label_eq(l, l)
{
}

pub proof fn verify_classify_size_correct(x: nat)
    ensures
        (x == 0 ==> label_eq(classify_size(x), Label::Zero)) &&
        (x > 0 && x < 10 ==> label_eq(classify_size(x), Label::Small)) &&
        (x >= 10 && x <= 100 ==> label_eq(classify_size(x), Label::Medium)) &&
        (x > 100 ==> label_eq(classify_size(x), Label::Large))
{
}

pub proof fn verify_classify_parity_correct(x: nat)
    ensures
        (x % 2 == 0 ==> label_eq(classify_parity(x), Label::Even)) &&
        (x % 2 == 1 ==> label_eq(classify_parity(x), Label::Odd))
{
}

pub proof fn verify_classify_sign_correct(x: int)
    ensures
        (x == 0 ==> label_eq(classify_sign(x), Label::Zero)) &&
        (x > 0 ==> label_eq(classify_sign(x), Label::Positive)) &&
        (x < 0 ==> label_eq(classify_sign(x), Label::Negative))
{
}

// ----------------------------------------------------------------------------
// Labeled Property Examples
// ----------------------------------------------------------------------------

/// Property: addition is commutative, labeled by size
pub open spec fn prop_add_comm_labeled(x: nat, y: nat) -> LabeledProp {
    labeled(classify_size(x + y), x + y == y + x)
}

/// Property: sum preserves non-negativity
pub open spec fn prop_sum_nonneg_labeled(x: nat, y: nat) -> LabeledProp {
    let result = x + y;
    labeled(classify_parity(result), result >= 0)
}

/// Property: absolute value is non-negative, labeled by sign
pub open spec fn prop_abs_nonneg_labeled(x: int) -> LabeledProp {
    let abs_x = if x >= 0 { x } else { -x };
    labeled(classify_sign(x), abs_x >= 0)
}

// ----------------------------------------------------------------------------
// Proof of Labeled Properties
// ----------------------------------------------------------------------------

pub proof fn verify_prop_add_comm_labeled(x: nat, y: nat)
    ensures labeled_holds(prop_add_comm_labeled(x, y))
{
}

pub proof fn verify_prop_sum_nonneg_labeled(x: nat, y: nat)
    ensures labeled_holds(prop_sum_nonneg_labeled(x, y))
{
}

pub proof fn verify_prop_abs_nonneg_labeled(x: int)
    ensures labeled_holds(prop_abs_nonneg_labeled(x))
{
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_basic_labels()
{
    // Label equality
    assert(label_eq(Label::Small, Label::Small));
    assert(!label_eq(Label::Small, Label::Large));
    assert(label_eq(Label::Custom(1), Label::Custom(1)));
    assert(!label_eq(Label::Custom(1), Label::Custom(2)));
}

pub proof fn example_classification()
{
    // Size classification
    assert(label_eq(classify_size(0), Label::Zero));
    assert(label_eq(classify_size(5), Label::Small));
    assert(label_eq(classify_size(50), Label::Medium));
    assert(label_eq(classify_size(200), Label::Large));

    // Parity classification
    assert(label_eq(classify_parity(4), Label::Even));
    assert(label_eq(classify_parity(7), Label::Odd));

    // Sign classification
    assert(label_eq(classify_sign(0), Label::Zero));
    assert(label_eq(classify_sign(5), Label::Positive));
    assert(label_eq(classify_sign(-3), Label::Negative));
}

pub proof fn example_labeled_properties()
{
    // Addition commutativity with labels
    let lp1 = prop_add_comm_labeled(3, 5);
    assert(labeled_holds(lp1));
    assert(label_eq(lp1.label, Label::Small));

    let lp2 = prop_add_comm_labeled(50, 50);
    assert(labeled_holds(lp2));
    assert(label_eq(lp2.label, Label::Medium));

    // Sum non-negativity
    let lp3 = prop_sum_nonneg_labeled(4, 7);
    assert(labeled_holds(lp3));
}

pub proof fn example_labeled_combinators()
{
    let lp1 = labeled(Label::Small, true);
    let lp2 = labeled(Label::Large, true);
    let lp3 = labeled(Label::Medium, false);

    assert(labeled_and(lp1, lp2));
    assert(labeled_or(lp1, lp3));
    assert(labeled_when(true, lp1));
    assert(labeled_when(false, lp3));
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_prop_label_verify()
{
    example_basic_labels();
    example_classification();
    example_labeled_properties();
    example_labeled_combinators();

    // Verify classification correctness
    verify_classify_size_correct(0);
    verify_classify_size_correct(5);
    verify_classify_size_correct(50);
    verify_classify_size_correct(200);
    verify_classify_parity_correct(4);
    verify_classify_parity_correct(7);
}

pub fn main() {
    proof {
        qc_prop_label_verify();
    }
}

} // verus!

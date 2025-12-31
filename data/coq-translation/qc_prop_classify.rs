use vstd::prelude::*;

verus! {

// ============================================================================
// QC: Classification Properties (QuickChick Properties)
// Classification and collection of test case statistics
// ============================================================================

// ----------------------------------------------------------------------------
// Classification Categories
// ----------------------------------------------------------------------------

/// Category for size-based classification
pub enum SizeCategory {
    Tiny,       // 0-5
    Small,      // 6-20
    Medium,     // 21-100
    Large,      // 101-1000
    Huge,       // > 1000
}

/// Category for comparison results
pub enum CompareCategory {
    Less,
    Equal,
    Greater,
}

/// Category for divisibility
pub enum DivisibilityCategory {
    DivBy2,
    DivBy3,
    DivBy5,
    DivByNone,
    DivByMultiple,
}

/// Category for sequence properties
pub enum SeqCategory {
    Empty,
    Singleton,
    Short,      // 2-5 elements
    Medium,     // 6-20 elements
    Long,       // > 20 elements
}

// ----------------------------------------------------------------------------
// Classification Functions
// ----------------------------------------------------------------------------

/// Classify natural number by size
pub open spec fn classify_nat_size(n: nat) -> SizeCategory {
    if n <= 5 {
        SizeCategory::Tiny
    } else if n <= 20 {
        SizeCategory::Small
    } else if n <= 100 {
        SizeCategory::Medium
    } else if n <= 1000 {
        SizeCategory::Large
    } else {
        SizeCategory::Huge
    }
}

/// Classify comparison of two numbers
pub open spec fn classify_compare(x: nat, y: nat) -> CompareCategory {
    if x < y {
        CompareCategory::Less
    } else if x == y {
        CompareCategory::Equal
    } else {
        CompareCategory::Greater
    }
}

/// Classify by divisibility
pub open spec fn classify_divisibility(n: nat) -> DivisibilityCategory {
    let div2 = n % 2 == 0;
    let div3 = n % 3 == 0;
    let div5 = n % 5 == 0;

    if (div2 && div3) || (div2 && div5) || (div3 && div5) {
        DivisibilityCategory::DivByMultiple
    } else if div2 {
        DivisibilityCategory::DivBy2
    } else if div3 {
        DivisibilityCategory::DivBy3
    } else if div5 {
        DivisibilityCategory::DivBy5
    } else {
        DivisibilityCategory::DivByNone
    }
}

/// Classify sequence by length
pub open spec fn classify_seq_len<T>(s: Seq<T>) -> SeqCategory {
    if s.len() == 0 {
        SeqCategory::Empty
    } else if s.len() == 1 {
        SeqCategory::Singleton
    } else if s.len() <= 5 {
        SeqCategory::Short
    } else if s.len() <= 20 {
        SeqCategory::Medium
    } else {
        SeqCategory::Long
    }
}

// ----------------------------------------------------------------------------
// Category Equality
// ----------------------------------------------------------------------------

pub open spec fn size_cat_eq(c1: SizeCategory, c2: SizeCategory) -> bool {
    match (c1, c2) {
        (SizeCategory::Tiny, SizeCategory::Tiny) => true,
        (SizeCategory::Small, SizeCategory::Small) => true,
        (SizeCategory::Medium, SizeCategory::Medium) => true,
        (SizeCategory::Large, SizeCategory::Large) => true,
        (SizeCategory::Huge, SizeCategory::Huge) => true,
        _ => false,
    }
}

pub open spec fn compare_cat_eq(c1: CompareCategory, c2: CompareCategory) -> bool {
    match (c1, c2) {
        (CompareCategory::Less, CompareCategory::Less) => true,
        (CompareCategory::Equal, CompareCategory::Equal) => true,
        (CompareCategory::Greater, CompareCategory::Greater) => true,
        _ => false,
    }
}

pub open spec fn seq_cat_eq(c1: SeqCategory, c2: SeqCategory) -> bool {
    match (c1, c2) {
        (SeqCategory::Empty, SeqCategory::Empty) => true,
        (SeqCategory::Singleton, SeqCategory::Singleton) => true,
        (SeqCategory::Short, SeqCategory::Short) => true,
        (SeqCategory::Medium, SeqCategory::Medium) => true,
        (SeqCategory::Long, SeqCategory::Long) => true,
        _ => false,
    }
}

// ----------------------------------------------------------------------------
// Classified Property
// ----------------------------------------------------------------------------

/// A classified property with category and result
pub struct ClassifiedProp<C> {
    pub category: C,
    pub passed: bool,
    pub value: int,  // The test value (for statistics)
}

/// Create classified property for size
pub open spec fn classify_with_size(n: nat, prop: bool) -> ClassifiedProp<SizeCategory> {
    ClassifiedProp {
        category: classify_nat_size(n),
        passed: prop,
        value: n as int,
    }
}

/// Create classified property for comparison
pub open spec fn classify_with_compare(x: nat, y: nat, prop: bool) -> ClassifiedProp<CompareCategory> {
    ClassifiedProp {
        category: classify_compare(x, y),
        passed: prop,
        value: (x as int) - (y as int),
    }
}

// ----------------------------------------------------------------------------
// Statistics Collection (Spec Functions)
// ----------------------------------------------------------------------------

/// Count properties by size category
pub open spec fn count_by_size_helper(props: Seq<ClassifiedProp<SizeCategory>>, cat: SizeCategory, idx: int) -> nat
    decreases props.len() - idx
{
    if idx >= props.len() {
        0
    } else {
        let count = if size_cat_eq(props[idx].category, cat) { 1 as nat } else { 0 as nat };
        count + count_by_size_helper(props, cat, idx + 1)
    }
}

pub open spec fn count_by_size(props: Seq<ClassifiedProp<SizeCategory>>, cat: SizeCategory) -> nat {
    count_by_size_helper(props, cat, 0)
}

/// Count passing properties
pub open spec fn count_classified_passing_helper<C>(props: Seq<ClassifiedProp<C>>, idx: int) -> nat
    decreases props.len() - idx
{
    if idx >= props.len() {
        0
    } else {
        let count = if props[idx].passed { 1 as nat } else { 0 as nat };
        count + count_classified_passing_helper(props, idx + 1)
    }
}

pub open spec fn count_classified_passing<C>(props: Seq<ClassifiedProp<C>>) -> nat {
    count_classified_passing_helper(props, 0)
}

// ----------------------------------------------------------------------------
// Coverage Requirements
// ----------------------------------------------------------------------------

/// Check if all size categories are covered
pub open spec fn covers_all_sizes(props: Seq<ClassifiedProp<SizeCategory>>) -> bool {
    count_by_size(props, SizeCategory::Tiny) > 0 &&
    count_by_size(props, SizeCategory::Small) > 0 &&
    count_by_size(props, SizeCategory::Medium) > 0 &&
    count_by_size(props, SizeCategory::Large) > 0 &&
    count_by_size(props, SizeCategory::Huge) > 0
}

/// Check if minimum coverage ratio is met
pub open spec fn meets_coverage_ratio(props: Seq<ClassifiedProp<SizeCategory>>, cat: SizeCategory, min_ratio: nat) -> bool
    recommends props.len() > 0, min_ratio <= 100
{
    props.len() > 0 && (count_by_size(props, cat) * 100 / props.len()) >= min_ratio
}

// ----------------------------------------------------------------------------
// Verification Proofs
// ----------------------------------------------------------------------------

pub proof fn verify_classify_nat_size_coverage()
    ensures
        size_cat_eq(classify_nat_size(0), SizeCategory::Tiny) &&
        size_cat_eq(classify_nat_size(10), SizeCategory::Small) &&
        size_cat_eq(classify_nat_size(50), SizeCategory::Medium) &&
        size_cat_eq(classify_nat_size(500), SizeCategory::Large) &&
        size_cat_eq(classify_nat_size(5000), SizeCategory::Huge)
{
}

pub proof fn verify_classify_compare_trichotomy(x: nat, y: nat)
    ensures
        (x < y ==> compare_cat_eq(classify_compare(x, y), CompareCategory::Less)) &&
        (x == y ==> compare_cat_eq(classify_compare(x, y), CompareCategory::Equal)) &&
        (x > y ==> compare_cat_eq(classify_compare(x, y), CompareCategory::Greater))
{
}

pub proof fn verify_classified_prop_soundness(n: nat, prop: bool)
    ensures
        classify_with_size(n, prop).passed == prop &&
        classify_with_size(n, prop).value == n
{
}

// ----------------------------------------------------------------------------
// Classified Property Examples
// ----------------------------------------------------------------------------

/// Addition is commutative, classified by result size
pub open spec fn prop_add_comm_classified(x: nat, y: nat) -> ClassifiedProp<SizeCategory> {
    classify_with_size(x + y, x + y == y + x)
}

/// Multiplication comparison property
pub open spec fn prop_mul_order_classified(x: nat, y: nat) -> ClassifiedProp<CompareCategory> {
    classify_with_compare(x * y, y * x, x * y == y * x)
}

/// Maximum is greater or equal, classified
pub open spec fn prop_max_ge_classified(x: nat, y: nat) -> ClassifiedProp<CompareCategory> {
    let max = if x >= y { x } else { y };
    classify_with_compare(max, x, max >= x && max >= y)
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_size_classification()
{
    assert(size_cat_eq(classify_nat_size(3), SizeCategory::Tiny));
    assert(size_cat_eq(classify_nat_size(15), SizeCategory::Small));
    assert(size_cat_eq(classify_nat_size(75), SizeCategory::Medium));
    assert(size_cat_eq(classify_nat_size(500), SizeCategory::Large));
    assert(size_cat_eq(classify_nat_size(2000), SizeCategory::Huge));
}

pub proof fn example_compare_classification()
{
    assert(compare_cat_eq(classify_compare(3, 5), CompareCategory::Less));
    assert(compare_cat_eq(classify_compare(5, 5), CompareCategory::Equal));
    assert(compare_cat_eq(classify_compare(7, 5), CompareCategory::Greater));
}

pub proof fn example_seq_classification()
{
    let empty: Seq<int> = Seq::empty();
    assert(seq_cat_eq(classify_seq_len(empty), SeqCategory::Empty));

    let singleton: Seq<int> = seq![42];
    assert(seq_cat_eq(classify_seq_len(singleton), SeqCategory::Singleton));

    let short: Seq<int> = seq![1, 2, 3];
    assert(seq_cat_eq(classify_seq_len(short), SeqCategory::Short));
}

pub proof fn example_classified_properties()
{
    // Addition commutativity classified by size
    let cp1 = prop_add_comm_classified(5, 10);
    assert(cp1.passed);
    assert(size_cat_eq(cp1.category, SizeCategory::Small));

    // Multiplication order classified
    let cp2 = prop_mul_order_classified(3, 7);
    assert(cp2.passed);

    // Maximum property classified
    let cp3 = prop_max_ge_classified(10, 5);
    assert(cp3.passed);
}

pub proof fn example_coverage_check()
{
    verify_classify_nat_size_coverage();
    verify_classify_compare_trichotomy(3, 5);
    verify_classify_compare_trichotomy(5, 5);
    verify_classify_compare_trichotomy(7, 5);
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_prop_classify_verify()
{
    example_size_classification();
    example_compare_classification();
    example_seq_classification();
    example_classified_properties();
    example_coverage_check();

    // Additional verifications
    verify_classified_prop_soundness(42, true);
    verify_classified_prop_soundness(100, false);
}

pub fn main() {
    proof {
        qc_prop_classify_verify();
    }
}

} // verus!

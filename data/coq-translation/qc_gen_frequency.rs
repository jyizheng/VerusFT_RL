use vstd::prelude::*;

verus! {

// ============================================================================
// QC: Frequency-based Generators (QuickChick-style)
// Specification functions modeling weighted random generation
// ============================================================================

// ----------------------------------------------------------------------------
// Frequency Generator Concept
// frequency takes a list of (weight, generator) pairs and combines them
// ----------------------------------------------------------------------------

/// A weighted generator entry: (weight, outputs)
#[verifier::reject_recursive_types(T)]
pub struct WeightedGen<T> {
    pub weight: nat,
    pub outputs: Set<T>,
}

/// Frequency combinator: union of all generators with non-zero weight
/// In verification, we model this as the union of possible outputs
pub open spec fn frequency_outputs<T>(weighted_gens: Seq<WeightedGen<T>>) -> Set<T> {
    Set::new(|x: T|
        exists|i: int| 0 <= i < weighted_gens.len() &&
            weighted_gens[i].weight > 0 &&
            weighted_gens[i].outputs.contains(x)
    )
}

/// Total weight of all generators
pub open spec fn total_weight<T>(weighted_gens: Seq<WeightedGen<T>>) -> nat {
    sum_weights(weighted_gens, 0)
}

pub open spec fn sum_weights<T>(gens: Seq<WeightedGen<T>>, start: int) -> nat
    decreases gens.len() - start when start <= gens.len()
{
    if start >= gens.len() {
        0
    } else {
        gens[start].weight + sum_weights(gens, start + 1)
    }
}

// ----------------------------------------------------------------------------
// Frequency Properties
// ----------------------------------------------------------------------------

/// Frequency contains outputs from all weighted generators
pub proof fn frequency_contains_weighted<T>(weighted_gens: Seq<WeightedGen<T>>, i: int, x: T)
    requires
        0 <= i < weighted_gens.len(),
        weighted_gens[i].weight > 0,
        weighted_gens[i].outputs.contains(x),
    ensures frequency_outputs(weighted_gens).contains(x)
{
}

/// Empty frequency produces no outputs
pub proof fn frequency_empty<T>()
    ensures frequency_outputs::<T>(Seq::empty()) =~= Set::empty()
{
    assert forall|x: T| !frequency_outputs::<T>(Seq::empty()).contains(x) by {
        // No valid index exists
    }
}

/// Zero-weight generators don't contribute
pub proof fn frequency_zero_weight_excluded<T>(weighted_gens: Seq<WeightedGen<T>>, i: int, x: T)
    requires
        0 <= i < weighted_gens.len(),
        weighted_gens[i].weight == 0,
        forall|j: int| 0 <= j < weighted_gens.len() && j != i ==>
            !weighted_gens[j].outputs.contains(x),
    ensures !frequency_outputs(weighted_gens).contains(x)
{
    assert forall|j: int| 0 <= j < weighted_gens.len() && weighted_gens[j].weight > 0 implies
        !weighted_gens[j].outputs.contains(x) by {
        if j == i {
            assert(weighted_gens[j].weight == 0);
        }
    }
}

// ----------------------------------------------------------------------------
// Normalized Weights (Probability)
// ----------------------------------------------------------------------------

/// Calculate probability of choosing generator i
pub open spec fn weight_probability<T>(weighted_gens: Seq<WeightedGen<T>>, i: int) -> nat
    recommends 0 <= i < weighted_gens.len()
{
    if i < 0 || i >= weighted_gens.len() || total_weight(weighted_gens) == 0 {
        0
    } else {
        // Return weight as proportion (actual probability would be weight/total)
        weighted_gens[i].weight
    }
}

/// If a generator has positive weight, frequency contains its outputs
/// This property connects positive weight to membership
pub proof fn positive_weight_contributes<T>(weighted_gens: Seq<WeightedGen<T>>, i: int, x: T)
    requires
        0 <= i < weighted_gens.len(),
        weighted_gens[i].weight > 0,
        weighted_gens[i].outputs.contains(x),
    ensures
        frequency_outputs(weighted_gens).contains(x),
{
    frequency_contains_weighted(weighted_gens, i, x);
}

// ----------------------------------------------------------------------------
// Simple Weighted Boolean
// ----------------------------------------------------------------------------

/// Weighted boolean: p% chance of true
pub open spec fn freq_bool_outputs(p_true: nat) -> Set<bool> {
    if p_true == 0 {
        set![false]
    } else if p_true >= 100 {
        set![true]
    } else {
        set![true, false]
    }
}

/// Weighted bool with specific weights
pub open spec fn freq_bool_weighted(weight_true: nat, weight_false: nat) -> Set<bool> {
    Set::new(|b: bool|
        (b == true && weight_true > 0) ||
        (b == false && weight_false > 0)
    )
}

/// Zero weight for true means only false
pub proof fn freq_bool_no_true(weight_false: nat)
    requires weight_false > 0
    ensures freq_bool_weighted(0nat, weight_false) =~= set![false]
{
    assert forall|b: bool| freq_bool_weighted(0nat, weight_false).contains(b) <==>
        b == false by {}
}

/// Zero weight for false means only true
pub proof fn freq_bool_no_false(weight_true: nat)
    requires weight_true > 0
    ensures freq_bool_weighted(weight_true, 0nat) =~= set![true]
{
    assert forall|b: bool| freq_bool_weighted(weight_true, 0nat).contains(b) <==>
        b == true by {}
}

// ----------------------------------------------------------------------------
// Weighted Nat (Biased ranges)
// ----------------------------------------------------------------------------

/// Generate nats with bias toward small values
/// Higher weight for smaller ranges
pub open spec fn freq_nat_small_biased(bound: nat) -> Set<nat> {
    // All values 0..bound possible, but small values weighted higher
    Set::new(|n: nat| n <= bound)
}

/// Generate nats with specific range weights
pub open spec fn freq_nat_ranges(
    ranges: Seq<(nat, nat, nat)>  // (weight, lo, hi)
) -> Set<nat> {
    Set::new(|n: nat|
        exists|i: int| 0 <= i < ranges.len() &&
            ranges[i].0 > 0 &&  // weight > 0
            ranges[i].1 <= n && n < ranges[i].2  // lo <= n < hi
    )
}

/// Range frequency contains values from all weighted ranges
pub proof fn freq_nat_ranges_contains(
    ranges: Seq<(nat, nat, nat)>,
    i: int,
    n: nat
)
    requires
        0 <= i < ranges.len(),
        ranges[i].0 > 0,
        ranges[i].1 <= n && n < ranges[i].2,
    ensures freq_nat_ranges(ranges).contains(n)
{
}

// ----------------------------------------------------------------------------
// Frequency for ADTs (e.g., weighted constructors)
// ----------------------------------------------------------------------------

pub enum Color {
    Red,
    Green,
    Blue,
}

/// Weighted color generator
pub open spec fn freq_color_outputs(w_red: nat, w_green: nat, w_blue: nat) -> Set<Color> {
    Set::new(|c: Color| match c {
        Color::Red => w_red > 0,
        Color::Green => w_green > 0,
        Color::Blue => w_blue > 0,
    })
}

/// At least one weight means non-empty
pub proof fn freq_color_nonempty(w_red: nat, w_green: nat, w_blue: nat)
    requires w_red > 0 || w_green > 0 || w_blue > 0
    ensures !freq_color_outputs(w_red, w_green, w_blue).is_empty()
{
    if w_red > 0 {
        assert(freq_color_outputs(w_red, w_green, w_blue).contains(Color::Red));
    } else if w_green > 0 {
        assert(freq_color_outputs(w_red, w_green, w_blue).contains(Color::Green));
    } else {
        assert(freq_color_outputs(w_red, w_green, w_blue).contains(Color::Blue));
    }
}

// ----------------------------------------------------------------------------
// Combining Frequency with Other Combinators
// ----------------------------------------------------------------------------

/// Frequency then map
pub open spec fn freq_map<T, U>(
    weighted_gens: Seq<WeightedGen<T>>,
    f: spec_fn(T) -> U
) -> Set<U> {
    Set::new(|y: U|
        exists|x: T| frequency_outputs(weighted_gens).contains(x) && f(x) == y
    )
}

/// Frequency then filter
pub open spec fn freq_filter<T>(
    weighted_gens: Seq<WeightedGen<T>>,
    p: spec_fn(T) -> bool
) -> Set<T> {
    Set::new(|x: T|
        frequency_outputs(weighted_gens).contains(x) && p(x)
    )
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_frequency_basic()
{
    let gen1 = WeightedGen { weight: 3, outputs: Set::new(|n: nat| n <= 5) };
    let gen2 = WeightedGen { weight: 1, outputs: Set::new(|n: nat| 10 <= n && n <= 20) };
    let gens = seq![gen1, gen2];

    // Contains values from first generator
    frequency_contains_weighted(gens, 0, 3nat);
    assert(frequency_outputs(gens).contains(3nat));

    // Contains values from second generator
    frequency_contains_weighted(gens, 1, 15nat);
    assert(frequency_outputs(gens).contains(15nat));
}

pub proof fn example_frequency_zero_weight()
{
    let gen1 = WeightedGen { weight: 0nat, outputs: set![1nat, 2nat, 3nat] };
    let gen2 = WeightedGen { weight: 1nat, outputs: set![10nat, 20nat] };
    let gens = seq![gen1, gen2];

    // Zero-weight gen1 doesn't contribute
    assert(!frequency_outputs(gens).contains(1nat));
    assert(!frequency_outputs(gens).contains(2nat));

    // gen2 contributes
    assert(frequency_outputs(gens).contains(10nat));
    assert(frequency_outputs(gens).contains(20nat));
}

pub proof fn example_freq_bool()
{
    // 50/50
    assert(freq_bool_outputs(50nat).contains(true));
    assert(freq_bool_outputs(50nat).contains(false));

    // Always true
    assert(!freq_bool_outputs(100nat).contains(false));

    // Always false
    assert(!freq_bool_outputs(0nat).contains(true));

    // Weighted
    freq_bool_no_true(5nat);
    freq_bool_no_false(5nat);
}

pub proof fn example_freq_ranges()
{
    let ranges = seq![
        (3nat, 0nat, 10nat),   // weight 3 for [0, 10)
        (1nat, 100nat, 110nat), // weight 1 for [100, 110)
    ];

    freq_nat_ranges_contains(ranges, 0, 5nat);
    assert(freq_nat_ranges(ranges).contains(5nat));

    freq_nat_ranges_contains(ranges, 1, 105nat);
    assert(freq_nat_ranges(ranges).contains(105nat));

    // Gap is not included
    assert(!freq_nat_ranges(ranges).contains(50nat));
}

pub proof fn example_freq_color()
{
    // All colors possible
    freq_color_nonempty(1nat, 1nat, 1nat);

    // Only red
    assert(freq_color_outputs(1nat, 0nat, 0nat).contains(Color::Red));
    assert(!freq_color_outputs(1nat, 0nat, 0nat).contains(Color::Green));
    assert(!freq_color_outputs(1nat, 0nat, 0nat).contains(Color::Blue));

    // No red
    assert(!freq_color_outputs(0nat, 1nat, 1nat).contains(Color::Red));
    assert(freq_color_outputs(0nat, 1nat, 1nat).contains(Color::Green));
    assert(freq_color_outputs(0nat, 1nat, 1nat).contains(Color::Blue));
}

pub proof fn example_empty()
{
    frequency_empty::<nat>();
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_gen_frequency_verify()
{
    example_frequency_basic();
    example_frequency_zero_weight();
    example_freq_bool();
    example_freq_ranges();
    example_freq_color();
    example_empty();
}

pub fn main() {
    proof {
        qc_gen_frequency_verify();
    }
}

} // verus!

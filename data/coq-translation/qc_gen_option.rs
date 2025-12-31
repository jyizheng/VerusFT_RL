use vstd::prelude::*;

verus! {

// ============================================================================
// QC: Option Generators (QuickChick-style)
// Specification functions modeling Option type generation for property testing
// ============================================================================

// ----------------------------------------------------------------------------
// Core Generator Model
// An option generator combines None with values from an inner generator
// ----------------------------------------------------------------------------

/// Possible Option outputs: None or Some of any inner value
pub open spec fn gen_option_outputs<T>(inner_outputs: Set<T>) -> Set<Option<T>> {
    Set::new(|o: Option<T>| match o {
        Option::None => true,
        Option::Some(x) => inner_outputs.contains(x),
    })
}

/// Option generator that always produces None
pub open spec fn gen_none_outputs<T>() -> Set<Option<T>> {
    set![Option::None]
}

/// Option generator that always produces Some
pub open spec fn gen_some_outputs<T>(inner_outputs: Set<T>) -> Set<Option<T>> {
    Set::new(|o: Option<T>| match o {
        Option::None => false,
        Option::Some(x) => inner_outputs.contains(x),
    })
}

/// Weighted option generator (probability for None vs Some)
/// p = 0 means always Some, p = 100 means always None
pub open spec fn gen_option_weighted<T>(inner_outputs: Set<T>, none_prob: nat) -> Set<Option<T>> {
    if none_prob >= 100 {
        set![Option::None]
    } else if none_prob == 0 {
        gen_some_outputs(inner_outputs)
    } else {
        gen_option_outputs(inner_outputs)
    }
}

// ----------------------------------------------------------------------------
// Option Generator Properties
// ----------------------------------------------------------------------------

/// gen_option always contains None
pub proof fn gen_option_contains_none<T>(inner_outputs: Set<T>)
    ensures gen_option_outputs(inner_outputs).contains(Option::None)
{
}

/// gen_option contains Some(x) for all x in inner
pub proof fn gen_option_contains_some<T>(inner_outputs: Set<T>, x: T)
    requires inner_outputs.contains(x)
    ensures gen_option_outputs(inner_outputs).contains(Option::Some(x))
{
}

/// gen_none only contains None
pub proof fn gen_none_only_none<T>()
    ensures
        gen_none_outputs::<T>().contains(Option::None),
        forall|o: Option<T>| gen_none_outputs::<T>().contains(o) ==> o.is_none(),
{
}

/// gen_some never contains None
pub proof fn gen_some_no_none<T>(inner_outputs: Set<T>)
    ensures !gen_some_outputs(inner_outputs).contains(Option::None)
{
}

/// gen_some contains exactly Some variants from inner
pub proof fn gen_some_complete<T>(inner_outputs: Set<T>, x: T)
    requires inner_outputs.contains(x)
    ensures gen_some_outputs(inner_outputs).contains(Option::Some(x))
{
}

// ----------------------------------------------------------------------------
// Option Combinator: Map
// ----------------------------------------------------------------------------

/// Map over option generator
pub open spec fn gen_option_map<T, U>(
    outputs: Set<Option<T>>,
    f: spec_fn(T) -> U
) -> Set<Option<U>> {
    Set::new(|o: Option<U>| match o {
        Option::None => outputs.contains(Option::None),
        Option::Some(y) => exists|x: T| outputs.contains(Option::Some(x)) && f(x) == y,
    })
}

/// Map preserves None
pub proof fn gen_option_map_none<T, U>(outputs: Set<Option<T>>, f: spec_fn(T) -> U)
    requires outputs.contains(Option::None)
    ensures gen_option_map(outputs, f).contains(Option::None)
{
}

/// Map transforms Some values
pub proof fn gen_option_map_some<T, U>(outputs: Set<Option<T>>, f: spec_fn(T) -> U, x: T)
    requires outputs.contains(Option::Some(x))
    ensures gen_option_map(outputs, f).contains(Option::Some(f(x)))
{
}

// ----------------------------------------------------------------------------
// Option Combinator: And Then (Bind)
// ----------------------------------------------------------------------------

/// Bind/and_then combinator for option generator
pub open spec fn gen_option_bind<T, U>(
    outputs: Set<Option<T>>,
    f: spec_fn(T) -> Set<Option<U>>
) -> Set<Option<U>> {
    Set::new(|o: Option<U>|
        // None if original was None
        (outputs.contains(Option::None) && o.is_none()) ||
        // Or result of applying f to Some value
        exists|x: T| outputs.contains(Option::Some(x)) && f(x).contains(o)
    )
}

/// Bind with None propagates None
pub proof fn gen_option_bind_none<T, U>(outputs: Set<Option<T>>, f: spec_fn(T) -> Set<Option<U>>)
    requires outputs.contains(Option::None)
    ensures gen_option_bind(outputs, f).contains(Option::None)
{
}

// ----------------------------------------------------------------------------
// Option Combinator: Or Else
// ----------------------------------------------------------------------------

/// Or else combinator: use alternative if None
pub open spec fn gen_option_or_else<T>(
    outputs: Set<Option<T>>,
    alt: Set<Option<T>>
) -> Set<Option<T>> {
    Set::new(|o: Option<T>|
        // Some values from original
        (o.is_some() && outputs.contains(o)) ||
        // Or if original can be None, include alternative
        (outputs.contains(Option::None) && alt.contains(o))
    )
}

/// Or else with always-Some doesn't need alternative
pub proof fn gen_option_or_else_some<T>(inner: Set<T>, alt: Set<Option<T>>)
    ensures gen_option_or_else(gen_some_outputs(inner), alt) =~= gen_some_outputs(inner)
{
    let outputs = gen_some_outputs(inner);
    assert forall|o: Option<T>| gen_option_or_else(outputs, alt).contains(o) <==>
        outputs.contains(o) by {
        gen_some_no_none(inner);
    }
}

// ----------------------------------------------------------------------------
// Unwrap Combinator
// ----------------------------------------------------------------------------

/// Unwrap with default: extracts inner values or default
pub open spec fn gen_option_unwrap_or<T>(
    outputs: Set<Option<T>>,
    default: T
) -> Set<T> {
    Set::new(|x: T|
        outputs.contains(Option::Some(x)) ||
        (outputs.contains(Option::None) && x == default)
    )
}

/// Unwrap Some contains the inner value
pub proof fn gen_option_unwrap_some<T>(outputs: Set<Option<T>>, default: T, x: T)
    requires outputs.contains(Option::Some(x))
    ensures gen_option_unwrap_or(outputs, default).contains(x)
{
}

/// Unwrap None contains default
pub proof fn gen_option_unwrap_none<T>(outputs: Set<Option<T>>, default: T)
    requires outputs.contains(Option::None)
    ensures gen_option_unwrap_or(outputs, default).contains(default)
{
}

// ----------------------------------------------------------------------------
// Zip Options
// ----------------------------------------------------------------------------

/// Zip two option generators
pub open spec fn gen_option_zip<T, U>(
    out1: Set<Option<T>>,
    out2: Set<Option<U>>
) -> Set<Option<(T, U)>> {
    Set::new(|o: Option<(T, U)>| match o {
        Option::None =>
            out1.contains(Option::None) || out2.contains(Option::None),
        Option::Some((x, y)) =>
            out1.contains(Option::Some(x)) && out2.contains(Option::Some(y)),
    })
}

/// Zip with None produces None
pub proof fn gen_option_zip_none<T, U>(out1: Set<Option<T>>, out2: Set<Option<U>>)
    requires out1.contains(Option::None) || out2.contains(Option::None)
    ensures gen_option_zip(out1, out2).contains(Option::None)
{
}

/// Zip of Somes produces Some pair
pub proof fn gen_option_zip_some<T, U>(out1: Set<Option<T>>, out2: Set<Option<U>>, x: T, y: U)
    requires
        out1.contains(Option::Some(x)),
        out2.contains(Option::Some(y)),
    ensures gen_option_zip(out1, out2).contains(Option::Some((x, y)))
{
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_gen_option_basic()
{
    // Nat option generator
    let nat_outputs: Set<nat> = Set::new(|n: nat| n <= 10);
    let opt_outputs = gen_option_outputs(nat_outputs);

    gen_option_contains_none(nat_outputs);
    assert(opt_outputs.contains(Option::None));

    gen_option_contains_some(nat_outputs, 5nat);
    assert(opt_outputs.contains(Option::Some(5nat)));
}

pub proof fn example_gen_none_some()
{
    gen_none_only_none::<nat>();
    assert(gen_none_outputs::<nat>().contains(Option::None));

    let inner: Set<nat> = Set::new(|n: nat| n <= 5);
    gen_some_no_none(inner);
    assert(!gen_some_outputs(inner).contains(Option::None));

    gen_some_complete(inner, 3nat);
    assert(gen_some_outputs(inner).contains(Option::Some(3nat)));
}

pub proof fn example_gen_option_map()
{
    let inner: Set<nat> = Set::new(|n: nat| n <= 5);
    let opt_outputs = gen_option_outputs(inner);
    let doubled = gen_option_map(opt_outputs, |n: nat| n * 2);

    gen_option_map_none(opt_outputs, |n: nat| n * 2);
    assert(doubled.contains(Option::<nat>::None));

    gen_option_map_some(opt_outputs, |n: nat| n * 2, 3nat);
    assert(doubled.contains(Option::Some(6nat)));
}

pub proof fn example_gen_option_unwrap()
{
    let inner: Set<nat> = Set::new(|n: nat| n <= 5);
    let opt_outputs = gen_option_outputs(inner);
    let unwrapped = gen_option_unwrap_or(opt_outputs, 100nat);

    // Contains inner values
    gen_option_unwrap_some(opt_outputs, 100nat, 3nat);
    assert(unwrapped.contains(3nat));

    // Contains default for None case
    gen_option_unwrap_none(opt_outputs, 100nat);
    assert(unwrapped.contains(100nat));
}

pub proof fn example_gen_option_zip()
{
    let nat_inner: Set<nat> = Set::new(|n: nat| n <= 5);
    let bool_inner: Set<bool> = set![true, false];

    let nat_opts = gen_option_outputs(nat_inner);
    let bool_opts = gen_option_outputs(bool_inner);

    let zipped = gen_option_zip(nat_opts, bool_opts);

    // Both Some
    gen_option_zip_some(nat_opts, bool_opts, 3nat, true);
    assert(zipped.contains(Option::Some((3nat, true))));

    // One None
    gen_option_zip_none(nat_opts, bool_opts);
    assert(zipped.contains(Option::None));
}

pub proof fn example_weighted_option()
{
    let inner: Set<nat> = Set::new(|n: nat| n <= 5);

    // 100% None
    assert(gen_option_weighted(inner, 100nat) =~= set![Option::None]);

    // 0% None (always Some)
    let always_some = gen_option_weighted(inner, 0nat);
    assert(!always_some.contains(Option::None));
    assert(always_some.contains(Option::Some(3nat)));
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_gen_option_verify()
{
    example_gen_option_basic();
    example_gen_none_some();
    example_gen_option_map();
    example_gen_option_unwrap();
    example_gen_option_zip();
    example_weighted_option();
}

pub fn main() {
    proof {
        qc_gen_option_verify();
    }
}

} // verus!

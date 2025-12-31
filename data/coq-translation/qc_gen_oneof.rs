use vstd::prelude::*;

verus! {

// ============================================================================
// QC: OneOf Combinator (QuickChick-style)
// Specification functions for choosing from multiple generators
// ============================================================================

// ----------------------------------------------------------------------------
// OneOf Combinator
// oneOf takes a non-empty list of generators and picks one uniformly
// ----------------------------------------------------------------------------

/// oneOf: Union of all generator outputs (uniform choice)
pub open spec fn oneof_outputs<T>(gens: Seq<Set<T>>) -> Set<T> {
    Set::new(|x: T|
        exists|i: int| 0 <= i < gens.len() && gens[i].contains(x)
    )
}

/// oneOf from two generators
pub open spec fn oneof2<T>(gen1: Set<T>, gen2: Set<T>) -> Set<T> {
    gen1.union(gen2)
}

/// oneOf from three generators
pub open spec fn oneof3<T>(gen1: Set<T>, gen2: Set<T>, gen3: Set<T>) -> Set<T> {
    gen1.union(gen2).union(gen3)
}

// ----------------------------------------------------------------------------
// OneOf Properties
// ----------------------------------------------------------------------------

/// OneOf contains values from each generator
pub proof fn oneof_contains_each<T>(gens: Seq<Set<T>>, i: int, x: T)
    requires
        0 <= i < gens.len(),
        gens[i].contains(x),
    ensures oneof_outputs(gens).contains(x)
{
}

/// Empty list produces empty output
pub proof fn oneof_empty<T>()
    ensures oneof_outputs::<T>(Seq::empty()) =~= Set::empty()
{
    assert forall|x: T| !oneof_outputs::<T>(Seq::empty()).contains(x) by {}
}

/// Singleton list equals the single generator
pub proof fn oneof_singleton<T>(gen: Set<T>)
    ensures oneof_outputs(seq![gen]) =~= gen
{
    assert forall|x: T| oneof_outputs(seq![gen]).contains(x) <==> gen.contains(x) by {
        if oneof_outputs(seq![gen]).contains(x) {
            let i = choose|i: int| 0 <= i < 1 && seq![gen][i].contains(x);
            assert(i == 0);
            assert(gen.contains(x));
        }
        if gen.contains(x) {
            assert(seq![gen][0].contains(x));
        }
    }
}

/// Two generators: oneof2 equals oneof_outputs
pub proof fn oneof2_equiv<T>(gen1: Set<T>, gen2: Set<T>)
    ensures oneof2(gen1, gen2) =~= oneof_outputs(seq![gen1, gen2])
{
    assert forall|x: T| oneof2(gen1, gen2).contains(x) <==>
        oneof_outputs(seq![gen1, gen2]).contains(x) by {
        if oneof2(gen1, gen2).contains(x) {
            if gen1.contains(x) {
                assert(seq![gen1, gen2][0].contains(x));
            } else {
                assert(gen2.contains(x));
                assert(seq![gen1, gen2][1].contains(x));
            }
        }
        if oneof_outputs(seq![gen1, gen2]).contains(x) {
            let i = choose|i: int| 0 <= i < 2 && seq![gen1, gen2][i].contains(x);
            if i == 0 {
                assert(gen1.contains(x));
            } else {
                assert(gen2.contains(x));
            }
        }
    }
}

// ----------------------------------------------------------------------------
// OneOf is Commutative and Associative
// ----------------------------------------------------------------------------

/// OneOf2 is commutative
pub proof fn oneof2_comm<T>(gen1: Set<T>, gen2: Set<T>)
    ensures oneof2(gen1, gen2) =~= oneof2(gen2, gen1)
{
    // Union is commutative
}

/// OneOf2 is associative
pub proof fn oneof2_assoc<T>(gen1: Set<T>, gen2: Set<T>, gen3: Set<T>)
    ensures oneof2(oneof2(gen1, gen2), gen3) =~= oneof2(gen1, oneof2(gen2, gen3))
{
    // Union is associative
}

// ----------------------------------------------------------------------------
// Elements Combinator (special case of oneOf for elements)
// ----------------------------------------------------------------------------

/// elements: choose from a fixed set of values
pub open spec fn elements_outputs<T>(elems: Seq<T>) -> Set<T> {
    Set::new(|x: T| exists|i: int| 0 <= i < elems.len() && elems[i] == x)
}

/// Elements contains all listed elements
pub proof fn elements_complete<T>(elems: Seq<T>, i: int)
    requires 0 <= i < elems.len()
    ensures elements_outputs(elems).contains(elems[i])
{
}

/// Elements only contains listed elements
pub proof fn elements_exact<T>(elems: Seq<T>, x: T)
    requires elements_outputs(elems).contains(x)
    ensures exists|i: int| 0 <= i < elems.len() && elems[i] == x
{
}

// ----------------------------------------------------------------------------
// Enum Generation (common use case)
// ----------------------------------------------------------------------------

pub enum Suit {
    Hearts,
    Diamonds,
    Clubs,
    Spades,
}

/// All suits
pub open spec fn gen_suit_outputs() -> Set<Suit> {
    set![Suit::Hearts, Suit::Diamonds, Suit::Clubs, Suit::Spades]
}

/// OneOf for suits
pub proof fn gen_suit_is_oneof()
    ensures gen_suit_outputs() =~= oneof_outputs(seq![
        set![Suit::Hearts],
        set![Suit::Diamonds],
        set![Suit::Clubs],
        set![Suit::Spades],
    ])
{
    let gens = seq![
        set![Suit::Hearts],
        set![Suit::Diamonds],
        set![Suit::Clubs],
        set![Suit::Spades],
    ];

    assert forall|s: Suit| gen_suit_outputs().contains(s) <==>
        oneof_outputs(gens).contains(s) by {
        match s {
            Suit::Hearts => {
                assert(gens[0].contains(s));
            }
            Suit::Diamonds => {
                assert(gens[1].contains(s));
            }
            Suit::Clubs => {
                assert(gens[2].contains(s));
            }
            Suit::Spades => {
                assert(gens[3].contains(s));
            }
        }
    }
}

// ----------------------------------------------------------------------------
// Return Combinator (constant generator)
// ----------------------------------------------------------------------------

/// return_: generator that produces exactly one value
pub open spec fn return_outputs<T>(x: T) -> Set<T> {
    set![x]
}

/// Return produces the given value
pub proof fn return_value<T>(x: T)
    ensures return_outputs(x).contains(x)
{
}

/// Return produces only the given value
pub proof fn return_only<T>(x: T, y: T)
    requires return_outputs(x).contains(y)
    ensures x == y
{
}

// ----------------------------------------------------------------------------
// Combining OneOf with Other Combinators
// ----------------------------------------------------------------------------

/// Map after oneOf
pub open spec fn oneof_map<T, U>(gens: Seq<Set<T>>, f: spec_fn(T) -> U) -> Set<U> {
    Set::new(|y: U| exists|x: T| oneof_outputs(gens).contains(x) && f(x) == y)
}

/// Filter after oneOf
pub open spec fn oneof_filter<T>(gens: Seq<Set<T>>, p: spec_fn(T) -> bool) -> Set<T> {
    Set::new(|x: T| oneof_outputs(gens).contains(x) && p(x))
}

/// OneOf then bind
pub open spec fn oneof_bind<T, U>(gens: Seq<Set<T>>, f: spec_fn(T) -> Set<U>) -> Set<U> {
    Set::new(|y: U| exists|x: T| oneof_outputs(gens).contains(x) && f(x).contains(y))
}

// ----------------------------------------------------------------------------
// Nested OneOf
// ----------------------------------------------------------------------------

/// Flatten nested oneOf
pub open spec fn oneof_flatten<T>(nested: Seq<Seq<Set<T>>>) -> Set<T> {
    Set::new(|x: T|
        exists|i: int, j: int|
            0 <= i < nested.len() &&
            0 <= j < nested[i].len() &&
            nested[i][j].contains(x)
    )
}

/// Flatten contains values from nested generators
pub proof fn oneof_flatten_contains<T>(nested: Seq<Seq<Set<T>>>, i: int, j: int, x: T)
    requires
        0 <= i < nested.len(),
        0 <= j < nested[i].len(),
        nested[i][j].contains(x),
    ensures oneof_flatten(nested).contains(x)
{
}

// ----------------------------------------------------------------------------
// Selective OneOf (conditional choice)
// ----------------------------------------------------------------------------

/// Choose based on predicate
pub open spec fn oneof_when<T>(cond: bool, then_gen: Set<T>, else_gen: Set<T>) -> Set<T> {
    if cond { then_gen } else { else_gen }
}

/// When true, use then branch
pub proof fn oneof_when_true<T>(then_gen: Set<T>, else_gen: Set<T>)
    ensures oneof_when(true, then_gen, else_gen) =~= then_gen
{
}

/// When false, use else branch
pub proof fn oneof_when_false<T>(then_gen: Set<T>, else_gen: Set<T>)
    ensures oneof_when(false, then_gen, else_gen) =~= else_gen
{
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_oneof_basic()
{
    let gen1: Set<nat> = Set::new(|n: nat| n <= 5);
    let gen2: Set<nat> = Set::new(|n: nat| 10 <= n && n <= 15);

    // Contains values from both
    oneof_contains_each(seq![gen1, gen2], 0, 3nat);
    assert(oneof_outputs(seq![gen1, gen2]).contains(3nat));

    oneof_contains_each(seq![gen1, gen2], 1, 12nat);
    assert(oneof_outputs(seq![gen1, gen2]).contains(12nat));

    // Gap not included
    assert(!oneof_outputs(seq![gen1, gen2]).contains(7nat));
}

pub proof fn example_oneof2()
{
    let gen1: Set<nat> = set![1nat, 2nat];
    let gen2: Set<nat> = set![10nat, 20nat];

    let combined = oneof2(gen1, gen2);
    assert(combined.contains(1nat));
    assert(combined.contains(20nat));
    assert(!combined.contains(5nat));

    oneof2_equiv(gen1, gen2);
    oneof2_comm(gen1, gen2);
}

pub proof fn example_oneof_singleton()
{
    let gen: Set<nat> = set![1nat, 2nat, 3nat];
    oneof_singleton(gen);
    assert(oneof_outputs(seq![gen]).contains(2nat));
}

pub proof fn example_elements()
{
    let colors = seq![1nat, 2nat, 3nat, 4nat];

    elements_complete(colors, 0);
    assert(elements_outputs(colors).contains(1nat));

    elements_complete(colors, 3);
    assert(elements_outputs(colors).contains(4nat));

    assert(!elements_outputs(colors).contains(5nat));
}

pub proof fn example_return()
{
    return_value(42nat);
    assert(return_outputs(42nat).contains(42nat));

    return_only(42nat, 42nat);
}

pub proof fn example_suit()
{
    gen_suit_is_oneof();

    assert(gen_suit_outputs().contains(Suit::Hearts));
    assert(gen_suit_outputs().contains(Suit::Spades));
}

pub proof fn example_oneof_when()
{
    let small: Set<nat> = Set::new(|n: nat| n <= 10);
    let large: Set<nat> = Set::new(|n: nat| 100 <= n && n <= 200);

    oneof_when_true(small, large);
    assert(oneof_when(true, small, large).contains(5nat));
    assert(!oneof_when(true, small, large).contains(150nat));

    oneof_when_false(small, large);
    assert(oneof_when(false, small, large).contains(150nat));
    assert(!oneof_when(false, small, large).contains(5nat));
}

pub proof fn example_oneof_empty()
{
    oneof_empty::<nat>();
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_gen_oneof_verify()
{
    example_oneof_basic();
    example_oneof2();
    example_oneof_singleton();
    example_elements();
    example_return();
    example_suit();
    example_oneof_when();
    example_oneof_empty();
}

pub fn main() {
    proof {
        qc_gen_oneof_verify();
    }
}

} // verus!

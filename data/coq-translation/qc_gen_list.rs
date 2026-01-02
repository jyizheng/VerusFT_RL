use vstd::prelude::*;

verus! {

// ============================================================================
// QC: List/Seq Generators (QuickChick-style)
// Specification functions modeling list generation for property testing
// ============================================================================

// ----------------------------------------------------------------------------
// Core Generator Model
// A list generator produces sequences of elements from an inner generator
// ----------------------------------------------------------------------------

/// Empty list generator
pub open spec fn gen_nil_outputs<T>() -> Set<Seq<T>> {
    set![Seq::empty()]
}

/// Singleton list generator
pub open spec fn gen_singleton_outputs<T>(inner_outputs: Set<T>) -> Set<Seq<T>> {
    Set::new(|s: Seq<T>| s.len() == 1 && inner_outputs.contains(s[0]))
}

/// List of exactly n elements
pub open spec fn gen_list_n_outputs<T>(inner_outputs: Set<T>, n: nat) -> Set<Seq<T>>
    decreases n
{
    if n == 0 {
        set![Seq::empty()]
    } else {
        Set::new(|s: Seq<T>|
            s.len() == n &&
            forall|i: int| 0 <= i < n ==> inner_outputs.contains(#[trigger] s[i])
        )
    }
}

/// List of up to n elements (gen_list with size parameter)
pub open spec fn gen_list_outputs<T>(inner_outputs: Set<T>, max_len: nat) -> Set<Seq<T>> {
    Set::new(|s: Seq<T>|
        s.len() <= max_len &&
        forall|i: int| 0 <= i < s.len() ==> inner_outputs.contains(#[trigger] s[i])
    )
}

/// list_of: Generate list where each element comes from inner generator
pub open spec fn list_of<T>(inner_outputs: Set<T>) -> Set<Seq<T>> {
    Set::new(|s: Seq<T>|
        forall|i: int| 0 <= i < s.len() ==> inner_outputs.contains(#[trigger] s[i])
    )
}

// ----------------------------------------------------------------------------
// List Generator Properties
// ----------------------------------------------------------------------------

/// Empty list is always generable
pub proof fn gen_list_contains_empty<T>(inner_outputs: Set<T>, max_len: nat)
    ensures gen_list_outputs(inner_outputs, max_len).contains(Seq::empty())
{
}

/// Singleton is generable if element is
pub proof fn gen_list_contains_singleton<T>(inner_outputs: Set<T>, max_len: nat, x: T)
    requires inner_outputs.contains(x), max_len >= 1
    ensures gen_list_outputs(inner_outputs, max_len).contains(seq![x])
{
    let s = seq![x];
    assert(s.len() == 1);
    assert(s.len() <= max_len);
    assert forall|i: int| 0 <= i < s.len() implies inner_outputs.contains(#[trigger] s[i]) by {
        assert(s[0] == x);
    }
}

/// gen_list respects length bound
pub proof fn gen_list_length_bound<T>(inner_outputs: Set<T>, max_len: nat, s: Seq<T>)
    requires gen_list_outputs(inner_outputs, max_len).contains(s)
    ensures s.len() <= max_len
{
}

/// All elements in generated list are from inner
pub proof fn gen_list_elements_valid<T>(inner_outputs: Set<T>, max_len: nat, s: Seq<T>, i: int)
    requires
        gen_list_outputs(inner_outputs, max_len).contains(s),
        0 <= i < s.len(),
    ensures inner_outputs.contains(s[i])
{
}

// ----------------------------------------------------------------------------
// List Combinators
// ----------------------------------------------------------------------------

/// Map over list generator
pub open spec fn gen_list_map<T, U>(
    outputs: Set<Seq<T>>,
    f: spec_fn(T) -> U
) -> Set<Seq<U>> {
    Set::new(|s: Seq<U>|
        exists|t: Seq<T>| outputs.contains(t) && s.len() == t.len() &&
            forall|i: int| 0 <= i < s.len() ==> s[i] == f(#[trigger] t[i])
    )
}

/// Filter elements in generated lists
pub open spec fn gen_list_filter<T>(
    outputs: Set<Seq<T>>,
    p: spec_fn(T) -> bool
) -> Set<Seq<T>> {
    Set::new(|s: Seq<T>|
        exists|t: Seq<T>| outputs.contains(t) && s == t.filter(p)
    )
}

/// Concatenate lists from two generators
pub open spec fn gen_list_concat<T>(
    out1: Set<Seq<T>>,
    out2: Set<Seq<T>>
) -> Set<Seq<T>> {
    Set::new(|s: Seq<T>|
        exists|s1: Seq<T>, s2: Seq<T>| out1.contains(s1) && out2.contains(s2) && s == s1 + s2
    )
}

/// Append single element to lists
pub open spec fn gen_list_cons<T>(
    elem_outputs: Set<T>,
    list_outputs: Set<Seq<T>>
) -> Set<Seq<T>> {
    Set::new(|s: Seq<T>|
        s.len() > 0 &&
        elem_outputs.contains(s[0]) &&
        list_outputs.contains(s.drop_first())
    )
}

// ----------------------------------------------------------------------------
// Combinator Properties
// ----------------------------------------------------------------------------

/// Map preserves length
pub proof fn gen_list_map_length<T, U>(outputs: Set<Seq<T>>, f: spec_fn(T) -> U, s: Seq<U>, t: Seq<T>)
    requires
        outputs.contains(t),
        s.len() == t.len(),
        forall|i: int| 0 <= i < s.len() ==> s[i] == f(#[trigger] t[i]),
    ensures gen_list_map(outputs, f).contains(s)
{
}

/// Concat of empty lists is empty
pub proof fn gen_list_concat_empty<T>()
    ensures gen_list_concat(gen_nil_outputs::<T>(), gen_nil_outputs::<T>()).contains(Seq::empty())
{
    let s1: Seq<T> = Seq::empty();
    let s2: Seq<T> = Seq::empty();
    assert(gen_nil_outputs::<T>().contains(s1));
    assert(gen_nil_outputs::<T>().contains(s2));
    assert(s1 + s2 =~= Seq::empty());
}

/// Cons builds longer lists
pub proof fn gen_list_cons_length<T>(elem_outputs: Set<T>, list_outputs: Set<Seq<T>>, s: Seq<T>)
    requires gen_list_cons(elem_outputs, list_outputs).contains(s)
    ensures s.len() > 0
{
}

// ----------------------------------------------------------------------------
// Non-empty List Generator
// ----------------------------------------------------------------------------

/// Generate non-empty lists
pub open spec fn gen_list_nonempty_outputs<T>(inner_outputs: Set<T>, max_len: nat) -> Set<Seq<T>> {
    Set::new(|s: Seq<T>|
        s.len() >= 1 &&
        s.len() <= max_len &&
        forall|i: int| 0 <= i < s.len() ==> inner_outputs.contains(#[trigger] s[i])
    )
}

/// Non-empty lists have at least one element
pub proof fn gen_list_nonempty_has_element<T>(inner_outputs: Set<T>, max_len: nat, s: Seq<T>)
    requires gen_list_nonempty_outputs(inner_outputs, max_len).contains(s), max_len >= 1
    ensures s.len() >= 1
{
}

// ----------------------------------------------------------------------------
// List with specific properties
// ----------------------------------------------------------------------------

/// Generate sorted lists (ascending)
pub open spec fn gen_sorted_list_outputs(max_len: nat, bound: nat) -> Set<Seq<nat>> {
    Set::new(|s: Seq<nat>|
        s.len() <= max_len &&
        (forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] <= bound) &&
        (forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j])
    )
}

/// Sorted lists maintain ordering
pub proof fn gen_sorted_is_sorted(max_len: nat, bound: nat, s: Seq<nat>, i: int, j: int)
    requires
        gen_sorted_list_outputs(max_len, bound).contains(s),
        0 <= i < j < s.len(),
    ensures s[i] <= s[j]
{
}

// ----------------------------------------------------------------------------
// Distinct Element Lists
// ----------------------------------------------------------------------------

/// Generate lists with distinct elements
pub open spec fn gen_distinct_list_outputs(max_len: nat, bound: nat) -> Set<Seq<nat>> {
    Set::new(|s: Seq<nat>|
        s.len() <= max_len &&
        (forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] <= bound) &&
        (forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j])
    )
}

/// Distinct lists have unique elements
pub proof fn gen_distinct_are_distinct(max_len: nat, bound: nat, s: Seq<nat>, i: int, j: int)
    requires
        gen_distinct_list_outputs(max_len, bound).contains(s),
        0 <= i < j < s.len(),
    ensures s[i] != s[j]
{
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_gen_list_basic()
{
    let inner: Set<nat> = Set::new(|n: nat| n <= 5);

    gen_list_contains_empty(inner, 10nat);
    assert(gen_list_outputs(inner, 10nat).contains(Seq::empty()));

    gen_list_contains_singleton(inner, 10nat, 3nat);
    assert(gen_list_outputs(inner, 10nat).contains(seq![3nat]));
}

pub proof fn example_gen_list_n()
{
    let inner: Set<nat> = Set::new(|n: nat| n <= 5);

    // List of exactly 2 elements
    let s = seq![1nat, 2nat];
    assert(s.len() == 2);
    assert forall|i: int| 0 <= i < 2 implies inner.contains(#[trigger] s[i]) by {
        if i == 0 { assert(s[0] == 1); }
        if i == 1 { assert(s[1] == 2); }
    }
    assert(gen_list_n_outputs(inner, 2nat).contains(s));
}

pub proof fn example_list_of()
{
    let inner: Set<nat> = Set::new(|n: nat| n <= 10);

    // Any length list is allowed by list_of
    let s = seq![1nat, 5nat, 10nat];
    assert forall|i: int| 0 <= i < s.len() implies inner.contains(#[trigger] s[i]) by {
        if i == 0 { assert(s[0] == 1); }
        if i == 1 { assert(s[1] == 5); }
        if i == 2 { assert(s[2] == 10); }
    }
    assert(list_of(inner).contains(s));

    // Empty list is also in list_of
    assert(list_of(inner).contains(Seq::<nat>::empty()));
}

pub proof fn example_gen_list_concat()
{
    gen_list_concat_empty::<nat>();
    assert(gen_list_concat(gen_nil_outputs::<nat>(), gen_nil_outputs::<nat>()).contains(Seq::empty()));

    let inner: Set<nat> = Set::new(|n: nat| n <= 5);
    let single = gen_singleton_outputs(inner);

    // Concatenating singletons gives length 2
    let s1 = seq![1nat];
    let s2 = seq![2nat];
    assert(single.contains(s1));
    assert(single.contains(s2));
    let concat_out = gen_list_concat(single, single);
    assert(s1 + s2 == seq![1nat, 2nat]);
}

pub proof fn example_gen_sorted()
{
    let s = seq![1nat, 2nat, 5nat];
    assert(s.len() == 3);
    assert(s.len() <= 5);

    // Check all elements <= bound
    assert forall|i: int| 0 <= i < s.len() implies #[trigger] s[i] <= 10 by {
        if i == 0 { assert(s[0] == 1); }
        if i == 1 { assert(s[1] == 2); }
        if i == 2 { assert(s[2] == 5); }
    }

    // Check sorted
    assert forall|i: int, j: int| 0 <= i < j < s.len() implies s[i] <= s[j] by {
        if i == 0 && j == 1 { assert(s[0] <= s[1]); }
        if i == 0 && j == 2 { assert(s[0] <= s[2]); }
        if i == 1 && j == 2 { assert(s[1] <= s[2]); }
    }

    assert(gen_sorted_list_outputs(5nat, 10nat).contains(s));
}

pub proof fn example_gen_distinct()
{
    let s = seq![1nat, 3nat, 5nat];
    assert(s.len() == 3);
    assert(s.len() <= 5);

    // Check all elements <= bound
    assert forall|i: int| 0 <= i < s.len() implies #[trigger] s[i] <= 10 by {
        if i == 0 { assert(s[0] == 1); }
        if i == 1 { assert(s[1] == 3); }
        if i == 2 { assert(s[2] == 5); }
    }

    // Check distinct
    assert forall|i: int, j: int| 0 <= i < j < s.len() implies s[i] != s[j] by {
        if i == 0 && j == 1 { assert(s[0] != s[1]); }
        if i == 0 && j == 2 { assert(s[0] != s[2]); }
        if i == 1 && j == 2 { assert(s[1] != s[2]); }
    }

    assert(gen_distinct_list_outputs(5nat, 10nat).contains(s));
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_gen_list_verify()
{
    example_gen_list_basic();
    example_gen_list_n();
    example_list_of();
    example_gen_list_concat();
    example_gen_sorted();
    example_gen_distinct();
}

pub fn main() {
    proof {
        qc_gen_list_verify();
    }
}

} // verus!

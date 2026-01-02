use vstd::prelude::*;

verus! {

// ============================================================================
// QC: Option Predicate Decidability (QuickChick-style)
// Models decidable predicates for Option types: is_some, is_none, etc.
// ============================================================================

// ----------------------------------------------------------------------------
// Decidability Result Type
// ----------------------------------------------------------------------------

pub enum Dec {
    Yes,
    No,
}

pub open spec fn dec_to_bool(d: Dec) -> bool {
    match d {
        Dec::Yes => true,
        Dec::No => false,
    }
}

pub open spec fn bool_to_dec(b: bool) -> Dec {
    if b { Dec::Yes } else { Dec::No }
}

// ----------------------------------------------------------------------------
// Basic Option Predicates
// ----------------------------------------------------------------------------

/// is_some is decidable
pub open spec fn dec_is_some<T>(opt: Option<T>) -> Dec {
    match opt {
        Option::Some(_) => Dec::Yes,
        Option::None => Dec::No,
    }
}

/// is_none is decidable
pub open spec fn dec_is_none<T>(opt: Option<T>) -> Dec {
    match opt {
        Option::Some(_) => Dec::No,
        Option::None => Dec::Yes,
    }
}

// ----------------------------------------------------------------------------
// Option Equality Decidability
// ----------------------------------------------------------------------------

/// Option equality is decidable given decidable element equality
pub open spec fn dec_eq_option<T>(
    a: Option<T>,
    b: Option<T>,
    dec_eq_t: spec_fn(T, T) -> Dec
) -> Dec {
    match (a, b) {
        (Option::None, Option::None) => Dec::Yes,
        (Option::Some(x), Option::Some(y)) => dec_eq_t(x, y),
        _ => Dec::No,
    }
}

/// Option<nat> equality is decidable
pub open spec fn dec_eq_option_nat(a: Option<nat>, b: Option<nat>) -> Dec {
    dec_eq_option(a, b, |x: nat, y: nat| bool_to_dec(x == y))
}

// ----------------------------------------------------------------------------
// Option Contains Decidability
// ----------------------------------------------------------------------------

/// Check if Some contains a specific value
pub open spec fn dec_option_contains<T>(
    opt: Option<T>,
    x: T,
    eq: spec_fn(T, T) -> bool
) -> Dec {
    match opt {
        Option::None => Dec::No,
        Option::Some(v) => bool_to_dec(eq(v, x)),
    }
}

/// Option<nat> contains is decidable
pub open spec fn dec_option_contains_nat(opt: Option<nat>, x: nat) -> Dec {
    dec_option_contains(opt, x, |a: nat, b: nat| a == b)
}

// ----------------------------------------------------------------------------
// Option Predicate Decidability
// ----------------------------------------------------------------------------

/// Check if Some value satisfies a predicate
pub open spec fn option_satisfies<T>(opt: Option<T>, p: spec_fn(T) -> bool) -> bool {
    match opt {
        Option::None => false,
        Option::Some(v) => p(v),
    }
}

/// Option satisfies predicate is decidable
pub open spec fn dec_option_satisfies<T>(opt: Option<T>, p: spec_fn(T) -> bool) -> Dec {
    bool_to_dec(option_satisfies(opt, p))
}

/// Check if None or Some value satisfies predicate
pub open spec fn option_forall<T>(opt: Option<T>, p: spec_fn(T) -> bool) -> bool {
    match opt {
        Option::None => true,
        Option::Some(v) => p(v),
    }
}

/// Option forall is decidable
pub open spec fn dec_option_forall<T>(opt: Option<T>, p: spec_fn(T) -> bool) -> Dec {
    bool_to_dec(option_forall(opt, p))
}

// ----------------------------------------------------------------------------
// Option Ordering Decidability
// ----------------------------------------------------------------------------

/// Option less than (None < Some(_))
pub open spec fn option_lt<T>(
    a: Option<T>,
    b: Option<T>,
    lt_t: spec_fn(T, T) -> bool
) -> bool {
    match (a, b) {
        (Option::None, Option::None) => false,
        (Option::None, Option::Some(_)) => true,
        (Option::Some(_), Option::None) => false,
        (Option::Some(x), Option::Some(y)) => lt_t(x, y),
    }
}

/// Option lt is decidable
pub open spec fn dec_option_lt<T>(
    a: Option<T>,
    b: Option<T>,
    lt_t: spec_fn(T, T) -> bool
) -> Dec {
    bool_to_dec(option_lt(a, b, lt_t))
}

/// Option<nat> lt is decidable
pub open spec fn dec_option_lt_nat(a: Option<nat>, b: Option<nat>) -> Dec {
    dec_option_lt(a, b, |x: nat, y: nat| x < y)
}

// ----------------------------------------------------------------------------
// Soundness Proofs
// ----------------------------------------------------------------------------

/// dec_is_some is sound
pub proof fn dec_is_some_sound<T>(opt: Option<T>)
    ensures dec_to_bool(dec_is_some(opt)) <==> opt.is_some()
{
}

/// dec_is_none is sound
pub proof fn dec_is_none_sound<T>(opt: Option<T>)
    ensures dec_to_bool(dec_is_none(opt)) <==> opt.is_none()
{
}

/// is_some and is_none are complements
pub proof fn dec_is_some_none_complement<T>(opt: Option<T>)
    ensures dec_to_bool(dec_is_some(opt)) == !dec_to_bool(dec_is_none(opt))
{
}

/// dec_option_contains is sound
pub proof fn dec_option_contains_sound<T>(opt: Option<T>, x: T, eq: spec_fn(T, T) -> bool)
    requires forall|a: T, b: T| #[trigger] eq(a, b) <==> (a == b)
    ensures dec_to_bool(dec_option_contains(opt, x, eq)) <==>
        (opt.is_some() && opt.unwrap() == x)
{
}

/// dec_option_satisfies is sound
pub proof fn dec_option_satisfies_sound<T>(opt: Option<T>, p: spec_fn(T) -> bool)
    ensures dec_to_bool(dec_option_satisfies(opt, p)) <==> option_satisfies(opt, p)
{
}

/// dec_option_forall is sound
pub proof fn dec_option_forall_sound<T>(opt: Option<T>, p: spec_fn(T) -> bool)
    ensures dec_to_bool(dec_option_forall(opt, p)) <==> option_forall(opt, p)
{
}

// ----------------------------------------------------------------------------
// Option Map Decidability
// ----------------------------------------------------------------------------

/// Spec for Option map
pub open spec fn option_map<T, U>(opt: Option<T>, f: spec_fn(T) -> U) -> Option<U> {
    match opt {
        Option::None => Option::None,
        Option::Some(v) => Option::Some(f(v)),
    }
}

/// Result of map satisfies predicate is decidable
pub open spec fn dec_option_map_satisfies<T, U>(
    opt: Option<T>,
    f: spec_fn(T) -> U,
    p: spec_fn(U) -> bool
) -> Dec {
    dec_option_satisfies(option_map(opt, f), p)
}

/// Map preserves is_some
pub proof fn option_map_preserves_is_some<T, U>(opt: Option<T>, f: spec_fn(T) -> U)
    ensures dec_to_bool(dec_is_some(opt)) == dec_to_bool(dec_is_some(option_map(opt, f)))
{
}

/// Map preserves is_none
pub proof fn option_map_preserves_is_none<T, U>(opt: Option<T>, f: spec_fn(T) -> U)
    ensures dec_to_bool(dec_is_none(opt)) == dec_to_bool(dec_is_none(option_map(opt, f)))
{
}

// ----------------------------------------------------------------------------
// Option Bind (and_then) Decidability
// ----------------------------------------------------------------------------

/// Spec for Option bind/and_then
pub open spec fn option_bind<T, U>(opt: Option<T>, f: spec_fn(T) -> Option<U>) -> Option<U> {
    match opt {
        Option::None => Option::None,
        Option::Some(v) => f(v),
    }
}

/// Result of bind is some is decidable
pub open spec fn dec_option_bind_is_some<T, U>(
    opt: Option<T>,
    f: spec_fn(T) -> Option<U>
) -> Dec {
    dec_is_some(option_bind(opt, f))
}

/// None binds to None
pub proof fn option_bind_none<T, U>(f: spec_fn(T) -> Option<U>)
    ensures dec_to_bool(dec_is_none(option_bind(Option::<T>::None, f)))
{
}

// ----------------------------------------------------------------------------
// Option Or Decidability
// ----------------------------------------------------------------------------

/// Spec for Option or (get first Some or second)
pub open spec fn option_or<T>(a: Option<T>, b: Option<T>) -> Option<T> {
    match a {
        Option::Some(_) => a,
        Option::None => b,
    }
}

/// Result of or is some
pub open spec fn dec_option_or_is_some<T>(a: Option<T>, b: Option<T>) -> Dec {
    dec_is_some(option_or(a, b))
}

/// Or is some if either is some
pub proof fn option_or_some<T>(a: Option<T>, b: Option<T>)
    ensures dec_to_bool(dec_option_or_is_some(a, b)) <==>
        (dec_to_bool(dec_is_some(a)) || dec_to_bool(dec_is_some(b)))
{
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_dec_is_some_none()
{
    let some_val: Option<nat> = Option::Some(5);
    let none_val: Option<nat> = Option::None;

    assert(dec_to_bool(dec_is_some(some_val)));
    assert(!dec_to_bool(dec_is_some(none_val)));

    assert(!dec_to_bool(dec_is_none(some_val)));
    assert(dec_to_bool(dec_is_none(none_val)));

    dec_is_some_none_complement(some_val);
    dec_is_some_none_complement(none_val);
}

pub proof fn example_dec_eq_option()
{
    let a: Option<nat> = Option::Some(5);
    let b: Option<nat> = Option::Some(5);
    let c: Option<nat> = Option::Some(7);
    let n: Option<nat> = Option::None;

    assert(dec_to_bool(dec_eq_option_nat(a, b)));
    assert(!dec_to_bool(dec_eq_option_nat(a, c)));
    assert(!dec_to_bool(dec_eq_option_nat(a, n)));
    assert(dec_to_bool(dec_eq_option_nat(n, n)));
}

pub proof fn example_dec_option_contains()
{
    let some_5: Option<nat> = Option::Some(5);
    let some_7: Option<nat> = Option::Some(7);
    let none: Option<nat> = Option::None;

    assert(dec_to_bool(dec_option_contains_nat(some_5, 5)));
    assert(!dec_to_bool(dec_option_contains_nat(some_5, 7)));
    assert(!dec_to_bool(dec_option_contains_nat(some_7, 5)));
    assert(!dec_to_bool(dec_option_contains_nat(none, 5)));
}

pub proof fn example_dec_option_satisfies()
{
    let some_even: Option<nat> = Option::Some(4);
    let some_odd: Option<nat> = Option::Some(5);
    let none: Option<nat> = Option::None;

    let is_even = |n: nat| n % 2 == 0;

    assert(dec_to_bool(dec_option_satisfies(some_even, is_even)));
    assert(!dec_to_bool(dec_option_satisfies(some_odd, is_even)));
    assert(!dec_to_bool(dec_option_satisfies(none, is_even)));
}

pub proof fn example_dec_option_forall()
{
    let some_even: Option<nat> = Option::Some(4);
    let some_odd: Option<nat> = Option::Some(5);
    let none: Option<nat> = Option::None;

    let is_even = |n: nat| n % 2 == 0;

    assert(dec_to_bool(dec_option_forall(some_even, is_even)));
    assert(!dec_to_bool(dec_option_forall(some_odd, is_even)));
    // None satisfies forall vacuously
    assert(dec_to_bool(dec_option_forall(none, is_even)));
}

pub proof fn example_dec_option_lt()
{
    let none: Option<nat> = Option::None;
    let some_3: Option<nat> = Option::Some(3);
    let some_5: Option<nat> = Option::Some(5);

    // None < Some
    assert(dec_to_bool(dec_option_lt_nat(none, some_3)));
    assert(!dec_to_bool(dec_option_lt_nat(some_3, none)));

    // Compare Some values
    assert(dec_to_bool(dec_option_lt_nat(some_3, some_5)));
    assert(!dec_to_bool(dec_option_lt_nat(some_5, some_3)));
    assert(!dec_to_bool(dec_option_lt_nat(some_3, some_3)));

    // None is not < None
    assert(!dec_to_bool(dec_option_lt_nat(none, none)));
}

pub proof fn example_dec_option_map()
{
    let some_5: Option<nat> = Option::Some(5);
    let none: Option<nat> = Option::None;

    let double = |n: nat| n * 2;
    let is_even = |n: nat| n % 2 == 0;

    // map(Some(5), double) = Some(10), which is even
    assert(dec_to_bool(dec_option_map_satisfies(some_5, double, is_even)));

    // map(None, double) = None, which doesn't satisfy
    assert(!dec_to_bool(dec_option_map_satisfies(none, double, is_even)));

    option_map_preserves_is_some(some_5, double);
    option_map_preserves_is_none(none, double);
}

pub proof fn example_dec_option_or()
{
    let some_5: Option<nat> = Option::Some(5);
    let some_7: Option<nat> = Option::Some(7);
    let none: Option<nat> = Option::None;

    // Some or anything is Some
    assert(dec_to_bool(dec_option_or_is_some(some_5, some_7)));
    assert(dec_to_bool(dec_option_or_is_some(some_5, none)));

    // None or Some is Some
    assert(dec_to_bool(dec_option_or_is_some(none, some_7)));

    // None or None is None
    assert(!dec_to_bool(dec_option_or_is_some(none, none)));

    option_or_some(some_5, none);
    option_or_some(none, some_7);
    option_or_some(none, none);
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_dec_option_verify()
{
    example_dec_is_some_none();
    example_dec_eq_option();
    example_dec_option_contains();
    example_dec_option_satisfies();
    example_dec_option_forall();
    example_dec_option_lt();
    example_dec_option_map();
    example_dec_option_or();
}

pub fn main() {
    proof {
        qc_dec_option_verify();
    }
}

} // verus!

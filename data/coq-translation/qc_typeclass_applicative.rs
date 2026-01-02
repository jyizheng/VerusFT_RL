use vstd::prelude::*;

verus! {

// ============================================================================
// QC Typeclass: Applicative Functor
// ============================================================================
// Models the Applicative typeclass with pure and ap operations.
// Applicative functors are useful in QuickCheck for combining generators.

// Applicative laws:
// 1. Identity: pure id <*> v = v
// 2. Composition: pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
// 3. Homomorphism: pure f <*> pure x = pure (f x)
// 4. Interchange: u <*> pure y = pure ($ y) <*> u

// ----------------------------------------------------------------------------
// Applicative for Option
// ----------------------------------------------------------------------------

pub open spec fn pure_option<A>(a: A) -> Option<A> {
    Option::Some(a)
}

pub open spec fn ap_option<A, B>(
    of: Option<spec_fn(A) -> B>,
    oa: Option<A>
) -> Option<B> {
    match (of, oa) {
        (Option::Some(f), Option::Some(a)) => Option::Some(f(a)),
        _ => Option::None,
    }
}

// Derived: fmap for Option (from Applicative)
pub open spec fn fmap_option<A, B>(f: spec_fn(A) -> B, oa: Option<A>) -> Option<B> {
    ap_option(Option::Some(f), oa)
}

// Identity law: pure id <*> v = v
pub proof fn ap_option_identity<A>(v: Option<A>)
    ensures ap_option(Option::Some(|a: A| a), v) == v
{
    match v {
        Option::None => {
            assert(ap_option(Option::Some(|a: A| a), Option::<A>::None) == Option::<A>::None);
        }
        Option::Some(x) => {
            assert(ap_option(Option::Some(|a: A| a), Option::Some(x)) == Option::Some(x));
        }
    }
}

// Homomorphism law: pure f <*> pure x = pure (f x)
pub proof fn ap_option_homomorphism<A, B>(f: spec_fn(A) -> B, x: A)
    ensures ap_option(pure_option(f), pure_option(x)) == pure_option(f(x))
{
    assert(ap_option(Option::Some(f), Option::Some(x)) == Option::Some(f(x)));
}

// ----------------------------------------------------------------------------
// Applicative for Seq (ZipList style)
// ----------------------------------------------------------------------------

// ZipList applicative: applies functions pointwise
pub open spec fn pure_seq<A>(a: A, len: nat) -> Seq<A> {
    Seq::new(len, |_i: int| a)
}

pub open spec fn ap_seq_zip<A, B>(
    fs: Seq<spec_fn(A) -> B>,
    xs: Seq<A>
) -> Seq<B> {
    let min_len = if fs.len() < xs.len() { fs.len() } else { xs.len() };
    Seq::new(min_len, |i: int| fs[i](xs[i]))
}

// Identity law for ZipList
pub proof fn ap_seq_zip_identity<A>(xs: Seq<A>)
    ensures ap_seq_zip(pure_seq(|a: A| a, xs.len()), xs) =~= xs
{
    let fs = pure_seq(|a: A| a, xs.len());
    let result = ap_seq_zip(fs, xs);
    assert(result.len() == xs.len());
    assert forall|i: int| 0 <= i < xs.len() as int implies result[i] == xs[i] by {
        assert(fs[i] == (|a: A| a));
        assert(result[i] == fs[i](xs[i]));
        assert(result[i] == xs[i]);
    };
}

// Length property
pub proof fn ap_seq_zip_length<A, B>(fs: Seq<spec_fn(A) -> B>, xs: Seq<A>)
    ensures ap_seq_zip(fs, xs).len() == if fs.len() < xs.len() { fs.len() } else { xs.len() }
{
    // Trivially true by definition
}

// ----------------------------------------------------------------------------
// Applicative for Result/Either
// ----------------------------------------------------------------------------

pub enum Result<A, E> {
    Ok(A),
    Err(E),
}

pub open spec fn pure_result<A, E>(a: A) -> Result<A, E> {
    Result::Ok(a)
}

pub open spec fn ap_result<A, B, E>(
    rf: Result<spec_fn(A) -> B, E>,
    ra: Result<A, E>
) -> Result<B, E> {
    match rf {
        Result::Err(e) => Result::Err(e),
        Result::Ok(f) => match ra {
            Result::Err(e) => Result::Err(e),
            Result::Ok(a) => Result::Ok(f(a)),
        }
    }
}

// Identity law for Result
pub proof fn ap_result_identity<A, E>(v: Result<A, E>)
    ensures ap_result::<A, A, E>(Result::Ok(|a: A| a), v) == v
{
    match v {
        Result::Err(e) => {}
        Result::Ok(x) => {}
    }
}

// Homomorphism for Result
pub proof fn ap_result_homomorphism<A, B, E>(f: spec_fn(A) -> B, x: A)
    ensures ap_result::<A, B, E>(pure_result(f), pure_result(x)) == pure_result::<B, E>(f(x))
{
    // Trivially true
}

// ----------------------------------------------------------------------------
// Applicative for Gen (generator applicative)
// ----------------------------------------------------------------------------

// Gen<A> modeled as spec_fn(nat, nat) -> A (seed, size) -> value

pub open spec fn pure_gen<A>(a: A) -> spec_fn(nat, nat) -> A {
    |_seed: nat, _size: nat| a
}

pub open spec fn ap_gen<A, B>(
    gf: spec_fn(nat, nat) -> spec_fn(A) -> B,
    ga: spec_fn(nat, nat) -> A
) -> spec_fn(nat, nat) -> B {
    |seed: nat, size: nat| gf(seed, size)(ga(seed + 1, size))
}

// Identity for Gen
pub proof fn ap_gen_identity<A>(ga: spec_fn(nat, nat) -> A, seed: nat, size: nat)
    ensures ap_gen(pure_gen(|a: A| a), ga)(seed, size) == ga(seed + 1, size)
{
    let gf = pure_gen(|a: A| a);
    assert(gf(seed, size) == (|a: A| a));
    assert(ap_gen(gf, ga)(seed, size) == gf(seed, size)(ga(seed + 1, size)));
}

// ----------------------------------------------------------------------------
// Applicative combinators
// ----------------------------------------------------------------------------

// liftA2: lift a binary function
pub open spec fn lift_a2_option<A, B, C>(
    f: spec_fn(A, B) -> C,
    oa: Option<A>,
    ob: Option<B>
) -> Option<C> {
    match (oa, ob) {
        (Option::Some(a), Option::Some(b)) => Option::Some(f(a, b)),
        _ => Option::None,
    }
}

pub proof fn lift_a2_option_both_some<A, B, C>(f: spec_fn(A, B) -> C, a: A, b: B)
    ensures lift_a2_option(f, Option::Some(a), Option::Some(b)) == Option::Some(f(a, b))
{
    // Trivially true
}

pub proof fn lift_a2_option_any_none_1<A, B, C>(f: spec_fn(A, B) -> C, ob: Option<B>)
    ensures lift_a2_option(f, Option::<A>::None, ob) == Option::<C>::None
{
    // Trivially true
}

// liftA3: lift a ternary function
pub open spec fn lift_a3_option<A, B, C, D>(
    f: spec_fn(A, B, C) -> D,
    oa: Option<A>,
    ob: Option<B>,
    oc: Option<C>
) -> Option<D> {
    match (oa, ob, oc) {
        (Option::Some(a), Option::Some(b), Option::Some(c)) => Option::Some(f(a, b, c)),
        _ => Option::None,
    }
}

// sequence for Option
pub open spec fn sequence_option<A>(xs: Seq<Option<A>>) -> Option<Seq<A>>
    decreases xs.len()
{
    if xs.len() == 0 {
        Option::Some(Seq::empty())
    } else {
        match (xs[0], sequence_option(xs.skip(1))) {
            (Option::Some(a), Option::Some(rest)) => Option::Some(seq![a].add(rest)),
            _ => Option::None,
        }
    }
}

pub proof fn sequence_option_all_some(xs: Seq<Option<nat>>)
    requires forall|i: int| 0 <= i < xs.len() as int ==> xs[i].is_some()
    ensures sequence_option(xs).is_some()
    decreases xs.len()
{
    if xs.len() == 0 {
        assert(sequence_option(xs) == Option::Some(Seq::<nat>::empty()));
    } else {
        assert(xs[0].is_some());
        sequence_option_all_some(xs.skip(1));
        assert(sequence_option(xs.skip(1)).is_some());
    }
}

pub proof fn sequence_option_any_none(xs: Seq<Option<nat>>, k: int)
    requires 0 <= k < xs.len() as int,
             xs[k] == Option::<nat>::None
    ensures sequence_option(xs) == Option::<Seq<nat>>::None
    decreases xs.len()
{
    if xs.len() == 0 {
        // Vacuously true
    } else if k == 0 {
        assert(xs[0] == Option::<nat>::None);
    } else {
        // None is in the tail
        sequence_option_any_none(xs.skip(1), k - 1);
    }
}

// ----------------------------------------------------------------------------
// Applicative for pairs (with monoid on first component)
// ----------------------------------------------------------------------------

// For pairs (M, A) where M is a monoid, we have an Applicative
// pure a = (mempty, a)
// (m1, f) <*> (m2, a) = (m1 + m2, f a)

pub open spec fn pure_pair_nat<A>(a: A) -> (nat, A) {
    (0, a)  // 0 is monoid identity for nat addition
}

pub open spec fn ap_pair_nat<A, B>(
    pf: (nat, spec_fn(A) -> B),
    pa: (nat, A)
) -> (nat, B) {
    ((pf.0 + pa.0) as nat, pf.1(pa.1))
}

pub proof fn ap_pair_nat_identity<A>(v: (nat, A))
    ensures ap_pair_nat((0, |a: A| a), v) == v
{
    let result = ap_pair_nat((0, |a: A| a), v);
    assert(result.0 == (0 + v.0) as nat);
    assert(result.0 == v.0);
    assert(result.1 == v.1);
}

// ----------------------------------------------------------------------------
// Example and verification
// ----------------------------------------------------------------------------

pub proof fn example_applicative()
{
    // Option applicative
    ap_option_identity(Option::Some(42nat));
    ap_option_identity::<nat>(Option::None);
    ap_option_homomorphism(|x: nat| x + 1, 5nat);

    // ZipList applicative
    let xs: Seq<nat> = seq![1nat, 2, 3];
    ap_seq_zip_identity(xs);

    // Result applicative
    ap_result_identity::<nat, nat>(Result::Ok(42));
    ap_result_identity::<nat, nat>(Result::Err(0));
    ap_result_homomorphism::<nat, nat, nat>(|x: nat| x + 1, 5);

    // liftA2
    lift_a2_option_both_some(|a: nat, b: nat| a + b, 3nat, 4nat);
    lift_a2_option_any_none_1::<nat, nat, nat>(|a: nat, b: nat| a + b, Option::Some(4nat));

    // sequence
    let all_some: Seq<Option<nat>> = seq![Option::Some(1nat), Option::Some(2nat)];
    sequence_option_all_some(all_some);

    // Pair applicative
    ap_pair_nat_identity((5nat, 42nat));
}

pub proof fn applicative_verify()
{
    example_applicative();
}

pub fn main()
{
    proof {
        applicative_verify();
    }
}

} // verus!

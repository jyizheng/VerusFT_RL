use vstd::prelude::*;

verus! {

// ============================================================================
// QC Typeclass: Foldable
// ============================================================================
// Models the Foldable typeclass for containers that can be folded/reduced.
// Core operations: foldr, foldl, and derived operations.

// Foldable laws relate foldr and foldl to list conversion (toList)

// ----------------------------------------------------------------------------
// Foldable for Seq (the canonical instance)
// ----------------------------------------------------------------------------

pub open spec fn foldr<A, B>(xs: Seq<A>, init: B, f: spec_fn(A, B) -> B) -> B
    decreases xs.len()
{
    if xs.len() == 0 {
        init
    } else {
        f(xs[0], foldr(xs.skip(1), init, f))
    }
}

pub open spec fn foldl<A, B>(xs: Seq<A>, init: B, f: spec_fn(B, A) -> B) -> B
    decreases xs.len()
{
    if xs.len() == 0 {
        init
    } else {
        foldl(xs.skip(1), f(init, xs[0]), f)
    }
}

// foldr unfolds correctly
pub proof fn foldr_unfold<A, B>(xs: Seq<A>, init: B, f: spec_fn(A, B) -> B)
    requires xs.len() > 0
    ensures foldr(xs, init, f) == f(xs[0], foldr(xs.skip(1), init, f))
{
    // Trivially true by definition
}

// foldl unfolds correctly
pub proof fn foldl_unfold<A, B>(xs: Seq<A>, init: B, f: spec_fn(B, A) -> B)
    requires xs.len() > 0
    ensures foldl(xs, init, f) == foldl(xs.skip(1), f(init, xs[0]), f)
{
    // Trivially true by definition
}

// Empty sequence
pub proof fn foldr_empty<A, B>(init: B, f: spec_fn(A, B) -> B)
    ensures foldr(Seq::<A>::empty(), init, f) == init
{
    assert(Seq::<A>::empty().len() == 0);
}

pub proof fn foldl_empty<A, B>(init: B, f: spec_fn(B, A) -> B)
    ensures foldl(Seq::<A>::empty(), init, f) == init
{
    assert(Seq::<A>::empty().len() == 0);
}

// ----------------------------------------------------------------------------
// Derived operations from foldable
// ----------------------------------------------------------------------------

// sum via foldr
pub open spec fn sum_foldr(xs: Seq<nat>) -> nat {
    foldr(xs, 0nat, |a: nat, acc: nat| (a + acc) as nat)
}

// sum via foldl
pub open spec fn sum_foldl(xs: Seq<nat>) -> nat {
    foldl(xs, 0nat, |acc: nat, a: nat| (acc + a) as nat)
}

// product via foldr
pub open spec fn product_foldr(xs: Seq<nat>) -> nat {
    foldr(xs, 1nat, |a: nat, acc: nat| a * acc)
}

// length via foldr
pub open spec fn length_foldr<A>(xs: Seq<A>) -> nat {
    foldr(xs, 0nat, |_a: A, acc: nat| (acc + 1) as nat)
}

pub proof fn length_foldr_correct<A>(xs: Seq<A>)
    ensures length_foldr(xs) == xs.len()
    decreases xs.len()
{
    if xs.len() == 0 {
        assert(length_foldr(xs) == 0);
    } else {
        length_foldr_correct(xs.skip(1));
        assert(length_foldr(xs) == 1 + length_foldr(xs.skip(1)));
        assert(xs.skip(1).len() == xs.len() - 1);
    }
}

// any: check if any element satisfies predicate
pub open spec fn any_foldr<A>(xs: Seq<A>, p: spec_fn(A) -> bool) -> bool {
    foldr(xs, false, |a: A, acc: bool| p(a) || acc)
}

// all: check if all elements satisfy predicate
pub open spec fn all_foldr<A>(xs: Seq<A>, p: spec_fn(A) -> bool) -> bool {
    foldr(xs, true, |a: A, acc: bool| p(a) && acc)
}

pub proof fn any_foldr_correct<A>(xs: Seq<A>, p: spec_fn(A) -> bool)
    ensures any_foldr(xs, p) <==> exists|i: int| 0 <= i < xs.len() as int && p(xs[i])
    decreases xs.len()
{
    if xs.len() == 0 {
        assert(!any_foldr(xs, p));
    } else {
        any_foldr_correct(xs.skip(1), p);
        assert(any_foldr(xs, p) == (p(xs[0]) || any_foldr(xs.skip(1), p)));

        if p(xs[0]) {
            assert(p(xs[0]));
        }

        assert forall|i: int| 0 <= i < xs.len() as int && p(xs[i])
            implies any_foldr(xs, p) by {
            if i == 0 {
                assert(p(xs[0]));
            } else {
                assert(0 <= i - 1 < xs.skip(1).len() as int);
                assert(xs.skip(1)[i - 1] == xs[i]);
                assert(p(xs.skip(1)[i - 1]));
            }
        };
    }
}

pub proof fn all_foldr_correct<A>(xs: Seq<A>, p: spec_fn(A) -> bool)
    ensures all_foldr(xs, p) <==> forall|i: int| 0 <= i < xs.len() as int ==> p(xs[i])
    decreases xs.len()
{
    if xs.len() == 0 {
        assert(all_foldr(xs, p));
    } else {
        all_foldr_correct(xs.skip(1), p);
        assert(all_foldr(xs, p) == (p(xs[0]) && all_foldr(xs.skip(1), p)));

        // Forward direction: all_foldr(xs, p) ==> forall|i| ...
        if all_foldr(xs, p) {
            assert(p(xs[0]));
            assert(all_foldr(xs.skip(1), p));
            assert forall|i: int| 0 <= i < xs.len() as int implies p(xs[i]) by {
                if i == 0 {
                    assert(p(xs[0]));
                } else {
                    assert(0 <= i - 1 < xs.skip(1).len() as int);
                    assert(xs.skip(1)[i - 1] == xs[i]);
                }
            };
        }

        // Backward direction: (forall|i| ...) ==> all_foldr(xs, p)
        if forall|i: int| 0 <= i < xs.len() as int ==> p(xs[i]) {
            assert(p(xs[0]));
            assert forall|j: int| 0 <= j < xs.skip(1).len() as int implies p(xs.skip(1)[j]) by {
                assert(xs.skip(1)[j] == xs[j + 1]);
                assert(p(xs[j + 1]));
            };
        }
    }
}

// elem: check membership
pub open spec fn elem_foldr<A>(xs: Seq<A>, x: A) -> bool {
    any_foldr(xs, |a: A| a == x)
}

// maximum (for non-empty sequences)
pub open spec fn maximum_foldr(xs: Seq<nat>) -> nat
    recommends xs.len() > 0
{
    if xs.len() == 0 {
        0  // Fallback
    } else {
        foldr(xs.skip(1), xs[0], |a: nat, acc: nat| if a > acc { a } else { acc })
    }
}

// minimum
pub open spec fn minimum_foldr(xs: Seq<nat>) -> nat
    recommends xs.len() > 0
{
    if xs.len() == 0 {
        0  // Fallback
    } else {
        foldr(xs.skip(1), xs[0], |a: nat, acc: nat| if a < acc { a } else { acc })
    }
}

// ----------------------------------------------------------------------------
// Foldable for Option
// ----------------------------------------------------------------------------

pub open spec fn foldr_option<A, B>(o: Option<A>, init: B, f: spec_fn(A, B) -> B) -> B {
    match o {
        Option::None => init,
        Option::Some(a) => f(a, init),
    }
}

pub open spec fn foldl_option<A, B>(o: Option<A>, init: B, f: spec_fn(B, A) -> B) -> B {
    match o {
        Option::None => init,
        Option::Some(a) => f(init, a),
    }
}

pub proof fn foldr_option_none<A, B>(init: B, f: spec_fn(A, B) -> B)
    ensures foldr_option(Option::<A>::None, init, f) == init
{
    // Trivially true
}

pub proof fn foldr_option_some<A, B>(a: A, init: B, f: spec_fn(A, B) -> B)
    ensures foldr_option(Option::Some(a), init, f) == f(a, init)
{
    // Trivially true
}

// ----------------------------------------------------------------------------
// Foldable for pairs (fold over second component)
// ----------------------------------------------------------------------------

pub open spec fn foldr_pair<M, A, B>(p: (M, A), init: B, f: spec_fn(A, B) -> B) -> B {
    f(p.1, init)
}

// ----------------------------------------------------------------------------
// fold fusion law
// ----------------------------------------------------------------------------

// If h is a homomorphism: h(f(a, b)) = g(a, h(b))
// Then: h(foldr(xs, init, f)) = foldr(xs, h(init), g)
pub proof fn fold_fusion<A, B, C>(
    xs: Seq<A>,
    init: B,
    f: spec_fn(A, B) -> B,
    g: spec_fn(A, C) -> C,
    h: spec_fn(B) -> C
)
    requires forall|a: A, b: B| #[trigger] h(f(a, b)) == g(a, h(b))
    ensures h(foldr(xs, init, f)) == foldr(xs, h(init), g)
    decreases xs.len()
{
    if xs.len() == 0 {
        assert(foldr(xs, init, f) == init);
        assert(foldr(xs, h(init), g) == h(init));
    } else {
        fold_fusion(xs.skip(1), init, f, g, h);
        assert(h(foldr(xs.skip(1), init, f)) == foldr(xs.skip(1), h(init), g));

        assert(foldr(xs, init, f) == f(xs[0], foldr(xs.skip(1), init, f)));
        assert(h(foldr(xs, init, f)) == h(f(xs[0], foldr(xs.skip(1), init, f))));
        assert(h(f(xs[0], foldr(xs.skip(1), init, f))) == g(xs[0], h(foldr(xs.skip(1), init, f))));
        assert(g(xs[0], h(foldr(xs.skip(1), init, f))) == g(xs[0], foldr(xs.skip(1), h(init), g)));
        assert(foldr(xs, h(init), g) == g(xs[0], foldr(xs.skip(1), h(init), g)));
    }
}

// ----------------------------------------------------------------------------
// Monoid folding
// ----------------------------------------------------------------------------

// fold with a monoid (identity and associative operation)
pub open spec fn fold_monoid_nat_add(xs: Seq<nat>) -> nat {
    foldr(xs, 0nat, |a: nat, acc: nat| (a + acc) as nat)
}

pub open spec fn fold_monoid_nat_mul(xs: Seq<nat>) -> nat {
    foldr(xs, 1nat, |a: nat, acc: nat| a * acc)
}

// concat: fold with sequence concatenation monoid
pub open spec fn concat_foldr<A>(xss: Seq<Seq<A>>) -> Seq<A>
    decreases xss.len()
{
    foldr(xss, Seq::empty(), |xs: Seq<A>, acc: Seq<A>| xs.add(acc))
}

pub proof fn concat_foldr_empty<A>()
    ensures concat_foldr(Seq::<Seq<A>>::empty()) =~= Seq::<A>::empty()
{
    assert(concat_foldr(Seq::<Seq<A>>::empty()) == Seq::<A>::empty());
}

// ----------------------------------------------------------------------------
// Example and verification
// ----------------------------------------------------------------------------

pub proof fn example_foldable()
{
    let xs: Seq<nat> = seq![1nat, 2, 3, 4, 5];

    // Basic foldr/foldl
    foldr_empty::<nat, nat>(0nat, |a: nat, acc: nat| (a + acc) as nat);
    foldl_empty::<nat, nat>(0nat, |acc: nat, a: nat| (acc + a) as nat);

    // Length
    length_foldr_correct(xs);

    // Any/All
    any_foldr_correct(xs, |n: nat| n > 3);
    all_foldr_correct(xs, |n: nat| n > 0);

    // Option foldable
    foldr_option_none::<nat, nat>(0nat, |a: nat, acc: nat| (a + acc) as nat);
    foldr_option_some(5nat, 10nat, |a: nat, acc: nat| (a + acc) as nat);

    // Concat
    concat_foldr_empty::<nat>();
}

pub proof fn foldable_verify()
{
    example_foldable();
}

pub fn main()
{
    proof {
        foldable_verify();
    }
}

} // verus!

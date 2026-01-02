use vstd::prelude::*;

verus! {

// ============================================================================
// QC Typeclass: Traversable
// ============================================================================
// Models the Traversable typeclass for structures that can be traversed
// while accumulating effects. Combines Functor and Foldable capabilities.

// Core operations:
// - traverse: (A -> F<B>) -> T<A> -> F<T<B>>
// - sequence: T<F<A>> -> F<T<A>>

// Traversable laws:
// 1. Identity: traverse Identity = Identity
// 2. Naturality: t . traverse f = traverse (t . f) for applicative morphism t
// 3. Composition: traverse (Compose . fmap g . f) = Compose . fmap (traverse g) . traverse f

// ----------------------------------------------------------------------------
// Traversable for Seq with Option applicative
// ----------------------------------------------------------------------------

// traverse: apply effectful function to each element, collecting results
pub open spec fn traverse_seq_option<A, B>(
    xs: Seq<A>,
    f: spec_fn(A) -> Option<B>
) -> Option<Seq<B>>
    decreases xs.len()
{
    if xs.len() == 0 {
        Option::Some(Seq::empty())
    } else {
        match (f(xs[0]), traverse_seq_option(xs.skip(1), f)) {
            (Option::Some(b), Option::Some(bs)) => Option::Some(seq![b].add(bs)),
            _ => Option::None,
        }
    }
}

// sequence: flip Seq<Option<A>> to Option<Seq<A>>
pub open spec fn sequence_seq_option<A>(xs: Seq<Option<A>>) -> Option<Seq<A>>
    decreases xs.len()
{
    if xs.len() == 0 {
        Option::Some(Seq::empty())
    } else {
        match (xs[0], sequence_seq_option(xs.skip(1))) {
            (Option::Some(a), Option::Some(rest)) => Option::Some(seq![a].add(rest)),
            _ => Option::None,
        }
    }
}

// Law: sequence is traverse with identity
pub proof fn sequence_is_traverse_id<A>(xs: Seq<Option<A>>)
    ensures sequence_seq_option(xs) == traverse_seq_option(xs, |o: Option<A>| o)
    decreases xs.len()
{
    if xs.len() == 0 {
        assert(sequence_seq_option(xs) == Option::Some(Seq::<A>::empty()));
        assert(traverse_seq_option(xs, |o: Option<A>| o) == Option::Some(Seq::<A>::empty()));
    } else {
        sequence_is_traverse_id(xs.skip(1));
    }
}

// All Some implies Some result
pub proof fn traverse_all_some<A, B>(xs: Seq<A>, f: spec_fn(A) -> Option<B>)
    requires forall|i: int| 0 <= i < xs.len() as int ==> f(xs[i]).is_some()
    ensures traverse_seq_option(xs, f).is_some()
    decreases xs.len()
{
    if xs.len() == 0 {
        // Base case
    } else {
        assert(f(xs[0]).is_some());
        traverse_all_some(xs.skip(1), f);
    }
}

// Any None implies None result
pub proof fn traverse_any_none<A, B>(xs: Seq<A>, f: spec_fn(A) -> Option<B>, k: int)
    requires 0 <= k < xs.len() as int,
             f(xs[k]) == Option::<B>::None
    ensures traverse_seq_option(xs, f) == Option::<Seq<B>>::None
    decreases xs.len()
{
    if xs.len() == 0 {
        // Vacuously true
    } else if k == 0 {
        assert(f(xs[0]) == Option::<B>::None);
    } else {
        traverse_any_none(xs.skip(1), f, k - 1);
    }
}

// Length preservation
pub proof fn traverse_preserves_length<A, B>(xs: Seq<A>, f: spec_fn(A) -> Option<B>, result: Seq<B>)
    requires traverse_seq_option(xs, f) == Option::Some(result)
    ensures result.len() == xs.len()
    decreases xs.len()
{
    if xs.len() == 0 {
        assert(result =~= Seq::empty());
    } else {
        match (f(xs[0]), traverse_seq_option(xs.skip(1), f)) {
            (Option::Some(b), Option::Some(bs)) => {
                traverse_preserves_length(xs.skip(1), f, bs);
                assert(result =~= seq![b].add(bs));
                assert(result.len() == 1 + bs.len());
            }
            _ => {}  // Cannot happen given precondition
        }
    }
}

// ----------------------------------------------------------------------------
// Traversable for Option
// ----------------------------------------------------------------------------

pub open spec fn traverse_option<A, B>(o: Option<A>, f: spec_fn(A) -> Option<B>) -> Option<Option<B>> {
    match o {
        Option::None => Option::Some(Option::None),
        Option::Some(a) => match f(a) {
            Option::None => Option::None,
            Option::Some(b) => Option::Some(Option::Some(b)),
        }
    }
}

pub open spec fn sequence_option<A>(o: Option<Option<A>>) -> Option<Option<A>> {
    match o {
        Option::None => Option::Some(Option::None),
        Option::Some(inner) => match inner {
            Option::None => Option::None,
            Option::Some(a) => Option::Some(Option::Some(a)),
        }
    }
}

pub proof fn traverse_option_none<A, B>(f: spec_fn(A) -> Option<B>)
    ensures traverse_option(Option::<A>::None, f) == Option::Some(Option::<B>::None)
{
    // Trivially true
}

pub proof fn traverse_option_some_some<A, B>(a: A, b: B, f: spec_fn(A) -> Option<B>)
    requires f(a) == Option::Some(b)
    ensures traverse_option(Option::Some(a), f) == Option::Some(Option::Some(b))
{
    // Trivially true
}

// ----------------------------------------------------------------------------
// Traversable for pairs (traverse over second component)
// ----------------------------------------------------------------------------

pub open spec fn traverse_pair<M, A, B>(
    p: (M, A),
    f: spec_fn(A) -> Option<B>
) -> Option<(M, B)> {
    match f(p.1) {
        Option::None => Option::None,
        Option::Some(b) => Option::Some((p.0, b)),
    }
}

pub proof fn traverse_pair_preserves_first<M, A, B>(p: (M, A), f: spec_fn(A) -> Option<B>, b: B)
    requires f(p.1) == Option::Some(b)
    ensures traverse_pair(p, f) == Option::Some((p.0, b))
{
    // Trivially true
}

// ----------------------------------------------------------------------------
// mapM-style operations (traverse specialized)
// ----------------------------------------------------------------------------

// mapM for sequences with Option
pub open spec fn map_m_option<A, B>(xs: Seq<A>, f: spec_fn(A) -> Option<B>) -> Option<Seq<B>> {
    traverse_seq_option(xs, f)
}

// forM (mapM with arguments flipped)
pub open spec fn for_m_option<A, B>(xs: Seq<A>, f: spec_fn(A) -> Option<B>) -> Option<Seq<B>> {
    map_m_option(xs, f)
}

// filterM: filter with effectful predicate
pub open spec fn filter_m_option<A>(xs: Seq<A>, p: spec_fn(A) -> Option<bool>) -> Option<Seq<A>>
    decreases xs.len()
{
    if xs.len() == 0 {
        Option::Some(Seq::empty())
    } else {
        match (p(xs[0]), filter_m_option(xs.skip(1), p)) {
            (Option::Some(keep), Option::Some(rest)) => {
                if keep {
                    Option::Some(seq![xs[0]].add(rest))
                } else {
                    Option::Some(rest)
                }
            }
            _ => Option::None,
        }
    }
}

pub proof fn filter_m_all_some<A>(xs: Seq<A>, p: spec_fn(A) -> Option<bool>)
    requires forall|i: int| 0 <= i < xs.len() as int ==> p(xs[i]).is_some()
    ensures filter_m_option(xs, p).is_some()
    decreases xs.len()
{
    if xs.len() == 0 {
        // Base case
    } else {
        filter_m_all_some(xs.skip(1), p);
    }
}

// ----------------------------------------------------------------------------
// Zip with effects
// ----------------------------------------------------------------------------

pub open spec fn zip_with_m_option<A, B, C>(
    xs: Seq<A>,
    ys: Seq<B>,
    f: spec_fn(A, B) -> Option<C>
) -> Option<Seq<C>>
    decreases xs.len()
{
    if xs.len() == 0 || ys.len() == 0 {
        Option::Some(Seq::empty())
    } else {
        match (f(xs[0], ys[0]), zip_with_m_option(xs.skip(1), ys.skip(1), f)) {
            (Option::Some(c), Option::Some(cs)) => Option::Some(seq![c].add(cs)),
            _ => Option::None,
        }
    }
}

pub proof fn zip_with_m_length<A, B, C>(
    xs: Seq<A>,
    ys: Seq<B>,
    f: spec_fn(A, B) -> Option<C>,
    result: Seq<C>
)
    requires zip_with_m_option(xs, ys, f) == Option::Some(result)
    ensures result.len() == if xs.len() < ys.len() { xs.len() } else { ys.len() }
    decreases xs.len()
{
    if xs.len() == 0 || ys.len() == 0 {
        assert(result =~= Seq::empty());
    } else {
        match (f(xs[0], ys[0]), zip_with_m_option(xs.skip(1), ys.skip(1), f)) {
            (Option::Some(c), Option::Some(cs)) => {
                zip_with_m_length(xs.skip(1), ys.skip(1), f, cs);
            }
            _ => {}
        }
    }
}

// ----------------------------------------------------------------------------
// Indexed traversal
// ----------------------------------------------------------------------------

// traverseWithIndex: traverse with index information
pub open spec fn traverse_with_index<A, B>(
    xs: Seq<A>,
    f: spec_fn(nat, A) -> Option<B>
) -> Option<Seq<B>>
    decreases xs.len()
{
    traverse_with_index_helper(xs, f, 0)
}

pub open spec fn traverse_with_index_helper<A, B>(
    xs: Seq<A>,
    f: spec_fn(nat, A) -> Option<B>,
    start_idx: nat
) -> Option<Seq<B>>
    decreases xs.len()
{
    if xs.len() == 0 {
        Option::Some(Seq::empty())
    } else {
        match (f(start_idx, xs[0]), traverse_with_index_helper(xs.skip(1), f, start_idx + 1)) {
            (Option::Some(b), Option::Some(bs)) => Option::Some(seq![b].add(bs)),
            _ => Option::None,
        }
    }
}

// ----------------------------------------------------------------------------
// Traversable composition
// ----------------------------------------------------------------------------

// Traversing nested structures
pub open spec fn sequence_nested<A>(xss: Seq<Seq<Option<A>>>) -> Option<Seq<Seq<A>>>
    decreases xss.len()
{
    if xss.len() == 0 {
        Option::Some(Seq::empty())
    } else {
        match (sequence_seq_option(xss[0]), sequence_nested(xss.skip(1))) {
            (Option::Some(xs), Option::Some(rest)) => Option::Some(seq![xs].add(rest)),
            _ => Option::None,
        }
    }
}

// ----------------------------------------------------------------------------
// Example and verification
// ----------------------------------------------------------------------------

pub proof fn example_traversable()
{
    // Seq traverse
    let xs: Seq<nat> = seq![1nat, 2, 3];
    let f = |n: nat| if n > 0 { Option::Some(n * 2) } else { Option::<nat>::None };

    traverse_all_some(xs, f);

    // Sequence is traverse id
    let opts: Seq<Option<nat>> = seq![Option::Some(1nat), Option::Some(2nat)];
    sequence_is_traverse_id(opts);

    // Option traverse
    traverse_option_none::<nat, nat>(f);

    // filterM
    let p = |n: nat| Option::Some(n % 2 == 0);
    filter_m_all_some(xs, p);
}

pub proof fn traversable_verify()
{
    example_traversable();
}

pub fn main()
{
    proof {
        traversable_verify();
    }
}

} // verus!

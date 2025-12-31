use vstd::prelude::*;

verus! {

// ============================================================================
// QC: Functor Typeclass (qc-current/Typeclasses)
// Mappable containers
// ============================================================================

// Functor: containers that support mapping a function over their contents

// ----------------------------------------------------------------------------
// Functor for Option
// ----------------------------------------------------------------------------

pub open spec fn option_fmap<A, B>(f: spec_fn(A) -> B, m: Option<A>) -> Option<B> {
    match m {
        None => None,
        Some(a) => Some(f(a)),
    }
}

// ----------------------------------------------------------------------------
// Functor for Seq (List)
// ----------------------------------------------------------------------------

pub open spec fn seq_fmap<A, B>(f: spec_fn(A) -> B, s: Seq<A>) -> Seq<B> {
    Seq::new(s.len(), |i: int| f(s[i]))
}

// ----------------------------------------------------------------------------
// Functor Laws
// ----------------------------------------------------------------------------

// Identity: fmap id == id
pub proof fn option_fmap_identity<A>(m: Option<A>)
    ensures option_fmap(|x: A| x, m) == m
{
}

// Composition: fmap (f . g) == fmap f . fmap g
pub proof fn option_fmap_composition<A, B, C>(
    f: spec_fn(B) -> C,
    g: spec_fn(A) -> B,
    m: Option<A>
)
    ensures option_fmap(|x: A| f(g(x)), m) == option_fmap(f, option_fmap(g, m))
{
}

pub proof fn seq_fmap_identity(s: Seq<nat>)
    ensures seq_fmap(|x: nat| x, s) =~= s
{
    assert forall|i: int| 0 <= i < s.len() implies seq_fmap(|x: nat| x, s)[i] == s[i] by {}
}

pub proof fn seq_fmap_length<A, B>(f: spec_fn(A) -> B, s: Seq<A>)
    ensures seq_fmap(f, s).len() == s.len()
{
}

// ----------------------------------------------------------------------------
// Functor Utilities
// ----------------------------------------------------------------------------

// void: replace contents with unit
pub open spec fn option_void<A>(m: Option<A>) -> Option<()> {
    option_fmap(|_x: A| (), m)
}

// <$ : replace contents with constant
pub open spec fn option_replace<A, B>(b: B, m: Option<A>) -> Option<B> {
    option_fmap(|_x: A| b, m)
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_option_fmap()
{
    let x: Option<nat> = Some(5);
    let y = option_fmap(|n: nat| n * 2, x);
    assert(y == Some(10nat));

    let z: Option<nat> = None;
    let w = option_fmap(|n: nat| n * 2, z);
    assert(w.is_none());
}

pub proof fn example_seq_fmap()
{
    let s = seq![1nat, 2, 3];
    let t = seq_fmap(|x: nat| x + 10, s);
    assert(t[0] == 11);
    assert(t[1] == 12);
    assert(t[2] == 13);
}

pub proof fn typeclass_functor_verify()
{
    example_option_fmap();
    example_seq_fmap();
    option_fmap_identity(Some(42nat));
    seq_fmap_identity(seq![1nat, 2, 3]);
}

pub fn main() {
    proof { typeclass_functor_verify(); }
}

} // verus!

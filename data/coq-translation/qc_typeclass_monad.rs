use vstd::prelude::*;

verus! {

// ============================================================================
// QC: Monad Typeclass (qc-current/Typeclasses)
// Monadic computations - foundation for generators
// ============================================================================

// ----------------------------------------------------------------------------
// Option Monad
// ----------------------------------------------------------------------------

pub open spec fn option_return<A>(a: A) -> Option<A> {
    Some(a)
}

pub open spec fn option_bind<A, B>(m: Option<A>, f: spec_fn(A) -> Option<B>) -> Option<B> {
    match m {
        None => None,
        Some(a) => f(a),
    }
}

pub open spec fn option_map<A, B>(m: Option<A>, f: spec_fn(A) -> B) -> Option<B> {
    option_bind(m, |a: A| option_return(f(a)))
}

pub open spec fn option_join<A>(m: Option<Option<A>>) -> Option<A> {
    option_bind(m, |x: Option<A>| x)
}

// ----------------------------------------------------------------------------
// Sequence/List Monad
// ----------------------------------------------------------------------------

pub open spec fn seq_return<A>(a: A) -> Seq<A> {
    seq![a]
}

pub open spec fn seq_bind_helper<A, B>(s: Seq<A>, f: spec_fn(A) -> Seq<B>, idx: int) -> Seq<B>
    decreases s.len() - idx
{
    if idx >= s.len() {
        Seq::empty()
    } else {
        f(s[idx]) + seq_bind_helper(s, f, idx + 1)
    }
}

pub open spec fn seq_bind<A, B>(s: Seq<A>, f: spec_fn(A) -> Seq<B>) -> Seq<B> {
    seq_bind_helper(s, f, 0)
}

pub open spec fn seq_map<A, B>(s: Seq<A>, f: spec_fn(A) -> B) -> Seq<B> {
    Seq::new(s.len(), |i: int| f(s[i]))
}

// ----------------------------------------------------------------------------
// Monad Laws
// ----------------------------------------------------------------------------

// Left identity: return a >>= f == f a
pub proof fn option_left_identity<A, B>(a: A, f: spec_fn(A) -> Option<B>)
    ensures option_bind(option_return(a), f) == f(a)
{
}

// Right identity: m >>= return == m
pub proof fn option_right_identity<A>(m: Option<A>)
    ensures option_bind(m, |x: A| option_return(x)) == m
{
}

// Associativity: (m >>= f) >>= g == m >>= (\x -> f x >>= g)
pub proof fn option_associativity<A, B, C>(
    m: Option<A>,
    f: spec_fn(A) -> Option<B>,
    g: spec_fn(B) -> Option<C>
)
    ensures option_bind(option_bind(m, f), g) ==
            option_bind(m, |x: A| option_bind(f(x), g))
{
}

// ----------------------------------------------------------------------------
// Monad Combinators
// ----------------------------------------------------------------------------

// sequence: convert Seq<Option<A>> to Option<Seq<A>>
pub open spec fn option_sequence_helper(s: Seq<Option<nat>>, idx: int, acc: Seq<nat>) -> Option<Seq<nat>>
    decreases s.len() - idx
{
    if idx >= s.len() {
        Some(acc)
    } else {
        match s[idx] {
            None => None,
            Some(x) => option_sequence_helper(s, idx + 1, acc.push(x)),
        }
    }
}

pub open spec fn option_sequence(s: Seq<Option<nat>>) -> Option<Seq<nat>> {
    option_sequence_helper(s, 0, Seq::empty())
}

// mapM: map with monadic function
pub open spec fn option_map_m_helper(s: Seq<nat>, f: spec_fn(nat) -> Option<nat>, idx: int, acc: Seq<nat>) -> Option<Seq<nat>>
    decreases s.len() - idx
{
    if idx >= s.len() {
        Some(acc)
    } else {
        match f(s[idx]) {
            None => None,
            Some(y) => option_map_m_helper(s, f, idx + 1, acc.push(y)),
        }
    }
}

pub open spec fn option_map_m(s: Seq<nat>, f: spec_fn(nat) -> Option<nat>) -> Option<Seq<nat>> {
    option_map_m_helper(s, f, 0, Seq::empty())
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_option_monad()
{
    let x: Option<nat> = Some(5);
    let y = option_bind(x, |n: nat| Some(n + 1));
    assert(y == Some(6nat));

    let z: Option<nat> = None;
    let w = option_bind(z, |n: nat| Some(n + 1));
    assert(w.is_none());
}

pub proof fn example_option_map()
{
    let x: Option<nat> = Some(10);
    let y = option_map(x, |n: nat| n * 2);
    assert(y == Some(20nat));
}

pub proof fn example_seq_monad()
{
    reveal_with_fuel(seq_bind_helper, 3);
    let s = seq![1nat, 2];
    let result = seq_bind(s, |x: nat| seq![x, x + 10]);
    // result should be [1, 11, 2, 12]
    assert(result.len() == 4);
}

pub proof fn typeclass_monad_verify()
{
    example_option_monad();
    example_option_map();
    example_seq_monad();

    // Test monad laws
    option_left_identity(42nat, |x: nat| Some(x + 1));
    option_right_identity(Some(42nat));
}

pub fn main() {
    proof { typeclass_monad_verify(); }
}

} // verus!

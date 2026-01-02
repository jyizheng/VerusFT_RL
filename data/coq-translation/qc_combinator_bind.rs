use vstd::prelude::*;

verus! {

// ============================================================================
// QC Combinator: Bind (Monadic Composition)
// ============================================================================

pub open spec fn gen_bind<A, B>(gen_a: Set<A>, f: spec_fn(A) -> Set<B>) -> Set<B> {
    Set::new(|b: B| exists|a: A| gen_a.contains(a) && f(a).contains(b))
}

pub open spec fn gen_return<A>(a: A) -> Set<A> {
    Set::new(|x: A| x == a)
}

// Left identity: return a >>= f == f a
pub proof fn bind_left_identity<A, B>(a: A, f: spec_fn(A) -> Set<B>, b: B)
    requires f(a).contains(b)
    ensures gen_bind(gen_return(a), f).contains(b)
{
    // Witness that a is in gen_return(a) and f(a) contains b
    assert(gen_return(a).contains(a));
    assert(f(a).contains(b));
}

// Right identity: m >>= return == m
pub proof fn bind_right_identity<A>(gen: Set<A>, a: A)
    requires gen.contains(a)
    ensures gen_bind(gen, |x: A| gen_return(x)).contains(a)
{
}

pub proof fn combinator_bind_verify()
{
    let gen_nat: Set<nat> = Set::new(|n: nat| n <= 10);
    bind_right_identity(gen_nat, 5nat);
}

pub fn main() {
    proof { combinator_bind_verify(); }
}

} // verus!

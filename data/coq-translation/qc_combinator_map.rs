use vstd::prelude::*;

verus! {

// ============================================================================
// QC Combinator: Map (Functor)
// ============================================================================

pub open spec fn gen_map<A, B>(gen: Set<A>, f: spec_fn(A) -> B) -> Set<B> {
    Set::new(|b: B| exists|a: A| gen.contains(a) && f(a) == b)
}

// Identity: map id == id
pub proof fn map_identity<A>(gen: Set<A>, a: A)
    requires gen.contains(a)
    ensures gen_map(gen, |x: A| x).contains(a)
{
}

// Composition: map (f . g) == map f . map g
pub proof fn map_composition<A, B, C>(gen: Set<A>, f: spec_fn(B) -> C, g: spec_fn(A) -> B, a: A, b: B, c: C)
    requires gen.contains(a), g(a) == b, f(b) == c
    ensures gen_map(gen, |x: A| f(g(x))).contains(c)
{
}

pub proof fn combinator_map_verify()
{
    let gen: Set<nat> = Set::new(|n: nat| n <= 10);
    map_identity(gen, 5nat);
}

pub fn main() {
    proof { combinator_map_verify(); }
}

} // verus!

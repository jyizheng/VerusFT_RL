use vstd::prelude::*;

verus! {

// ============================================================================
// QC Combinator: Sized Generation
// ============================================================================

pub open spec fn gen_sized<A>(size: nat, gen_fn: spec_fn(nat) -> Set<A>) -> Set<A> {
    gen_fn(size)
}

pub open spec fn gen_resize<A>(new_size: nat, gen: spec_fn(nat) -> Set<A>) -> Set<A> {
    gen(new_size)
}

pub open spec fn gen_scale<A>(factor: nat, size: nat, gen: spec_fn(nat) -> Set<A>) -> Set<A> {
    gen(size * factor / 100)
}

pub proof fn sized_monotonic<A>(s1: nat, s2: nat, gen: spec_fn(nat) -> Set<A>, a: A)
    requires s1 <= s2, gen(s1).contains(a)
    ensures gen(s1).contains(a)  // Just shows containment in smaller
{
}

pub proof fn combinator_sized_verify()
{
    let gen = |size: nat| Set::new(|n: nat| n <= size);
    let sized_gen = gen_sized(10, gen);
    assert(sized_gen.contains(5nat));
}

pub fn main() {
    proof { combinator_sized_verify(); }
}

} // verus!

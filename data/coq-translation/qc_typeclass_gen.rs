use vstd::prelude::*;

verus! {

// ============================================================================
// QC Typeclass: Gen (Generator)
// ============================================================================
// Models the QuickCheck Gen typeclass for generating random test values.
// In a spec context, we model generators as functions from a seed/size to values.

// A generator is modeled as a spec function from (seed, size) to a value.
// The seed provides randomness, the size controls the "complexity" of generated values.

// ----------------------------------------------------------------------------
// Generator type (modeled as spec function)
// ----------------------------------------------------------------------------

// Gen<A> is conceptually: spec_fn(nat, nat) -> A
// where first nat is seed, second is size parameter

// ----------------------------------------------------------------------------
// Gen for basic types
// ----------------------------------------------------------------------------

// Generate a nat in range [0, size)
pub open spec fn gen_nat(seed: nat, size: nat) -> nat {
    if size == 0 {
        0
    } else {
        seed % size
    }
}

// Generate a bool (based on seed parity)
pub open spec fn gen_bool(seed: nat) -> bool {
    seed % 2 == 0
}

// Generate an int in range [-size, size]
pub open spec fn gen_int(seed: nat, size: nat) -> int {
    if size == 0 {
        0
    } else {
        let raw = (seed % (2 * size + 1)) as int;
        raw - size as int
    }
}

// ----------------------------------------------------------------------------
// Generator combinators
// ----------------------------------------------------------------------------

// pure: lift a value into a generator (constant generator)
pub open spec fn gen_pure<A>(a: A, _seed: nat, _size: nat) -> A {
    a
}

// map: transform generated values
pub open spec fn gen_map<A, B>(
    gen_a: spec_fn(nat, nat) -> A,
    f: spec_fn(A) -> B,
    seed: nat,
    size: nat
) -> B {
    f(gen_a(seed, size))
}

// bind: sequence generators (monadic bind)
pub open spec fn gen_bind<A, B>(
    gen_a: spec_fn(nat, nat) -> A,
    f: spec_fn(A) -> spec_fn(nat, nat) -> B,
    seed: nat,
    size: nat
) -> B {
    let a = gen_a(seed, size);
    let next_seed = seed + 1;  // Simple seed advancement
    f(a)(next_seed, size)
}

// ----------------------------------------------------------------------------
// Gen for compound types
// ----------------------------------------------------------------------------

// Generate Option<nat>
pub open spec fn gen_option_nat(seed: nat, size: nat) -> Option<nat> {
    if seed % 3 == 0 {
        Option::None
    } else {
        Option::Some(gen_nat(seed / 3, size))
    }
}

// Generate a pair (nat, nat)
pub open spec fn gen_pair_nat(seed: nat, size: nat) -> (nat, nat) {
    let seed1 = seed;
    let seed2 = seed + 1;  // Different seed for second component
    (gen_nat(seed1, size), gen_nat(seed2, size))
}

// Generate a sequence of nats with given length
pub open spec fn gen_seq_nat(seed: nat, size: nat, len: nat) -> Seq<nat>
    decreases len
{
    if len == 0 {
        Seq::empty()
    } else {
        let elem = gen_nat(seed, size);
        seq![elem].add(gen_seq_nat(seed + 1, size, (len - 1) as nat))
    }
}

// ----------------------------------------------------------------------------
// Size control combinators
// ----------------------------------------------------------------------------

// resize: run generator with a different size
pub open spec fn gen_resize<A>(
    gen_a: spec_fn(nat, nat) -> A,
    new_size: nat,
    seed: nat,
    _size: nat
) -> A {
    gen_a(seed, new_size)
}

// scale: multiply size by a factor
pub open spec fn gen_scale<A>(
    gen_a: spec_fn(nat, nat) -> A,
    factor: nat,
    seed: nat,
    size: nat
) -> A {
    gen_a(seed, size * factor)
}

// ----------------------------------------------------------------------------
// Choice combinators
// ----------------------------------------------------------------------------

// one_of: choose from multiple generators based on seed
pub open spec fn gen_one_of_2<A>(
    gen1: spec_fn(nat, nat) -> A,
    gen2: spec_fn(nat, nat) -> A,
    seed: nat,
    size: nat
) -> A {
    if seed % 2 == 0 {
        gen1(seed / 2, size)
    } else {
        gen2(seed / 2, size)
    }
}

pub open spec fn gen_one_of_3<A>(
    gen1: spec_fn(nat, nat) -> A,
    gen2: spec_fn(nat, nat) -> A,
    gen3: spec_fn(nat, nat) -> A,
    seed: nat,
    size: nat
) -> A {
    let choice = seed % 3;
    if choice == 0 {
        gen1(seed / 3, size)
    } else if choice == 1 {
        gen2(seed / 3, size)
    } else {
        gen3(seed / 3, size)
    }
}

// frequency: weighted choice
// (modeled simply - choose gen1 with weight w1 out of w1+w2)
pub open spec fn gen_frequency_2<A>(
    w1: nat,
    gen1: spec_fn(nat, nat) -> A,
    w2: nat,
    gen2: spec_fn(nat, nat) -> A,
    seed: nat,
    size: nat
) -> A
    recommends w1 + w2 > 0
{
    if w1 + w2 == 0 {
        gen1(seed, size)  // Fallback
    } else if seed % (w1 + w2) < w1 {
        gen1(seed / (w1 + w2), size)
    } else {
        gen2(seed / (w1 + w2), size)
    }
}

// ----------------------------------------------------------------------------
// Generator laws (functor/monad laws in spec form)
// ----------------------------------------------------------------------------

// Functor identity: map id == id
pub proof fn gen_map_identity<A>(gen_a: spec_fn(nat, nat) -> A, seed: nat, size: nat)
    ensures gen_map(gen_a, |a: A| a, seed, size) == gen_a(seed, size)
{
    // Trivially true by definition
}

// Functor composition: map (g . f) == map g . map f
pub proof fn gen_map_composition<A, B, C>(
    gen_a: spec_fn(nat, nat) -> A,
    f: spec_fn(A) -> B,
    g: spec_fn(B) -> C,
    seed: nat,
    size: nat
)
    ensures gen_map(gen_a, |a: A| g(f(a)), seed, size) ==
            gen_map(|s: nat, sz: nat| gen_map(gen_a, f, s, sz), g, seed, size)
{
    // LHS: g(f(gen_a(seed, size)))
    // RHS: g(gen_map(gen_a, f, seed, size)) = g(f(gen_a(seed, size)))
}

// pure law: pure a generates a
pub proof fn gen_pure_law<A>(a: A, seed: nat, size: nat)
    ensures gen_pure(a, seed, size) == a
{
    // Trivially true
}

// ----------------------------------------------------------------------------
// Constrained generation
// ----------------------------------------------------------------------------

// Generate nat satisfying a predicate (by filtering)
// Note: This is a simplified model - real QC uses rejection sampling
pub open spec fn gen_nat_satisfying(
    pred: spec_fn(nat) -> bool,
    seed: nat,
    size: nat,
    attempts: nat
) -> Option<nat>
    decreases attempts
{
    if attempts == 0 {
        Option::None
    } else {
        let candidate = gen_nat(seed, size);
        if pred(candidate) {
            Option::Some(candidate)
        } else {
            gen_nat_satisfying(pred, seed + 1, size, (attempts - 1) as nat)
        }
    }
}

// Generate even nat
pub open spec fn gen_even_nat(seed: nat, size: nat) -> nat {
    let n = gen_nat(seed, size);
    (n - n % 2) as nat  // Round down to even
}

pub proof fn gen_even_nat_is_even(seed: nat, size: nat)
    ensures gen_even_nat(seed, size) % 2 == 0
{
    let n = gen_nat(seed, size);
    let result = n - n % 2;
    assert(result % 2 == 0);
}

// ----------------------------------------------------------------------------
// Sample multiple values
// ----------------------------------------------------------------------------

pub open spec fn gen_sample(size: nat, count: nat) -> Seq<nat>
    decreases count
{
    if count == 0 {
        Seq::empty()
    } else {
        let seed = count;  // Use count as seed for variety
        seq![gen_nat(seed, size)].add(gen_sample(size, (count - 1) as nat))
    }
}

pub proof fn gen_sample_length(size: nat, count: nat)
    ensures gen_sample(size, count).len() == count
    decreases count
{
    if count == 0 {
        assert(gen_sample(size, 0) =~= Seq::empty());
    } else {
        gen_sample_length(size, (count - 1) as nat);
    }
}

// ----------------------------------------------------------------------------
// Properties of generators
// ----------------------------------------------------------------------------

// gen_nat produces values in range
pub proof fn gen_nat_in_range(seed: nat, size: nat)
    requires size > 0
    ensures gen_nat(seed, size) < size
{
    assert(seed % size < size);
}

// gen_int produces values in range
pub proof fn gen_int_in_range(seed: nat, size: nat)
    requires size > 0
    ensures -(size as int) <= gen_int(seed, size) <= size as int
{
    let raw = (seed % (2 * size + 1)) as int;
    assert(0 <= raw < (2 * size + 1) as int);
    let result = raw - size as int;
    assert(-(size as int) <= result);
    assert(result <= size as int);
}

// gen_seq_nat produces sequence of correct length
pub proof fn gen_seq_nat_length(seed: nat, size: nat, len: nat)
    ensures gen_seq_nat(seed, size, len).len() == len
    decreases len
{
    if len == 0 {
        assert(gen_seq_nat(seed, size, 0) =~= Seq::empty());
    } else {
        gen_seq_nat_length(seed + 1, size, (len - 1) as nat);
    }
}

// ----------------------------------------------------------------------------
// Example and verification
// ----------------------------------------------------------------------------

pub proof fn example_gen()
{
    // Basic generation
    gen_nat_in_range(42, 10);
    gen_int_in_range(42, 10);

    // Generator laws
    gen_pure_law(42nat, 0, 10);
    gen_map_identity(|s: nat, sz: nat| gen_nat(s, sz), 0, 10);

    // Even number generation
    gen_even_nat_is_even(42, 100);

    // Sampling
    gen_sample_length(10, 5);

    // Sequence generation
    gen_seq_nat_length(0, 10, 5);
}

pub proof fn gen_verify()
{
    example_gen();
}

pub fn main()
{
    proof {
        gen_verify();
    }
}

} // verus!

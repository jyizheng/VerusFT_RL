use vstd::prelude::*;

verus! {

// ============================================================================
// QC Typeclass: Arbitrary
// ============================================================================
// Combines Gen and Shrink into a single typeclass for property-based testing.
// Arbitrary provides both generation of random values and shrinking of
// counterexamples.

// An Arbitrary instance for type A provides:
// 1. arbitrary: Gen<A> - a generator for random values
// 2. shrink: A -> Seq<A> - produces smaller test cases

// ----------------------------------------------------------------------------
// Arbitrary for nat
// ----------------------------------------------------------------------------

// Generator component
pub open spec fn arbitrary_nat(seed: nat, size: nat) -> nat {
    if size == 0 {
        0
    } else {
        seed % size
    }
}

// Shrink component
pub open spec fn shrink_nat(n: nat) -> Seq<nat> {
    if n == 0 {
        Seq::empty()
    } else {
        let half = (n / 2) as nat;
        if half == 0 {
            seq![0nat]
        } else {
            seq![0nat, half]
        }
    }
}

// Laws for Arbitrary nat
pub proof fn arbitrary_nat_in_range(seed: nat, size: nat)
    requires size > 0
    ensures arbitrary_nat(seed, size) < size
{
    assert(seed % size < size);
}

pub proof fn shrink_nat_smaller(n: nat, i: int)
    requires n > 0,
             0 <= i < shrink_nat(n).len() as int
    ensures shrink_nat(n)[i] < n
{
    let half = (n / 2) as nat;
    if half == 0 {
        assert(shrink_nat(n) =~= seq![0nat]);
        assert(shrink_nat(n)[0] == 0 < n);
    } else {
        if i == 0 {
            assert(shrink_nat(n)[0] == 0 < n);
        } else {
            assert(shrink_nat(n)[1] == half < n);
        }
    }
}

// ----------------------------------------------------------------------------
// Arbitrary for bool
// ----------------------------------------------------------------------------

pub open spec fn arbitrary_bool(seed: nat, _size: nat) -> bool {
    seed % 2 == 0
}

pub open spec fn shrink_bool(b: bool) -> Seq<bool> {
    if b {
        seq![false]
    } else {
        Seq::empty()
    }
}

pub proof fn shrink_bool_law(b: bool, i: int)
    requires 0 <= i < shrink_bool(b).len() as int
    ensures !shrink_bool(b)[i]  // Shrunk values are "smaller" (false < true)
{
    assert(b);  // Only true has shrink candidates
    assert(shrink_bool(true) =~= seq![false]);
    assert(shrink_bool(b)[0] == false);
}

// ----------------------------------------------------------------------------
// Arbitrary for int
// ----------------------------------------------------------------------------

pub open spec fn arbitrary_int(seed: nat, size: nat) -> int {
    if size == 0 {
        0
    } else {
        let raw = (seed % (2 * size + 1)) as int;
        raw - size as int
    }
}

pub open spec fn shrink_int(n: int) -> Seq<int> {
    if n == 0 {
        Seq::empty()
    } else if n > 0 {
        let half = n / 2;
        if half == 0 {
            seq![0int]
        } else {
            seq![0int, half]
        }
    } else {
        let abs_n = -n;
        let half = abs_n / 2;
        if half == 0 {
            seq![0int, abs_n]
        } else {
            seq![0int, -half, abs_n]
        }
    }
}

pub proof fn arbitrary_int_in_range(seed: nat, size: nat)
    requires size > 0
    ensures -(size as int) <= arbitrary_int(seed, size) <= size as int
{
    let raw = (seed % (2 * size + 1)) as int;
    assert(0 <= raw < (2 * size + 1) as int);
    let result = raw - size as int;
    assert(-(size as int) <= result <= size as int);
}

// ----------------------------------------------------------------------------
// Arbitrary for Option<A>
// ----------------------------------------------------------------------------

pub open spec fn arbitrary_option_nat(seed: nat, size: nat) -> Option<nat> {
    if seed % 4 == 0 {
        Option::None
    } else {
        Option::Some(arbitrary_nat(seed / 4, size))
    }
}

pub open spec fn shrink_option_nat(o: Option<nat>) -> Seq<Option<nat>> {
    match o {
        Option::None => Seq::empty(),
        Option::Some(n) => {
            let shrunk_inner = shrink_nat(n);
            Seq::new(shrunk_inner.len() + 1, |i: int|
                if i == 0 {
                    Option::None
                } else {
                    Option::Some(shrunk_inner[i - 1])
                }
            )
        }
    }
}

pub proof fn shrink_option_includes_none(n: nat)
    ensures shrink_option_nat(Option::Some(n)).len() > 0,
            shrink_option_nat(Option::Some(n))[0] == Option::<nat>::None
{
    let result = shrink_option_nat(Option::Some(n));
    assert(result.len() == shrink_nat(n).len() + 1);
    assert(result[0] == Option::<nat>::None);
}

// ----------------------------------------------------------------------------
// Arbitrary for sequences
// ----------------------------------------------------------------------------

pub open spec fn arbitrary_seq_nat(seed: nat, size: nat) -> Seq<nat>
    decreases size
{
    if size == 0 {
        Seq::empty()
    } else {
        let len = seed % (size + 1);
        Seq::new(len, |i: int| arbitrary_nat(seed + i as nat + 1, size))
    }
}

pub open spec fn shrink_seq_nat(xs: Seq<nat>) -> Seq<Seq<nat>> {
    if xs.len() == 0 {
        Seq::empty()
    } else if xs.len() == 1 {
        seq![Seq::empty()]
    } else {
        Seq::new(xs.len(), |i: int| xs.remove(i))
    }
}

pub proof fn arbitrary_seq_bounded_len(seed: nat, size: nat)
    ensures arbitrary_seq_nat(seed, size).len() <= size
{
    if size == 0 {
        assert(arbitrary_seq_nat(seed, 0) =~= Seq::empty());
    } else {
        let len = seed % (size + 1);
        assert(len <= size);
    }
}

pub proof fn shrink_seq_shorter(xs: Seq<nat>, i: int)
    requires xs.len() > 1,
             0 <= i < xs.len() as int
    ensures shrink_seq_nat(xs)[i].len() < xs.len()
{
    assert(shrink_seq_nat(xs)[i] == xs.remove(i));
    assert(xs.remove(i).len() == xs.len() - 1);
}

// ----------------------------------------------------------------------------
// Arbitrary for pairs
// ----------------------------------------------------------------------------

pub open spec fn arbitrary_pair_nat(seed: nat, size: nat) -> (nat, nat) {
    (arbitrary_nat(seed, size), arbitrary_nat(seed + 1, size))
}

pub open spec fn shrink_pair_nat(p: (nat, nat)) -> Seq<(nat, nat)> {
    let (a, b) = p;
    let shrink_a = shrink_nat(a);
    let shrink_b = shrink_nat(b);

    let first_shrinks = Seq::new(shrink_a.len(), |i: int| (shrink_a[i], b));
    let second_shrinks = Seq::new(shrink_b.len(), |i: int| (a, shrink_b[i]));

    first_shrinks.add(second_shrinks)
}

pub proof fn arbitrary_pair_in_range(seed: nat, size: nat)
    requires size > 0
    ensures arbitrary_pair_nat(seed, size).0 < size,
            arbitrary_pair_nat(seed, size).1 < size
{
    arbitrary_nat_in_range(seed, size);
    arbitrary_nat_in_range(seed + 1, size);
}

// ----------------------------------------------------------------------------
// Arbitrary combinators
// ----------------------------------------------------------------------------

// lift arbitrary through a function
pub open spec fn arbitrary_map<A, B>(
    arb_a: spec_fn(nat, nat) -> A,
    f: spec_fn(A) -> B,
    seed: nat,
    size: nat
) -> B {
    f(arb_a(seed, size))
}

// Two generators combined
pub open spec fn arbitrary_both<A, B>(
    arb_a: spec_fn(nat, nat) -> A,
    arb_b: spec_fn(nat, nat) -> B,
    seed: nat,
    size: nat
) -> (A, B) {
    (arb_a(seed, size), arb_b(seed + 1, size))
}

// Choose between two arbitrary instances
pub open spec fn arbitrary_one_of<A>(
    arb1: spec_fn(nat, nat) -> A,
    arb2: spec_fn(nat, nat) -> A,
    seed: nat,
    size: nat
) -> A {
    if seed % 2 == 0 {
        arb1(seed / 2, size)
    } else {
        arb2(seed / 2, size)
    }
}

// ----------------------------------------------------------------------------
// Recursive shrinking (for finding minimal counterexamples)
// ----------------------------------------------------------------------------

// Shrink until fixed point or max iterations
pub open spec fn shrink_nat_until_minimal(n: nat, max_iter: nat) -> nat
    decreases max_iter
{
    if max_iter == 0 {
        n
    } else if n == 0 {
        0
    } else {
        let shrunk = shrink_nat(n);
        if shrunk.len() == 0 {
            n
        } else {
            shrink_nat_until_minimal(shrunk[0], (max_iter - 1) as nat)
        }
    }
}

pub proof fn shrink_nat_until_minimal_result(n: nat, max_iter: nat)
    ensures shrink_nat_until_minimal(n, max_iter) <= n
    decreases max_iter
{
    if max_iter == 0 || n == 0 {
        // Base cases
    } else {
        let shrunk = shrink_nat(n);
        if shrunk.len() == 0 {
            // n doesn't shrink
        } else {
            shrink_nat_smaller(n, 0);
            assert(shrunk[0] < n);
            shrink_nat_until_minimal_result(shrunk[0], (max_iter - 1) as nat);
        }
    }
}

// ----------------------------------------------------------------------------
// Property testing model
// ----------------------------------------------------------------------------

// A property is a spec function from A to bool
// forAll runs arbitrary and checks property
pub open spec fn for_all_nat(
    prop: spec_fn(nat) -> bool,
    seed: nat,
    size: nat,
    num_tests: nat
) -> bool
    decreases num_tests
{
    if num_tests == 0 {
        true
    } else {
        let val = arbitrary_nat(seed, size);
        if !prop(val) {
            false
        } else {
            for_all_nat(prop, seed + 1, size, (num_tests - 1) as nat)
        }
    }
}

// Soundness lemma for for_all_nat (single test)
pub proof fn for_all_nat_soundness_single(
    prop: spec_fn(nat) -> bool,
    seed: nat,
    size: nat,
    num_tests: nat
)
    requires for_all_nat(prop, seed, size, num_tests),
             num_tests > 0
    ensures prop(arbitrary_nat(seed, size))
{
    // When for_all_nat returns true with num_tests > 0,
    // it means prop(arbitrary_nat(seed, size)) is true
}

// ----------------------------------------------------------------------------
// Example and verification
// ----------------------------------------------------------------------------

pub proof fn example_arbitrary()
{
    // Nat arbitrary
    arbitrary_nat_in_range(42, 10);
    shrink_nat_smaller(10, 0);

    // Bool arbitrary
    shrink_bool_law(true, 0);

    // Int arbitrary
    arbitrary_int_in_range(42, 10);

    // Option arbitrary
    shrink_option_includes_none(5);

    // Seq arbitrary
    arbitrary_seq_bounded_len(42, 10);
    shrink_seq_shorter(seq![1nat, 2, 3], 1);

    // Pair arbitrary
    arbitrary_pair_in_range(42, 10);

    // Recursive shrinking
    shrink_nat_until_minimal_result(100, 10);
}

pub proof fn arbitrary_verify()
{
    example_arbitrary();
}

pub fn main()
{
    proof {
        arbitrary_verify();
    }
}

} // verus!

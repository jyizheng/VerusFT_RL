use vstd::prelude::*;

verus! {

// ============================================================================
// QC Typeclass: Enumerable
// ============================================================================
// Models the Haskell QuickCheck Enum typeclass for types that can be
// exhaustively enumerated. Useful for small finite types in property testing.

// Enumerable typeclass operations modeled as spec functions
// enum_all: returns all values of the type as a sequence
// enum_count: returns the number of elements in the type

// ----------------------------------------------------------------------------
// Enumerable for Bool
// ----------------------------------------------------------------------------

pub open spec fn enum_all_bool() -> Seq<bool> {
    seq![false, true]
}

pub open spec fn enum_count_bool() -> nat {
    2
}

// Law: enum_count equals length of enum_all
pub proof fn enum_count_eq_len_bool()
    ensures enum_count_bool() == enum_all_bool().len()
{
    assert(enum_all_bool().len() == 2);
    assert(enum_count_bool() == 2);
}

// Law: enum_all contains all values (completeness)
pub proof fn enum_all_complete_bool(b: bool)
    ensures enum_all_bool().contains(b)
{
    if b {
        assert(enum_all_bool()[1] == true);
        assert(enum_all_bool().contains(true));
    } else {
        assert(enum_all_bool()[0] == false);
        assert(enum_all_bool().contains(false));
    }
}

// Law: enum_all has no duplicates (distinctness)
pub proof fn enum_all_distinct_bool()
    ensures forall|i: int, j: int| 0 <= i < j < enum_all_bool().len() as int
        ==> enum_all_bool()[i] != enum_all_bool()[j]
{
    assert(enum_all_bool()[0] == false);
    assert(enum_all_bool()[1] == true);
    assert(enum_all_bool()[0] != enum_all_bool()[1]);
}

// ----------------------------------------------------------------------------
// Enumerable for Option<bool>
// ----------------------------------------------------------------------------

pub open spec fn enum_all_option_bool() -> Seq<Option<bool>> {
    seq![Option::None, Option::Some(false), Option::Some(true)]
}

pub open spec fn enum_count_option_bool() -> nat {
    3
}

pub proof fn enum_count_eq_len_option_bool()
    ensures enum_count_option_bool() == enum_all_option_bool().len()
{
    assert(enum_all_option_bool().len() == 3);
}

pub proof fn enum_all_complete_option_bool(o: Option<bool>)
    ensures enum_all_option_bool().contains(o)
{
    match o {
        Option::None => {
            assert(enum_all_option_bool()[0] == Option::<bool>::None);
        }
        Option::Some(b) => {
            if b {
                assert(enum_all_option_bool()[2] == Option::Some(true));
            } else {
                assert(enum_all_option_bool()[1] == Option::Some(false));
            }
        }
    }
}

// ----------------------------------------------------------------------------
// Enumerable for small nat ranges [0, n)
// ----------------------------------------------------------------------------

pub open spec fn enum_all_nat_range(n: nat) -> Seq<nat>
    decreases n
{
    if n == 0 {
        Seq::empty()
    } else {
        enum_all_nat_range((n - 1) as nat).push((n - 1) as nat)
    }
}

pub open spec fn enum_count_nat_range(n: nat) -> nat {
    n
}

pub proof fn enum_count_eq_len_nat_range(n: nat)
    ensures enum_count_nat_range(n) == enum_all_nat_range(n).len()
    decreases n
{
    if n == 0 {
        assert(enum_all_nat_range(0) =~= Seq::empty());
        assert(enum_all_nat_range(0).len() == 0);
    } else {
        enum_count_eq_len_nat_range((n - 1) as nat);
        assert(enum_all_nat_range(n).len() == enum_all_nat_range((n - 1) as nat).len() + 1);
    }
}

pub proof fn enum_all_nat_range_index(n: nat, i: nat)
    requires i < n
    ensures enum_all_nat_range(n)[i as int] == i
    decreases n
{
    enum_count_eq_len_nat_range(n);
    if n == 0 {
        // vacuously true
    } else if i < n - 1 {
        enum_count_eq_len_nat_range((n - 1) as nat);
        enum_all_nat_range_index((n - 1) as nat, i);
        // The push operation preserves earlier indices
        let prev = enum_all_nat_range((n - 1) as nat);
        assert(prev.len() == (n - 1) as nat);
        assert(enum_all_nat_range(n) == prev.push((n - 1) as nat));
        assert(prev.push((n - 1) as nat)[i as int] == prev[i as int]);
    } else {
        // i == n - 1
        enum_count_eq_len_nat_range((n - 1) as nat);
        let prev = enum_all_nat_range((n - 1) as nat);
        assert(prev.len() == (n - 1) as nat);
        assert(enum_all_nat_range(n) == prev.push((n - 1) as nat));
        assert(prev.push((n - 1) as nat)[(n - 1) as int] == (n - 1) as nat);
    }
}

pub proof fn enum_all_complete_nat_range(n: nat, k: nat)
    requires k < n
    ensures enum_all_nat_range(n).contains(k)
    decreases n
{
    enum_count_eq_len_nat_range(n);
    enum_all_nat_range_index(n, k);
    assert(enum_all_nat_range(n)[k as int] == k);
}

// ----------------------------------------------------------------------------
// Generic Enumerable Laws
// ----------------------------------------------------------------------------

// For any enumerable type, if we can enumerate n elements,
// then the sequence should have length n
pub open spec fn enum_law_count_matches_len<A>(enum_all: Seq<A>, count: nat) -> bool {
    enum_all.len() == count
}

// All elements in enum_all should be distinct
pub open spec fn enum_law_distinct<A>(enum_all: Seq<A>) -> bool {
    forall|i: int, j: int| 0 <= i < j < enum_all.len() as int ==> enum_all[i] != enum_all[j]
}

// ----------------------------------------------------------------------------
// Enumerable for pairs (product of two enumerable types)
// ----------------------------------------------------------------------------

pub open spec fn enum_all_pair_bool() -> Seq<(bool, bool)> {
    seq![
        (false, false),
        (false, true),
        (true, false),
        (true, true)
    ]
}

pub open spec fn enum_count_pair_bool() -> nat {
    4  // 2 * 2
}

pub proof fn enum_count_pair_bool_is_product()
    ensures enum_count_pair_bool() == enum_count_bool() * enum_count_bool()
{
    assert(enum_count_pair_bool() == 4);
    assert(enum_count_bool() == 2);
    assert(2 * 2 == 4);
}

pub proof fn enum_all_complete_pair_bool(p: (bool, bool))
    ensures enum_all_pair_bool().contains(p)
{
    match p {
        (false, false) => assert(enum_all_pair_bool()[0] == (false, false)),
        (false, true) => assert(enum_all_pair_bool()[1] == (false, true)),
        (true, false) => assert(enum_all_pair_bool()[2] == (true, false)),
        (true, true) => assert(enum_all_pair_bool()[3] == (true, true)),
    }
}

// ----------------------------------------------------------------------------
// Example and verification
// ----------------------------------------------------------------------------

pub proof fn example_enum()
{
    // Bool enumeration
    enum_count_eq_len_bool();
    enum_all_complete_bool(true);
    enum_all_complete_bool(false);
    enum_all_distinct_bool();

    // Option<bool> enumeration
    enum_count_eq_len_option_bool();
    enum_all_complete_option_bool(Option::None);
    enum_all_complete_option_bool(Option::Some(true));

    // Nat range enumeration
    enum_count_eq_len_nat_range(5);
    enum_all_complete_nat_range(5, 3);

    // Pair enumeration
    enum_count_pair_bool_is_product();
    enum_all_complete_pair_bool((true, false));
}

pub proof fn enum_verify()
{
    example_enum();
}

pub fn main()
{
    proof {
        enum_verify();
    }
}

} // verus!

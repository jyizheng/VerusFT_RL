use vstd::prelude::*;

verus! {

// ============================================================================
// QC Typeclass: Default
// ============================================================================
// Models types with a default/initial value.
// Useful in QuickCheck for providing base cases and initial states.

// ----------------------------------------------------------------------------
// Default for basic types
// ----------------------------------------------------------------------------

pub open spec fn default_bool() -> bool {
    false
}

pub open spec fn default_nat() -> nat {
    0
}

pub open spec fn default_int() -> int {
    0
}

// ----------------------------------------------------------------------------
// Default for Option<A>
// ----------------------------------------------------------------------------

pub open spec fn default_option<A>() -> Option<A> {
    Option::None
}

pub proof fn default_option_is_none<A>()
    ensures default_option::<A>() == Option::<A>::None
{
    // Trivially true by definition
}

// ----------------------------------------------------------------------------
// Default for Seq<A>
// ----------------------------------------------------------------------------

pub open spec fn default_seq<A>() -> Seq<A> {
    Seq::empty()
}

pub proof fn default_seq_is_empty<A>()
    ensures default_seq::<A>().len() == 0
{
    assert(Seq::<A>::empty().len() == 0);
}

// ----------------------------------------------------------------------------
// Default for pairs
// ----------------------------------------------------------------------------

pub open spec fn default_pair<A, B>(da: A, db: B) -> (A, B) {
    (da, db)
}

pub open spec fn default_pair_nat() -> (nat, nat) {
    default_pair(default_nat(), default_nat())
}

pub proof fn default_pair_nat_is_zeros()
    ensures default_pair_nat() == (0nat, 0nat)
{
    assert(default_nat() == 0);
}

// ----------------------------------------------------------------------------
// Default Laws
// ----------------------------------------------------------------------------

// Law 1: Default should be a valid value of the type
// (This is enforced by the type system)

// Law 2: Default combined with a monoid operation should be identity
// For addition: default_nat() + x == x
pub proof fn default_nat_add_left_identity(x: nat)
    ensures (default_nat() + x) as nat == x
{
    assert(0 + x == x);
}

pub proof fn default_nat_add_right_identity(x: nat)
    ensures (x + default_nat()) as nat == x
{
    assert(x + 0 == x);
}

// For sequence concatenation: default_seq() ++ xs == xs
pub proof fn default_seq_concat_left_identity<A>(xs: Seq<A>)
    ensures default_seq::<A>().add(xs) =~= xs
{
    assert(Seq::<A>::empty().add(xs) =~= xs);
}

pub proof fn default_seq_concat_right_identity<A>(xs: Seq<A>)
    ensures xs.add(default_seq::<A>()) =~= xs
{
    assert(xs.add(Seq::<A>::empty()) =~= xs);
}

// For boolean and: default_bool() && x == x (false && x == false, not identity)
// Actually for &&, true is the identity
pub open spec fn default_bool_and_identity() -> bool {
    true
}

pub proof fn and_identity_left(x: bool)
    ensures (default_bool_and_identity() && x) == x
{
    assert(true && x == x);
}

// For boolean or: false is the identity
pub proof fn or_identity_left(x: bool)
    ensures (default_bool() || x) == x
{
    assert(false || x == x);
}

// ----------------------------------------------------------------------------
// Default with Option operations
// ----------------------------------------------------------------------------

pub open spec fn unwrap_or<A>(o: Option<A>, default: A) -> A {
    match o {
        Option::None => default,
        Option::Some(x) => x,
    }
}

pub proof fn unwrap_or_none_is_default<A>(default: A)
    ensures unwrap_or(Option::None, default) == default
{
    // Trivially true
}

pub proof fn unwrap_or_some_ignores_default<A>(x: A, default: A)
    ensures unwrap_or(Option::Some(x), default) == x
{
    // Trivially true
}

// get_or_insert semantics
pub open spec fn get_or_insert<A>(o: Option<A>, default: A) -> (Option<A>, A) {
    match o {
        Option::None => (Option::Some(default), default),
        Option::Some(x) => (Option::Some(x), x),
    }
}

pub proof fn get_or_insert_none(default: nat)
    ensures get_or_insert(Option::<nat>::None, default) == (Option::Some(default), default)
{
    // Trivially true
}

pub proof fn get_or_insert_some(x: nat, default: nat)
    ensures get_or_insert(Option::Some(x), default) == (Option::Some(x), x)
{
    // Trivially true
}

// ----------------------------------------------------------------------------
// Default for custom enum types
// ----------------------------------------------------------------------------

// Example: Result-like type
pub enum MyResult<A, E> {
    Ok(A),
    Err(E),
}

pub open spec fn default_my_result<A, E>(default_a: A) -> MyResult<A, E> {
    MyResult::Ok(default_a)
}

// Example: Three-valued logic
pub enum Trilean {
    TFalse,
    TUnknown,
    TTrue,
}

pub open spec fn default_trilean() -> Trilean {
    Trilean::TUnknown
}

// ----------------------------------------------------------------------------
// Default-based initialization patterns
// ----------------------------------------------------------------------------

// Initialize a sequence with n copies of default value
pub open spec fn replicate_default_nat(n: nat) -> Seq<nat>
    decreases n
{
    if n == 0 {
        Seq::empty()
    } else {
        seq![default_nat()].add(replicate_default_nat((n - 1) as nat))
    }
}

pub proof fn replicate_default_length(n: nat)
    ensures replicate_default_nat(n).len() == n
    decreases n
{
    if n == 0 {
        assert(replicate_default_nat(0) =~= Seq::empty());
    } else {
        replicate_default_length((n - 1) as nat);
        assert(replicate_default_nat(n).len() == 1 + replicate_default_nat((n - 1) as nat).len());
    }
}

pub proof fn replicate_default_all_zeros(n: nat, i: nat)
    requires i < n
    ensures replicate_default_nat(n)[i as int] == 0
    decreases n
{
    replicate_default_length(n);
    if n == 0 {
        // vacuously true
    } else if i == 0 {
        assert(replicate_default_nat(n)[0] == 0);
    } else {
        replicate_default_length((n - 1) as nat);
        replicate_default_all_zeros((n - 1) as nat, (i - 1) as nat);
        // Show the structure of replicate_default_nat(n)
        let rest = replicate_default_nat((n - 1) as nat);
        assert(replicate_default_nat(n) == seq![default_nat()].add(rest));
        assert(rest.len() == (n - 1) as nat);
        assert(i - 1 < rest.len());
        assert(seq![default_nat()].add(rest)[i as int] == rest[(i - 1) as int]);
    }
}

// ----------------------------------------------------------------------------
// Semigroup/Monoid default
// ----------------------------------------------------------------------------

// A monoid needs an identity element (often the "default")
pub open spec fn monoid_nat_add_identity() -> nat {
    default_nat()  // 0
}

pub open spec fn monoid_nat_mul_identity() -> nat {
    1  // Different from default_nat for multiplication
}

pub proof fn monoid_nat_add_laws(x: nat, y: nat, z: nat)
    ensures (monoid_nat_add_identity() + x) as nat == x,
            (x + monoid_nat_add_identity()) as nat == x,
            ((x + y) + z) as nat == (x + (y + z)) as nat
{
    // All trivially true for nat addition
}

pub proof fn monoid_nat_mul_laws_identity_left(x: nat)
    ensures monoid_nat_mul_identity() * x == x
{
    assert(1 * x == x);
}

pub proof fn monoid_nat_mul_laws_identity_right(x: nat)
    ensures x * monoid_nat_mul_identity() == x
{
    assert(x * 1 == x);
}

pub proof fn monoid_nat_mul_laws_assoc(x: nat, y: nat, z: nat)
    ensures (x * y) * z == x * (y * z)
{
    // Associativity of nat multiplication
    assert((x * y) * z == x * (y * z)) by(nonlinear_arith);
}

// ----------------------------------------------------------------------------
// Example and verification
// ----------------------------------------------------------------------------

pub proof fn example_default()
{
    // Basic defaults
    assert(default_bool() == false);
    assert(default_nat() == 0);
    assert(default_int() == 0);

    // Option default
    default_option_is_none::<nat>();

    // Seq default
    default_seq_is_empty::<nat>();

    // Pair default
    default_pair_nat_is_zeros();

    // Identity laws
    default_nat_add_left_identity(42);
    default_nat_add_right_identity(42);
    default_seq_concat_left_identity::<nat>(seq![1nat, 2, 3]);

    // Boolean identities
    and_identity_left(true);
    or_identity_left(true);

    // Option operations
    unwrap_or_none_is_default(99nat);
    unwrap_or_some_ignores_default(42nat, 99nat);
    get_or_insert_none(0nat);
    get_or_insert_some(42nat, 0nat);

    // Replication
    replicate_default_length(5);
    replicate_default_all_zeros(5, 2);

    // Monoid laws
    monoid_nat_add_laws(1, 2, 3);
    monoid_nat_mul_laws_identity_left(10);
    monoid_nat_mul_laws_identity_right(10);
    monoid_nat_mul_laws_assoc(2, 3, 4);
}

pub proof fn default_verify()
{
    example_default();
}

pub fn main()
{
    proof {
        default_verify();
    }
}

} // verus!

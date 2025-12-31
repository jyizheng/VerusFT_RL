use vstd::prelude::*;

verus! {

// ============================================================================
// QC: Universal Properties (QuickChick Properties)
// Properties using forall quantifier for universal statements
// ============================================================================

// ----------------------------------------------------------------------------
// Universal Quantification (with triggers)
// ----------------------------------------------------------------------------

/// Universal property over naturals: addition is commutative for all x, y
pub open spec fn forall_add_comm() -> bool {
    forall|x: nat, y: nat| #[trigger] (x + y) == y + x
}

/// Universal property: addition is associative
pub open spec fn forall_add_assoc() -> bool {
    forall|x: nat, y: nat, z: nat| #[trigger] ((x + y) + z) == x + (y + z)
}

/// Universal property: multiplication is commutative
pub open spec fn forall_mul_comm() -> bool {
    forall|x: nat, y: nat| #[trigger] (x * y) == y * x
}

/// Universal property: zero is identity for addition
pub open spec fn forall_add_identity() -> bool {
    forall|x: nat| #[trigger] (x + 0) == x && 0 + x == x
}

/// Universal property: one is identity for multiplication
pub open spec fn forall_mul_identity() -> bool {
    forall|x: nat| #[trigger] (x * 1) == x && 1 * x == x
}

/// Universal property: zero annihilates multiplication
pub open spec fn forall_mul_zero() -> bool {
    forall|x: nat| #[trigger] (x * 0) == 0 && 0 * x == 0
}

// ----------------------------------------------------------------------------
// Bounded Universal Properties
// ----------------------------------------------------------------------------

/// All elements less than bound satisfy property
pub open spec fn forall_bounded(bound: nat, pred: spec_fn(nat) -> bool) -> bool {
    forall|x: nat| x < bound ==> #[trigger] pred(x)
}

/// All elements in range [lo, hi) satisfy property
pub open spec fn forall_range(lo: nat, hi: nat, pred: spec_fn(nat) -> bool) -> bool {
    forall|x: nat| (lo <= x && x < hi) ==> #[trigger] pred(x)
}

/// Property: all natural squares equal self times self
pub open spec fn forall_square_def() -> bool {
    forall|x: nat| #[trigger] (x * x) == x * x
}

/// Property: all numbers equal themselves (reflexivity)
pub open spec fn forall_eq_refl() -> bool {
    forall|x: nat| #![trigger (x + 0)] x == x
}

// ----------------------------------------------------------------------------
// Universal Properties over Sequences
// ----------------------------------------------------------------------------

/// All elements in sequence satisfy predicate
pub open spec fn forall_seq_elements<T>(s: Seq<T>, pred: spec_fn(T) -> bool) -> bool {
    forall|i: int| 0 <= i < s.len() ==> #[trigger] pred(s[i])
}

/// All pairs of adjacent elements satisfy relation
pub open spec fn forall_seq_adjacent<T>(s: Seq<T>, rel: spec_fn(T, T) -> bool) -> bool {
    forall|i: int| 0 <= i < s.len() - 1 ==> #[trigger] rel(s[i], s[i + 1])
}

/// Sequence is sorted if all pairs are ordered
pub open spec fn forall_sorted(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> #[trigger] s[i] <= #[trigger] s[j]
}

/// All indices are valid
pub open spec fn forall_valid_indices<T>(s: Seq<T>) -> bool {
    forall|i: int| #![trigger s[i]] (0 <= i && i < s.len()) ==> (i >= 0)
}

// ----------------------------------------------------------------------------
// Nested Universal Properties
// ----------------------------------------------------------------------------

/// For all x, y: if x <= y then x + z <= y + z for all z
pub open spec fn forall_add_mono() -> bool {
    forall|x: nat, y: nat, z: nat| #![trigger x + z, y + z] x <= y ==> (x + z) <= (y + z)
}

/// For all x, y: max(x, y) >= x and max(x, y) >= y
pub open spec fn forall_max_ge() -> bool {
    forall|x: nat, y: nat| #![trigger x + y]
        (if x >= y { x } else { y }) >= x &&
        (if x >= y { x } else { y }) >= y
}

/// For all x, y: min(x, y) <= x and min(x, y) <= y
pub open spec fn forall_min_le() -> bool {
    forall|x: nat, y: nat| #![trigger x + y]
        (if x <= y { x } else { y }) <= x &&
        (if x <= y { x } else { y }) <= y
}

// ----------------------------------------------------------------------------
// Verification Proofs
// ----------------------------------------------------------------------------

pub proof fn verify_forall_add_comm()
    ensures forall_add_comm()
{
}

pub proof fn verify_forall_add_assoc()
    ensures forall_add_assoc()
{
}

pub proof fn verify_forall_mul_comm()
    ensures forall_mul_comm()
{
}

pub proof fn verify_forall_add_identity()
    ensures forall_add_identity()
{
}

pub proof fn verify_forall_mul_identity()
    ensures forall_mul_identity()
{
}

pub proof fn verify_forall_mul_zero()
    ensures forall_mul_zero()
{
}

pub proof fn verify_forall_square_def()
    ensures forall_square_def()
{
}

pub proof fn verify_forall_eq_refl()
    ensures forall_eq_refl()
{
}

pub proof fn verify_forall_add_mono()
    ensures forall_add_mono()
{
}

pub proof fn verify_forall_max_ge()
    ensures forall_max_ge()
{
}

pub proof fn verify_forall_min_le()
    ensures forall_min_le()
{
}

// ----------------------------------------------------------------------------
// Instantiation Proofs
// ----------------------------------------------------------------------------

/// Forall elimination: extract specific instance
pub proof fn forall_elim_add_comm(a: nat, b: nat)
    ensures a + b == b + a
{
    verify_forall_add_comm();
}

/// Forall elimination for multiplication
pub proof fn forall_elim_mul_comm(a: nat, b: nat)
    ensures a * b == b * a
{
    verify_forall_mul_comm();
}

/// Forall elimination for identity
pub proof fn forall_elim_add_identity(x: nat)
    ensures x + 0 == x
{
    verify_forall_add_identity();
}

// ----------------------------------------------------------------------------
// Bounded Quantification Examples
// ----------------------------------------------------------------------------

/// All x < 10 have x + 1 <= 10
pub open spec fn bounded_example() -> bool {
    forall_bounded(10, |x: nat| x + 1 <= 10)
}

pub proof fn verify_bounded_example()
    ensures bounded_example()
{
}

/// All x in [5, 10) have x >= 5
pub open spec fn range_example() -> bool {
    forall_range(5, 10, |x: nat| x >= 5)
}

pub proof fn verify_range_example()
    ensures range_example()
{
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_universal_arithmetic()
{
    verify_forall_add_comm();
    assert(forall_add_comm());

    verify_forall_mul_comm();
    assert(forall_mul_comm());

    verify_forall_add_identity();
    assert(forall_add_identity());
}

pub proof fn example_universal_order()
{
    verify_forall_add_mono();
    assert(forall_add_mono());

    verify_forall_max_ge();
    assert(forall_max_ge());

    verify_forall_min_le();
    assert(forall_min_le());
}

pub proof fn example_bounded_quantification()
{
    verify_bounded_example();
    assert(bounded_example());

    verify_range_example();
    assert(range_example());
}

pub proof fn example_instantiation()
{
    // Use universal property for specific values
    forall_elim_add_comm(3, 7);
    assert(3 + 7 == 7 + 3);

    forall_elim_mul_comm(4, 5);
    assert(4 * 5 == 5 * 4);

    forall_elim_add_identity(42);
    assert(42 + 0 == 42);
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_prop_forall_verify()
{
    example_universal_arithmetic();
    example_universal_order();
    example_bounded_quantification();
    example_instantiation();

    // Verify fundamental properties
    verify_forall_add_comm();
    verify_forall_mul_comm();
    verify_forall_square_def();
    verify_forall_eq_refl();
}

pub fn main() {
    proof {
        qc_prop_forall_verify();
    }
}

} // verus!

use vstd::prelude::*;

verus! {

// ============================================================================
// QC Typeclass: Ring
// ============================================================================
// Models the algebraic structure of a Ring with operations:
// - add: addition (forms an abelian group)
// - mul: multiplication (forms a monoid)
// - zero: additive identity
// - one: multiplicative identity
// - neg: additive inverse

// Ring laws:
// 1. (R, +, 0) is an abelian group
// 2. (R, *, 1) is a monoid
// 3. Distributivity: a * (b + c) = a*b + a*c and (a + b) * c = a*c + b*c

// ----------------------------------------------------------------------------
// Ring for int
// ----------------------------------------------------------------------------

pub open spec fn ring_zero_int() -> int {
    0
}

pub open spec fn ring_one_int() -> int {
    1
}

pub open spec fn ring_add_int(a: int, b: int) -> int {
    a + b
}

pub open spec fn ring_mul_int(a: int, b: int) -> int {
    a * b
}

pub open spec fn ring_neg_int(a: int) -> int {
    -a
}

// Subtraction derived from add and neg
pub open spec fn ring_sub_int(a: int, b: int) -> int {
    ring_add_int(a, ring_neg_int(b))
}

// ----------------------------------------------------------------------------
// Ring laws for int
// ----------------------------------------------------------------------------

// Addition is associative
pub proof fn ring_add_assoc_int(a: int, b: int, c: int)
    ensures ring_add_int(ring_add_int(a, b), c) == ring_add_int(a, ring_add_int(b, c))
{
    assert((a + b) + c == a + (b + c));
}

// Addition is commutative
pub proof fn ring_add_comm_int(a: int, b: int)
    ensures ring_add_int(a, b) == ring_add_int(b, a)
{
    assert(a + b == b + a);
}

// Zero is additive identity
pub proof fn ring_add_zero_left_int(a: int)
    ensures ring_add_int(ring_zero_int(), a) == a
{
    assert(0 + a == a);
}

pub proof fn ring_add_zero_right_int(a: int)
    ensures ring_add_int(a, ring_zero_int()) == a
{
    assert(a + 0 == a);
}

// Negation gives additive inverse
pub proof fn ring_add_neg_left_int(a: int)
    ensures ring_add_int(ring_neg_int(a), a) == ring_zero_int()
{
    assert(-a + a == 0);
}

pub proof fn ring_add_neg_right_int(a: int)
    ensures ring_add_int(a, ring_neg_int(a)) == ring_zero_int()
{
    assert(a + (-a) == 0);
}

// Multiplication is associative
pub proof fn ring_mul_assoc_int(a: int, b: int, c: int)
    ensures ring_mul_int(ring_mul_int(a, b), c) == ring_mul_int(a, ring_mul_int(b, c))
{
    assert((a * b) * c == a * (b * c)) by(nonlinear_arith);
}

// One is multiplicative identity
pub proof fn ring_mul_one_left_int(a: int)
    ensures ring_mul_int(ring_one_int(), a) == a
{
    assert(1 * a == a);
}

pub proof fn ring_mul_one_right_int(a: int)
    ensures ring_mul_int(a, ring_one_int()) == a
{
    assert(a * 1 == a);
}

// Left distributivity: a * (b + c) = a*b + a*c
pub proof fn ring_distrib_left_int(a: int, b: int, c: int)
    ensures ring_mul_int(a, ring_add_int(b, c)) == ring_add_int(ring_mul_int(a, b), ring_mul_int(a, c))
{
    assert(a * (b + c) == a * b + a * c) by(nonlinear_arith);
}

// Right distributivity: (a + b) * c = a*c + b*c
pub proof fn ring_distrib_right_int(a: int, b: int, c: int)
    ensures ring_mul_int(ring_add_int(a, b), c) == ring_add_int(ring_mul_int(a, c), ring_mul_int(b, c))
{
    assert((a + b) * c == a * c + b * c) by(nonlinear_arith);
}

// Zero annihilates multiplication
pub proof fn ring_mul_zero_left_int(a: int)
    ensures ring_mul_int(ring_zero_int(), a) == ring_zero_int()
{
    assert(0 * a == 0);
}

pub proof fn ring_mul_zero_right_int(a: int)
    ensures ring_mul_int(a, ring_zero_int()) == ring_zero_int()
{
    assert(a * 0 == 0);
}

// Negation distributes: -(a+b) = -a + -b
pub proof fn ring_neg_distrib_int(a: int, b: int)
    ensures ring_neg_int(ring_add_int(a, b)) == ring_add_int(ring_neg_int(a), ring_neg_int(b))
{
    assert(-(a + b) == -a + -b);
}

// Double negation
pub proof fn ring_neg_neg_int(a: int)
    ensures ring_neg_int(ring_neg_int(a)) == a
{
    assert(-(-a) == a);
}

// neg(a) * b = -(a * b)
pub proof fn ring_neg_mul_left_int(a: int, b: int)
    ensures ring_mul_int(ring_neg_int(a), b) == ring_neg_int(ring_mul_int(a, b))
{
    assert((-a) * b == -(a * b)) by(nonlinear_arith);
}

// a * neg(b) = -(a * b)
pub proof fn ring_neg_mul_right_int(a: int, b: int)
    ensures ring_mul_int(a, ring_neg_int(b)) == ring_neg_int(ring_mul_int(a, b))
{
    assert(a * (-b) == -(a * b)) by(nonlinear_arith);
}

// neg(a) * neg(b) = a * b
pub proof fn ring_neg_neg_mul_int(a: int, b: int)
    ensures ring_mul_int(ring_neg_int(a), ring_neg_int(b)) == ring_mul_int(a, b)
{
    assert((-a) * (-b) == a * b) by(nonlinear_arith);
}

// ----------------------------------------------------------------------------
// Ring for nat (actually a semiring - no negation, but we model it)
// ----------------------------------------------------------------------------

pub open spec fn ring_zero_nat() -> nat {
    0
}

pub open spec fn ring_one_nat() -> nat {
    1
}

pub open spec fn ring_add_nat(a: nat, b: nat) -> nat {
    (a + b) as nat
}

pub open spec fn ring_mul_nat(a: nat, b: nat) -> nat {
    a * b
}

// Semiring laws (no negation for nat)
pub proof fn ring_add_assoc_nat(a: nat, b: nat, c: nat)
    ensures ring_add_nat(ring_add_nat(a, b), c) == ring_add_nat(a, ring_add_nat(b, c))
{
    assert(((a + b) + c) as nat == (a + (b + c)) as nat);
}

pub proof fn ring_add_comm_nat(a: nat, b: nat)
    ensures ring_add_nat(a, b) == ring_add_nat(b, a)
{
    assert((a + b) as nat == (b + a) as nat);
}

pub proof fn ring_add_zero_nat(a: nat)
    ensures ring_add_nat(ring_zero_nat(), a) == a,
            ring_add_nat(a, ring_zero_nat()) == a
{
    assert((0 + a) as nat == a);
    assert((a + 0) as nat == a);
}

pub proof fn ring_mul_assoc_nat(a: nat, b: nat, c: nat)
    ensures ring_mul_nat(ring_mul_nat(a, b), c) == ring_mul_nat(a, ring_mul_nat(b, c))
{
    assert((a * b) * c == a * (b * c)) by(nonlinear_arith);
}

pub proof fn ring_mul_one_nat(a: nat)
    ensures ring_mul_nat(ring_one_nat(), a) == a,
            ring_mul_nat(a, ring_one_nat()) == a
{
    assert(1 * a == a);
    assert(a * 1 == a);
}

pub proof fn ring_distrib_nat(a: nat, b: nat, c: nat)
    ensures ring_mul_nat(a, ring_add_nat(b, c)) == ring_add_nat(ring_mul_nat(a, b), ring_mul_nat(a, c))
{
    assert(a * ((b + c) as nat) == ((a * b) + (a * c)) as nat) by(nonlinear_arith);
}

// ----------------------------------------------------------------------------
// Commutative ring (int is commutative)
// ----------------------------------------------------------------------------

pub proof fn ring_mul_comm_int(a: int, b: int)
    ensures ring_mul_int(a, b) == ring_mul_int(b, a)
{
    assert(a * b == b * a);
}

// ----------------------------------------------------------------------------
// Ring homomorphism: int to int (identity)
// ----------------------------------------------------------------------------

pub open spec fn ring_hom_id(x: int) -> int {
    x
}

pub proof fn ring_hom_id_preserves_zero()
    ensures ring_hom_id(ring_zero_int()) == ring_zero_int()
{
    // Trivially true
}

pub proof fn ring_hom_id_preserves_one()
    ensures ring_hom_id(ring_one_int()) == ring_one_int()
{
    // Trivially true
}

pub proof fn ring_hom_id_preserves_add(a: int, b: int)
    ensures ring_hom_id(ring_add_int(a, b)) == ring_add_int(ring_hom_id(a), ring_hom_id(b))
{
    // Trivially true
}

pub proof fn ring_hom_id_preserves_mul(a: int, b: int)
    ensures ring_hom_id(ring_mul_int(a, b)) == ring_mul_int(ring_hom_id(a), ring_hom_id(b))
{
    // Trivially true
}

// ----------------------------------------------------------------------------
// Polynomial-like expressions
// ----------------------------------------------------------------------------

// Evaluate a polynomial represented as coefficients [a0, a1, a2, ...] at x
// p(x) = a0 + a1*x + a2*x^2 + ...
pub open spec fn ring_power_int(base: int, exp: nat) -> int
    decreases exp
{
    if exp == 0 {
        ring_one_int()
    } else {
        ring_mul_int(base, ring_power_int(base, (exp - 1) as nat))
    }
}

pub open spec fn ring_eval_poly_int(coeffs: Seq<int>, x: int) -> int
    decreases coeffs.len()
{
    if coeffs.len() == 0 {
        ring_zero_int()
    } else {
        ring_add_int(
            coeffs[0],
            ring_mul_int(x, ring_eval_poly_int(coeffs.skip(1), x))
        )
    }
}

pub proof fn ring_power_zero_int(base: int)
    ensures ring_power_int(base, 0) == ring_one_int()
{
    // Trivially true by definition
}

pub proof fn ring_power_one_int(base: int)
    ensures ring_power_int(base, 1) == base
{
    // ring_power_int(base, 1) = ring_mul_int(base, ring_power_int(base, 0))
    //                        = ring_mul_int(base, 1)
    //                        = base
    assert(ring_power_int(base, 0) == 1);
    assert(ring_power_int(base, 1) == ring_mul_int(base, ring_power_int(base, 0)));
    assert(ring_mul_int(base, 1) == base);
}

pub proof fn ring_eval_poly_empty_int(x: int)
    ensures ring_eval_poly_int(Seq::empty(), x) == ring_zero_int()
{
    // Trivially true
}

pub proof fn ring_eval_poly_constant_int(c: int, x: int)
    ensures ring_eval_poly_int(seq![c], x) == c
{
    let coeffs = seq![c];
    assert(coeffs.len() == 1);
    assert(coeffs[0] == c);
    // ring_eval_poly_int(seq![c], x) expands to:
    // ring_add_int(c, ring_mul_int(x, ring_eval_poly_int(coeffs.skip(1), x)))
    // = ring_add_int(c, ring_mul_int(x, 0))
    // = ring_add_int(c, 0)
    // = c
    assert(coeffs.skip(1).len() == 0);
    assert(ring_eval_poly_int(coeffs.skip(1), x) == 0);
    assert(ring_mul_int(x, 0) == 0);
    assert(ring_add_int(c, 0) == c);
}

// ----------------------------------------------------------------------------
// Sum and product operations
// ----------------------------------------------------------------------------

pub open spec fn ring_sum_int(xs: Seq<int>) -> int
    decreases xs.len()
{
    if xs.len() == 0 {
        ring_zero_int()
    } else {
        ring_add_int(xs[0], ring_sum_int(xs.skip(1)))
    }
}

pub open spec fn ring_product_int(xs: Seq<int>) -> int
    decreases xs.len()
{
    if xs.len() == 0 {
        ring_one_int()
    } else {
        ring_mul_int(xs[0], ring_product_int(xs.skip(1)))
    }
}

pub proof fn ring_sum_empty_int()
    ensures ring_sum_int(Seq::empty()) == ring_zero_int()
{
    // Trivially true
}

pub proof fn ring_product_empty_int()
    ensures ring_product_int(Seq::empty()) == ring_one_int()
{
    // Trivially true
}

// ----------------------------------------------------------------------------
// Example and verification
// ----------------------------------------------------------------------------

pub proof fn example_ring()
{
    // Basic ring laws for int
    ring_add_assoc_int(1, 2, 3);
    ring_add_comm_int(3, 5);
    ring_add_zero_left_int(42);
    ring_add_neg_left_int(7);

    ring_mul_assoc_int(2, 3, 4);
    ring_mul_one_left_int(10);
    ring_mul_comm_int(4, 5);

    ring_distrib_left_int(2, 3, 4);
    ring_distrib_right_int(2, 3, 4);

    ring_mul_zero_left_int(42);
    ring_neg_distrib_int(3, 5);
    ring_neg_neg_int(7);
    ring_neg_neg_mul_int(3, 4);

    // Semiring laws for nat
    ring_add_assoc_nat(1, 2, 3);
    ring_add_comm_nat(3, 5);
    ring_add_zero_nat(42);
    ring_mul_assoc_nat(2, 3, 4);
    ring_mul_one_nat(10);
    ring_distrib_nat(2, 3, 4);

    // Ring homomorphism
    ring_hom_id_preserves_zero();
    ring_hom_id_preserves_one();
    ring_hom_id_preserves_add(3, 5);
    ring_hom_id_preserves_mul(3, 5);

    // Power and polynomial
    ring_power_zero_int(5);
    ring_power_one_int(5);
    ring_eval_poly_empty_int(10);
    ring_eval_poly_constant_int(7, 10);

    // Sum and product
    ring_sum_empty_int();
    ring_product_empty_int();
}

pub proof fn ring_verify()
{
    example_ring();
}

pub fn main()
{
    proof {
        ring_verify();
    }
}

} // verus!

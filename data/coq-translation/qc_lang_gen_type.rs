use vstd::prelude::*;

verus! {

// ============================================================================
// QC Lang: Type Generation (Random Types with Size Bound)
// ============================================================================
// Models type generation for property-based testing of a typed language.
// Uses size bounds to ensure termination and control complexity.

// ----------------------------------------------------------------------------
// Types
// ----------------------------------------------------------------------------

#[derive(PartialEq, Eq)]
pub enum Ty {
    TBool,
    TNat,
    TUnit,
    TProd { t1: Box<Ty>, t2: Box<Ty> },  // Product type
    TSum { t1: Box<Ty>, t2: Box<Ty> },   // Sum type
    TArrow { t1: Box<Ty>, t2: Box<Ty> }, // Function type
}

// ----------------------------------------------------------------------------
// Type Size (Depth)
// ----------------------------------------------------------------------------

pub open spec fn ty_size(t: Ty) -> nat
    decreases t
{
    match t {
        Ty::TBool => 1,
        Ty::TNat => 1,
        Ty::TUnit => 1,
        Ty::TProd { t1, t2 } => 1 + ty_size(*t1) + ty_size(*t2),
        Ty::TSum { t1, t2 } => 1 + ty_size(*t1) + ty_size(*t2),
        Ty::TArrow { t1, t2 } => 1 + ty_size(*t1) + ty_size(*t2),
    }
}

pub proof fn ty_size_positive(t: Ty)
    ensures ty_size(t) >= 1
    decreases t
{
    match t {
        Ty::TBool => {}
        Ty::TNat => {}
        Ty::TUnit => {}
        Ty::TProd { t1, t2 } => {
            ty_size_positive(*t1);
            ty_size_positive(*t2);
        }
        Ty::TSum { t1, t2 } => {
            ty_size_positive(*t1);
            ty_size_positive(*t2);
        }
        Ty::TArrow { t1, t2 } => {
            ty_size_positive(*t1);
            ty_size_positive(*t2);
        }
    }
}

// ----------------------------------------------------------------------------
// Type Depth (Alternative Measure)
// ----------------------------------------------------------------------------

pub open spec fn ty_depth(t: Ty) -> nat
    decreases t
{
    match t {
        Ty::TBool => 0,
        Ty::TNat => 0,
        Ty::TUnit => 0,
        Ty::TProd { t1, t2 } => {
            let d1 = ty_depth(*t1);
            let d2 = ty_depth(*t2);
            1 + if d1 > d2 { d1 } else { d2 }
        }
        Ty::TSum { t1, t2 } => {
            let d1 = ty_depth(*t1);
            let d2 = ty_depth(*t2);
            1 + if d1 > d2 { d1 } else { d2 }
        }
        Ty::TArrow { t1, t2 } => {
            let d1 = ty_depth(*t1);
            let d2 = ty_depth(*t2);
            1 + if d1 > d2 { d1 } else { d2 }
        }
    }
}

// ----------------------------------------------------------------------------
// Generator Output Sets
// ----------------------------------------------------------------------------

// Set of types with size at most n
pub open spec fn types_of_size(n: nat) -> Set<Ty> {
    Set::new(|t: Ty| ty_size(t) <= n)
}

// Set of types with depth at most d
pub open spec fn types_of_depth(d: nat) -> Set<Ty> {
    Set::new(|t: Ty| ty_depth(t) <= d)
}

// Base types (size 1)
pub open spec fn base_types() -> Set<Ty> {
    Set::new(|t: Ty| t == Ty::TBool || t == Ty::TNat || t == Ty::TUnit)
}

// ----------------------------------------------------------------------------
// Generator Properties
// ----------------------------------------------------------------------------

// Base types are included in types of size >= 1
pub proof fn base_types_in_size_one()
    ensures
        types_of_size(1).contains(Ty::TBool),
        types_of_size(1).contains(Ty::TNat),
        types_of_size(1).contains(Ty::TUnit),
{
    assert(ty_size(Ty::TBool) == 1);
    assert(ty_size(Ty::TNat) == 1);
    assert(ty_size(Ty::TUnit) == 1);
}

// Larger sizes contain more types
pub proof fn size_monotonic(n: nat, m: nat, t: Ty)
    requires n <= m, types_of_size(n).contains(t)
    ensures types_of_size(m).contains(t)
{
    assert(ty_size(t) <= n);
    assert(n <= m);
    assert(ty_size(t) <= m);
}

// Arrow types need size >= 3
pub proof fn arrow_needs_size_three(t1: Ty, t2: Ty)
    ensures ty_size(Ty::TArrow { t1: Box::new(t1), t2: Box::new(t2) }) >= 3
{
    ty_size_positive(t1);
    ty_size_positive(t2);
    assert(ty_size(t1) >= 1);
    assert(ty_size(t2) >= 1);
}

// ----------------------------------------------------------------------------
// Type Generation Model (Sized)
// ----------------------------------------------------------------------------

// Number of possible types at each size (rough bound)
pub open spec fn count_base_types() -> nat {
    3  // TBool, TNat, TUnit
}

// Generate all base types
pub open spec fn gen_base_type() -> Set<Ty> {
    base_types()
}

// Generate product types from component types
pub open spec fn gen_prod_types(components: Set<Ty>) -> Set<Ty> {
    Set::new(|t: Ty|
        exists|t1: Ty, t2: Ty|
            components.contains(t1) && components.contains(t2) &&
            t == Ty::TProd { t1: Box::new(t1), t2: Box::new(t2) }
    )
}

// Generate sum types from component types
pub open spec fn gen_sum_types(components: Set<Ty>) -> Set<Ty> {
    Set::new(|t: Ty|
        exists|t1: Ty, t2: Ty|
            components.contains(t1) && components.contains(t2) &&
            t == Ty::TSum { t1: Box::new(t1), t2: Box::new(t2) }
    )
}

// Generate arrow types from component types
pub open spec fn gen_arrow_types(components: Set<Ty>) -> Set<Ty> {
    Set::new(|t: Ty|
        exists|t1: Ty, t2: Ty|
            components.contains(t1) && components.contains(t2) &&
            t == Ty::TArrow { t1: Box::new(t1), t2: Box::new(t2) }
    )
}

// ----------------------------------------------------------------------------
// Sized Generation with Fuel
// ----------------------------------------------------------------------------

// Types generatable with size bound
pub open spec fn gen_type_sized(size: nat) -> Set<Ty>
    decreases size
{
    if size == 0 {
        Set::empty()
    } else if size == 1 {
        base_types()
    } else {
        // Include base types plus compound types built from smaller types
        let smaller = gen_type_sized((size - 1) as nat);
        let bases = base_types();
        let prods = gen_prod_types(smaller);
        let sums = gen_sum_types(smaller);
        let arrows = gen_arrow_types(smaller);
        bases.union(prods).union(sums).union(arrows)
    }
}

// Size 1 generates exactly base types
pub proof fn gen_type_size_one()
    ensures gen_type_sized(1) == base_types()
{
}

// Size 0 generates nothing
pub proof fn gen_type_size_zero()
    ensures gen_type_sized(0) == Set::<Ty>::empty()
{
}

// ----------------------------------------------------------------------------
// Completeness: All types of bounded size are generated
// ----------------------------------------------------------------------------

// All base types are generated at size 1
pub proof fn base_types_generated()
    ensures
        gen_type_sized(1).contains(Ty::TBool),
        gen_type_sized(1).contains(Ty::TNat),
        gen_type_sized(1).contains(Ty::TUnit),
{
    assert(base_types().contains(Ty::TBool));
    assert(base_types().contains(Ty::TNat));
    assert(base_types().contains(Ty::TUnit));
}

// Arrow type Bool -> Bool is generated at size 3
pub proof fn arrow_bool_bool_generated()
    ensures gen_type_sized(3).contains(
        Ty::TArrow { t1: Box::new(Ty::TBool), t2: Box::new(Ty::TBool) }
    )
{
    // At size 2, we have base types
    assert(gen_type_sized(2).contains(Ty::TBool));

    // At size 3, we can form arrows from size-2 types
    let t = Ty::TArrow { t1: Box::new(Ty::TBool), t2: Box::new(Ty::TBool) };
    let smaller = gen_type_sized(2);
    assert(smaller.contains(Ty::TBool));

    let arrows = gen_arrow_types(smaller);
    assert(arrows.contains(t));
}

// ----------------------------------------------------------------------------
// Frequency Control for Generators
// ----------------------------------------------------------------------------

// Weighted type generation: assign frequencies to constructors
pub open spec fn type_frequency(t: Ty) -> nat {
    match t {
        Ty::TBool => 10,   // Common
        Ty::TNat => 10,    // Common
        Ty::TUnit => 5,    // Less common
        Ty::TProd { .. } => 3,
        Ty::TSum { .. } => 2,
        Ty::TArrow { .. } => 5,
    }
}

// Total weight of base types
pub open spec fn base_type_total_weight() -> nat {
    type_frequency(Ty::TBool) + type_frequency(Ty::TNat) + type_frequency(Ty::TUnit)
}

pub proof fn base_type_weight()
    ensures base_type_total_weight() == 25
{
    assert(type_frequency(Ty::TBool) == 10);
    assert(type_frequency(Ty::TNat) == 10);
    assert(type_frequency(Ty::TUnit) == 5);
}

// ----------------------------------------------------------------------------
// Type Complexity Metrics
// ----------------------------------------------------------------------------

// Count number of arrows in a type
pub open spec fn count_arrows(t: Ty) -> nat
    decreases t
{
    match t {
        Ty::TBool => 0,
        Ty::TNat => 0,
        Ty::TUnit => 0,
        Ty::TProd { t1, t2 } => count_arrows(*t1) + count_arrows(*t2),
        Ty::TSum { t1, t2 } => count_arrows(*t1) + count_arrows(*t2),
        Ty::TArrow { t1, t2 } => 1 + count_arrows(*t1) + count_arrows(*t2),
    }
}

// Count number of type constructors
pub open spec fn count_constructors(t: Ty) -> nat
    decreases t
{
    match t {
        Ty::TBool => 1,
        Ty::TNat => 1,
        Ty::TUnit => 1,
        Ty::TProd { t1, t2 } => 1 + count_constructors(*t1) + count_constructors(*t2),
        Ty::TSum { t1, t2 } => 1 + count_constructors(*t1) + count_constructors(*t2),
        Ty::TArrow { t1, t2 } => 1 + count_constructors(*t1) + count_constructors(*t2),
    }
}

pub proof fn constructors_equals_size(t: Ty)
    ensures count_constructors(t) == ty_size(t)
    decreases t
{
    match t {
        Ty::TBool => {}
        Ty::TNat => {}
        Ty::TUnit => {}
        Ty::TProd { t1, t2 } => {
            constructors_equals_size(*t1);
            constructors_equals_size(*t2);
        }
        Ty::TSum { t1, t2 } => {
            constructors_equals_size(*t1);
            constructors_equals_size(*t2);
        }
        Ty::TArrow { t1, t2 } => {
            constructors_equals_size(*t1);
            constructors_equals_size(*t2);
        }
    }
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_type_sizes()
{
    reveal_with_fuel(ty_size, 5);

    // Base types have size 1
    assert(ty_size(Ty::TBool) == 1);
    assert(ty_size(Ty::TNat) == 1);
    assert(ty_size(Ty::TUnit) == 1);

    // Arrow type has size = 1 + size(t1) + size(t2)
    let arr = Ty::TArrow { t1: Box::new(Ty::TBool), t2: Box::new(Ty::TNat) };
    assert(ty_size(arr) == 3);

    // Nested arrow
    let nested = Ty::TArrow {
        t1: Box::new(Ty::TBool),
        t2: Box::new(Ty::TArrow { t1: Box::new(Ty::TNat), t2: Box::new(Ty::TBool) })
    };
    assert(ty_size(nested) == 5);
}

pub proof fn example_type_depths()
{
    reveal_with_fuel(ty_depth, 5);

    // Base types have depth 0
    assert(ty_depth(Ty::TBool) == 0);

    // Simple arrow has depth 1
    let arr = Ty::TArrow { t1: Box::new(Ty::TBool), t2: Box::new(Ty::TNat) };
    assert(ty_depth(arr) == 1);

    // Nested arrow has depth 2
    let nested = Ty::TArrow {
        t1: Box::new(Ty::TBool),
        t2: Box::new(Ty::TArrow { t1: Box::new(Ty::TNat), t2: Box::new(Ty::TBool) })
    };
    assert(ty_depth(nested) == 2);
}

pub proof fn example_generation()
{
    reveal_with_fuel(ty_size, 5);

    base_types_generated();
    arrow_bool_bool_generated();

    // Product types at size 3
    let prod = Ty::TProd { t1: Box::new(Ty::TBool), t2: Box::new(Ty::TNat) };
    assert(ty_size(prod) == 3);
}

pub proof fn example_arrows_count()
{
    reveal_with_fuel(count_arrows, 5);

    assert(count_arrows(Ty::TBool) == 0);

    let arr = Ty::TArrow { t1: Box::new(Ty::TBool), t2: Box::new(Ty::TNat) };
    assert(count_arrows(arr) == 1);

    let nested = Ty::TArrow {
        t1: Box::new(arr),
        t2: Box::new(Ty::TBool)
    };
    assert(count_arrows(nested) == 2);
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn gen_type_verify()
{
    ty_size_positive(Ty::TBool);
    ty_size_positive(Ty::TArrow { t1: Box::new(Ty::TBool), t2: Box::new(Ty::TNat) });

    base_types_in_size_one();
    gen_type_size_zero();
    gen_type_size_one();

    base_type_weight();

    example_type_sizes();
    example_type_depths();
    example_generation();
    example_arrows_count();
}

pub fn main() {
    proof {
        gen_type_verify();
    }
}

} // verus!

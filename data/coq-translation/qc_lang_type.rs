use vstd::prelude::*;

verus! {

// ============================================================================
// QC Language Case Study: Types
// Types for a typed imperative language with booleans, naturals, and functions
// ============================================================================

// ----------------------------------------------------------------------------
// Type Definition
// ----------------------------------------------------------------------------

/// Types in our language:
/// - TBool: boolean type
/// - TNat: natural number type
/// - TArrow: function type T1 -> T2
#[derive(PartialEq, Eq)]
pub enum Ty {
    TBool,                                    // Boolean type
    TNat,                                     // Natural number type
    TArrow { t1: Box<Ty>, t2: Box<Ty> },     // Function type: t1 -> t2
}

// ----------------------------------------------------------------------------
// Type Properties
// ----------------------------------------------------------------------------

/// Check if a type is a base type (not a function type)
pub open spec fn is_base_type(ty: Ty) -> bool {
    match ty {
        Ty::TBool => true,
        Ty::TNat => true,
        Ty::TArrow { .. } => false,
    }
}

/// Check if a type is a function type
pub open spec fn is_arrow_type(ty: Ty) -> bool {
    match ty {
        Ty::TArrow { .. } => true,
        _ => false,
    }
}

/// Get the domain type of a function type
pub open spec fn arrow_domain(ty: Ty) -> Ty
    recommends is_arrow_type(ty)
{
    match ty {
        Ty::TArrow { t1, t2: _ } => *t1,
        _ => Ty::TBool,  // arbitrary default
    }
}

/// Get the codomain (return type) of a function type
pub open spec fn arrow_codomain(ty: Ty) -> Ty
    recommends is_arrow_type(ty)
{
    match ty {
        Ty::TArrow { t1: _, t2 } => *t2,
        _ => Ty::TBool,  // arbitrary default
    }
}

// ----------------------------------------------------------------------------
// Type Size (for structural induction)
// ----------------------------------------------------------------------------

/// Size of a type (used for termination proofs)
pub open spec fn ty_size(ty: Ty) -> nat
    decreases ty
{
    match ty {
        Ty::TBool => 1,
        Ty::TNat => 1,
        Ty::TArrow { t1, t2 } => 1 + ty_size(*t1) + ty_size(*t2),
    }
}

/// Type size is always positive
pub proof fn ty_size_positive(ty: Ty)
    ensures ty_size(ty) >= 1
    decreases ty
{
    match ty {
        Ty::TBool => {}
        Ty::TNat => {}
        Ty::TArrow { t1, t2 } => {
            ty_size_positive(*t1);
            ty_size_positive(*t2);
        }
    }
}

// ----------------------------------------------------------------------------
// Type Equality (decidable)
// ----------------------------------------------------------------------------

/// Decidable type equality
pub open spec fn ty_eq(ty1: Ty, ty2: Ty) -> bool {
    ty1 == ty2
}

/// Type equality is decidable
pub proof fn ty_eq_decidable(ty1: Ty, ty2: Ty)
    ensures ty_eq(ty1, ty2) || !ty_eq(ty1, ty2)
{
}

/// Type equality is reflexive
pub proof fn ty_eq_refl(ty: Ty)
    ensures ty_eq(ty, ty)
{
}

/// Type equality is symmetric
pub proof fn ty_eq_sym(ty1: Ty, ty2: Ty)
    requires ty_eq(ty1, ty2)
    ensures ty_eq(ty2, ty1)
{
}

/// Type equality is transitive
pub proof fn ty_eq_trans(ty1: Ty, ty2: Ty, ty3: Ty)
    requires
        ty_eq(ty1, ty2),
        ty_eq(ty2, ty3),
    ensures ty_eq(ty1, ty3)
{
}

// ----------------------------------------------------------------------------
// Type Constructors as Spec Functions
// ----------------------------------------------------------------------------

/// Construct a boolean type
pub open spec fn bool_type() -> Ty {
    Ty::TBool
}

/// Construct a natural number type
pub open spec fn nat_type() -> Ty {
    Ty::TNat
}

/// Construct a function type
pub open spec fn arrow_type(t1: Ty, t2: Ty) -> Ty {
    Ty::TArrow { t1: Box::new(t1), t2: Box::new(t2) }
}

// ----------------------------------------------------------------------------
// Type Depth (maximum nesting of arrows)
// ----------------------------------------------------------------------------

/// Depth of arrow nesting
pub open spec fn ty_depth(ty: Ty) -> nat
    decreases ty
{
    match ty {
        Ty::TBool => 0,
        Ty::TNat => 0,
        Ty::TArrow { t1, t2 } => {
            let d1 = ty_depth(*t1);
            let d2 = ty_depth(*t2);
            1 + if d1 > d2 { d1 } else { d2 }
        }
    }
}

/// Base types have depth 0
pub proof fn base_type_depth_zero(ty: Ty)
    requires is_base_type(ty)
    ensures ty_depth(ty) == 0
{
}

// ----------------------------------------------------------------------------
// Common Type Patterns
// ----------------------------------------------------------------------------

/// Identity function type: T -> T
pub open spec fn id_type(ty: Ty) -> Ty {
    arrow_type(ty, ty)
}

/// Constant function type: T1 -> T2 -> T1
pub open spec fn const_type(t1: Ty, t2: Ty) -> Ty {
    arrow_type(t1, arrow_type(t2, t1))
}

/// Binary operation type: T -> T -> T
pub open spec fn binop_type(ty: Ty) -> Ty {
    arrow_type(ty, arrow_type(ty, ty))
}

/// Predicate type: T -> Bool
pub open spec fn pred_type(ty: Ty) -> Ty {
    arrow_type(ty, bool_type())
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

/// Example: Base types
pub proof fn example_base_types()
{
    assert(is_base_type(Ty::TBool));
    assert(is_base_type(Ty::TNat));
    assert(!is_base_type(arrow_type(Ty::TBool, Ty::TNat)));
}

/// Example: Arrow types
pub proof fn example_arrow_types()
{
    let arr = arrow_type(Ty::TBool, Ty::TNat);
    assert(is_arrow_type(arr));
    assert(arrow_domain(arr) == Ty::TBool);
    assert(arrow_codomain(arr) == Ty::TNat);
}

/// Example: Type size
pub proof fn example_ty_size()
{
    assert(ty_size(Ty::TBool) == 1);
    assert(ty_size(Ty::TNat) == 1);
    let arr = arrow_type(Ty::TBool, Ty::TNat);
    assert(ty_size(arr) == 3);
}

/// Example: Type depth
pub proof fn example_ty_depth()
{
    assert(ty_depth(Ty::TBool) == 0);
    assert(ty_depth(Ty::TNat) == 0);
    let arr = arrow_type(Ty::TBool, Ty::TNat);
    assert(ty_depth(arr) == 1);
    let nested = arrow_type(arr, Ty::TBool);
    assert(ty_depth(nested) == 2);
}

/// Example: Type equality
pub proof fn example_ty_equality()
{
    assert(ty_eq(Ty::TBool, Ty::TBool));
    assert(!ty_eq(Ty::TBool, Ty::TNat));
    assert(ty_eq(arrow_type(Ty::TBool, Ty::TNat), arrow_type(Ty::TBool, Ty::TNat)));
}

/// Example: Common type patterns
pub proof fn example_type_patterns()
{
    // Identity on Bool: Bool -> Bool
    let id_bool = id_type(Ty::TBool);
    assert(arrow_domain(id_bool) == Ty::TBool);
    assert(arrow_codomain(id_bool) == Ty::TBool);

    // Predicate on Nat: Nat -> Bool
    let is_zero = pred_type(Ty::TNat);
    assert(arrow_domain(is_zero) == Ty::TNat);
    assert(arrow_codomain(is_zero) == Ty::TBool);
}

/// Example: Curried function types
pub proof fn example_curried_types()
{
    // Nat -> Nat -> Nat (binary operation on Nat)
    let add_type = binop_type(Ty::TNat);
    assert(is_arrow_type(add_type));
    assert(arrow_domain(add_type) == Ty::TNat);

    let inner = arrow_codomain(add_type);
    assert(is_arrow_type(inner));
    assert(arrow_domain(inner) == Ty::TNat);
    assert(arrow_codomain(inner) == Ty::TNat);
}

// ----------------------------------------------------------------------------
// Type Well-formedness (trivially true for our simple types)
// ----------------------------------------------------------------------------

/// All types in our language are well-formed
pub open spec fn well_formed(ty: Ty) -> bool {
    true  // Our type syntax ensures well-formedness
}

pub proof fn all_types_well_formed(ty: Ty)
    ensures well_formed(ty)
{
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_lang_type_examples_verify()
{
    example_base_types();
    example_arrow_types();
    example_ty_size();
    example_ty_depth();
    example_ty_equality();
    example_type_patterns();
    example_curried_types();

    // Property proofs
    ty_size_positive(Ty::TBool);
    ty_size_positive(arrow_type(Ty::TNat, Ty::TBool));
    ty_eq_refl(Ty::TBool);
    base_type_depth_zero(Ty::TBool);
    all_types_well_formed(Ty::TNat);
}

pub fn main() {
    proof {
        qc_lang_type_examples_verify();
    }
}

} // verus!

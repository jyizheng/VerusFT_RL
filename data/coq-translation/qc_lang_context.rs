use vstd::prelude::*;
use vstd::map::*;

verus! {

// ============================================================================
// QC Language Case Study: Typing Contexts
// Maps from identifiers to types for type checking
// ============================================================================

broadcast use group_map_axioms;

// ----------------------------------------------------------------------------
// Type Definitions (copied for self-contained file)
// ----------------------------------------------------------------------------

pub type Id = nat;

pub spec const X_ID: Id = 0;
pub spec const Y_ID: Id = 1;
pub spec const Z_ID: Id = 2;
pub spec const F_ID: Id = 3;

#[derive(PartialEq, Eq)]
pub enum Ty {
    TBool,
    TNat,
    TArrow { t1: Box<Ty>, t2: Box<Ty> },
}

pub open spec fn arrow_type(t1: Ty, t2: Ty) -> Ty {
    Ty::TArrow { t1: Box::new(t1), t2: Box::new(t2) }
}

// ----------------------------------------------------------------------------
// Typing Context
// ----------------------------------------------------------------------------

/// A typing context maps variable identifiers to their types.
/// Also called a type environment or symbol table.
pub type Context = Map<Id, Ty>;

/// The empty context (no variable bindings)
pub open spec fn empty_ctx() -> Context {
    Map::<Id, Ty>::empty()
}

/// Extend a context with a new binding
pub open spec fn ctx_extend(ctx: Context, x: Id, ty: Ty) -> Context {
    ctx.insert(x, ty)
}

/// Look up a variable's type in the context
pub open spec fn ctx_lookup(ctx: Context, x: Id) -> Option<Ty> {
    if ctx.dom().contains(x) {
        Option::Some(ctx[x])
    } else {
        Option::None
    }
}

/// Check if a variable is bound in the context
pub open spec fn ctx_contains(ctx: Context, x: Id) -> bool {
    ctx.dom().contains(x)
}

/// Remove a binding from the context
pub open spec fn ctx_remove(ctx: Context, x: Id) -> Context {
    ctx.remove(x)
}

// ----------------------------------------------------------------------------
// Context Properties
// ----------------------------------------------------------------------------

/// Empty context contains no bindings
pub proof fn empty_ctx_is_empty()
    ensures forall|x: Id| !ctx_contains(empty_ctx(), x)
{
    assert forall|x: Id| !ctx_contains(empty_ctx(), x) by {
        assert(!Map::<Id, Ty>::empty().dom().contains(x));
    }
}

/// Extension adds the binding
pub proof fn ctx_extend_contains(ctx: Context, x: Id, ty: Ty)
    ensures ctx_contains(ctx_extend(ctx, x, ty), x)
{
    assert(ctx.insert(x, ty).dom().contains(x));
}

/// Extension preserves the type
pub proof fn ctx_extend_lookup(ctx: Context, x: Id, ty: Ty)
    ensures ctx_lookup(ctx_extend(ctx, x, ty), x) == Option::Some(ty)
{
    assert(ctx.insert(x, ty).dom().contains(x));
    assert(ctx.insert(x, ty)[x] == ty);
}

/// Extension doesn't affect other bindings
pub proof fn ctx_extend_other(ctx: Context, x: Id, y: Id, ty: Ty)
    requires x != y
    ensures ctx_lookup(ctx_extend(ctx, x, ty), y) == ctx_lookup(ctx, y)
{
    if ctx.dom().contains(y) {
        assert(ctx.insert(x, ty).dom().contains(y));
        assert(ctx.insert(x, ty)[y] == ctx[y]);
    } else {
        assert(!ctx.insert(x, ty).dom().contains(y));
    }
}

/// Remove eliminates the binding
pub proof fn ctx_remove_eliminates(ctx: Context, x: Id)
    ensures !ctx_contains(ctx_remove(ctx, x), x)
{
    assert(!ctx.remove(x).dom().contains(x));
}

// ----------------------------------------------------------------------------
// Context Inclusion (Subcontext)
// ----------------------------------------------------------------------------

/// Context ctx1 is included in ctx2 if all bindings in ctx1 are in ctx2
pub open spec fn ctx_included(ctx1: Context, ctx2: Context) -> bool {
    forall|x: Id| ctx_contains(ctx1, x) ==> ctx_contains(ctx2, x) && ctx1[x] == ctx2[x]
}

/// Empty context is included in any context
pub proof fn empty_ctx_included(ctx: Context)
    ensures ctx_included(empty_ctx(), ctx)
{
    assert forall|x: Id| ctx_contains(empty_ctx(), x) implies ctx_contains(ctx, x) && empty_ctx()[x] == ctx[x] by {
        assert(!ctx_contains(empty_ctx(), x));
    }
}

/// Inclusion is reflexive
pub proof fn ctx_included_refl(ctx: Context)
    ensures ctx_included(ctx, ctx)
{
}

/// Inclusion is transitive
pub proof fn ctx_included_trans(ctx1: Context, ctx2: Context, ctx3: Context)
    requires
        ctx_included(ctx1, ctx2),
        ctx_included(ctx2, ctx3),
    ensures ctx_included(ctx1, ctx3)
{
}

/// Extension preserves inclusion
pub proof fn ctx_extend_preserves_inclusion(ctx1: Context, ctx2: Context, x: Id, ty: Ty)
    requires
        ctx_included(ctx1, ctx2),
        !ctx_contains(ctx1, x),
    ensures ctx_included(ctx1, ctx_extend(ctx2, x, ty))
{
    assert forall|y: Id| ctx_contains(ctx1, y) implies ctx_contains(ctx_extend(ctx2, x, ty), y) && ctx1[y] == ctx_extend(ctx2, x, ty)[y] by {
        if ctx_contains(ctx1, y) {
            assert(y != x);  // Because !ctx_contains(ctx1, x)
            assert(ctx_contains(ctx2, y));
            assert(ctx1[y] == ctx2[y]);
            assert(ctx_extend(ctx2, x, ty)[y] == ctx2[y]);
        }
    }
}

// ----------------------------------------------------------------------------
// Context Size
// ----------------------------------------------------------------------------

/// Number of bindings in the context
/// Note: Using dom() which returns a Set<Id>, we'd need finite sets to count
/// For now, we use a simple spec function placeholder
pub open spec fn ctx_size(ctx: Context) -> nat {
    0  // Placeholder - Verus Maps don't have a direct size method
}

// ----------------------------------------------------------------------------
// Context Agreement
// ----------------------------------------------------------------------------

/// Two contexts agree on a set of variables
pub open spec fn ctx_agree(ctx1: Context, ctx2: Context, vars: Set<Id>) -> bool {
    forall|x: Id| vars.contains(x) ==>
        (ctx_contains(ctx1, x) <==> ctx_contains(ctx2, x)) &&
        (ctx_contains(ctx1, x) ==> ctx1[x] == ctx2[x])
}

/// Agreement is reflexive
pub proof fn ctx_agree_refl(ctx: Context, vars: Set<Id>)
    ensures ctx_agree(ctx, ctx, vars)
{
}

/// Agreement is symmetric
pub proof fn ctx_agree_sym(ctx1: Context, ctx2: Context, vars: Set<Id>)
    requires ctx_agree(ctx1, ctx2, vars)
    ensures ctx_agree(ctx2, ctx1, vars)
{
}

// ----------------------------------------------------------------------------
// Useful Context Operations
// ----------------------------------------------------------------------------

/// Extend context with multiple bindings from a sequence
pub open spec fn ctx_extend_many(ctx: Context, bindings: Seq<(Id, Ty)>) -> Context
    decreases bindings.len()
{
    if bindings.len() == 0 {
        ctx
    } else {
        let (x, ty) = bindings[0];
        ctx_extend_many(ctx_extend(ctx, x, ty), bindings.skip(1))
    }
}

/// Create a context from a sequence of bindings
pub open spec fn ctx_from_bindings(bindings: Seq<(Id, Ty)>) -> Context {
    ctx_extend_many(empty_ctx(), bindings)
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

/// Example: Empty context
pub proof fn example_empty_ctx()
{
    empty_ctx_is_empty();
    assert(!ctx_contains(empty_ctx(), X_ID));
    assert(ctx_lookup(empty_ctx(), X_ID) == Option::<Ty>::None);
}

/// Example: Single binding
pub proof fn example_single_binding()
{
    let ctx = ctx_extend(empty_ctx(), X_ID, Ty::TBool);
    ctx_extend_contains(empty_ctx(), X_ID, Ty::TBool);
    assert(ctx_contains(ctx, X_ID));
    assert(ctx_lookup(ctx, X_ID) == Option::Some(Ty::TBool));
    assert(!ctx_contains(ctx, Y_ID));
}

/// Example: Multiple bindings
pub proof fn example_multiple_bindings()
{
    let ctx1 = ctx_extend(empty_ctx(), X_ID, Ty::TBool);
    let ctx2 = ctx_extend(ctx1, Y_ID, Ty::TNat);

    assert(ctx_contains(ctx2, X_ID));
    assert(ctx_contains(ctx2, Y_ID));
    assert(ctx_lookup(ctx2, X_ID) == Option::Some(Ty::TBool));
    assert(ctx_lookup(ctx2, Y_ID) == Option::Some(Ty::TNat));
}

/// Example: Shadowing
pub proof fn example_shadowing()
{
    let ctx1 = ctx_extend(empty_ctx(), X_ID, Ty::TBool);
    let ctx2 = ctx_extend(ctx1, X_ID, Ty::TNat);

    // The new binding shadows the old one
    assert(ctx_lookup(ctx2, X_ID) == Option::Some(Ty::TNat));
}

/// Example: Function type in context
pub proof fn example_function_type_in_ctx()
{
    let fn_type = arrow_type(Ty::TNat, Ty::TBool);
    let ctx = ctx_extend(empty_ctx(), F_ID, fn_type);

    assert(ctx_contains(ctx, F_ID));
    assert(ctx_lookup(ctx, F_ID) == Option::Some(fn_type));
}

/// Example: Context inclusion
pub proof fn example_ctx_inclusion()
{
    let ctx1 = ctx_extend(empty_ctx(), X_ID, Ty::TBool);
    let ctx2 = ctx_extend(ctx1, Y_ID, Ty::TNat);

    // ctx1 is included in ctx2
    assert forall|x: Id| ctx_contains(ctx1, x) implies ctx_contains(ctx2, x) && ctx1[x] == ctx2[x] by {
        if ctx_contains(ctx1, x) {
            if x == X_ID {
                assert(ctx_contains(ctx2, X_ID));
                assert(ctx1[X_ID] == ctx2[X_ID]);
            }
        }
    }
    assert(ctx_included(ctx1, ctx2));
}

/// Example: Remove binding
pub proof fn example_remove_binding()
{
    let ctx1 = ctx_extend(empty_ctx(), X_ID, Ty::TBool);
    let ctx2 = ctx_extend(ctx1, Y_ID, Ty::TNat);
    let ctx3 = ctx_remove(ctx2, X_ID);

    ctx_remove_eliminates(ctx2, X_ID);
    assert(!ctx_contains(ctx3, X_ID));
    assert(ctx_contains(ctx3, Y_ID));
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_lang_context_examples_verify()
{
    example_empty_ctx();
    example_single_binding();
    example_multiple_bindings();
    example_shadowing();
    example_function_type_in_ctx();
    example_ctx_inclusion();
    example_remove_binding();

    // Property proofs
    empty_ctx_is_empty();
    ctx_extend_contains(empty_ctx(), X_ID, Ty::TBool);
    ctx_extend_lookup(empty_ctx(), X_ID, Ty::TBool);
    ctx_extend_other(empty_ctx(), X_ID, Y_ID, Ty::TBool);

    // Inclusion properties
    empty_ctx_included(empty_ctx());
    ctx_included_refl(empty_ctx());

    // Agreement properties
    ctx_agree_refl(empty_ctx(), Set::empty());
}

pub fn main() {
    proof {
        qc_lang_context_examples_verify();
    }
}

} // verus!

use vstd::prelude::*;

verus! {

// ============================================================================
// QC: Tree Generators (QuickChick-style)
// Specification functions modeling tree generation with sized generation
// ============================================================================

// ----------------------------------------------------------------------------
// Tree Type Definition
// ----------------------------------------------------------------------------

pub enum Tree<T> {
    Leaf,
    Node { left: Box<Tree<T>>, value: T, right: Box<Tree<T>> },
}

// ----------------------------------------------------------------------------
// Tree Size and Height
// ----------------------------------------------------------------------------

/// Number of nodes in tree
pub open spec fn tree_size<T>(t: Tree<T>) -> nat
    decreases t
{
    match t {
        Tree::Leaf => 0,
        Tree::Node { left, value: _, right } =>
            1 + tree_size(*left) + tree_size(*right),
    }
}

/// Height of tree
pub open spec fn tree_height<T>(t: Tree<T>) -> nat
    decreases t
{
    match t {
        Tree::Leaf => 0,
        Tree::Node { left, value: _, right } => {
            let lh = tree_height(*left);
            let rh = tree_height(*right);
            1 + if lh > rh { lh } else { rh }
        }
    }
}

// ----------------------------------------------------------------------------
// Core Tree Generator Model
// ----------------------------------------------------------------------------

/// Generate all trees with values from inner set and size <= max_size
pub open spec fn gen_tree_outputs<T>(inner_outputs: Set<T>, max_size: nat) -> Set<Tree<T>> {
    Set::new(|t: Tree<T>|
        tree_size(t) <= max_size &&
        all_values_from(t, inner_outputs)
    )
}

/// Check if all values in tree come from given set
pub open spec fn all_values_from<T>(t: Tree<T>, values: Set<T>) -> bool
    decreases t
{
    match t {
        Tree::Leaf => true,
        Tree::Node { left, value, right } =>
            values.contains(value) &&
            all_values_from(*left, values) &&
            all_values_from(*right, values),
    }
}

/// Generate trees with exact size
pub open spec fn gen_tree_exact_size<T>(inner_outputs: Set<T>, size: nat) -> Set<Tree<T>> {
    Set::new(|t: Tree<T>|
        tree_size(t) == size &&
        all_values_from(t, inner_outputs)
    )
}

/// Generate trees with max height
pub open spec fn gen_tree_max_height<T>(inner_outputs: Set<T>, max_height: nat) -> Set<Tree<T>> {
    Set::new(|t: Tree<T>|
        tree_height(t) <= max_height &&
        all_values_from(t, inner_outputs)
    )
}

// ----------------------------------------------------------------------------
// Sized Generation (QuickChick-style)
// ----------------------------------------------------------------------------

/// Sized tree generator: produces trees of size at most 'size' parameter
/// This models QuickChick's sized combinator for recursive types
pub open spec fn gen_tree_sized<T>(inner_outputs: Set<T>, size: nat) -> Set<Tree<T>>
    decreases size
{
    if size == 0 {
        set![Tree::Leaf]
    } else {
        Set::new(|t: Tree<T>| match t {
            Tree::Leaf => true,
            Tree::Node { left, value, right } =>
                inner_outputs.contains(value) &&
                gen_tree_sized(inner_outputs, (size - 1) as nat).contains(*left) &&
                gen_tree_sized(inner_outputs, (size - 1) as nat).contains(*right),
        })
    }
}

// ----------------------------------------------------------------------------
// Generator Properties
// ----------------------------------------------------------------------------

/// Leaf is always generable
pub proof fn gen_tree_contains_leaf<T>(inner_outputs: Set<T>, max_size: nat)
    ensures gen_tree_outputs(inner_outputs, max_size).contains(Tree::Leaf)
{
}

/// Size 0 trees are only leaves
pub proof fn gen_tree_size_0_is_leaf<T>(inner_outputs: Set<T>, t: Tree<T>)
    requires gen_tree_exact_size(inner_outputs, 0nat).contains(t)
    ensures t == Tree::<T>::Leaf
{
    reveal_with_fuel(tree_size, 2);
}

/// Generated trees respect size bound
pub proof fn gen_tree_respects_size<T>(inner_outputs: Set<T>, max_size: nat, t: Tree<T>)
    requires gen_tree_outputs(inner_outputs, max_size).contains(t)
    ensures tree_size(t) <= max_size
{
}

/// All values in generated tree are from inner set
pub proof fn gen_tree_values_valid<T>(inner_outputs: Set<T>, max_size: nat, t: Tree<T>)
    requires gen_tree_outputs(inner_outputs, max_size).contains(t)
    ensures all_values_from(t, inner_outputs)
{
}

/// Sized generator at 0 only produces Leaf
pub proof fn gen_tree_sized_0<T>(inner_outputs: Set<T>)
    ensures gen_tree_sized(inner_outputs, 0nat) =~= set![Tree::Leaf]
{
}

/// Sized generator contains Leaf for all sizes
pub proof fn gen_tree_sized_has_leaf<T>(inner_outputs: Set<T>, size: nat)
    ensures gen_tree_sized(inner_outputs, size).contains(Tree::Leaf)
    decreases size
{
    if size == 0 {
        // Base case: set![Tree::Leaf] contains Tree::Leaf
    } else {
        // Inductive case: Leaf matches the first branch of the match
    }
}

// ----------------------------------------------------------------------------
// Tree Combinators
// ----------------------------------------------------------------------------

/// Map values in tree
pub open spec fn tree_map<T, U>(t: Tree<T>, f: spec_fn(T) -> U) -> Tree<U>
    decreases t
{
    match t {
        Tree::Leaf => Tree::Leaf,
        Tree::Node { left, value, right } =>
            Tree::Node {
                left: Box::new(tree_map(*left, f)),
                value: f(value),
                right: Box::new(tree_map(*right, f)),
            },
    }
}

/// Map preserves structure
pub proof fn tree_map_preserves_size<T, U>(t: Tree<T>, f: spec_fn(T) -> U)
    ensures tree_size(tree_map(t, f)) == tree_size(t)
    decreases t
{
    reveal_with_fuel(tree_size, 2);
    reveal_with_fuel(tree_map, 2);
    match t {
        Tree::Leaf => {}
        Tree::Node { left, value: _, right } => {
            tree_map_preserves_size(*left, f);
            tree_map_preserves_size(*right, f);
        }
    }
}

/// Generator map
pub open spec fn gen_tree_map<T, U>(
    outputs: Set<Tree<T>>,
    f: spec_fn(T) -> U
) -> Set<Tree<U>> {
    Set::new(|t: Tree<U>| exists|s: Tree<T>| outputs.contains(s) && t == tree_map(s, f))
}

// ----------------------------------------------------------------------------
// Balanced Tree Generators
// ----------------------------------------------------------------------------

/// Check if tree is balanced (heights differ by at most 1)
pub open spec fn is_balanced<T>(t: Tree<T>) -> bool
    decreases t
{
    match t {
        Tree::Leaf => true,
        Tree::Node { left, value: _, right } => {
            let lh = tree_height(*left);
            let rh = tree_height(*right);
            is_balanced(*left) &&
            is_balanced(*right) &&
            (if lh > rh { lh - rh } else { rh - lh }) <= 1
        }
    }
}

/// Generate balanced trees
pub open spec fn gen_balanced_tree<T>(inner_outputs: Set<T>, max_height: nat) -> Set<Tree<T>> {
    Set::new(|t: Tree<T>|
        is_balanced(t) &&
        tree_height(t) <= max_height &&
        all_values_from(t, inner_outputs)
    )
}

/// Leaf is balanced
pub proof fn leaf_is_balanced<T>()
    ensures is_balanced::<T>(Tree::Leaf)
{
}

// ----------------------------------------------------------------------------
// Perfect Tree Generators
// ----------------------------------------------------------------------------

/// Check if tree is perfect (all leaves at same depth)
pub open spec fn is_perfect<T>(t: Tree<T>) -> bool
    decreases t
{
    match t {
        Tree::Leaf => true,
        Tree::Node { left, value: _, right } =>
            tree_height(*left) == tree_height(*right) &&
            is_perfect(*left) &&
            is_perfect(*right),
    }
}

/// Generate perfect trees
pub open spec fn gen_perfect_tree<T>(inner_outputs: Set<T>, height: nat) -> Set<Tree<T>> {
    Set::new(|t: Tree<T>|
        is_perfect(t) &&
        tree_height(t) == height &&
        all_values_from(t, inner_outputs)
    )
}

/// Perfect trees are balanced
pub proof fn perfect_implies_balanced<T>(t: Tree<T>)
    requires is_perfect(t)
    ensures is_balanced(t)
    decreases t
{
    reveal_with_fuel(is_perfect, 2);
    reveal_with_fuel(is_balanced, 2);
    reveal_with_fuel(tree_height, 2);
    match t {
        Tree::Leaf => {}
        Tree::Node { left, value: _, right } => {
            perfect_implies_balanced(*left);
            perfect_implies_balanced(*right);
        }
    }
}

// ----------------------------------------------------------------------------
// BST Generator
// ----------------------------------------------------------------------------

/// Check if tree is a valid BST
pub open spec fn is_bst(t: Tree<nat>, lo: nat, hi: nat) -> bool
    decreases t
{
    match t {
        Tree::Leaf => true,
        Tree::Node { left, value, right } =>
            lo <= value && value < hi &&
            is_bst(*left, lo, value) &&
            is_bst(*right, value + 1, hi),
    }
}

/// Generate BSTs
pub open spec fn gen_bst_outputs(max_size: nat, lo: nat, hi: nat) -> Set<Tree<nat>> {
    Set::new(|t: Tree<nat>|
        tree_size(t) <= max_size &&
        is_bst(t, lo, hi)
    )
}

/// BST generator contains leaf
pub proof fn gen_bst_contains_leaf(max_size: nat, lo: nat, hi: nat)
    ensures gen_bst_outputs(max_size, lo, hi).contains(Tree::Leaf)
{
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_gen_tree_basic()
{
    let inner: Set<nat> = Set::new(|n: nat| n <= 10);

    gen_tree_contains_leaf(inner, 5nat);
    assert(gen_tree_outputs(inner, 5nat).contains(Tree::Leaf));

    // Single node tree
    reveal_with_fuel(tree_size, 3);
    reveal_with_fuel(all_values_from, 2);
    let t: Tree<nat> = Tree::Node {
        left: Box::new(Tree::Leaf),
        value: 5,
        right: Box::new(Tree::Leaf),
    };
    assert(tree_size(t) == 1);
    assert(all_values_from(t, inner));
    assert(gen_tree_outputs(inner, 5nat).contains(t));
}

pub proof fn example_gen_tree_sized()
{
    let inner: Set<nat> = Set::new(|n: nat| n <= 5);

    gen_tree_sized_0(inner);
    gen_tree_sized_has_leaf(inner, 3nat);
    assert(gen_tree_sized(inner, 3nat).contains(Tree::Leaf));
}

pub proof fn example_gen_balanced()
{
    leaf_is_balanced::<nat>();
    assert(is_balanced::<nat>(Tree::Leaf));

    reveal_with_fuel(is_balanced, 3);
    reveal_with_fuel(tree_height, 3);
    let t: Tree<nat> = Tree::Node {
        left: Box::new(Tree::Leaf),
        value: 5,
        right: Box::new(Tree::Leaf),
    };
    assert(is_balanced(t));
}

pub proof fn example_gen_perfect()
{
    reveal_with_fuel(is_perfect, 3);
    reveal_with_fuel(tree_height, 3);

    // Leaf is perfect
    assert(is_perfect::<nat>(Tree::Leaf));

    // Single node is perfect
    let t: Tree<nat> = Tree::Node {
        left: Box::new(Tree::Leaf),
        value: 5,
        right: Box::new(Tree::Leaf),
    };
    assert(is_perfect(t));

    perfect_implies_balanced(t);
}

pub proof fn example_tree_map()
{
    let t: Tree<nat> = Tree::Node {
        left: Box::new(Tree::Leaf),
        value: 5,
        right: Box::new(Tree::Leaf),
    };

    tree_map_preserves_size(t, |n: nat| n * 2);
    let doubled = tree_map(t, |n: nat| n * 2);
    assert(tree_size(doubled) == tree_size(t));
}

pub proof fn example_gen_bst()
{
    gen_bst_contains_leaf(5nat, 0nat, 100nat);
    assert(gen_bst_outputs(5nat, 0nat, 100nat).contains(Tree::Leaf));

    reveal_with_fuel(tree_size, 3);
    reveal_with_fuel(is_bst, 3);
    let t: Tree<nat> = Tree::Node {
        left: Box::new(Tree::Leaf),
        value: 50,
        right: Box::new(Tree::Leaf),
    };
    assert(tree_size(t) == 1);
    assert(is_bst(t, 0nat, 100nat));
    assert(gen_bst_outputs(5nat, 0nat, 100nat).contains(t));
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_gen_tree_verify()
{
    example_gen_tree_basic();
    example_gen_tree_sized();
    example_gen_balanced();
    example_gen_perfect();
    example_tree_map();
    example_gen_bst();
}

pub fn main() {
    proof {
        qc_gen_tree_verify();
    }
}

} // verus!

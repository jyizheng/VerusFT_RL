use vstd::prelude::*;

verus! {

// ============================================================================
// QC: Tree Predicate Decidability (QuickChick-style)
// Models decidable predicates for trees: contains, valid BST
// ============================================================================

// ----------------------------------------------------------------------------
// Decidability Result Type
// ----------------------------------------------------------------------------

pub enum Dec {
    Yes,
    No,
}

pub open spec fn dec_to_bool(d: Dec) -> bool {
    match d {
        Dec::Yes => true,
        Dec::No => false,
    }
}

pub open spec fn bool_to_dec(b: bool) -> Dec {
    if b { Dec::Yes } else { Dec::No }
}

// ----------------------------------------------------------------------------
// Tree Type Definition
// ----------------------------------------------------------------------------

pub enum Tree<T> {
    Leaf,
    Node { left: Box<Tree<T>>, value: T, right: Box<Tree<T>> },
}

// ----------------------------------------------------------------------------
// Tree Contains Decidability
// ----------------------------------------------------------------------------

/// Check if tree contains a value
pub open spec fn tree_contains<T>(t: Tree<T>, x: T, eq: spec_fn(T, T) -> bool) -> bool
    decreases t
{
    match t {
        Tree::Leaf => false,
        Tree::Node { left, value, right } =>
            eq(value, x) ||
            tree_contains(*left, x, eq) ||
            tree_contains(*right, x, eq),
    }
}

/// Tree contains is decidable
pub open spec fn dec_tree_contains<T>(t: Tree<T>, x: T, eq: spec_fn(T, T) -> bool) -> Dec {
    bool_to_dec(tree_contains(t, x, eq))
}

/// Tree contains for nat trees
pub open spec fn dec_tree_contains_nat(t: Tree<nat>, x: nat) -> Dec {
    dec_tree_contains(t, x, |a: nat, b: nat| a == b)
}

// ----------------------------------------------------------------------------
// BST Contains (efficient search)
// ----------------------------------------------------------------------------

/// Check if BST contains a value (using ordering for efficiency)
pub open spec fn bst_contains(t: Tree<nat>, x: nat) -> bool
    decreases t
{
    match t {
        Tree::Leaf => false,
        Tree::Node { left, value, right } =>
            if x == value {
                true
            } else if x < value {
                bst_contains(*left, x)
            } else {
                bst_contains(*right, x)
            },
    }
}

/// BST contains is decidable
pub open spec fn dec_bst_contains(t: Tree<nat>, x: nat) -> Dec {
    bool_to_dec(bst_contains(t, x))
}

// ----------------------------------------------------------------------------
// Valid BST Decidability
// ----------------------------------------------------------------------------

/// Check if tree is a valid BST within bounds
pub open spec fn is_bst_bounded(t: Tree<nat>, lo: int, hi: int) -> bool
    decreases t
{
    match t {
        Tree::Leaf => true,
        Tree::Node { left, value, right } =>
            lo < value && (value as int) < hi &&
            is_bst_bounded(*left, lo, value as int) &&
            is_bst_bounded(*right, value as int, hi),
    }
}

/// Check if tree is a valid BST
pub open spec fn is_bst(t: Tree<nat>) -> bool {
    is_bst_bounded(t, -1, 0x7FFFFFFF) // Use wide bounds
}

/// Valid BST is decidable
pub open spec fn dec_is_bst(t: Tree<nat>) -> Dec {
    bool_to_dec(is_bst(t))
}

// ----------------------------------------------------------------------------
// Tree All/Any Decidability
// ----------------------------------------------------------------------------

/// Check if all values in tree satisfy predicate
pub open spec fn tree_all<T>(t: Tree<T>, p: spec_fn(T) -> bool) -> bool
    decreases t
{
    match t {
        Tree::Leaf => true,
        Tree::Node { left, value, right } =>
            p(value) &&
            tree_all(*left, p) &&
            tree_all(*right, p),
    }
}

/// Tree all is decidable
pub open spec fn dec_tree_all<T>(t: Tree<T>, p: spec_fn(T) -> bool) -> Dec {
    bool_to_dec(tree_all(t, p))
}

/// Check if any value in tree satisfies predicate
pub open spec fn tree_any<T>(t: Tree<T>, p: spec_fn(T) -> bool) -> bool
    decreases t
{
    match t {
        Tree::Leaf => false,
        Tree::Node { left, value, right } =>
            p(value) ||
            tree_any(*left, p) ||
            tree_any(*right, p),
    }
}

/// Tree any is decidable
pub open spec fn dec_tree_any<T>(t: Tree<T>, p: spec_fn(T) -> bool) -> Dec {
    bool_to_dec(tree_any(t, p))
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
// Balanced Tree Decidability
// ----------------------------------------------------------------------------

/// Check if tree is balanced
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

/// Balanced is decidable
pub open spec fn dec_is_balanced<T>(t: Tree<T>) -> Dec {
    bool_to_dec(is_balanced(t))
}

// ----------------------------------------------------------------------------
// Perfect Tree Decidability
// ----------------------------------------------------------------------------

/// Check if tree is perfect
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

/// Perfect is decidable
pub open spec fn dec_is_perfect<T>(t: Tree<T>) -> Dec {
    bool_to_dec(is_perfect(t))
}

// ----------------------------------------------------------------------------
// Soundness Proofs
// ----------------------------------------------------------------------------

/// tree_contains is sound
pub proof fn dec_tree_contains_sound<T>(t: Tree<T>, x: T, eq: spec_fn(T, T) -> bool)
    requires forall|a: T, b: T| #[trigger] eq(a, b) <==> (a == b)
    ensures dec_to_bool(dec_tree_contains(t, x, eq)) <==> tree_contains(t, x, eq)
{
}

/// is_bst is sound for node values
pub proof fn dec_is_bst_sound(t: Tree<nat>)
    ensures dec_to_bool(dec_is_bst(t)) <==> is_bst(t)
{
}

/// is_balanced is sound
pub proof fn dec_is_balanced_sound<T>(t: Tree<T>)
    ensures dec_to_bool(dec_is_balanced(t)) <==> is_balanced(t)
{
}

// ----------------------------------------------------------------------------
// BST Property Proofs
// ----------------------------------------------------------------------------

/// If BST contains x, then tree_contains also finds x
pub proof fn bst_contains_implies_tree_contains(t: Tree<nat>, x: nat)
    requires bst_contains(t, x)
    ensures tree_contains(t, x, |a: nat, b: nat| a == b)
    decreases t
{
    reveal_with_fuel(bst_contains, 3);
    reveal_with_fuel(tree_contains, 3);

    match t {
        Tree::Leaf => {}
        Tree::Node { left, value, right } => {
            if x == value {
            } else if x < value {
                bst_contains_implies_tree_contains(*left, x);
            } else {
                bst_contains_implies_tree_contains(*right, x);
            }
        }
    }
}

// ----------------------------------------------------------------------------
// Leaf Properties
// ----------------------------------------------------------------------------

/// Leaf contains nothing
pub proof fn leaf_contains_nothing<T>(x: T, eq: spec_fn(T, T) -> bool)
    ensures !dec_to_bool(dec_tree_contains(Tree::<T>::Leaf, x, eq))
{
}

/// Leaf is a valid BST
pub proof fn leaf_is_bst()
    ensures dec_to_bool(dec_is_bst(Tree::<nat>::Leaf))
{
}

/// Leaf is balanced
pub proof fn leaf_is_balanced()
    ensures dec_to_bool(dec_is_balanced::<nat>(Tree::Leaf))
{
}

/// Leaf is perfect
pub proof fn leaf_is_perfect()
    ensures dec_to_bool(dec_is_perfect::<nat>(Tree::Leaf))
{
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_dec_tree_contains()
{
    reveal_with_fuel(tree_contains, 4);

    let t: Tree<nat> = Tree::Node {
        left: Box::new(Tree::Node {
            left: Box::new(Tree::Leaf),
            value: 2,
            right: Box::new(Tree::Leaf),
        }),
        value: 5,
        right: Box::new(Tree::Node {
            left: Box::new(Tree::Leaf),
            value: 8,
            right: Box::new(Tree::Leaf),
        }),
    };

    assert(dec_to_bool(dec_tree_contains_nat(t, 5)));
    assert(dec_to_bool(dec_tree_contains_nat(t, 2)));
    assert(dec_to_bool(dec_tree_contains_nat(t, 8)));
    assert(!dec_to_bool(dec_tree_contains_nat(t, 10)));
}

pub proof fn example_dec_bst_contains()
{
    reveal_with_fuel(bst_contains, 4);
    reveal_with_fuel(is_bst_bounded, 4);

    let t: Tree<nat> = Tree::Node {
        left: Box::new(Tree::Node {
            left: Box::new(Tree::Leaf),
            value: 2,
            right: Box::new(Tree::Leaf),
        }),
        value: 5,
        right: Box::new(Tree::Node {
            left: Box::new(Tree::Leaf),
            value: 8,
            right: Box::new(Tree::Leaf),
        }),
    };

    assert(is_bst(t));
    assert(dec_to_bool(dec_bst_contains(t, 5)));
    assert(dec_to_bool(dec_bst_contains(t, 2)));
    assert(dec_to_bool(dec_bst_contains(t, 8)));
    assert(!dec_to_bool(dec_bst_contains(t, 10)));
}

pub proof fn example_dec_is_bst()
{
    reveal_with_fuel(is_bst_bounded, 4);

    // Valid BST
    let valid: Tree<nat> = Tree::Node {
        left: Box::new(Tree::Node {
            left: Box::new(Tree::Leaf),
            value: 2,
            right: Box::new(Tree::Leaf),
        }),
        value: 5,
        right: Box::new(Tree::Node {
            left: Box::new(Tree::Leaf),
            value: 8,
            right: Box::new(Tree::Leaf),
        }),
    };
    assert(dec_to_bool(dec_is_bst(valid)));

    // Invalid BST (left child > parent)
    let invalid: Tree<nat> = Tree::Node {
        left: Box::new(Tree::Node {
            left: Box::new(Tree::Leaf),
            value: 10,  // 10 > 5, violates BST
            right: Box::new(Tree::Leaf),
        }),
        value: 5,
        right: Box::new(Tree::Leaf),
    };
    assert(!dec_to_bool(dec_is_bst(invalid)));
}

pub proof fn example_dec_tree_all_any()
{
    reveal_with_fuel(tree_all, 4);
    reveal_with_fuel(tree_any, 4);

    let t: Tree<nat> = Tree::Node {
        left: Box::new(Tree::Node {
            left: Box::new(Tree::Leaf),
            value: 2,
            right: Box::new(Tree::Leaf),
        }),
        value: 4,
        right: Box::new(Tree::Node {
            left: Box::new(Tree::Leaf),
            value: 6,
            right: Box::new(Tree::Leaf),
        }),
    };

    // All elements are even
    let is_even = |n: nat| n % 2 == 0;
    assert(dec_to_bool(dec_tree_all(t, is_even)));

    // Any element > 5
    let gt_five = |n: nat| n > 5;
    assert(dec_to_bool(dec_tree_any(t, gt_five)));

    // Not all elements > 5
    assert(!dec_to_bool(dec_tree_all(t, gt_five)));
}

pub proof fn example_dec_balanced()
{
    reveal_with_fuel(is_balanced, 4);
    reveal_with_fuel(tree_height, 4);

    let balanced: Tree<nat> = Tree::Node {
        left: Box::new(Tree::Node {
            left: Box::new(Tree::Leaf),
            value: 2,
            right: Box::new(Tree::Leaf),
        }),
        value: 5,
        right: Box::new(Tree::Node {
            left: Box::new(Tree::Leaf),
            value: 8,
            right: Box::new(Tree::Leaf),
        }),
    };
    assert(dec_to_bool(dec_is_balanced(balanced)));

    // This tree is also balanced (heights differ by 1)
    let also_balanced: Tree<nat> = Tree::Node {
        left: Box::new(Tree::Node {
            left: Box::new(Tree::Node {
                left: Box::new(Tree::Leaf),
                value: 1,
                right: Box::new(Tree::Leaf),
            }),
            value: 2,
            right: Box::new(Tree::Leaf),
        }),
        value: 5,
        right: Box::new(Tree::Node {
            left: Box::new(Tree::Leaf),
            value: 8,
            right: Box::new(Tree::Leaf),
        }),
    };
    assert(dec_to_bool(dec_is_balanced(also_balanced)));
}

pub proof fn example_dec_perfect()
{
    reveal_with_fuel(is_perfect, 4);
    reveal_with_fuel(tree_height, 4);

    // Perfect tree (complete binary tree)
    let perfect: Tree<nat> = Tree::Node {
        left: Box::new(Tree::Node {
            left: Box::new(Tree::Leaf),
            value: 2,
            right: Box::new(Tree::Leaf),
        }),
        value: 5,
        right: Box::new(Tree::Node {
            left: Box::new(Tree::Leaf),
            value: 8,
            right: Box::new(Tree::Leaf),
        }),
    };
    assert(dec_to_bool(dec_is_perfect(perfect)));

    // Not perfect (unequal subtree heights)
    let not_perfect: Tree<nat> = Tree::Node {
        left: Box::new(Tree::Node {
            left: Box::new(Tree::Node {
                left: Box::new(Tree::Leaf),
                value: 1,
                right: Box::new(Tree::Leaf),
            }),
            value: 2,
            right: Box::new(Tree::Leaf),
        }),
        value: 5,
        right: Box::new(Tree::Leaf),
    };
    assert(!dec_to_bool(dec_is_perfect(not_perfect)));
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_dec_tree_verify()
{
    example_dec_tree_contains();
    example_dec_bst_contains();
    example_dec_is_bst();
    example_dec_tree_all_any();
    example_dec_balanced();
    example_dec_perfect();

    // Verify leaf properties
    leaf_is_bst();
    leaf_is_balanced();
    leaf_is_perfect();
}

pub fn main() {
    proof {
        qc_dec_tree_verify();
    }
}

} // verus!

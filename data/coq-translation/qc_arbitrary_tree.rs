use vstd::prelude::*;

verus! {

// ============================================================================
// QC Arbitrary: Tree Generation
// ============================================================================

#[derive(PartialEq, Eq)]
pub enum Tree {
    Leaf,
    Node { left: Box<Tree>, right: Box<Tree> },
}

pub open spec fn tree_size(t: Tree) -> nat
    decreases t
{
    match t {
        Tree::Leaf => 1,
        Tree::Node { left, right } => 1 + tree_size(*left) + tree_size(*right),
    }
}

pub open spec fn arbitrary_tree_sized(max_size: nat) -> Set<Tree> {
    Set::new(|t: Tree| tree_size(t) <= max_size)
}

pub proof fn leaf_always_arbitrary(max_size: nat)
    requires max_size >= 1
    ensures arbitrary_tree_sized(max_size).contains(Tree::Leaf)
{
    assert(tree_size(Tree::Leaf) == 1);
}

pub proof fn arbitrary_tree_verify()
{
    leaf_always_arbitrary(10);
}

pub fn main() {
    proof { arbitrary_tree_verify(); }
}

} // verus!

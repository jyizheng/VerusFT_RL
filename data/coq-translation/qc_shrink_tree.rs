use vstd::prelude::*;

verus! {

// ============================================================================
// QC Shrink: Tree Shrinking
// ============================================================================

#[derive(PartialEq, Eq)]
pub enum Tree {
    Leaf,
    Node { left: Box<Tree>, right: Box<Tree> },
}

pub open spec fn shrink_tree(t: Tree) -> Seq<Tree>
    decreases t
{
    match t {
        Tree::Leaf => seq![],
        Tree::Node { left, right } => {
            seq![Tree::Leaf, *left, *right]
        }
    }
}

pub proof fn leaf_no_shrinks()
    ensures shrink_tree(Tree::Leaf).len() == 0
{
}

pub proof fn node_shrinks_to_children()
{
    let t = Tree::Node { left: Box::new(Tree::Leaf), right: Box::new(Tree::Leaf) };
    assert(shrink_tree(t).len() == 3);
}

pub proof fn shrink_tree_verify()
{
    leaf_no_shrinks();
    node_shrinks_to_children();
}

pub fn main() {
    proof { shrink_tree_verify(); }
}

} // verus!

use vstd::prelude::*;

verus! {

// ============================================================================
// QC: Sized Generators (QuickChick-style)
// Specification functions modeling sized generation with size parameter
// ============================================================================

// ----------------------------------------------------------------------------
// Sized Generator Concept
// A sized generator takes a size parameter and produces values bounded by it
// ----------------------------------------------------------------------------

/// A sized generator is a function from size to set of possible values
/// This models QuickChick's `sized` combinator
pub open spec fn sized_gen<T>(gen_at_size: spec_fn(nat) -> Set<T>, size: nat) -> Set<T> {
    gen_at_size(size)
}

/// Resize: apply a transformation to the size parameter
pub open spec fn resize<T>(
    gen_at_size: spec_fn(nat) -> Set<T>,
    transform: spec_fn(nat) -> nat,
    size: nat
) -> Set<T> {
    gen_at_size(transform(size))
}

/// Scale: multiply size by a factor (as integer division)
pub open spec fn scale<T>(
    gen_at_size: spec_fn(nat) -> Set<T>,
    numerator: nat,
    denominator: nat,
    size: nat
) -> Set<T>
    recommends denominator > 0
{
    if denominator == 0 {
        gen_at_size(0)
    } else {
        gen_at_size((size * numerator / denominator) as nat)
    }
}

// ----------------------------------------------------------------------------
// Common Size Transformations
// ----------------------------------------------------------------------------

/// Identity sizing (no change)
pub open spec fn size_id(size: nat) -> nat {
    size
}

/// Half the size
pub open spec fn size_half(size: nat) -> nat {
    size / 2
}

/// Double the size (capped)
pub open spec fn size_double(size: nat, cap: nat) -> nat {
    if size * 2 > cap { cap } else { size * 2 }
}

/// Square root of size (approximation)
pub open spec fn size_sqrt(size: nat) -> nat
    decreases size
{
    if size <= 1 {
        size
    } else {
        let guess = size / 2;
        // Simple approximation
        if guess * guess <= size && (guess + 1) * (guess + 1) > size {
            guess
        } else if guess * guess > size {
            size_sqrt(guess)
        } else {
            guess + 1
        }
    }
}

// ----------------------------------------------------------------------------
// Sized Nat Generator
// ----------------------------------------------------------------------------

/// Sized nat generator: values from 0 to size
pub open spec fn gen_nat_sized(size: nat) -> Set<nat> {
    Set::new(|n: nat| n <= size)
}

/// Sized nat respects bound
pub proof fn gen_nat_sized_bounded(size: nat, n: nat)
    requires gen_nat_sized(size).contains(n)
    ensures n <= size
{
}

/// Larger size includes more values
pub proof fn gen_nat_sized_monotonic(size1: nat, size2: nat, n: nat)
    requires size1 <= size2, gen_nat_sized(size1).contains(n)
    ensures gen_nat_sized(size2).contains(n)
{
}

// ----------------------------------------------------------------------------
// Sized List Generator
// ----------------------------------------------------------------------------

/// Sized list generator: lists of length 0 to size with elements 0 to size
pub open spec fn gen_list_sized(size: nat) -> Set<Seq<nat>> {
    Set::new(|s: Seq<nat>|
        s.len() <= size &&
        forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] <= size
    )
}

/// Sized list respects length bound
pub proof fn gen_list_sized_length(size: nat, s: Seq<nat>)
    requires gen_list_sized(size).contains(s)
    ensures s.len() <= size
{
}

/// Sized list contains empty
pub proof fn gen_list_sized_empty(size: nat)
    ensures gen_list_sized(size).contains(Seq::empty())
{
}

// ----------------------------------------------------------------------------
// Sized Tree (Height-bounded)
// ----------------------------------------------------------------------------

pub enum Tree<T> {
    Leaf,
    Node { left: Box<Tree<T>>, value: T, right: Box<Tree<T>> },
}

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

/// Sized tree: height bounded by size
pub open spec fn gen_tree_sized(size: nat) -> Set<Tree<nat>> {
    Set::new(|t: Tree<nat>|
        tree_height(t) <= size &&
        all_values_bounded(t, size)
    )
}

pub open spec fn all_values_bounded(t: Tree<nat>, bound: nat) -> bool
    decreases t
{
    match t {
        Tree::Leaf => true,
        Tree::Node { left, value, right } =>
            value <= bound &&
            all_values_bounded(*left, bound) &&
            all_values_bounded(*right, bound),
    }
}

/// Size 0 only produces Leaf
pub proof fn gen_tree_sized_0()
    ensures forall|t: Tree<nat>| #[trigger] gen_tree_sized(0nat).contains(t) ==> t == Tree::<nat>::Leaf
{
    assert forall|t: Tree<nat>| #[trigger] gen_tree_sized(0nat).contains(t) implies t == Tree::<nat>::Leaf by {
        reveal_with_fuel(tree_height, 2);
        if tree_height(t) == 0 {
            match t {
                Tree::Leaf => {}
                Tree::Node { left: _, value: _, right: _ } => {
                    assert(false);  // Height would be > 0
                }
            }
        }
    }
}

// ----------------------------------------------------------------------------
// Compose Sized Generators
// ----------------------------------------------------------------------------

/// Apply inner generator with outer's size
pub open spec fn sized_compose<T>(
    outer_at_size: spec_fn(nat) -> Set<nat>,
    inner_at_size: spec_fn(nat) -> Set<T>,
    size: nat
) -> Set<T> {
    Set::new(|x: T|
        exists|s: nat| #[trigger] outer_at_size(size).contains(s) && inner_at_size(s).contains(x)
    )
}

/// Pair of sized generators
pub open spec fn sized_pair<A, B>(
    gen_a: spec_fn(nat) -> Set<A>,
    gen_b: spec_fn(nat) -> Set<B>,
    size: nat
) -> Set<(A, B)> {
    Set::new(|p: (A, B)|
        gen_a(size).contains(p.0) && gen_b(size).contains(p.1)
    )
}

/// Sized pair contains pairs from both at same size
pub proof fn sized_pair_membership<A, B>(
    gen_a: spec_fn(nat) -> Set<A>,
    gen_b: spec_fn(nat) -> Set<B>,
    size: nat,
    a: A,
    b: B
)
    requires gen_a(size).contains(a), gen_b(size).contains(b)
    ensures sized_pair(gen_a, gen_b, size).contains((a, b))
{
}

// ----------------------------------------------------------------------------
// Size Shrinking for Recursion
// ----------------------------------------------------------------------------

/// Shrink factor for recursive calls
pub open spec fn shrink_size(size: nat, factor: nat) -> nat
    recommends factor > 0
{
    if factor == 0 || size == 0 {
        0
    } else {
        ((size - 1) as int / factor as int) as nat
    }
}

/// Size shrinks
pub proof fn shrink_decreases(size: nat, factor: nat)
    requires size > 0, factor > 0
    ensures shrink_size(size, factor) < size
{
}

/// Size eventually reaches 0
pub proof fn shrink_reaches_zero(size: nat, factor: nat)
    requires factor >= 1
    ensures shrink_size(0, factor) == 0
{
}

// ----------------------------------------------------------------------------
// QuickCheck-style getSize/resize
// ----------------------------------------------------------------------------

/// Model of getting current size
pub open spec fn get_size(current: nat) -> nat {
    current
}

/// Model of locally resizing
pub open spec fn with_size<T>(gen_at_size: spec_fn(nat) -> Set<T>, new_size: nat) -> Set<T> {
    gen_at_size(new_size)
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_sized_nat()
{
    // Size 5 produces 0-5
    assert(gen_nat_sized(5nat).contains(0nat));
    assert(gen_nat_sized(5nat).contains(5nat));
    assert(!gen_nat_sized(5nat).contains(6nat));

    gen_nat_sized_bounded(5nat, 3nat);

    // Monotonicity
    gen_nat_sized_monotonic(3nat, 5nat, 2nat);
}

pub proof fn example_sized_list()
{
    gen_list_sized_empty(5nat);
    assert(gen_list_sized(5nat).contains(Seq::empty()));

    // Singleton list
    let s = seq![3nat];
    assert(s.len() == 1);
    assert(s.len() <= 5);
    assert forall|i: int| 0 <= i < s.len() implies #[trigger] s[i] <= 5 by {
        assert(s[0] == 3);
    }
    assert(gen_list_sized(5nat).contains(s));
}

pub proof fn example_sized_tree()
{
    gen_tree_sized_0();

    // Leaf at any size
    assert(gen_tree_sized(3nat).contains(Tree::Leaf));
}

pub proof fn example_resize()
{
    // Half-sized nat generator at size 10 produces 0-5
    let gen_fn: spec_fn(nat) -> Set<nat> = |s: nat| gen_nat_sized(s);
    let trans_fn: spec_fn(nat) -> nat = |s: nat| size_half(s);
    let half_sized = resize(gen_fn, trans_fn, 10nat);
    assert(half_sized.contains(5nat));
    assert(!half_sized.contains(6nat));
}

pub proof fn example_scale()
{
    // Scale by 1/2 at size 10 produces 0-5
    let gen_fn: spec_fn(nat) -> Set<nat> = |s: nat| gen_nat_sized(s);
    let scaled = scale(gen_fn, 1nat, 2nat, 10nat);
    assert(scaled.contains(5nat));
    assert(!scaled.contains(6nat));
}

pub proof fn example_shrink()
{
    shrink_decreases(5nat, 2nat);
    assert(shrink_size(5nat, 2nat) < 5);

    shrink_reaches_zero(0nat, 2nat);
    assert(shrink_size(0nat, 2nat) == 0);
}

pub proof fn example_sized_pair()
{
    let gen_fn: spec_fn(nat) -> Set<nat> = |s: nat| gen_nat_sized(s);
    sized_pair_membership(gen_fn, gen_fn, 5nat, 3nat, 4nat);
    assert(sized_pair(gen_fn, gen_fn, 5nat).contains((3nat, 4nat)));
}

pub proof fn example_compose()
{
    // Outer produces sizes 0-5, inner uses those sizes
    let gen_fn: spec_fn(nat) -> Set<nat> = |s: nat| gen_nat_sized(s);
    let composed = sized_compose(gen_fn, gen_fn, 5nat);

    // Size 3 is possible, and 2 is in gen_nat_sized(3)
    assert(gen_nat_sized(5nat).contains(3nat));
    assert(gen_nat_sized(3nat).contains(2nat));
    assert(composed.contains(2nat));
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn qc_gen_sized_verify()
{
    example_sized_nat();
    example_sized_list();
    example_sized_tree();
    example_resize();
    example_scale();
    example_shrink();
    example_sized_pair();
    example_compose();
}

pub fn main() {
    proof {
        qc_gen_sized_verify();
    }
}

} // verus!

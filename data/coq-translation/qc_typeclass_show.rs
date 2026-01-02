use vstd::prelude::*;

verus! {

// ============================================================================
// QC: Show Typeclass (qc-current/Typeclasses)
// Converting values to string representations
// ============================================================================

// String representation as sequence of chars (nat for simplicity)
pub type Str = Seq<nat>;

// Show trait - convert value to string representation
pub trait ShowSpec {
    spec fn show_spec(&self) -> Str;
}

// ----------------------------------------------------------------------------
// Show for Basic Types
// ----------------------------------------------------------------------------

pub open spec fn show_bool(b: bool) -> Str {
    if b { seq![116nat, 114, 117, 101] }  // "true"
    else { seq![102nat, 97, 108, 115, 101] }  // "false"
}

pub open spec fn show_nat_digit(n: nat) -> nat
    recommends n < 10
{
    48 + n  // ASCII '0' = 48
}

pub open spec fn show_nat_helper(n: nat, acc: Str) -> Str
    decreases n
{
    if n == 0 && acc.len() > 0 {
        acc
    } else if n == 0 {
        seq![48nat]  // "0"
    } else {
        let digit = show_nat_digit(n % 10);
        show_nat_helper(n / 10, seq![digit] + acc)
    }
}

pub open spec fn show_nat(n: nat) -> Str {
    show_nat_helper(n, Seq::empty())
}

// ----------------------------------------------------------------------------
// Show for Compound Types
// ----------------------------------------------------------------------------

pub open spec fn show_option<T>(o: Option<T>, show_t: spec_fn(T) -> Str) -> Str {
    match o {
        None => seq![78nat, 111, 110, 101],  // "None"
        Some(x) => seq![83nat, 111, 109, 101, 40] + show_t(x) + seq![41nat],  // "Some(...)"
    }
}

pub open spec fn show_pair<A, B>(p: (A, B), show_a: spec_fn(A) -> Str, show_b: spec_fn(B) -> Str) -> Str {
    seq![40nat] + show_a(p.0) + seq![44nat, 32nat] + show_b(p.1) + seq![41nat]  // "(a, b)"
}

pub open spec fn show_list_helper(s: Seq<nat>, show_elem: spec_fn(nat) -> Str, idx: int) -> Str
    decreases s.len() - idx
{
    if idx >= s.len() {
        Seq::empty()
    } else if idx == s.len() - 1 {
        show_elem(s[idx])
    } else {
        show_elem(s[idx]) + seq![44nat, 32nat] + show_list_helper(s, show_elem, idx + 1)
    }
}

pub open spec fn show_list(s: Seq<nat>, show_elem: spec_fn(nat) -> Str) -> Str {
    seq![91nat] + show_list_helper(s, show_elem, 0) + seq![93nat]  // "[...]"
}

// ----------------------------------------------------------------------------
// Properties
// ----------------------------------------------------------------------------

pub proof fn show_bool_nonempty(b: bool)
    ensures show_bool(b).len() > 0
{
}

pub proof fn show_nat_helper_nonempty(n: nat, acc: Str)
    ensures show_nat_helper(n, acc).len() > 0
    decreases n
{
    reveal_with_fuel(show_nat_helper, 2);
    if n == 0 && acc.len() > 0 {
        // Returns acc, which has len > 0
    } else if n == 0 {
        // Returns seq![48nat] which has len 1
    } else {
        // Recursive case
        let digit = show_nat_digit(n % 10);
        show_nat_helper_nonempty(n / 10, seq![digit] + acc);
    }
}

pub proof fn show_nat_nonempty(n: nat)
    ensures show_nat(n).len() > 0
{
    show_nat_helper_nonempty(n, Seq::empty());
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_show_bool()
{
    assert(show_bool(true).len() == 4);
    assert(show_bool(false).len() == 5);
}

pub proof fn example_show_nat()
{
    reveal_with_fuel(show_nat_helper, 5);
    assert(show_nat(0) =~= seq![48nat]);
}

pub proof fn typeclass_show_verify()
{
    example_show_bool();
    example_show_nat();
}

pub fn main() {
    proof { typeclass_show_verify(); }
}

} // verus!

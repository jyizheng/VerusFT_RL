use vstd::prelude::*;

verus! {

// ============================================================================
// QC Result: Success and Failure Handling
// ============================================================================

#[derive(PartialEq, Eq)]
pub enum Result<A> {
    Success { value: A },
    Failure { reason: nat },
}

pub open spec fn is_success<A>(r: Result<A>) -> bool {
    match r { Result::Success { .. } => true, _ => false }
}

pub open spec fn is_failure<A>(r: Result<A>) -> bool {
    match r { Result::Failure { .. } => true, _ => false }
}

pub open spec fn map_result<A, B>(r: Result<A>, f: spec_fn(A) -> B) -> Result<B> {
    match r {
        Result::Success { value } => Result::Success { value: f(value) },
        Result::Failure { reason } => Result::Failure { reason },
    }
}

pub proof fn success_or_failure<A>(r: Result<A>)
    ensures is_success(r) || is_failure(r)
{
    match r {
        Result::Success { .. } => {}
        Result::Failure { .. } => {}
    }
}

pub proof fn result_success_verify()
{
    let r: Result<nat> = Result::Success { value: 42 };
    assert(is_success(r));
    success_or_failure(r);
}

pub fn main() {
    proof { result_success_verify(); }
}

} // verus!

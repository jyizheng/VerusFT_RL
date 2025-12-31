use vstd::prelude::*;

verus! {

// ============================================================================
// QC Test Data: Test Data Generation Model
// ============================================================================

pub struct TestData<A> {
    pub value: A,
    pub size: nat,
    pub shrinks: Seq<A>,
}

pub open spec fn create_test_data<A>(value: A, size: nat, shrinks: Seq<A>) -> TestData<A> {
    TestData { value, size, shrinks }
}

pub open spec fn map_test_data<A, B>(data: TestData<A>, f: spec_fn(A) -> B) -> TestData<B>
    where A: std::marker::Copy
{
    TestData {
        value: f(data.value),
        size: data.size,
        shrinks: data.shrinks.map(|_i: int, a: A| f(a)),
    }
}

pub proof fn map_preserves_size<A, B>(data: TestData<A>, f: spec_fn(A) -> B)
    where A: std::marker::Copy
    ensures map_test_data(data, f).size == data.size
{
}

pub proof fn map_preserves_shrink_count<A, B>(data: TestData<A>, f: spec_fn(A) -> B)
    where A: std::marker::Copy
    ensures map_test_data(data, f).shrinks.len() == data.shrinks.len()
{
}

pub proof fn test_data_verify()
{
    let data = create_test_data(42nat, 10, seq![0nat, 21]);
    assert(data.size == 10);
    assert(data.shrinks.len() == 2);
}

pub fn main() {
    proof { test_data_verify(); }
}

} // verus!

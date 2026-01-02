use vstd::prelude::*;

verus! {

// ============================================================================
// QC Coverage Analysis: Test Coverage Concepts
// ============================================================================

pub struct CoverageData {
    pub total_branches: nat,
    pub covered_branches: nat,
    pub total_paths: nat,
    pub covered_paths: nat,
}

pub open spec fn branch_coverage(data: CoverageData) -> nat {
    if data.total_branches == 0 { 100 }
    else { (data.covered_branches * 100) / data.total_branches }
}

pub open spec fn path_coverage(data: CoverageData) -> nat {
    if data.total_paths == 0 { 100 }
    else { (data.covered_paths * 100) / data.total_paths }
}

pub open spec fn full_coverage(data: CoverageData) -> bool {
    data.covered_branches == data.total_branches && data.covered_paths == data.total_paths
}

pub proof fn full_coverage_means_100_percent(data: CoverageData)
    requires full_coverage(data), data.total_branches > 0, data.total_paths > 0
    ensures branch_coverage(data) == 100, path_coverage(data) == 100
{
    assert((data.total_branches * 100) / data.total_branches == 100) by(nonlinear_arith)
        requires data.total_branches > 0;
    assert((data.total_paths * 100) / data.total_paths == 100) by(nonlinear_arith)
        requires data.total_paths > 0;
}

pub proof fn coverage_analysis_verify()
{
    let data = CoverageData { total_branches: 10, covered_branches: 10, total_paths: 8, covered_paths: 8 };
    full_coverage_means_100_percent(data);
}

pub fn main() {
    proof { coverage_analysis_verify(); }
}

} // verus!

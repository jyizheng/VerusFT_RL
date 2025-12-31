use vstd::prelude::*;

verus! {

// ============================================================================
// QC Runner: Basic Test Runner Concepts
// ============================================================================
// Models the basic test runner from QuickChick.
// The runner executes tests and collects results.

// ----------------------------------------------------------------------------
// Test Results
// ----------------------------------------------------------------------------

pub ghost enum TestResult {
    Success,
    Failure { counterexample: nat },
    Discarded,
    GaveUp,
}

// Check if result indicates success
pub open spec fn is_success(r: TestResult) -> bool {
    r == TestResult::Success
}

// Check if result indicates failure
pub open spec fn is_failure(r: TestResult) -> bool {
    match r {
        TestResult::Failure { .. } => true,
        _ => false,
    }
}

// Check if result was discarded
pub open spec fn is_discarded(r: TestResult) -> bool {
    r == TestResult::Discarded
}

// ----------------------------------------------------------------------------
// Test Outcome Statistics
// ----------------------------------------------------------------------------

pub struct TestStats {
    pub successful: nat,
    pub failed: nat,
    pub discarded: nat,
    pub total: nat,
}

pub open spec fn empty_stats() -> TestStats {
    TestStats {
        successful: 0,
        failed: 0,
        discarded: 0,
        total: 0,
    }
}

pub open spec fn add_result(stats: TestStats, r: TestResult) -> TestStats {
    TestStats {
        successful: stats.successful + if is_success(r) { 1nat } else { 0nat },
        failed: stats.failed + if is_failure(r) { 1nat } else { 0nat },
        discarded: stats.discarded + if is_discarded(r) { 1nat } else { 0nat },
        total: stats.total + 1,
    }
}

// ----------------------------------------------------------------------------
// Runner Configuration
// ----------------------------------------------------------------------------

pub struct RunnerConfig {
    pub max_success: nat,     // Tests needed for success
    pub max_discard: nat,     // Max discards before giving up
    pub max_shrinks: nat,     // Max shrinking attempts
}

pub open spec fn default_config() -> RunnerConfig {
    RunnerConfig {
        max_success: 100,
        max_discard: 500,
        max_shrinks: 1000,
    }
}

// Check if runner should continue
pub open spec fn should_continue(config: RunnerConfig, stats: TestStats) -> bool {
    stats.successful < config.max_success &&
    stats.failed == 0 &&
    stats.discarded < config.max_discard
}

// Check if testing is complete
pub open spec fn is_complete(config: RunnerConfig, stats: TestStats) -> bool {
    stats.successful >= config.max_success || stats.failed > 0 || stats.discarded >= config.max_discard
}

// ----------------------------------------------------------------------------
// Properties about Runner
// ----------------------------------------------------------------------------

pub proof fn stats_consistency(stats: TestStats, r: TestResult)
    ensures add_result(stats, r).total == stats.total + 1
{
}

pub proof fn continue_means_not_complete(config: RunnerConfig, stats: TestStats)
    requires should_continue(config, stats)
    ensures !is_complete(config, stats)
{
}

pub proof fn complete_means_not_continue(config: RunnerConfig, stats: TestStats)
    requires is_complete(config, stats)
    ensures !should_continue(config, stats)
{
}

// ----------------------------------------------------------------------------
// Test Run Outcome
// ----------------------------------------------------------------------------

pub ghost enum RunOutcome {
    Passed { tests: nat },
    Failed { tests: nat, counterexample: nat },
    GaveUp { tests: nat, discarded: nat },
}

pub open spec fn run_outcome(config: RunnerConfig, stats: TestStats) -> RunOutcome {
    if stats.failed > 0 {
        RunOutcome::Failed { tests: stats.total, counterexample: 0 }
    } else if stats.successful >= config.max_success {
        RunOutcome::Passed { tests: stats.total }
    } else {
        RunOutcome::GaveUp { tests: stats.total, discarded: stats.discarded }
    }
}

// ----------------------------------------------------------------------------
// Examples
// ----------------------------------------------------------------------------

pub proof fn example_empty_stats()
{
    let stats = empty_stats();
    assert(stats.total == 0);
    assert(stats.successful == 0);
    assert(stats.failed == 0);
}

pub proof fn example_add_success()
{
    let stats = empty_stats();
    let stats2 = add_result(stats, TestResult::Success);
    assert(stats2.successful == 1);
    assert(stats2.total == 1);
}

pub proof fn example_should_continue()
{
    let config = default_config();
    let stats = empty_stats();
    assert(should_continue(config, stats));
}

// ============================================================================
// MAIN
// ============================================================================

pub proof fn runner_basic_verify()
{
    let stats = empty_stats();
    stats_consistency(stats, TestResult::Success);

    let config = default_config();
    if should_continue(config, stats) {
        continue_means_not_complete(config, stats);
    }

    example_empty_stats();
    example_add_success();
    example_should_continue();
}

pub fn main() {
    proof { runner_basic_verify(); }
}

} // verus!

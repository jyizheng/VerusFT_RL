use vstd::prelude::*;

verus! {

// ============================================================================
// QC Label Collect: Test Labeling and Statistics Collection
// ============================================================================

pub struct Label {
    pub name: nat,  // Using nat as label identifier
    pub count: nat,
}

pub struct LabelStats {
    pub labels: Seq<Label>,
    pub total_tests: nat,
}

pub open spec fn empty_stats() -> LabelStats {
    LabelStats { labels: Seq::empty(), total_tests: 0 }
}

pub open spec fn add_label(stats: LabelStats, label_id: nat) -> LabelStats {
    LabelStats {
        labels: stats.labels.push(Label { name: label_id, count: 1 }),
        total_tests: stats.total_tests + 1,
    }
}

pub open spec fn count_label(stats: LabelStats, label_id: nat) -> nat
    decreases stats.labels.len()
{
    if stats.labels.len() == 0 {
        0
    } else {
        let last = stats.labels.last();
        let rest = LabelStats { labels: stats.labels.drop_last(), total_tests: stats.total_tests };
        if last.name == label_id {
            last.count + count_label(rest, label_id)
        } else {
            count_label(rest, label_id)
        }
    }
}

pub open spec fn label_percentage(stats: LabelStats, label_id: nat) -> nat {
    if stats.total_tests == 0 { 0 }
    else { (count_label(stats, label_id) * 100) / stats.total_tests }
}

pub proof fn empty_stats_has_no_labels()
    ensures empty_stats().labels.len() == 0
{
}

pub proof fn add_label_increases_count(stats: LabelStats)
    ensures add_label(stats, 0).total_tests == stats.total_tests + 1
{
}

pub proof fn label_collect_verify()
{
    let stats = empty_stats();
    empty_stats_has_no_labels();

    let stats1 = add_label(stats, 1);
    add_label_increases_count(stats);
    assert(stats1.total_tests == 1);
}

pub fn main() {
    proof { label_collect_verify(); }
}

} // verus!

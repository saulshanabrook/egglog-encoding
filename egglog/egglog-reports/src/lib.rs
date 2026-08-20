use clap::clap_derive::ValueEnum;
use rustc_hash::FxHasher;
use serde::Serialize;
use std::{
    collections::BTreeMap,
    fmt::{Display, Formatter},
    hash::BuildHasherDefault,
    sync::Arc,
};
use web_time::Duration;

pub(crate) type HashMap<K, V> = hashbrown::HashMap<K, V, BuildHasherDefault<FxHasher>>;

#[derive(ValueEnum, Default, Serialize, Debug, Clone, Copy)]
pub enum ReportLevel {
    /// Report pre-merge, merge, and rebuild time.
    ///
    /// Pre-merge time is split into search, apply, and unattributed time when
    /// execution can attribute those phases without overlap.
    #[default]
    TimeOnly,
    /// Report [`ReportLevel::TimeOnly`] and query plan for each rule
    WithPlan,
    /// Report [`ReportLevel::WithPlan`] and the detailed statistics at each stage of the query plan.
    StageInfo,
}

#[derive(Serialize, Clone, Debug)]
pub struct SingleScan(pub String, pub (String, i64));
#[derive(Serialize, Clone, Debug)]
pub struct Scan(pub String, pub Vec<(String, i64)>);

#[derive(Serialize, Clone, Debug)]
pub enum Stage {
    Intersect {
        scans: Vec<SingleScan>,
    },
    FusedIntersect {
        cover: Scan,             // build side
        to_intersect: Vec<Scan>, // probe sides
    },
}

#[derive(Serialize, Clone, Debug)]
pub struct StageStats {
    pub num_candidates: usize,
    pub num_succeeded: usize,
}

#[derive(Serialize, Clone, Debug, Default)]
pub struct Plan {
    pub stages: Vec<(
        Stage,
        Option<StageStats>,
        // indices of next stages
        Vec<usize>,
    )>,
}

#[derive(Debug, Serialize, Clone, Default)]
pub struct RuleReport {
    pub plan: Option<Plan>,
    pub search_and_apply_time: Duration,
    // TODO: succeeding matches
    pub num_matches: usize,
}

#[derive(Debug, Serialize, Clone, Default)]
pub struct RuleSetReport {
    pub changed: bool,
    pub rule_reports: HashMap<Arc<str>, Vec<RuleReport>>,
    /// Timed work before staged updates are merged, either as one elapsed
    /// duration or as an exhaustive serial phase breakdown.
    pub pre_merge: PreMergeTiming,
    pub merge_time: Duration,
}

/// Timing for work before staged updates are merged.
///
/// Parallel execution reports one wall-clock duration because search and apply
/// can overlap. Serial execution reports an additive phase breakdown and
/// derives `unattributed` so the components close its measured outer interval.
#[derive(Debug, Serialize, Clone, Copy, PartialEq, Eq)]
pub enum PreMergeTiming {
    /// One wall-clock duration for execution modes whose search and apply work
    /// can overlap.
    Combined { elapsed: Duration },
    /// Non-overlapping components of serial pre-merge timing.
    Split {
        search: Duration,
        apply: Duration,
        /// Remainder of a measured outer pre-merge interval after search and
        /// apply.
        unattributed: Duration,
    },
}

impl Default for PreMergeTiming {
    fn default() -> Self {
        Self::Combined {
            elapsed: Duration::ZERO,
        }
    }
}

impl PreMergeTiming {
    pub fn total(self) -> Duration {
        match self {
            Self::Combined { elapsed } => elapsed,
            Self::Split {
                search,
                apply,
                unattributed,
            } => search + apply + unattributed,
        }
    }

    fn union(&mut self, other: Self) {
        *self = match (*self, other) {
            (
                Self::Split {
                    search: left_search,
                    apply: left_apply,
                    unattributed: left_unattributed,
                },
                Self::Split {
                    search: right_search,
                    apply: right_apply,
                    unattributed: right_unattributed,
                },
            ) => Self::Split {
                search: left_search + right_search,
                apply: left_apply + right_apply,
                unattributed: left_unattributed + right_unattributed,
            },
            (left, right) => Self::Combined {
                elapsed: left.total() + right.total(),
            },
        };
    }
}

/// The semantic responsibility served by a ruleset invocation.
#[derive(Debug, Serialize, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[serde(rename_all = "snake_case")]
pub enum RulesetTimingRole {
    Program,
    Equality,
}

type AggregatedRulesetTimings =
    BTreeMap<(RulesetTimingRole, Arc<str>), (Duration, PreMergeTiming, Duration)>;

impl RuleSetReport {
    pub fn num_matches(&self, rule: &str) -> usize {
        self.rule_reports
            .get(rule)
            .map(|r| r.iter().map(|r| r.num_matches).sum())
            .unwrap_or(0)
    }

    pub fn rule_search_and_apply_time(&self, rule: &str) -> Duration {
        self.rule_reports
            .get(rule)
            .map(|r| r.iter().map(|r| r.search_and_apply_time).sum())
            .unwrap_or(Duration::ZERO)
    }
}

#[derive(Debug, Serialize, Clone, Default)]
pub struct IterationReport {
    /// Preparing this invocation's executable ruleset before execution starts.
    pub assembly_time: Duration,
    pub rule_set_report: RuleSetReport,
    pub rebuild_time: Duration,
}

impl IterationReport {
    pub fn changed(&self) -> bool {
        self.rule_set_report.changed
    }

    pub fn rule_reports(&self) -> &HashMap<Arc<str>, Vec<RuleReport>> {
        &self.rule_set_report.rule_reports
    }

    pub fn rules(&self) -> impl Iterator<Item = &Arc<str>> {
        self.rule_set_report.rule_reports.keys()
    }

    /// Total exclusive wall-clock work recorded for this invocation.
    pub fn total_time(&self) -> Duration {
        self.assembly_time
            + self.rule_set_report.pre_merge.total()
            + self.rule_set_report.merge_time
            + self.rebuild_time
    }
}

/// One ruleset invocation and the responsibility it served when it ran.
#[derive(Debug, Serialize, Clone)]
pub struct RulesetIteration {
    pub name: Arc<str>,
    pub role: RulesetTimingRole,
    pub report: Arc<IterationReport>,
}

/// Running a schedule produces a report of the results.
/// This includes rough timing information and whether
/// the database was updated.
/// Calling `union` on two run reports adds the timing
/// information together.
#[derive(Debug, Serialize, Clone)]
pub struct RunReport {
    // Each entry carries ruleset metadata; its immutable report payload remains
    // reference-counted so cloning e-graphs stays cheap.
    pub iterations: Vec<RulesetIteration>,
    /// If any changes were made to the database.
    pub updated: bool,
    /// True if this run observed no database changes and there is no deferred
    /// scheduler work requiring another iteration.
    pub can_stop: bool,
    pub num_matches_per_rule: HashMap<Arc<str>, usize>,
}

impl Default for RunReport {
    fn default() -> Self {
        Self {
            iterations: Vec::new(),
            updated: false,
            can_stop: true,
            num_matches_per_rule: HashMap::default(),
        }
    }
}

impl Display for RunReport {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let rule_times = self.search_and_apply_time_per_rule();
        let mut rule_times_vec: Vec<_> = rule_times.iter().collect();
        rule_times_vec.sort_by_key(|(_, time)| **time);

        for (rule, time) in rule_times_vec {
            let name = Self::truncate_rule_name(rule.to_string());
            let time = time.as_secs_f64();
            let num_matches = self.num_matches_per_rule.get(rule).copied().unwrap_or(0);
            writeln!(
                f,
                "Rule {name}: search and apply {time:.3}s, num matches {num_matches}",
            )?;
        }

        let (rulesets, native_rebuild) = self.aggregate_timings();
        for ((_, name), (assembly, pre_merge, merge)) in rulesets {
            let assembly_time = assembly.as_secs_f64();
            let merge_time = merge.as_secs_f64();
            match pre_merge {
                PreMergeTiming::Split {
                    search,
                    apply,
                    unattributed,
                } => {
                    writeln!(
                        f,
                        "Ruleset {}: assembly {assembly_time:.3}s, search {:.3}s, apply {:.3}s, unattributed {:.3}s, merge {merge_time:.3}s",
                        name,
                        search.as_secs_f64(),
                        apply.as_secs_f64(),
                        unattributed.as_secs_f64(),
                    )?;
                }
                PreMergeTiming::Combined { elapsed } => {
                    writeln!(
                        f,
                        "Ruleset {}: assembly {assembly_time:.3}s, pre-merge {:.3}s, merge {merge_time:.3}s",
                        name,
                        elapsed.as_secs_f64(),
                    )?;
                }
            }
        }
        writeln!(f, "Native rebuild: {:.3}s", native_rebuild.as_secs_f64())?;

        Ok(())
    }
}

impl RunReport {
    /// add a ... and a maximum size to the name
    /// for printing, since they may be the rule itself
    fn truncate_rule_name(mut s: String) -> String {
        // replace newlines in s with a space
        s = s.replace('\n', " ");
        if s.len() > 80 {
            s.truncate(80);
            s.push_str("...");
        }
        s
    }

    fn union_counts(counts: &mut HashMap<Arc<str>, usize>, other_counts: HashMap<Arc<str>, usize>) {
        for (k, v) in other_counts {
            *counts.entry(k).or_default() += v;
        }
    }

    pub fn singleton(ruleset: &str, role: RulesetTimingRole, iteration: IterationReport) -> Self {
        let mut report = RunReport::default();

        for rule in iteration.rules() {
            *report.num_matches_per_rule.entry(rule.clone()).or_default() +=
                iteration.rule_set_report.num_matches(rule);
        }

        report.updated = iteration.changed();
        report.can_stop = !report.updated;
        report.iterations.push(RulesetIteration {
            name: ruleset.into(),
            role,
            report: Arc::new(iteration),
        });

        report
    }

    pub fn add_iteration(
        &mut self,
        ruleset: &str,
        role: RulesetTimingRole,
        iteration: IterationReport,
    ) {
        self.union(RunReport::singleton(ruleset, role, iteration));
    }

    /// Derive per-rule search-and-apply totals from the recorded iterations.
    pub fn search_and_apply_time_per_rule(&self) -> HashMap<Arc<str>, Duration> {
        let mut result = HashMap::default();
        for iteration in &self.iterations {
            for rule in iteration.report.rules() {
                *result.entry(rule.clone()).or_default() += iteration
                    .report
                    .rule_set_report
                    .rule_search_and_apply_time(rule);
            }
        }
        result
    }

    /// Derive the ruleset-own-work and global rebuild partition of this run.
    fn aggregate_timings(&self) -> (AggregatedRulesetTimings, Duration) {
        let mut rulesets = AggregatedRulesetTimings::new();
        let mut native_rebuild = Duration::ZERO;
        for iteration in &self.iterations {
            native_rebuild = native_rebuild.saturating_add(iteration.report.rebuild_time);
            let key = (iteration.role, iteration.name.clone());
            match rulesets.entry(key) {
                std::collections::btree_map::Entry::Occupied(mut entry) => {
                    let (assembly, pre_merge, merge) = entry.get_mut();
                    *assembly += iteration.report.assembly_time;
                    pre_merge.union(iteration.report.rule_set_report.pre_merge);
                    *merge += iteration.report.rule_set_report.merge_time;
                }
                std::collections::btree_map::Entry::Vacant(entry) => {
                    entry.insert((
                        iteration.report.assembly_time,
                        iteration.report.rule_set_report.pre_merge,
                        iteration.report.rule_set_report.merge_time,
                    ));
                }
            }
        }
        (rulesets, native_rebuild)
    }

    /// Merge two reports.
    pub fn union(&mut self, other: Self) {
        self.iterations.extend(other.iterations);
        self.updated |= other.updated;
        self.can_stop &= other.can_stop;
        RunReport::union_counts(&mut self.num_matches_per_rule, other.num_matches_per_rule);
    }
}

/// All cumulative reporting state owned by an e-graph.
///
/// Local [`RunReport`] values remain scoped to schedules. Process timing lives
/// here because parsing, typechecking, and command work surrounds those runs
/// and must be counted exactly once.
#[derive(Debug, Clone, Default)]
pub struct OverallReport {
    pub run: RunReport,
    pub typecheck: Duration,
    pub frontend_parse: Duration,
    pub frontend_other: Duration,
    pub frontend_install: Duration,
    pub generated_construct: Duration,
    pub generated_signatures: Duration,
    pub generated_resolve: Duration,
    pub generated_lower: Duration,
    pub commands_actions: Duration,
    pub commands_check: Duration,
    pub commands_other: Duration,
}

impl OverallReport {
    pub fn process_time(&self) -> Duration {
        [
            self.typecheck,
            self.frontend_parse,
            self.frontend_other,
            self.frontend_install,
            self.generated_construct,
            self.generated_signatures,
            self.generated_resolve,
            self.generated_lower,
            self.commands_actions,
            self.commands_check,
            self.commands_other,
        ]
        .into_iter()
        .sum()
    }
}

/// Compact timing for one ruleset in the benchmark transport.
#[derive(Debug, Serialize, Clone, PartialEq, Eq)]
pub struct RulesetTimingRecord {
    pub name: String,
    pub role: RulesetTimingRole,
    pub assembly_ns: u64,
    pub search_ns: u64,
    pub apply_ns: u64,
    pub execution_ns: u64,
    pub merge_ns: u64,
}

/// Versioned, deterministic timing transport for successful egglog runs.
///
/// Every value is an exclusive wall-clock leaf. Rulesets are sorted by semantic
/// role and name. Native rebuild is global because the ruleset whose tail
/// happened to flush updates is not its semantic owner.
#[derive(Debug, Serialize, Clone, PartialEq, Eq)]
pub struct TimingSummary {
    pub schema_version: u32,
    pub typecheck_ns: u64,
    pub frontend_parse_ns: u64,
    pub frontend_other_ns: u64,
    pub frontend_install_ns: u64,
    pub frontend_generated_construct_ns: u64,
    pub frontend_generated_signatures_ns: u64,
    pub frontend_generated_resolve_ns: u64,
    pub frontend_generated_lower_ns: u64,
    pub commands_actions_ns: u64,
    pub commands_check_ns: u64,
    pub commands_other_ns: u64,
    pub native_rebuild_ns: u64,
    pub rulesets: Vec<RulesetTimingRecord>,
}

/// A requested timing summary cannot satisfy the serial, single-role contract.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TimingSummaryError {
    PhaseTimingUnavailable { ruleset: String },
    InconsistentRulesetRole { ruleset: String },
}

impl Display for TimingSummaryError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::PhaseTimingUnavailable { ruleset } => write!(
                f,
                "split pre-merge timing is unavailable for ruleset {ruleset:?}"
            ),
            Self::InconsistentRulesetRole { ruleset } => {
                write!(f, "ruleset {ruleset:?} ran with inconsistent timing roles")
            }
        }
    }
}

impl std::error::Error for TimingSummaryError {}

impl TimingSummary {
    pub const SCHEMA_VERSION: u32 = 5;

    pub fn from_report(report: &OverallReport) -> Result<Self, TimingSummaryError> {
        let (timings, native_rebuild) = report.run.aggregate_timings();
        let mut roles = BTreeMap::new();
        let mut rulesets = Vec::with_capacity(timings.len());
        for ((role, name), (assembly, pre_merge, merge)) in timings {
            if roles
                .insert(name.clone(), role)
                .is_some_and(|previous| previous != role)
            {
                return Err(TimingSummaryError::InconsistentRulesetRole {
                    ruleset: name.to_string(),
                });
            }
            let PreMergeTiming::Split {
                search,
                apply,
                unattributed,
            } = pre_merge
            else {
                return Err(TimingSummaryError::PhaseTimingUnavailable {
                    ruleset: name.to_string(),
                });
            };
            rulesets.push(RulesetTimingRecord {
                name: name.to_string(),
                role,
                assembly_ns: duration_ns(assembly),
                search_ns: duration_ns(search),
                apply_ns: duration_ns(apply),
                execution_ns: duration_ns(unattributed),
                merge_ns: duration_ns(merge),
            });
        }

        Ok(Self {
            schema_version: Self::SCHEMA_VERSION,
            typecheck_ns: duration_ns(report.typecheck),
            frontend_parse_ns: duration_ns(report.frontend_parse),
            frontend_other_ns: duration_ns(report.frontend_other),
            frontend_install_ns: duration_ns(report.frontend_install),
            frontend_generated_construct_ns: duration_ns(report.generated_construct),
            frontend_generated_signatures_ns: duration_ns(report.generated_signatures),
            frontend_generated_resolve_ns: duration_ns(report.generated_resolve),
            frontend_generated_lower_ns: duration_ns(report.generated_lower),
            commands_actions_ns: duration_ns(report.commands_actions),
            commands_check_ns: duration_ns(report.commands_check),
            commands_other_ns: duration_ns(report.commands_other),
            native_rebuild_ns: duration_ns(native_rebuild),
            rulesets,
        })
    }
}

fn duration_ns(duration: Duration) -> u64 {
    duration.as_nanos().min(u64::MAX as u128) as u64
}

#[cfg(test)]
mod tests {
    use super::*;

    fn split(search: u64, apply: u64, unattributed: u64) -> PreMergeTiming {
        PreMergeTiming::Split {
            search: Duration::from_nanos(search),
            apply: Duration::from_nanos(apply),
            unattributed: Duration::from_nanos(unattributed),
        }
    }

    fn iteration(
        assembly: u64,
        pre_merge: PreMergeTiming,
        merge: u64,
        rebuild: Duration,
    ) -> IterationReport {
        IterationReport {
            assembly_time: Duration::from_nanos(assembly),
            rule_set_report: RuleSetReport {
                pre_merge,
                merge_time: Duration::from_nanos(merge),
                ..RuleSetReport::default()
            },
            rebuild_time: rebuild,
        }
    }

    #[test]
    fn run_report_aggregates_every_iteration_of_a_ruleset() {
        let mut report = OverallReport::default();
        report.run.add_iteration(
            "timed",
            RulesetTimingRole::Program,
            iteration(2, split(11, 7, 3), 13, Duration::from_nanos(17)),
        );
        report.run.add_iteration(
            "timed",
            RulesetTimingRole::Program,
            iteration(3, split(19, 5, 4), 23, Duration::from_nanos(29)),
        );

        let summary = TimingSummary::from_report(&report).unwrap();
        assert_eq!(summary.rulesets[0].assembly_ns, 5);
        assert_eq!(summary.rulesets[0].search_ns, 30);
        assert_eq!(summary.rulesets[0].apply_ns, 12);
        assert_eq!(summary.rulesets[0].execution_ns, 7);
        assert_eq!(summary.rulesets[0].merge_ns, 36);
        assert_eq!(summary.native_rebuild_ns, 46);
    }

    #[test]
    fn run_report_preserves_mixed_pre_merge_totals() {
        let mut report = RunReport::default();
        report.add_iteration(
            "mixed",
            RulesetTimingRole::Program,
            iteration(2, split(3, 5, 7), 11, Duration::from_nanos(13)),
        );
        report.add_iteration(
            "mixed",
            RulesetTimingRole::Program,
            iteration(
                17,
                PreMergeTiming::Combined {
                    elapsed: Duration::from_nanos(19),
                },
                23,
                Duration::from_nanos(29),
            ),
        );

        let (rulesets, native_rebuild) = report.aggregate_timings();
        let ((role, name), (assembly, pre_merge, merge)) = rulesets.iter().next().unwrap();
        assert_eq!(rulesets.len(), 1);
        assert_eq!(
            (*role, name.as_ref()),
            (RulesetTimingRole::Program, "mixed")
        );
        assert_eq!(*assembly, Duration::from_nanos(19));
        assert_eq!(
            *pre_merge,
            PreMergeTiming::Combined {
                elapsed: Duration::from_nanos(34)
            }
        );
        assert_eq!(*merge, Duration::from_nanos(34));
        assert_eq!(native_rebuild, Duration::from_nanos(42));
    }

    #[test]
    fn timing_summary_exact_json_is_dense_and_sorted() {
        let mut report = OverallReport {
            typecheck: Duration::from_nanos(2),
            frontend_parse: Duration::from_nanos(1),
            generated_construct: Duration::from_nanos(14),
            generated_signatures: Duration::from_nanos(15),
            generated_resolve: Duration::from_nanos(16),
            generated_lower: Duration::from_nanos(17),
            commands_check: Duration::from_nanos(6),
            ..OverallReport::default()
        };
        report.run.add_iteration(
            "@parent",
            RulesetTimingRole::Equality,
            iteration(8, split(9, 10, 11), 12, Duration::from_nanos(13)),
        );
        report.run.add_iteration(
            "rules/λ",
            RulesetTimingRole::Program,
            iteration(0, split(1_000_000_234, 3, 4), 5, Duration::ZERO),
        );
        report.run.add_iteration(
            "",
            RulesetTimingRole::Program,
            iteration(0, split(0, 0, 0), 0, Duration::ZERO),
        );
        let summary = TimingSummary::from_report(&report).unwrap();

        assert_eq!(
            serde_json::to_string(&summary).unwrap(),
            r#"{"schema_version":5,"typecheck_ns":2,"frontend_parse_ns":1,"frontend_other_ns":0,"frontend_install_ns":0,"frontend_generated_construct_ns":14,"frontend_generated_signatures_ns":15,"frontend_generated_resolve_ns":16,"frontend_generated_lower_ns":17,"commands_actions_ns":0,"commands_check_ns":6,"commands_other_ns":0,"native_rebuild_ns":13,"rulesets":[{"name":"","role":"program","assembly_ns":0,"search_ns":0,"apply_ns":0,"execution_ns":0,"merge_ns":0},{"name":"rules/λ","role":"program","assembly_ns":0,"search_ns":1000000234,"apply_ns":3,"execution_ns":4,"merge_ns":5},{"name":"@parent","role":"equality","assembly_ns":8,"search_ns":9,"apply_ns":10,"execution_ns":11,"merge_ns":12}]}"#
        );
    }

    #[test]
    fn timing_summary_empty_report_golden() {
        let summary = TimingSummary::from_report(&OverallReport::default()).unwrap();
        assert_eq!(
            serde_json::to_string(&summary).unwrap(),
            r#"{"schema_version":5,"typecheck_ns":0,"frontend_parse_ns":0,"frontend_other_ns":0,"frontend_install_ns":0,"frontend_generated_construct_ns":0,"frontend_generated_signatures_ns":0,"frontend_generated_resolve_ns":0,"frontend_generated_lower_ns":0,"commands_actions_ns":0,"commands_check_ns":0,"commands_other_ns":0,"native_rebuild_ns":0,"rulesets":[]}"#
        );
    }

    #[test]
    fn generated_frontend_leaves_are_process_time() {
        let report = OverallReport {
            generated_construct: Duration::from_nanos(2),
            generated_signatures: Duration::from_nanos(3),
            generated_resolve: Duration::from_nanos(5),
            generated_lower: Duration::from_nanos(7),
            ..OverallReport::default()
        };

        assert_eq!(report.process_time(), Duration::from_nanos(17));
    }

    #[test]
    fn timing_summary_does_not_truncate_rulesets_and_saturates_nanoseconds() {
        let mut report = OverallReport::default();
        for index in (0_u64..40).rev() {
            report.run.add_iteration(
                &format!("ruleset-{index:02}"),
                RulesetTimingRole::Program,
                iteration(
                    0,
                    split(index + 1, 0, 0),
                    0,
                    if index == 0 {
                        Duration::from_secs(u64::MAX)
                    } else {
                        Duration::ZERO
                    },
                ),
            );
        }
        let summary = TimingSummary::from_report(&report).unwrap();

        assert_eq!(summary.rulesets.len(), 40);
        assert_eq!(summary.rulesets.first().unwrap().name, "ruleset-00");
        assert_eq!(summary.rulesets.last().unwrap().name, "ruleset-39");
        assert_eq!(summary.native_rebuild_ns, u64::MAX);
    }

    #[test]
    fn timing_summary_rejects_combined_timing_and_inconsistent_roles() {
        let mut combined_report = OverallReport::default();
        combined_report.run.add_iteration(
            "mixed",
            RulesetTimingRole::Program,
            iteration(
                0,
                PreMergeTiming::Combined {
                    elapsed: Duration::from_nanos(5),
                },
                0,
                Duration::ZERO,
            ),
        );
        let combined = TimingSummary::from_report(&combined_report);
        assert_eq!(
            combined,
            Err(TimingSummaryError::PhaseTimingUnavailable {
                ruleset: "mixed".into()
            })
        );

        let mut inconsistent_report = OverallReport::default();
        inconsistent_report.run.add_iteration(
            "mixed",
            RulesetTimingRole::Program,
            iteration(0, split(0, 0, 0), 0, Duration::ZERO),
        );
        inconsistent_report.run.add_iteration(
            "mixed",
            RulesetTimingRole::Equality,
            iteration(0, split(0, 0, 0), 0, Duration::ZERO),
        );
        let inconsistent = TimingSummary::from_report(&inconsistent_report);
        assert_eq!(
            inconsistent,
            Err(TimingSummaryError::InconsistentRulesetRole {
                ruleset: "mixed".into()
            })
        );
    }
}

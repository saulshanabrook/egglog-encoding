use clap::clap_derive::ValueEnum;
use rustc_hash::FxHasher;
use serde::Serialize;
use std::{
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
    /// Backends split pre-merge time into search, apply, and unattributed time
    /// when their execution mode can attribute the phases without overlap.
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
    /// Backend-defined timed work before staged updates are merged, either as
    /// one elapsed duration or as an exhaustive serial phase breakdown.
    pub pre_merge: PreMergeTiming,
    pub merge_time: Duration,
}

/// Timing for a backend's defined timed work before staged updates are merged.
///
/// Parallel execution reports one wall-clock duration because search and apply
/// can overlap. Serial execution reports an additive, backend-defined phase
/// breakdown. Main egglog derives `unattributed` so the components close its
/// measured outer interval. DD instead defines its pre-merge total directly as
/// its native search plus apply regions and therefore reports zero
/// `unattributed` time.
#[derive(Debug, Serialize, Clone, Copy, PartialEq, Eq)]
pub enum PreMergeTiming {
    /// One wall-clock duration for execution modes whose search and apply work
    /// can overlap.
    Combined { elapsed: Duration },
    /// Non-overlapping components of the backend's serial pre-merge timing.
    Split {
        search: Duration,
        apply: Duration,
        /// Remainder of a measured outer pre-merge interval after search and
        /// apply, or zero when the backend defines the total as their sum.
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

/// Aggregated timing for all iterations of one ruleset.
#[derive(Debug, Serialize, Clone, Copy, PartialEq, Eq, Default)]
pub struct RulesetTiming {
    /// Execution before staged updates are merged.
    pub pre_merge: PreMergeTiming,
    /// Resolving and installing staged updates.
    pub merge: Duration,
    /// Rebuilding indexes and e-graph state after merge.
    pub rebuild: Duration,
}

impl RulesetTiming {
    pub fn total(self) -> Duration {
        self.pre_merge.total() + self.merge + self.rebuild
    }

    fn union(&mut self, other: Self) {
        self.pre_merge.union(other.pre_merge);
        self.merge += other.merge;
        self.rebuild += other.rebuild;
    }
}

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
}

/// Running a schedule produces a report of the results.
/// This includes rough timing information and whether
/// the database was updated.
/// Calling `union` on two run reports adds the timing
/// information together.
#[derive(Debug, Serialize, Clone)]
pub struct RunReport {
    // Since `IterationReport`s are immutable, we can reference count them to avoid
    // expensive cloning when e-graphs are cloned.
    pub iterations: Vec<Arc<IterationReport>>,
    /// If any changes were made to the database.
    pub updated: bool,
    /// True if this run observed no database changes and there is no deferred
    /// scheduler work requiring another iteration.
    pub can_stop: bool,
    pub search_and_apply_time_per_rule: HashMap<Arc<str>, Duration>,
    pub num_matches_per_rule: HashMap<Arc<str>, usize>,
    pub ruleset_timings: HashMap<Arc<str>, RulesetTiming>,
}

impl Default for RunReport {
    fn default() -> Self {
        Self {
            iterations: Vec::new(),
            updated: false,
            can_stop: true,
            search_and_apply_time_per_rule: HashMap::default(),
            num_matches_per_rule: HashMap::default(),
            ruleset_timings: HashMap::default(),
        }
    }
}

impl Display for RunReport {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut rule_times_vec: Vec<_> = self.search_and_apply_time_per_rule.iter().collect();
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

        for (ruleset, timing) in &self.ruleset_timings {
            let merge_time = timing.merge.as_secs_f64();
            let rebuild_time = timing.rebuild.as_secs_f64();
            match timing.pre_merge {
                PreMergeTiming::Split {
                    search,
                    apply,
                    unattributed,
                } => {
                    writeln!(
                        f,
                        "Ruleset {ruleset}: search {:.3}s, apply {:.3}s, unattributed {:.3}s, merge {merge_time:.3}s, rebuild {rebuild_time:.3}s",
                        search.as_secs_f64(),
                        apply.as_secs_f64(),
                        unattributed.as_secs_f64(),
                    )?;
                }
                PreMergeTiming::Combined { elapsed } => {
                    writeln!(
                        f,
                        "Ruleset {ruleset}: pre-merge {:.3}s, merge {merge_time:.3}s, rebuild {rebuild_time:.3}s",
                        elapsed.as_secs_f64(),
                    )?;
                }
            }
        }

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

    fn union_times(
        times: &mut HashMap<Arc<str>, Duration>,
        other_times: HashMap<Arc<str>, Duration>,
    ) {
        for (k, v) in other_times {
            *times.entry(k).or_default() += v;
        }
    }

    fn union_counts(counts: &mut HashMap<Arc<str>, usize>, other_counts: HashMap<Arc<str>, usize>) {
        for (k, v) in other_counts {
            *counts.entry(k).or_default() += v;
        }
    }

    pub fn singleton(ruleset: &str, iteration: IterationReport) -> Self {
        let mut report = RunReport::default();

        for rule in iteration.rules() {
            *report
                .search_and_apply_time_per_rule
                .entry(rule.clone())
                .or_default() += iteration.rule_set_report.rule_search_and_apply_time(rule);
            *report.num_matches_per_rule.entry(rule.clone()).or_default() +=
                iteration.rule_set_report.num_matches(rule);
        }

        let ruleset: Arc<str> = ruleset.into();
        report.ruleset_timings.insert(
            ruleset,
            RulesetTiming {
                pre_merge: iteration.rule_set_report.pre_merge,
                merge: iteration.rule_set_report.merge_time,
                rebuild: iteration.rebuild_time,
            },
        );
        report.updated = iteration.changed();
        report.can_stop = !report.updated;
        report.iterations.push(Arc::new(iteration));

        report
    }

    pub fn add_iteration(&mut self, ruleset: &str, iteration: IterationReport) {
        self.union(RunReport::singleton(ruleset, iteration));
    }

    /// Merge two reports.
    pub fn union(&mut self, other: Self) {
        self.iterations.extend(other.iterations);
        self.updated |= other.updated;
        self.can_stop &= other.can_stop;
        RunReport::union_times(
            &mut self.search_and_apply_time_per_rule,
            other.search_and_apply_time_per_rule,
        );
        RunReport::union_counts(&mut self.num_matches_per_rule, other.num_matches_per_rule);
        for (ruleset, timing) in other.ruleset_timings {
            self.ruleset_timings
                .entry(ruleset)
                .and_modify(|current| current.union(timing))
                .or_insert(timing);
        }
    }
}

/// Compact, deterministic timing transport for benchmark runners.
#[derive(Debug, Serialize, Clone, PartialEq, Eq)]
pub struct RulesetTimingV2 {
    pub name: String,
    pub search_ns: u64,
    pub apply_ns: u64,
    pub unattributed_ns: u64,
    pub merge_ns: u64,
    pub rebuild_ns: u64,
}

/// Versioned ruleset timing summary for successful egglog runs.
///
/// V2 includes every name in [`RunReport::ruleset_timings`], preserves the
/// empty name used by the default ruleset, and sorts names lexicographically.
/// Split pre-merge timing must be available for every included ruleset;
/// otherwise construction returns [`PhaseTimingUnavailable`]. Durations are
/// converted to nanoseconds with saturation at [`u64::MAX`], and the ruleset
/// list is never truncated.
#[derive(Debug, Serialize, Clone, PartialEq, Eq)]
pub struct TimingSummaryV2 {
    pub schema_version: u32,
    pub rulesets: Vec<RulesetTimingV2>,
}

/// A requested timing summary contains a ruleset whose split phase timing was
/// not recorded.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PhaseTimingUnavailable {
    pub ruleset: String,
}

impl Display for PhaseTimingUnavailable {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "split pre-merge timing is unavailable for ruleset {ruleset:?}",
            ruleset = self.ruleset,
        )
    }
}

impl std::error::Error for PhaseTimingUnavailable {}

impl TimingSummaryV2 {
    pub fn from_run_report(report: &RunReport) -> Result<Self, PhaseTimingUnavailable> {
        let mut timings = report.ruleset_timings.iter().collect::<Vec<_>>();
        timings.sort_unstable_by(|(left, _), (right, _)| left.as_ref().cmp(right.as_ref()));

        let rulesets = timings
            .into_iter()
            .map(|(name, timing)| {
                let PreMergeTiming::Split {
                    search,
                    apply,
                    unattributed,
                } = timing.pre_merge
                else {
                    return Err(PhaseTimingUnavailable {
                        ruleset: name.to_string(),
                    });
                };
                Ok(RulesetTimingV2 {
                    search_ns: duration_ns(search),
                    apply_ns: duration_ns(apply),
                    unattributed_ns: duration_ns(unattributed),
                    merge_ns: duration_ns(timing.merge),
                    rebuild_ns: duration_ns(timing.rebuild),
                    name: name.to_string(),
                })
            })
            .collect::<Result<Vec<_>, PhaseTimingUnavailable>>()?;

        Ok(Self {
            schema_version: 2,
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

    #[test]
    fn timing_summary_v2_exact_json_is_sorted() {
        let mut report = RunReport::default();
        report.ruleset_timings.insert(
            "zeta".into(),
            RulesetTiming {
                pre_merge: PreMergeTiming::Split {
                    search: Duration::new(1, 234),
                    apply: Duration::ZERO,
                    unattributed: Duration::from_nanos(89),
                },
                ..RulesetTiming::default()
            },
        );
        report.ruleset_timings.insert(
            "beta".into(),
            RulesetTiming {
                pre_merge: split(0, 23, 0),
                ..RulesetTiming::default()
            },
        );
        report.ruleset_timings.insert(
            "".into(),
            RulesetTiming {
                pre_merge: split(0, 0, 0),
                merge: Duration::from_nanos(45),
                ..RulesetTiming::default()
            },
        );
        report.ruleset_timings.insert(
            "alpha".into(),
            RulesetTiming {
                pre_merge: split(0, 0, 0),
                rebuild: Duration::from_nanos(67),
                ..RulesetTiming::default()
            },
        );

        let summary = TimingSummaryV2::from_run_report(&report).unwrap();
        let json = serde_json::to_string(&summary).unwrap();

        assert_eq!(
            json,
            r#"{"schema_version":2,"rulesets":[{"name":"","search_ns":0,"apply_ns":0,"unattributed_ns":0,"merge_ns":45,"rebuild_ns":0},{"name":"alpha","search_ns":0,"apply_ns":0,"unattributed_ns":0,"merge_ns":0,"rebuild_ns":67},{"name":"beta","search_ns":0,"apply_ns":23,"unattributed_ns":0,"merge_ns":0,"rebuild_ns":0},{"name":"zeta","search_ns":1000000234,"apply_ns":0,"unattributed_ns":89,"merge_ns":0,"rebuild_ns":0}]}"#
        );
    }

    #[test]
    fn timing_summary_v2_empty_report_golden() {
        let summary = TimingSummaryV2::from_run_report(&RunReport::default()).unwrap();
        let json = serde_json::to_string(&summary).unwrap();

        assert_eq!(json, r#"{"schema_version":2,"rulesets":[]}"#);
    }

    #[test]
    fn timing_summary_v2_aggregates_every_iteration_of_a_ruleset() {
        let mut report = RunReport::default();
        report.add_iteration(
            "timed",
            IterationReport {
                rule_set_report: RuleSetReport {
                    pre_merge: split(11, 7, 3),
                    merge_time: Duration::from_nanos(13),
                    ..RuleSetReport::default()
                },
                rebuild_time: Duration::from_nanos(17),
            },
        );
        report.add_iteration(
            "timed",
            IterationReport {
                rule_set_report: RuleSetReport {
                    pre_merge: split(19, 5, 4),
                    merge_time: Duration::from_nanos(23),
                    ..RuleSetReport::default()
                },
                rebuild_time: Duration::from_nanos(29),
            },
        );

        let summary = TimingSummaryV2::from_run_report(&report).unwrap();

        assert_eq!(
            report.ruleset_timings["timed"].pre_merge.total(),
            Duration::from_nanos(49)
        );
        assert_eq!(
            report.ruleset_timings["timed"].total(),
            Duration::from_nanos(131)
        );

        assert_eq!(
            summary.rulesets,
            [RulesetTimingV2 {
                name: "timed".to_owned(),
                search_ns: 30,
                apply_ns: 12,
                unattributed_ns: 7,
                merge_ns: 36,
                rebuild_ns: 46,
            }]
        );
    }

    #[test]
    fn timing_summary_v2_does_not_truncate_rulesets() {
        let mut report = RunReport::default();
        for index in (0..40).rev() {
            report.ruleset_timings.insert(
                format!("ruleset-{index:02}").into(),
                RulesetTiming {
                    pre_merge: split(index + 1, 0, 0),
                    ..RulesetTiming::default()
                },
            );
        }

        let summary = TimingSummaryV2::from_run_report(&report).unwrap();

        assert_eq!(summary.rulesets.len(), 40);
        assert_eq!(summary.rulesets.first().unwrap().name, "ruleset-00");
        assert_eq!(summary.rulesets.last().unwrap().name, "ruleset-39");
    }

    #[test]
    fn timing_summary_v2_saturates_nanoseconds_to_u64() {
        let mut report = RunReport::default();
        report.ruleset_timings.insert(
            "long".into(),
            RulesetTiming {
                pre_merge: PreMergeTiming::Split {
                    search: Duration::from_secs(u64::MAX),
                    apply: Duration::ZERO,
                    unattributed: Duration::ZERO,
                },
                ..RulesetTiming::default()
            },
        );

        let summary = TimingSummaryV2::from_run_report(&report).unwrap();

        assert_eq!(summary.rulesets[0].search_ns, u64::MAX);
    }

    #[test]
    fn timing_summary_v2_rejects_unavailable_split_timing() {
        let mut report = RunReport::default();
        report.ruleset_timings.insert(
            "default".into(),
            RulesetTiming {
                pre_merge: PreMergeTiming::Combined {
                    elapsed: Duration::from_nanos(42),
                },
                ..RulesetTiming::default()
            },
        );

        assert_eq!(
            TimingSummaryV2::from_run_report(&report),
            Err(PhaseTimingUnavailable {
                ruleset: "default".to_owned(),
            })
        );
    }

    #[test]
    fn combined_iteration_degrades_aggregated_pre_merge_timing() {
        let mut report = RunReport::default();
        report.add_iteration(
            "mixed",
            IterationReport {
                rule_set_report: RuleSetReport {
                    pre_merge: split(1, 2, 3),
                    merge_time: Duration::from_nanos(7),
                    ..RuleSetReport::default()
                },
                rebuild_time: Duration::from_nanos(11),
            },
        );
        report.add_iteration(
            "mixed",
            IterationReport {
                rule_set_report: RuleSetReport {
                    pre_merge: PreMergeTiming::Combined {
                        elapsed: Duration::from_nanos(5),
                    },
                    merge_time: Duration::from_nanos(13),
                    ..RuleSetReport::default()
                },
                rebuild_time: Duration::from_nanos(17),
            },
        );

        assert_eq!(
            report.ruleset_timings["mixed"],
            RulesetTiming {
                pre_merge: PreMergeTiming::Combined {
                    elapsed: Duration::from_nanos(11),
                },
                merge: Duration::from_nanos(20),
                rebuild: Duration::from_nanos(28),
            }
        );
        assert_eq!(
            report.ruleset_timings["mixed"].total(),
            Duration::from_nanos(59)
        );
    }
}

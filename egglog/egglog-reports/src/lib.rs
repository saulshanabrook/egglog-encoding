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
pub(crate) type IndexSet<T> = indexmap::IndexSet<T, BuildHasherDefault<FxHasher>>;

#[derive(ValueEnum, Default, Serialize, Debug, Clone, Copy)]
pub enum ReportLevel {
    /// Report combined search/apply, merge, and rebuild time.
    ///
    /// Backends may additionally provide split search/apply timing when the
    /// orthogonal phase-timing opt-in is enabled.
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
    /// The backend's legacy combined search/apply value. Main egglog records
    /// its historical outer wall-clock span even when detailed timing is off;
    /// backends without a historical combined timer may leave this at zero.
    pub search_and_apply_time: Duration,
    /// Search time excluding timed rule-head instruction batches. `None` when
    /// detailed phase timing was disabled or execution was parallel.
    pub search_time: Option<Duration>,
    /// Rule-head instruction execution and staged writes. `None` when detailed
    /// phase timing was disabled or execution was parallel.
    pub apply_time: Option<Duration>,
    pub merge_time: Duration,
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

    pub fn search_time(&self) -> Option<Duration> {
        self.rule_set_report.search_time
    }

    pub fn apply_time(&self) -> Option<Duration> {
        self.rule_set_report.apply_time
    }

    /// Return search and apply together for callers that do not need the split.
    pub fn search_and_apply_time(&self) -> Duration {
        self.rule_set_report.search_and_apply_time
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
    pub search_and_apply_time_per_ruleset: HashMap<Arc<str>, Duration>,
    pub search_time_per_ruleset: HashMap<Arc<str>, Option<Duration>>,
    pub apply_time_per_ruleset: HashMap<Arc<str>, Option<Duration>>,
    pub merge_time_per_ruleset: HashMap<Arc<str>, Duration>,
    pub rebuild_time_per_ruleset: HashMap<Arc<str>, Duration>,
}

impl Default for RunReport {
    fn default() -> Self {
        Self {
            iterations: Vec::new(),
            updated: false,
            can_stop: true,
            search_and_apply_time_per_rule: HashMap::default(),
            num_matches_per_rule: HashMap::default(),
            search_and_apply_time_per_ruleset: HashMap::default(),
            search_time_per_ruleset: HashMap::default(),
            apply_time_per_ruleset: HashMap::default(),
            merge_time_per_ruleset: HashMap::default(),
            rebuild_time_per_ruleset: HashMap::default(),
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

        let rulesets = self
            .search_and_apply_time_per_ruleset
            .keys()
            .chain(self.search_time_per_ruleset.keys())
            .chain(self.apply_time_per_ruleset.keys())
            .chain(self.merge_time_per_ruleset.keys())
            .chain(self.rebuild_time_per_ruleset.keys())
            .collect::<IndexSet<_>>();

        for ruleset in rulesets {
            let search_time = self.search_time_per_ruleset.get(ruleset).copied().flatten();
            let apply_time = self.apply_time_per_ruleset.get(ruleset).copied().flatten();
            let search_and_apply_time = self
                .search_and_apply_time_per_ruleset
                .get(ruleset)
                .cloned()
                .unwrap_or(Duration::ZERO)
                .as_secs_f64();
            let merge_time = self
                .merge_time_per_ruleset
                .get(ruleset)
                .cloned()
                .unwrap_or(Duration::ZERO)
                .as_secs_f64();
            let rebuild_time = self
                .rebuild_time_per_ruleset
                .get(ruleset)
                .cloned()
                .unwrap_or(Duration::ZERO)
                .as_secs_f64();
            if let (Some(search_time), Some(apply_time)) = (search_time, apply_time) {
                writeln!(
                    f,
                    "Ruleset {ruleset}: search {:.3}s, apply {:.3}s, merge {merge_time:.3}s, rebuild {rebuild_time:.3}s",
                    search_time.as_secs_f64(),
                    apply_time.as_secs_f64(),
                )?;
            } else {
                writeln!(
                    f,
                    "Ruleset {ruleset}: search and apply {search_and_apply_time:.3}s, merge {merge_time:.3}s, rebuild {rebuild_time:.3}s",
                )?;
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

    fn union_optional_times(
        times: &mut HashMap<Arc<str>, Option<Duration>>,
        other_times: HashMap<Arc<str>, Option<Duration>>,
    ) {
        for (key, other) in other_times {
            let current = times.entry(key).or_insert(Some(Duration::ZERO));
            *current = match (*current, other) {
                (Some(current), Some(other)) => Some(current + other),
                _ => None,
            };
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
        let per_ruleset = |x| [(ruleset.clone(), x)].into_iter().collect();

        report.search_and_apply_time_per_ruleset = per_ruleset(iteration.search_and_apply_time());
        report.search_time_per_ruleset = [(ruleset.clone(), iteration.search_time())]
            .into_iter()
            .collect();
        report.apply_time_per_ruleset = [(ruleset.clone(), iteration.apply_time())]
            .into_iter()
            .collect();
        report.merge_time_per_ruleset = per_ruleset(iteration.rule_set_report.merge_time);
        report.rebuild_time_per_ruleset = per_ruleset(iteration.rebuild_time);
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
        RunReport::union_times(
            &mut self.search_and_apply_time_per_ruleset,
            other.search_and_apply_time_per_ruleset,
        );
        RunReport::union_optional_times(
            &mut self.search_time_per_ruleset,
            other.search_time_per_ruleset,
        );
        RunReport::union_optional_times(
            &mut self.apply_time_per_ruleset,
            other.apply_time_per_ruleset,
        );
        RunReport::union_times(
            &mut self.merge_time_per_ruleset,
            other.merge_time_per_ruleset,
        );
        RunReport::union_times(
            &mut self.rebuild_time_per_ruleset,
            other.rebuild_time_per_ruleset,
        );
    }
}

/// Compact, deterministic timing transport for benchmark runners.
#[derive(Debug, Serialize, Clone, PartialEq, Eq)]
pub struct RulesetTimingV1 {
    pub name: String,
    pub search_ns: u64,
    pub apply_ns: u64,
    pub merge_ns: u64,
    pub rebuild_ns: u64,
}

/// Versioned ruleset timing summary for successful egglog runs.
///
/// V1 includes every name present in any per-ruleset phase map, preserves the
/// empty name used by the default ruleset, and sorts names lexicographically.
/// Split search/apply timing must be available for every included ruleset;
/// otherwise construction returns [`PhaseTimingUnavailable`]. Missing
/// merge/rebuild entries are represented as zero, durations are converted to
/// nanoseconds with saturation at [`u64::MAX`], and the ruleset list is never
/// truncated.
#[derive(Debug, Serialize, Clone, PartialEq, Eq)]
pub struct TimingSummaryV1 {
    pub schema_version: u32,
    pub rulesets: Vec<RulesetTimingV1>,
}

/// A requested timing summary contains a ruleset whose split phase timing was
/// not recorded.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PhaseTimingUnavailable {
    pub ruleset: String,
    pub phase: &'static str,
}

impl Display for PhaseTimingUnavailable {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{phase} timing is unavailable for ruleset {ruleset:?}",
            phase = self.phase,
            ruleset = self.ruleset,
        )
    }
}

impl std::error::Error for PhaseTimingUnavailable {}

impl TimingSummaryV1 {
    pub fn from_run_report(report: &RunReport) -> Result<Self, PhaseTimingUnavailable> {
        let mut names = report
            .search_and_apply_time_per_ruleset
            .keys()
            .chain(report.search_time_per_ruleset.keys())
            .chain(report.apply_time_per_ruleset.keys())
            .chain(report.merge_time_per_ruleset.keys())
            .chain(report.rebuild_time_per_ruleset.keys())
            .cloned()
            .collect::<IndexSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        names.sort_unstable_by(|left, right| left.as_ref().cmp(right.as_ref()));

        let rulesets = names
            .into_iter()
            .map(|name| {
                Ok(RulesetTimingV1 {
                    search_ns: required_duration_ns(
                        &report.search_time_per_ruleset,
                        &name,
                        "search",
                    )?,
                    apply_ns: required_duration_ns(&report.apply_time_per_ruleset, &name, "apply")?,
                    merge_ns: zero_filled_duration_ns(report.merge_time_per_ruleset.get(&name)),
                    rebuild_ns: zero_filled_duration_ns(report.rebuild_time_per_ruleset.get(&name)),
                    name: name.to_string(),
                })
            })
            .collect::<Result<Vec<_>, PhaseTimingUnavailable>>()?;

        Ok(Self {
            schema_version: 1,
            rulesets,
        })
    }
}

fn required_duration_ns(
    timings: &HashMap<Arc<str>, Option<Duration>>,
    ruleset: &Arc<str>,
    phase: &'static str,
) -> Result<u64, PhaseTimingUnavailable> {
    timings
        .get(ruleset)
        .copied()
        .flatten()
        .map(duration_ns)
        .ok_or_else(|| PhaseTimingUnavailable {
            ruleset: ruleset.to_string(),
            phase,
        })
}

fn zero_filled_duration_ns(duration: Option<&Duration>) -> u64 {
    duration_ns(duration.copied().unwrap_or_default())
}

fn duration_ns(duration: Duration) -> u64 {
    duration.as_nanos().min(u64::MAX as u128) as u64
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn timing_summary_v1_exact_json_is_sorted_and_zero_filled() {
        let mut report = RunReport::default();
        report
            .search_time_per_ruleset
            .insert("zeta".into(), Some(Duration::new(1, 234)));
        report
            .apply_time_per_ruleset
            .insert("beta".into(), Some(Duration::from_nanos(23)));
        for name in ["", "alpha", "beta", "zeta"] {
            report
                .search_time_per_ruleset
                .entry(name.into())
                .or_insert(Some(Duration::ZERO));
            report
                .apply_time_per_ruleset
                .entry(name.into())
                .or_insert(Some(Duration::ZERO));
        }
        report
            .merge_time_per_ruleset
            .insert("".into(), Duration::from_nanos(45));
        report
            .rebuild_time_per_ruleset
            .insert("alpha".into(), Duration::from_nanos(67));

        let summary = TimingSummaryV1::from_run_report(&report).unwrap();
        let json = serde_json::to_string(&summary).unwrap();

        assert_eq!(
            json,
            r#"{"schema_version":1,"rulesets":[{"name":"","search_ns":0,"apply_ns":0,"merge_ns":45,"rebuild_ns":0},{"name":"alpha","search_ns":0,"apply_ns":0,"merge_ns":0,"rebuild_ns":67},{"name":"beta","search_ns":0,"apply_ns":23,"merge_ns":0,"rebuild_ns":0},{"name":"zeta","search_ns":1000000234,"apply_ns":0,"merge_ns":0,"rebuild_ns":0}]}"#
        );
    }

    #[test]
    fn timing_summary_v1_empty_report_golden() {
        let summary = TimingSummaryV1::from_run_report(&RunReport::default()).unwrap();
        let json = serde_json::to_string(&summary).unwrap();

        assert_eq!(json, r#"{"schema_version":1,"rulesets":[]}"#);
    }

    #[test]
    fn timing_summary_v1_aggregates_every_iteration_of_a_ruleset() {
        let mut report = RunReport::default();
        report.add_iteration(
            "timed",
            IterationReport {
                rule_set_report: RuleSetReport {
                    search_and_apply_time: Duration::from_nanos(18),
                    search_time: Some(Duration::from_nanos(11)),
                    apply_time: Some(Duration::from_nanos(7)),
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
                    search_and_apply_time: Duration::from_nanos(24),
                    search_time: Some(Duration::from_nanos(19)),
                    apply_time: Some(Duration::from_nanos(5)),
                    merge_time: Duration::from_nanos(23),
                    ..RuleSetReport::default()
                },
                rebuild_time: Duration::from_nanos(29),
            },
        );

        let summary = TimingSummaryV1::from_run_report(&report).unwrap();

        assert_eq!(
            summary.rulesets,
            [RulesetTimingV1 {
                name: "timed".to_owned(),
                search_ns: 30,
                apply_ns: 12,
                merge_ns: 36,
                rebuild_ns: 46,
            }]
        );
    }

    #[test]
    fn timing_summary_v1_does_not_truncate_rulesets() {
        let mut report = RunReport::default();
        for index in (0..40).rev() {
            report.search_time_per_ruleset.insert(
                format!("ruleset-{index:02}").into(),
                Some(Duration::from_nanos(index + 1)),
            );
            report
                .apply_time_per_ruleset
                .insert(format!("ruleset-{index:02}").into(), Some(Duration::ZERO));
        }

        let summary = TimingSummaryV1::from_run_report(&report).unwrap();

        assert_eq!(summary.rulesets.len(), 40);
        assert_eq!(summary.rulesets.first().unwrap().name, "ruleset-00");
        assert_eq!(summary.rulesets.last().unwrap().name, "ruleset-39");
    }

    #[test]
    fn timing_summary_v1_saturates_nanoseconds_to_u64() {
        let mut report = RunReport::default();
        report
            .search_time_per_ruleset
            .insert("long".into(), Some(Duration::from_secs(u64::MAX)));
        report
            .apply_time_per_ruleset
            .insert("long".into(), Some(Duration::ZERO));

        let summary = TimingSummaryV1::from_run_report(&report).unwrap();

        assert_eq!(summary.rulesets[0].search_ns, u64::MAX);
    }

    #[test]
    fn timing_summary_v1_rejects_unavailable_split_timing() {
        let mut report = RunReport::default();
        report
            .search_and_apply_time_per_ruleset
            .insert("default".into(), Duration::from_nanos(42));
        report
            .search_time_per_ruleset
            .insert("default".into(), None);
        report.apply_time_per_ruleset.insert("default".into(), None);

        assert_eq!(
            TimingSummaryV1::from_run_report(&report),
            Err(PhaseTimingUnavailable {
                ruleset: "default".to_owned(),
                phase: "search",
            })
        );
    }

    #[test]
    fn unavailable_iteration_taints_aggregated_split_timing() {
        let mut report = RunReport::default();
        report.add_iteration(
            "mixed",
            IterationReport {
                rule_set_report: RuleSetReport {
                    search_and_apply_time: Duration::from_nanos(3),
                    search_time: Some(Duration::from_nanos(1)),
                    apply_time: Some(Duration::from_nanos(2)),
                    ..RuleSetReport::default()
                },
                ..IterationReport::default()
            },
        );
        report.add_iteration(
            "mixed",
            IterationReport {
                rule_set_report: RuleSetReport {
                    search_and_apply_time: Duration::from_nanos(5),
                    ..RuleSetReport::default()
                },
                ..IterationReport::default()
            },
        );

        assert_eq!(report.search_time_per_ruleset["mixed"], None);
        assert_eq!(report.apply_time_per_ruleset["mixed"], None);
        assert_eq!(
            report.search_and_apply_time_per_ruleset["mixed"],
            Duration::from_nanos(8)
        );
    }
}

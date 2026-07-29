use std::sync::Arc;

use egglog_reports::{IterationReport, RuleReport, RuleSetReport};
use web_time::{Duration, Instant};

use super::{
    ColumnTy, EGraph, PanicError, PreMergeTiming, Result, RuleId, Value, VariableId, core_relations,
};

/// One typed value supplied for an exact grounded rule invocation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GroundedRuleBinding {
    pub variable: VariableId,
    pub ty: ColumnTy,
    pub value: Value,
}

/// One source-ordered grounded invocation.
///
/// A wave must have strictly increasing [`GroundedRuleRun::invocation_ordinal`]
/// values and is validated atomically against one pre-wave snapshot.
#[derive(Clone, Debug)]
pub struct GroundedRuleRun {
    pub invocation_ordinal: u64,
    pub rule: RuleId,
    pub bindings: Box<[GroundedRuleBinding]>,
}

/// A typed bridge variable descriptor used by the frontend to resolve names
/// without assuming that backend variable ids and bridge ids coincide.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GroundedRuleVariable {
    pub variable: VariableId,
    pub name: Option<Box<str>>,
    pub ty: ColumnTy,
}

impl EGraph {
    /// Return the bridge-local typed variables for one registered rule. Names
    /// are resolved here rather than by casting backend descriptor ids: hidden
    /// timestamp/proof variables make those numeric id spaces differ.
    pub fn grounded_rule_variables(&mut self, rule: RuleId) -> Result<Vec<GroundedRuleVariable>> {
        let info = &mut self.rules[rule];
        anyhow::ensure!(
            info.query.supports_grounded_execution(),
            "rule {} records trace capture and cannot be grounded",
            info.desc
        );
        if info.grounded_rule.is_none() {
            info.grounded_rule = Some(info.query.build_grounded_rule(&mut self.db)?);
        }
        let grounded = info.grounded_rule.as_ref().unwrap();
        Ok(info
            .query
            .grounded_variables()
            .filter(|(variable, _, _)| grounded.variables.get(*variable).is_some())
            .map(|(variable, ty, name)| GroundedRuleVariable { variable, name, ty })
            .collect())
    }

    /// Point-probe and atomically execute a source-ordered wave of exact rule
    /// firings without constructing or consulting a query plan.
    pub fn run_grounded_wave(&mut self, firings: &[GroundedRuleRun]) -> Result<IterationReport> {
        for firing in firings {
            let info = &mut self.rules[firing.rule];
            anyhow::ensure!(
                info.query.supports_grounded_execution(),
                "rule {} records trace capture and cannot be grounded",
                info.desc
            );
            if info.grounded_rule.is_none() {
                info.grounded_rule = Some(info.query.build_grounded_rule(&mut self.db)?);
            }
        }

        let mut core_firings = Vec::with_capacity(firings.len());
        for firing in firings {
            let info = &self.rules[firing.rule];
            let grounded = info.grounded_rule.as_ref().unwrap();
            let mut bindings = Vec::with_capacity(firing.bindings.len());
            for binding in firing.bindings.iter().copied() {
                let expected = info
                    .query
                    .grounded_variable_type(binding.variable)
                    .ok_or_else(|| {
                        anyhow::anyhow!(
                            "grounded invocation {} binds unknown variable {:?}",
                            firing.invocation_ordinal,
                            binding.variable
                        )
                    })?;
                anyhow::ensure!(
                    expected == binding.ty,
                    "grounded invocation {} binds variable {:?} as {:?}, expected {:?}",
                    firing.invocation_ordinal,
                    binding.variable,
                    binding.ty,
                    expected
                );
                let variable = grounded.variables.get(binding.variable).ok_or_else(|| {
                    anyhow::anyhow!(
                        "grounded invocation {} has no compiled slot for variable {:?}",
                        firing.invocation_ordinal,
                        binding.variable
                    )
                })?;
                bindings.push((*variable, binding.value));
            }
            core_firings.push(core_relations::GroundedRuleMatch {
                invocation_ordinal: firing.invocation_ordinal,
                rule: Arc::clone(&grounded.rule),
                bindings: bindings.into_boxed_slice(),
            });
        }

        let uf_size_before = self.db.get_table(self.uf_table).len();
        let panic_message = Arc::clone(&self.panic_message);
        let outcome = self.db.run_grounded_rule_batch(&core_firings, move || {
            panic_message.lock().unwrap().is_none()
        });
        if let Some(message) = self.panic_message.lock().unwrap().take() {
            return Err(PanicError(message).into());
        }
        let outcome = outcome?;
        let mut rule_reports = RuleSetReport::default().rule_reports;
        for firing in firings {
            let desc = Arc::clone(&self.rules[firing.rule].desc);
            let reports = rule_reports.entry(desc).or_default();
            if let Some(report) = reports.first_mut() {
                report.num_matches += 1;
            } else {
                reports.push(RuleReport {
                    num_matches: 1,
                    ..RuleReport::default()
                });
            }
        }
        let mut report = IterationReport {
            rule_set_report: RuleSetReport {
                changed: outcome.changed,
                rule_reports,
                // Grounded replay deliberately has no query plan, scan, or
                // join whose time could be classified as search/apply.
                // Preserve the exact total in the split report's explicit
                // residual bucket so benchmark timing summaries remain
                // available without inventing a phase attribution.
                pre_merge: PreMergeTiming::Split {
                    search: Duration::ZERO,
                    apply: Duration::ZERO,
                    unattributed: outcome.pre_merge_time,
                },
                merge_time: outcome.merge_time,
            },
            rebuild_time: Duration::ZERO,
        };
        let uf_size_after = self.db.get_table(self.uf_table).len();
        if uf_size_before == uf_size_after {
            self.inc_ts();
            return Ok(report);
        }

        let rebuild_timer = Instant::now();
        self.rebuild()?;
        report.rebuild_time = rebuild_timer.elapsed();
        if let Some(message) = self.panic_message.lock().unwrap().take() {
            return Err(PanicError(message).into());
        }
        Ok(report)
    }
}

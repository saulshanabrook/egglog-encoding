use std::sync::Mutex;

use core_relations::{ExecutionState, ExternalFunction, ExternalFunctionId, Value};
use egglog_backend_trait::{BackendExt, ReadMode, RuleSetRun, RuleValue};
use egglog_bridge::{
    ColumnTy, DefaultVal, FunctionConfig, FunctionId, MergeFn, RuleCursorAdvance, RuleId,
    TableAction,
};
use egglog_reports::RunReport;
use numeric_id::define_id;

use crate::{ast::ResolvedVar, core::GenericAtomTerm, core::ResolvedCoreRule, util::IndexMap, *};

/// Whether a scheduler wants a fresh seminaive query for a rule.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SearchPlan {
    /// Do not query this rule in the current scheduler step.
    Skip,
    /// Query the rule, optionally stopping after this many complete matches.
    Search { max_matches: Option<usize> },
}

/// The result of a scheduler-requested query.
#[derive(Clone, Copy, Debug)]
pub enum SearchResult<'a> {
    /// The complete query result.
    Complete(&'a Matches),
    /// The query exceeded its requested bound and was stopped early.
    LimitExceeded { at_least: usize },
}

/// A scheduler's decision for one freshly queried batch.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BatchDecision {
    /// Apply every match and commit the rule's seminaive cursor.
    ApplyAll,
    /// Discard every match and leave the seminaive cursor unchanged.
    Reject,
}

/// A scheduler decides whether to query and accept whole seminaive batches.
pub trait Scheduler: dyn_clone::DynClone + Send + Sync {
    /// Whether or not the rules can be considered as saturated once no database
    /// changes were made in the current iteration.
    ///
    /// This is only called when the runner is otherwise saturated.
    /// Default implementation just returns `true`.
    fn can_stop(&mut self, rules: &[&str], ruleset: &str) -> bool {
        let _ = (rules, ruleset);
        true
    }

    /// Decide whether to query a rule before executing its body.
    fn plan_search(&mut self, rule: &str, ruleset: &str) -> SearchPlan;

    /// Accept or reject the complete result of a requested query.
    fn finish_search(
        &mut self,
        rule: &str,
        ruleset: &str,
        result: SearchResult<'_>,
    ) -> BatchDecision;
}

dyn_clone::clone_trait_object!(Scheduler);

/// A complete collection of matches produced by one rule query.
#[derive(Debug)]
pub struct Matches {
    matches: Vec<Value>,
    vars: Vec<ResolvedVar>,
    row_count: usize,
}

/// A match is a tuple of values corresponding to the variables in a rule.
/// It allows you to retrieve the value corresponding to a variable in the match.
pub struct Match<'a> {
    values: &'a [Value],
    vars: &'a [ResolvedVar],
}

impl Match<'_> {
    /// Get the value corresponding a variable in this match.
    pub fn get_value(&self, var: &str) -> Value {
        let idx = self.vars.iter().position(|v| v.name == var).unwrap();
        self.values[idx]
    }
}

impl Matches {
    fn new(matches: Vec<Value>, vars: Vec<ResolvedVar>, row_count: usize) -> Self {
        assert_eq!(matches.len(), row_count * vars.len());
        Self {
            matches,
            vars,
            row_count,
        }
    }

    /// The number of matches in total.
    pub fn match_size(&self) -> usize {
        self.row_count
    }

    /// The length of a tuple.
    pub fn tuple_len(&self) -> usize {
        self.vars.len()
    }

    /// Get `idx`-th match.
    pub fn get_match(&self, idx: usize) -> Match<'_> {
        assert!(idx < self.row_count);
        Match {
            values: &self.matches[idx * self.tuple_len()..(idx + 1) * self.tuple_len()],
            vars: &self.vars,
        }
    }

    /// Stage every match into the scheduler's decided table.
    fn instantiate(self, state: &mut ExecutionState<'_>, table_action: &TableAction) {
        let tuple_len = self.tuple_len();
        let unit = state.base_values().get(());

        if tuple_len == 0 {
            for _ in 0..self.row_count {
                table_action.insert(state, std::iter::once(unit));
            }
            return;
        }

        for row in self.matches.chunks(tuple_len) {
            table_action.insert(state, row.iter().copied().chain(std::iter::once(unit)));
        }
    }
}

define_id!(
    pub SchedulerId, u32,
    "A unique identifier for a scheduler in the EGraph."
);

impl EGraph {
    /// Register a new scheduler and return its id.
    pub fn add_scheduler(&mut self, scheduler: Box<dyn Scheduler>) -> SchedulerId {
        self.schedulers.push(SchedulerRecord {
            scheduler,
            rule_info: Default::default(),
        })
    }

    /// Register a scheduler under a program-visible name.
    ///
    /// Returns `None` when the name is already bound.
    pub fn add_named_scheduler(
        &mut self,
        name: String,
        scheduler: Box<dyn Scheduler>,
    ) -> Option<SchedulerId> {
        if self.named_schedulers.contains_key(&name) {
            return None;
        }
        let id = self.add_scheduler(scheduler);
        self.named_schedulers.insert(name, id);
        Some(id)
    }

    /// Look up a program-visible scheduler name.
    pub fn named_scheduler(&self, name: &str) -> Option<SchedulerId> {
        self.named_schedulers.get(name).copied()
    }

    /// Removes a scheduler
    pub fn remove_scheduler(&mut self, scheduler_id: SchedulerId) -> Option<Box<dyn Scheduler>> {
        self.named_schedulers
            .retain(|_, named_id| *named_id != scheduler_id);
        self.schedulers.take(scheduler_id).map(|r| r.scheduler)
    }

    /// Runs a ruleset for one iteration using the given ruleset
    pub fn step_rules_with_scheduler(
        &mut self,
        scheduler_id: SchedulerId,
        ruleset: &str,
    ) -> Result<RunReport, Error> {
        fn collect_rules<'a>(
            ruleset: &str,
            rulesets: &'a IndexMap<String, Ruleset>,
            ids: &mut Vec<(String, &'a ResolvedCoreRule)>,
        ) {
            match &rulesets[ruleset] {
                Ruleset::Rules(rules) => {
                    for (rule_name, (core_rule, _)) in rules.iter() {
                        ids.push((rule_name.clone(), core_rule));
                    }
                }
                Ruleset::Combined(sub_rulesets) => {
                    for sub_ruleset in sub_rulesets {
                        collect_rules(sub_ruleset, rulesets, ids);
                    }
                }
            }
        }

        if !self.backend.as_any().is::<egglog_bridge::EGraph>() {
            return Err(Error::BackendError(
                "scheduler match instantiation requires the reference bridge backend".into(),
            ));
        }

        let mut rules = Vec::new();
        let rulesets = std::mem::take(&mut self.rulesets);
        collect_rules(ruleset, &rulesets, &mut rules);
        let mut schedulers = std::mem::take(&mut self.schedulers);
        let result = (|| -> Result<RunReport, Error> {
            // Step 1: build all the query/action rules and worklist if have not already
            let record = &mut schedulers[scheduler_id];
            for (id, rule) in &rules {
                if !record.rule_info.contains_key(id) {
                    let info = SchedulerRuleInfo::new(self, rule, id)?;
                    record.rule_info.insert(id.clone(), info);
                }
            }

            // Step 2: plan and run each bounded query against the same pre-action state.
            let mut query_report = RunReport::default();
            let mut accepted = Vec::new();
            for (rule_id, _rule) in &rules {
                let SearchPlan::Search { max_matches } =
                    record.scheduler.plan_search(rule_id, ruleset)
                else {
                    continue;
                };

                let rule_info = record.rule_info.get_mut(rule_id).unwrap();
                scheduler_collector(self, rule_info.collect_matches).begin(max_matches);
                let (iteration, advance) = self
                    .backend
                    .as_any_mut()
                    .downcast_mut::<egglog_bridge::EGraph>()
                    .expect("reference backend checked above")
                    .probe_rule(rule_info.query_rule)
                    .map_err(|error| Error::BackendError(error.to_string()))?;
                query_report.union(RunReport::singleton(ruleset, iteration));

                let collected = scheduler_collector(self, rule_info.collect_matches).take();
                if collected.limit_exceeded {
                    if record.scheduler.finish_search(
                        rule_id,
                        ruleset,
                        SearchResult::LimitExceeded {
                            at_least: collected.row_count,
                        },
                    ) == BatchDecision::ApplyAll
                    {
                        return Err(Error::BackendError(format!(
                            "scheduler accepted incomplete bounded result for rule `{rule_id}`"
                        )));
                    }
                    continue;
                }

                let matches = Matches::new(
                    collected.values,
                    rule_info.free_vars.clone(),
                    collected.row_count,
                );
                if record.scheduler.finish_search(
                    rule_id,
                    ruleset,
                    SearchResult::Complete(&matches),
                ) == BatchDecision::ApplyAll
                {
                    accepted.push(AcceptedBatch {
                        matches,
                        decided: rule_info.decided,
                        action_rule: rule_info.action_rule,
                        advance,
                    });
                }
            }

            // Step 3: expose only accepted batches to the action rules.
            let bridge = self
                .backend
                .as_any()
                .downcast_ref::<egglog_bridge::EGraph>()
                .expect("reference backend checked above");
            let has_decided_rows = accepted.iter().any(|batch| batch.matches.match_size() > 0);
            let mut action_rules = Vec::new();
            let mut cursor_advances = Vec::new();
            self.backend.with_execution_state(|state| {
                for batch in accepted {
                    if batch.matches.match_size() > 0 {
                        action_rules.push(batch.action_rule);
                    }
                    let table_action = TableAction::new(bridge, batch.decided);
                    batch.matches.instantiate(state, &table_action);
                    cursor_advances.push(batch.advance);
                }
            });
            if has_decided_rows {
                self.backend.flush_updates();
            }

            // Step 4: apply accepted batches, then commit their query cursors.
            let mut action_report = if action_rules.is_empty() {
                RunReport::default()
            } else {
                let action_iteration = self
                    .backend
                    .run_rules(RuleSetRun {
                        name: Some(ruleset),
                        rules: &action_rules,
                    })
                    .map_err(|error| Error::BackendError(error.to_string()))?;
                RunReport::singleton(ruleset, action_iteration)
            };
            let bridge = self
                .backend
                .as_any_mut()
                .downcast_mut::<egglog_bridge::EGraph>()
                .expect("reference backend checked above");
            for advance in cursor_advances {
                bridge.commit_rule_cursor(advance);
            }

            // Step 5: combine the reports.

            // query matches don't count
            query_report.updated = false;
            query_report.num_matches_per_rule.clear();
            // Scheduler state should not count as database progress. Instead it
            // determines whether a no-op iteration can be treated as fully stopped.
            action_report.can_stop = !action_report.updated && {
                let rule_ids = rules.iter().map(|(id, _)| id.as_str()).collect::<Vec<_>>();
                record.scheduler.can_stop(&rule_ids, ruleset)
            };

            query_report.union(action_report);
            Ok(query_report)
        })();

        self.rulesets = rulesets;
        self.schedulers = schedulers;

        result
    }
}

#[derive(Clone)]
pub(crate) struct SchedulerRecord {
    scheduler: Box<dyn Scheduler>,
    rule_info: HashMap<String, SchedulerRuleInfo>,
}

/// To enable scheduling without modifying the backend, split each rule into a
/// query that collects candidate rows and an action rule over a private decided
/// relation. The action rule removes each decided row after staging the source
/// actions so the same logical match can be scheduled again after reinsertion.
#[derive(Clone)]
struct SchedulerRuleInfo {
    collect_matches: ExternalFunctionId,
    decided: FunctionId,
    query_rule: RuleId,
    action_rule: RuleId,
    free_vars: Vec<ResolvedVar>,
}

struct AcceptedBatch {
    matches: Matches,
    decided: FunctionId,
    action_rule: RuleId,
    advance: RuleCursorAdvance,
}

struct SchedulerRuleBuild {
    collect_matches: ExternalFunctionId,
    query_rule: Option<RuleId>,
    decided: Option<FunctionId>,
}

#[derive(Clone, Debug, Default)]
struct CollectedMatches {
    values: Vec<Value>,
    row_count: usize,
    max_matches: Option<usize>,
    limit_exceeded: bool,
}

impl CollectedMatches {
    fn begin(&mut self, max_matches: Option<usize>) {
        self.values.clear();
        self.row_count = 0;
        self.max_matches = max_matches;
        self.limit_exceeded = false;
    }
}

struct CollectMatches {
    matches: Mutex<CollectedMatches>,
}

impl Clone for CollectMatches {
    fn clone(&self) -> Self {
        Self {
            matches: Mutex::new(self.matches.lock().unwrap().clone()),
        }
    }
}

impl CollectMatches {
    fn new() -> Self {
        Self {
            matches: Mutex::new(CollectedMatches::default()),
        }
    }

    fn begin(&self, max_matches: Option<usize>) {
        self.matches.lock().unwrap().begin(max_matches);
    }

    fn take(&self) -> CollectedMatches {
        std::mem::take(&mut *self.matches.lock().unwrap())
    }
}

fn scheduler_collector(egraph: &EGraph, id: ExternalFunctionId) -> &CollectMatches {
    egraph
        .backend
        .as_any()
        .downcast_ref::<egglog_bridge::EGraph>()
        .expect("scheduler collector requires the reference bridge backend")
        .external_function(id)
        .as_any()
        .downcast_ref::<CollectMatches>()
        .expect("scheduler collector id must refer to CollectMatches")
}

impl ExternalFunction for CollectMatches {
    fn invoke(&self, state: &mut core_relations::ExecutionState, args: &[Value]) -> Option<Value> {
        let mut matches = self.matches.lock().unwrap();
        if matches.limit_exceeded {
            state.trigger_early_stop();
            return Some(state.base_values().get(()));
        }

        matches.row_count += 1;
        if matches
            .max_matches
            .is_some_and(|max_matches| matches.row_count > max_matches)
        {
            matches.limit_exceeded = true;
            state.trigger_early_stop();
        } else {
            matches.values.extend(args.iter().copied());
        }
        Some(state.base_values().get(()))
    }
}

impl SchedulerRuleBuild {
    fn rollback(self, egraph: &mut EGraph, error: Error) -> Error {
        let table_result = self.decided.map_or(Ok(()), |table| {
            let bridge = egraph
                .backend
                .as_any_mut()
                .downcast_mut::<egglog_bridge::EGraph>()
                .ok_or_else(|| {
                    Error::BackendError(
                        "scheduler rollback requires the reference bridge backend".into(),
                    )
                })?;
            bridge
                .remove_last_table(table)
                .map_err(|error| Error::BackendError(error.to_string()))
        });
        if let Some(rule) = self.query_rule {
            egraph.backend.free_rule(rule);
        }
        egraph.backend.free_external_func(self.collect_matches);

        match table_result {
            Ok(()) => error,
            Err(rollback_error) => Error::BackendError(format!(
                "{error}; scheduler rule rollback also failed: {rollback_error}"
            )),
        }
    }
}

impl SchedulerRuleInfo {
    fn new(
        egraph: &mut EGraph,
        rule: &ResolvedCoreRule,
        name: &str,
    ) -> Result<SchedulerRuleInfo, Error> {
        let free_vars = rule.head.free_vars();
        let unit_type = egraph.backend.base_values().get_ty::<()>();
        let unit = egraph.backend.base_values().get(());
        let unit_entry = GenericAtomTerm::Literal(
            rule.span.clone(),
            RuleValue {
                value: unit,
                ty: ColumnTy::Base(unit_type),
            },
        );

        let collect_matches = egraph
            .backend
            .register_external_func(Box::new(CollectMatches::new()));
        let mut build = SchedulerRuleBuild {
            collect_matches,
            query_rule: None,
            decided: None,
        };
        let schema = free_vars
            .iter()
            .map(|v| v.sort.column_ty(egraph.backend.base_values()))
            .chain(std::iter::once(ColumnTy::Base(unit_type)))
            .collect();
        // Step 1: build the query rule
        let mut qrule_builder = BackendRule::new(
            &mut *egraph.backend,
            &egraph.functions,
            &egraph.type_info,
            false, // seminaive query: Pure/Write contexts
        );
        if let Err(error) = qrule_builder.query(&rule.body, false) {
            drop(qrule_builder);
            return Err(build.rollback(egraph, error));
        }
        let entries = free_vars
            .iter()
            .map(|fv| qrule_builder.entry(&GenericAtomTerm::Var(span!(), fv.clone())))
            .collect::<Result<Vec<_>, _>>();
        let entries = match entries {
            Ok(entries) => entries,
            Err(error) => {
                drop(qrule_builder);
                return Err(build.rollback(egraph, error));
            }
        };
        qrule_builder.call_external_func(
            rule.span.clone(),
            collect_matches,
            "collect_matches",
            entries,
            ColumnTy::Base(unit_type),
        );
        let qrule_id = match qrule_builder.try_build(name, true, false, rule.span.clone()) {
            Ok(rule) => rule,
            Err(error) => return Err(build.rollback(egraph, error)),
        };
        build.query_rule = Some(qrule_id);

        let decided = egraph.backend.add_table(FunctionConfig {
            schema,
            n_vals: 1,
            n_identity_vals: None,
            default: DefaultVal::Const(unit),
            merge: MergeFn::Old,
            name: "backend".to_string(),
            can_subsume: false,
        });
        build.decided = Some(decided);

        // Step 2: build the action rule
        let mut arule_builder = BackendRule::new(
            &mut *egraph.backend,
            &egraph.functions,
            &egraph.type_info,
            true, // action rule reads the DB: Read/Full contexts
        );
        let entries = free_vars
            .iter()
            .map(|fv| arule_builder.entry(&GenericAtomTerm::Var(span!(), fv.clone())))
            .collect::<Result<Vec<_>, _>>();
        let mut entries = match entries {
            Ok(entries) => entries,
            Err(error) => {
                drop(arule_builder);
                return Err(build.rollback(egraph, error));
            }
        };
        entries.push(unit_entry);
        arule_builder.query_table(rule.span.clone(), decided, entries.clone(), ReadMode::All);
        if let Err(error) = arule_builder.actions(&rule.head) {
            drop(arule_builder);
            return Err(build.rollback(egraph, error));
        }
        // Remove the entry after its source actions have been staged.
        entries.pop();
        arule_builder.remove(rule.span.clone(), decided, "backend", entries);
        let arule_id = match arule_builder.try_build(name, false, false, rule.span.clone()) {
            Ok(rule) => rule,
            Err(error) => return Err(build.rollback(egraph, error)),
        };

        Ok(SchedulerRuleInfo {
            collect_matches,
            free_vars,
            query_rule: qrule_id,
            action_rule: arule_id,
            decided,
        })
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use egglog_backend_trait::RuleSpec;
    use std::sync::Arc;

    fn scheduler_rule_fixture() -> (EGraph, ResolvedCoreRule) {
        let mut egraph = EGraph::default();
        egraph
            .parse_and_run_program(
                None,
                r#"
                (ruleset test)
                (relation R (i64))
                (function F (i64) i64 :no-merge)
                (rule ((R x)) ((set (F x) x)) :ruleset test :name "test-rule")
                "#,
            )
            .unwrap();
        let Ruleset::Rules(rules) = &egraph.rulesets["test"] else {
            unreachable!()
        };
        let rule = rules["test-rule"].0.clone();
        (egraph, rule)
    }

    fn backend_probe(egraph: &mut EGraph) -> ([ExternalFunctionId; 2], [RuleId; 2], FunctionId) {
        let external = std::array::from_fn(|_| {
            egraph
                .backend
                .register_external_func(Box::new(core_relations::make_external_func(
                    |state: &mut ExecutionState<'_>, _args: &[Value]| {
                        Some(state.base_values().get(()))
                    },
                )))
        });
        let rules = std::array::from_fn(|_| {
            egraph
                .backend
                .add_rule(RuleSpec {
                    name: "probe".into(),
                    seminaive: false,
                    no_decomp: false,
                    core: egglog_ast::core::GenericCoreRule {
                        span: span!(),
                        body: Default::default(),
                        head: Default::default(),
                    },
                })
                .unwrap()
        });
        let unit_type = egraph.backend.base_values().get_ty::<()>();
        let unit = egraph.backend.base_values().get(());
        let table = egraph.backend.add_table(FunctionConfig {
            schema: vec![ColumnTy::Base(unit_type)],
            n_vals: 1,
            n_identity_vals: None,
            default: DefaultVal::Const(unit),
            merge: MergeFn::AssertEq,
            name: "probe".into(),
            can_subsume: false,
        });
        (external, rules, table)
    }

    fn assert_failed_construction_restores_backend(mut failed: EGraph, rule: &ResolvedCoreRule) {
        let (mut baseline, _) = scheduler_rule_fixture();
        assert!(SchedulerRuleInfo::new(&mut failed, rule, "test-rule").is_err());

        let bridge = failed
            .backend
            .as_any()
            .downcast_ref::<egglog_bridge::EGraph>()
            .unwrap();
        assert!(
            bridge
                .action_registry()
                .read()
                .unwrap()
                .lookup_table("backend")
                .is_none()
        );
        assert_eq!(backend_probe(&mut baseline), backend_probe(&mut failed));
    }

    #[test]
    fn scheduler_query_failure_rolls_back_backend_resources() {
        let (egraph, mut rule) = scheduler_rule_fixture();
        rule.body.atoms[0].args.pop();
        assert_failed_construction_restores_backend(egraph, &rule);
    }

    #[test]
    fn scheduler_action_failure_rolls_back_backend_resources() {
        let (egraph, mut rule) = scheduler_rule_fixture();
        let (span, function, args) = rule
            .head
            .0
            .iter()
            .find_map(|action| match action {
                crate::core::GenericCoreAction::Set(span, function, args, _) => {
                    Some((span.clone(), function.clone(), args.clone()))
                }
                _ => None,
            })
            .unwrap();
        rule.head.0 = vec![crate::core::GenericCoreAction::Change(
            span,
            crate::ast::Change::Subsume,
            function,
            args,
        )];

        assert_failed_construction_restores_backend(egraph, &rule);
    }

    #[derive(Clone)]
    struct AcceptAllScheduler;

    impl Scheduler for AcceptAllScheduler {
        fn plan_search(&mut self, _rule: &str, _ruleset: &str) -> SearchPlan {
            SearchPlan::Search { max_matches: None }
        }

        fn finish_search(
            &mut self,
            _rule: &str,
            _ruleset: &str,
            _result: SearchResult<'_>,
        ) -> BatchDecision {
            BatchDecision::ApplyAll
        }
    }

    #[test]
    fn test_whole_batch_scheduler() {
        let mut egraph = EGraph::default();
        let scheduler_id = egraph.add_scheduler(Box::new(AcceptAllScheduler));
        let input = r#"
        (relation R (i64))
        (R 0)
        (rule ((R x) (< x 100)) ((R (+ x 1))))
        (run-schedule (saturate (run)))

        (ruleset test)
        (relation S (i64))
        (rule ((R x)) ((S x)) :ruleset test :name "test-rule")
        "#;
        egraph.parse_and_run_program(None, input).unwrap();
        assert_eq!(egraph.get_size("R"), 101);
        let report = egraph
            .step_rules_with_scheduler(scheduler_id, "test")
            .unwrap();
        assert_eq!(egraph.get_size("S"), 101);
        assert_eq!(
            report.num_matches_per_rule.iter().collect::<Vec<_>>(),
            [(&"test-rule".into(), &101)]
        );

        let report = egraph
            .step_rules_with_scheduler(scheduler_id, "test")
            .unwrap();
        assert!(!report.updated);
        assert!(report.can_stop);
    }

    #[test]
    fn scheduler_collectors_are_isolated_across_egraph_clones() {
        let mut original = EGraph::default();
        let scheduler_id = original.add_scheduler(Box::new(AcceptAllScheduler));
        original
            .parse_and_run_program(
                None,
                r#"
                (ruleset test)
                (relation R (i64))
                (relation S (i64))
                (R 0)
                (rule ((R x)) ((S x)) :ruleset test :name "copy")
                "#,
            )
            .unwrap();
        original
            .step_rules_with_scheduler(scheduler_id, "test")
            .unwrap();

        let cloned = original.clone();
        let original_id = original.schedulers[scheduler_id].rule_info["copy"].collect_matches;
        let cloned_id = cloned.schedulers[scheduler_id].rule_info["copy"].collect_matches;
        assert_eq!(original_id, cloned_id);

        let original_collector = scheduler_collector(&original, original_id);
        let cloned_collector = scheduler_collector(&cloned, cloned_id);
        original_collector.begin(Some(17));
        cloned_collector.begin(Some(23));

        assert_eq!(
            original_collector.matches.lock().unwrap().max_matches,
            Some(17)
        );
        assert_eq!(
            cloned_collector.matches.lock().unwrap().max_matches,
            Some(23)
        );
    }

    #[test]
    fn initialized_schedulers_run_independently_across_concurrent_clones() {
        struct CloneAwareScheduler {
            clone_id: usize,
            next_clone_id: Arc<std::sync::atomic::AtomicUsize>,
            observations: Arc<Mutex<Vec<(usize, usize)>>>,
        }

        impl Clone for CloneAwareScheduler {
            fn clone(&self) -> Self {
                Self {
                    clone_id: self
                        .next_clone_id
                        .fetch_add(1, std::sync::atomic::Ordering::Relaxed),
                    next_clone_id: self.next_clone_id.clone(),
                    observations: self.observations.clone(),
                }
            }
        }

        impl Scheduler for CloneAwareScheduler {
            fn plan_search(&mut self, _rule: &str, _ruleset: &str) -> SearchPlan {
                SearchPlan::Search { max_matches: None }
            }

            fn finish_search(
                &mut self,
                _rule: &str,
                _ruleset: &str,
                result: SearchResult<'_>,
            ) -> BatchDecision {
                let SearchResult::Complete(matches) = result else {
                    panic!("unbounded query must complete")
                };
                self.observations
                    .lock()
                    .unwrap()
                    .push((self.clone_id, matches.match_size()));
                BatchDecision::ApplyAll
            }
        }

        let mut left = EGraph::default();
        let observations = Arc::new(Mutex::new(Vec::new()));
        let scheduler_id = left.add_scheduler(Box::new(CloneAwareScheduler {
            clone_id: 0,
            next_clone_id: Arc::new(std::sync::atomic::AtomicUsize::new(1)),
            observations: observations.clone(),
        }));
        left.parse_and_run_program(
            None,
            r#"
            (ruleset test)
            (relation R (i64))
            (relation S (i64))
            (rule ((R x)) ((S x)) :ruleset test :name "copy")
            "#,
        )
        .unwrap();
        left.step_rules_with_scheduler(scheduler_id, "test")
            .unwrap();
        observations.lock().unwrap().clear();

        let mut right = left.clone();
        let left_rows = (0..5_000).map(|i| format!("(R {i})")).collect::<String>();
        let right_rows = (5_000..10_000)
            .map(|i| format!("(R {i})"))
            .collect::<String>();
        left.parse_and_run_program(None, &left_rows).unwrap();
        right.parse_and_run_program(None, &right_rows).unwrap();

        let barrier = Arc::new(std::sync::Barrier::new(2));
        let (left, right) = std::thread::scope(|scope| {
            let left_barrier = barrier.clone();
            let left = scope.spawn(move || {
                left_barrier.wait();
                left.step_rules_with_scheduler(scheduler_id, "test")
                    .unwrap();
                left
            });
            let right = scope.spawn(move || {
                barrier.wait();
                right
                    .step_rules_with_scheduler(scheduler_id, "test")
                    .unwrap();
                right
            });
            (left.join().unwrap(), right.join().unwrap())
        });
        let mut observations = observations.lock().unwrap().clone();
        observations.sort_unstable();
        assert_eq!(observations, [(0, 5_000), (1, 5_000)]);
        assert_eq!(left.get_size("S"), 5_000);
        assert_eq!(right.get_size("S"), 5_000);
    }

    #[derive(Clone)]
    struct BoundedRejectScheduler {
        observed: Arc<Mutex<Option<usize>>>,
    }

    impl Scheduler for BoundedRejectScheduler {
        fn plan_search(&mut self, _rule: &str, _ruleset: &str) -> SearchPlan {
            SearchPlan::Search {
                max_matches: Some(10),
            }
        }

        fn finish_search(
            &mut self,
            _rule: &str,
            _ruleset: &str,
            result: SearchResult<'_>,
        ) -> BatchDecision {
            let SearchResult::LimitExceeded { at_least } = result else {
                panic!("bounded query unexpectedly completed")
            };
            *self.observed.lock().unwrap() = Some(at_least);
            BatchDecision::Reject
        }
    }

    #[test]
    fn test_scheduler_bounds_collected_matches() {
        let mut egraph = EGraph::default();
        let observed = Arc::new(Mutex::new(None));
        let scheduler_id = egraph.add_scheduler(Box::new(BoundedRejectScheduler {
            observed: observed.clone(),
        }));
        egraph
            .parse_and_run_program(
                None,
                r#"
                (relation R (i64))
                (R 0)
                (rule ((R x) (< x 100)) ((R (+ x 1))))
                (run-schedule (saturate (run)))
                (ruleset test)
                (relation S (i64))
                (rule ((R x)) ((S x)) :ruleset test :name "bounded")
                "#,
            )
            .unwrap();

        let report = egraph
            .step_rules_with_scheduler(scheduler_id, "test")
            .unwrap();
        assert_eq!(*observed.lock().unwrap(), Some(11));
        assert_eq!(egraph.get_size("S"), 0);
        assert!(!report.updated);
    }

    #[test]
    fn test_scheduler_does_not_apply_fresh_subsumed_matches() {
        let mut egraph = EGraph::default();
        let scheduler_id = egraph.add_scheduler(Box::new(AcceptAllScheduler));
        let input = r#"
        (ruleset analysis)
        (ruleset test)
        (datatype Math
          (Add Math Math)
          (Mul Math Math)
          (Num i64))
        (relation Hit (i64))
        (let expr (Add (Mul (Num 0) (Num 1)) (Num 2)))
        (rewrite (Mul (Num 0) x) (Num 0) :subsume :ruleset analysis)
        (rewrite (Add (Num 0) x) x :subsume :ruleset analysis)
        (rule ((= e (Add (Mul (Num a) x) (Num b)))) ((Hit a)) :ruleset test :name "hit-subsumed-affine")
        (run-schedule (saturate (run analysis)))
        "#;
        egraph.parse_and_run_program(None, input).unwrap();

        let report = egraph
            .step_rules_with_scheduler(scheduler_id, "test")
            .unwrap();

        assert_eq!(egraph.get_size("Hit"), 0);
        assert!(
            !report.updated,
            "subsumed rows should not be collected as fresh scheduler matches"
        );
    }

    #[derive(Clone, Default)]
    struct DelayStopScheduler {
        can_stop_calls: usize,
    }

    impl Scheduler for DelayStopScheduler {
        fn can_stop(&mut self, _rules: &[&str], _ruleset: &str) -> bool {
            self.can_stop_calls += 1;
            self.can_stop_calls > 1
        }

        fn plan_search(&mut self, _rule: &str, _ruleset: &str) -> SearchPlan {
            SearchPlan::Search { max_matches: None }
        }

        fn finish_search(
            &mut self,
            _rule: &str,
            _ruleset: &str,
            _result: SearchResult<'_>,
        ) -> BatchDecision {
            BatchDecision::Reject
        }
    }

    #[test]
    fn test_scheduler_progress_is_separate_from_database_progress() {
        let mut egraph = EGraph::default();
        let scheduler_id = egraph.add_scheduler(Box::new(DelayStopScheduler::default()));
        let input = r#"
        (ruleset test)
        (relation R (i64))
        (rule ((R x)) ((R x)) :ruleset test :name "noop")
        (R 1)
        (R 2)
        (R 3)
        (R 4)
        "#;
        egraph.parse_and_run_program(None, input).unwrap();

        let before = egraph.get_size("R");
        let report = egraph
            .step_rules_with_scheduler(scheduler_id, "test")
            .unwrap();
        let after = egraph.get_size("R");

        assert_eq!(before, after);
        assert!(!report.updated);
        assert!(!report.can_stop);
    }
}

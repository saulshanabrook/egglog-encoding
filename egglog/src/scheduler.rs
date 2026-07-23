use std::sync::Arc;
use std::sync::Mutex;

use core_relations::{ExecutionState, ExternalFunction, ExternalFunctionId, Value};
use egglog_backend_trait::{BackendExt, ReadMode, RuleSetRun, RuleValue};
use egglog_bridge::{
    ColumnTy, DefaultVal, FunctionConfig, FunctionId, MergeFn, RuleId, TableAction,
};
use egglog_reports::RunReport;
use numeric_id::define_id;

use crate::{ast::ResolvedVar, core::GenericAtomTerm, core::ResolvedCoreRule, util::IndexMap, *};

/// A scheduler decides which matches to be applied for a rule.
///
/// The matches that are not chosen in this iteration will be delayed
/// to the next iteration.
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

    /// Filter the matches for a rule.
    ///
    /// Return `true` if the scheduler's next run of the rule should feed
    /// `filter_matches` with a new iteration of matches.
    fn filter_matches(&mut self, rule: &str, ruleset: &str, matches: &mut Matches) -> bool;
}

dyn_clone::clone_trait_object!(Scheduler);

/// A collection of matches produced by a rule.
/// The user can choose which matches to be fired.
pub struct Matches {
    matches: Vec<Value>,
    chosen: Vec<usize>,
    vars: Vec<ResolvedVar>,
    all_chosen: bool,
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
    fn new(matches: Vec<Value>, vars: Vec<ResolvedVar>) -> Self {
        let total_len = matches.len();
        let tuple_len = vars.len();
        assert!(total_len.is_multiple_of(tuple_len));
        Self {
            matches,
            vars,
            chosen: Vec::new(),
            all_chosen: false,
        }
    }

    /// The number of matches in total.
    pub fn match_size(&self) -> usize {
        self.matches.len() / self.vars.len()
    }

    /// The length of a tuple.
    pub fn tuple_len(&self) -> usize {
        self.vars.len()
    }

    /// Get `idx`-th match.
    pub fn get_match(&self, idx: usize) -> Match<'_> {
        Match {
            values: &self.matches[idx * self.tuple_len()..(idx + 1) * self.tuple_len()],
            vars: &self.vars,
        }
    }

    /// Pick the match at `idx` to be fired.
    pub fn choose(&mut self, idx: usize) {
        self.chosen.push(idx);
    }

    /// Pick all matches to be fired.
    ///
    /// This is more efficient than calling `choose` for each match.
    pub fn choose_all(&mut self) {
        self.all_chosen = true;
    }

    /// Apply the chosen matches and return the residual matches.
    fn instantiate(
        mut self,
        state: &mut ExecutionState<'_>,
        table_action: &TableAction,
    ) -> Vec<Value> {
        let tuple_len = self.tuple_len();
        let unit = state.base_values().get(());

        if self.all_chosen {
            for row in self.matches.chunks(tuple_len) {
                table_action.insert(state, row.iter().cloned().chain(std::iter::once(unit)));
            }
            vec![]
        } else {
            for idx in self.chosen.iter() {
                let row = &self.matches[idx * tuple_len..(idx + 1) * tuple_len];
                table_action.insert(state, row.iter().cloned().chain(std::iter::once(unit)));
            }

            // swap remove the chosen matches
            self.chosen.sort_unstable();
            self.chosen.dedup();
            let mut p = self.match_size();
            for c in self.chosen.into_iter().rev() {
                // It's important to decrement `p` first, because otherwise it might underflow when
                // matches are exhausted.
                p -= 1;
                if c != p {
                    let idx_c = c * tuple_len;
                    let idx_p = p * tuple_len;
                    for i in 0..tuple_len {
                        self.matches.swap(idx_c + i, idx_p + i);
                    }
                }
            }
            self.matches.truncate(p * tuple_len);

            self.matches
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

    /// Removes a scheduler
    pub fn remove_scheduler(&mut self, scheduler_id: SchedulerId) -> Option<Box<dyn Scheduler>> {
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
                    for (rule_name, rule) in rules.iter() {
                        ids.push((rule_name.clone(), &rule.core));
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

            // Step 2: run all the queries for one iteration
            let query_rules = rules
                .iter()
                .filter_map(|(rule_id, _rule)| {
                    let rule_info = record.rule_info.get(rule_id).unwrap();

                    if rule_info.should_seek {
                        Some(rule_info.query_rule)
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();

            let query_iter_report = self
                .backend
                .run_rules(RuleSetRun {
                    name: Some(ruleset),
                    rules: &query_rules,
                })
                .map_err(|e| Error::BackendError(e.to_string()))?;

            // Step 3: let the scheduler decide which matches need to be kept
            let bridge = self
                .backend
                .as_any()
                .downcast_ref::<egglog_bridge::EGraph>()
                .ok_or_else(|| {
                    Error::BackendError(
                        "scheduler match instantiation requires the reference bridge backend"
                            .into(),
                    )
                })?;
            self.backend.with_execution_state(|state| {
                for (rule_id, _rule) in &rules {
                    let rule_info = record.rule_info.get_mut(rule_id).unwrap();

                    let matches: Vec<Value> =
                        std::mem::take(rule_info.matches.lock().unwrap().as_mut());
                    let mut matches = Matches::new(matches, rule_info.free_vars.clone());
                    rule_info.should_seek =
                        record
                            .scheduler
                            .filter_matches(rule_id, ruleset, &mut matches);
                    let table_action = TableAction::new(bridge, rule_info.decided);
                    *rule_info.matches.lock().unwrap() = matches.instantiate(state, &table_action);
                }
            });
            self.backend.flush_updates();

            // Step 4: run the action rules
            let action_rules = rules
                .iter()
                .map(|(rule_id, _rule)| {
                    let rule_info = record.rule_info.get(rule_id).unwrap();
                    rule_info.action_rule
                })
                .collect::<Vec<_>>();
            let action_iter_report = self
                .backend
                .run_rules(RuleSetRun {
                    name: Some(ruleset),
                    rules: &action_rules,
                })
                .map_err(|e| Error::BackendError(e.to_string()))?;

            // Step 5: combine the reports
            let mut query_report = RunReport::singleton(ruleset, query_iter_report);
            let mut action_report = RunReport::singleton(ruleset, action_iter_report);

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

/// To enable scheduling without modifying the backend,
/// we split a rule (rule query action) into a worklist relation
/// two rules (rule query (worklist vars false)) and
/// (rule (worklist vars false) (action ... (delete (worklist vars false))))
#[derive(Clone)]
struct SchedulerRuleInfo {
    matches: Arc<Mutex<Vec<Value>>>,
    should_seek: bool,
    decided: FunctionId,
    query_rule: RuleId,
    action_rule: RuleId,
    free_vars: Vec<ResolvedVar>,
}

struct SchedulerRuleBuild {
    collect_matches: ExternalFunctionId,
    query_rule: Option<RuleId>,
    decided: Option<FunctionId>,
}

struct CollectMatches {
    matches: Arc<Mutex<Vec<Value>>>,
}

impl Clone for CollectMatches {
    fn clone(&self) -> Self {
        Self {
            matches: Arc::new(Mutex::new(self.matches.lock().unwrap().clone())),
        }
    }
}

impl CollectMatches {
    fn new(matches: Arc<Mutex<Vec<Value>>>) -> Self {
        Self { matches }
    }
}

impl ExternalFunction for CollectMatches {
    fn invoke(&self, state: &mut core_relations::ExecutionState, args: &[Value]) -> Option<Value> {
        self.matches.lock().unwrap().extend(args.iter().copied());
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

        let matches = Arc::new(Mutex::new(Vec::new()));
        let collect_matches = egraph
            .backend
            .register_external_func(Box::new(CollectMatches::new(matches.clone())));
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
            &mut egraph.unstable_fn_panic_ids,
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
            &mut egraph.unstable_fn_panic_ids,
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
        // Remove the entry as it's now done
        entries.pop();
        arule_builder.remove(rule.span.clone(), decided, "backend", entries);
        let arule_id = match arule_builder.try_build(name, false, false, rule.span.clone()) {
            Ok(rule) => rule,
            Err(error) => return Err(build.rollback(egraph, error)),
        };

        Ok(SchedulerRuleInfo {
            free_vars,
            query_rule: qrule_id,
            action_rule: arule_id,
            matches,
            decided,
            should_seek: true,
        })
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use egglog_backend_trait::RuleSpec;

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
        let rule = rules["test-rule"].core.clone();
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
                    owned_external_funcs: Vec::new(),
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
    struct FirstNScheduler {
        n: usize,
    }

    impl Scheduler for FirstNScheduler {
        fn filter_matches(&mut self, _rule: &str, _ruleset: &str, matches: &mut Matches) -> bool {
            if matches.match_size() <= self.n {
                matches.choose_all();
            } else {
                for i in 0..self.n {
                    matches.choose(i);
                }
            }
            matches.match_size() < self.n * 2
        }
    }

    #[test]
    fn test_first_n_scheduler() {
        let mut egraph = EGraph::default();
        let scheduler = FirstNScheduler { n: 10 };
        let scheduler_id = egraph.add_scheduler(Box::new(scheduler));
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
        let mut iter = 0;
        loop {
            let report = egraph
                .step_rules_with_scheduler(scheduler_id, "test")
                .unwrap();
            let table_size = egraph.get_size("S");
            iter += 1;
            assert_eq!(table_size, std::cmp::min(iter * 10, 101));

            let expected_matches = if iter <= 10 { 10 } else { 12 - iter };
            assert_eq!(
                report.num_matches_per_rule.iter().collect::<Vec<_>>(),
                [(&"test-rule".into(), &expected_matches)]
            );

            // Because of semi-naive, the exact rules that are run are more than just `test-rule`
            assert!(
                report
                    .search_and_apply_time_per_rule
                    .keys()
                    .all(|k| k.starts_with("test-rule"))
            );
            assert_eq!(
                report.ruleset_timings.keys().collect::<Vec<_>>(),
                [&"test".into()]
            );

            if report.can_stop {
                break;
            }
        }

        assert_eq!(iter, 12);
    }

    #[test]
    fn test_scheduler_does_not_apply_fresh_subsumed_matches() {
        let mut egraph = EGraph::default();
        let scheduler_id = egraph.add_scheduler(Box::new(FirstNScheduler { n: 10 }));
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

        fn filter_matches(&mut self, _rule: &str, _ruleset: &str, _matches: &mut Matches) -> bool {
            false
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

use std::sync::Arc;

use egglog_reports::{PreMergeTiming, ReportLevel, RuleReport, RuleSetReport};
use web_time::{Duration, Instant};

use crate::{
    AtomId, Database, GuardedRuleSetBatchRunOutcome, GuardedRuleSetRunError, OffsetRange, RuleSet,
    Subset, Value,
    common::{HashMap, HashSet},
    free_join::{ActionId, Variable},
    numeric_id::NumericId,
};

use super::{Bindings, ExecutionState};

impl Database {
    /// Validate exact native premise rows against one shared pre-state, then
    /// execute the already-compiled rule-head suffixes in list order and merge
    /// once. No rule body join or residual-query instruction is re-executed.
    ///
    /// Each premise is addressed by its plan-local [`AtomId`]. A mismatch in
    /// any run returns before any head is executed. This initial replay seam is
    /// deliberately fail-closed for heads that depend on residual-query
    /// instructions; a receipt for such a rule would need to retain those
    /// derived values as well as its exact table rows.
    pub fn run_rule_sets_exact_rows_batch(
        &mut self,
        runs: &[(&RuleSet, &[(AtomId, &[Value])])],
        report_level: ReportLevel,
    ) -> Result<GuardedRuleSetBatchRunOutcome, GuardedRuleSetRunError> {
        let pre_merge_timer = Instant::now();
        let mut prepared = Vec::with_capacity(runs.len());
        let mut validation_times = Vec::with_capacity(runs.len());
        let mut total_validation_time = Duration::ZERO;

        // Finish every read and structural check before constructing the
        // execution state. This is the atomicity boundary for premise failure.
        for (run_index, (rule_set, premises)) in runs.iter().enumerate() {
            let validation_timer = Instant::now();
            let Some((action, bindings)) = prepare_exact_row_run(self, rule_set, premises)? else {
                return Ok(GuardedRuleSetBatchRunOutcome::MatchCountMismatch {
                    run_index,
                    expected_matches: 1,
                    observed_matches: 0,
                });
            };
            let elapsed = validation_timer.elapsed();
            total_validation_time += elapsed;
            validation_times.push(elapsed);
            prepared.push((action, bindings));
        }

        let mut apply_times = Vec::with_capacity(runs.len());
        let mut action_matches = Vec::with_capacity(runs.len());
        let mut total_apply_time = Duration::ZERO;
        let mut exec_state = ExecutionState::new(self.read_only_view(), Default::default());
        for ((rule_set, _), (action, mut bindings)) in runs.iter().zip(prepared) {
            let action_info = &rule_set.actions[action];
            let apply_timer = Instant::now();
            let succeeded =
                exec_state.run_instrs(&action_info.instrs[action_info.head_start..], &mut bindings);
            let elapsed = apply_timer.elapsed();
            total_apply_time += elapsed;
            apply_times.push(elapsed);
            action_matches.push(succeeded);
        }
        // Buffer handles publish staged rows on drop. Publish all heads before
        // the one merge below, matching grounded-batch action execution.
        drop(exec_state);

        let mut rule_reports: HashMap<Arc<str>, Vec<RuleReport>> = HashMap::default();
        for (run_index, (rule_set, _)) in runs.iter().enumerate() {
            let (plan, description, symbol_map) = rule_set
                .plans
                .values()
                .next()
                .expect("a prepared exact-row run has one plan");
            let plan = match report_level {
                ReportLevel::TimeOnly => None,
                ReportLevel::WithPlan | ReportLevel::StageInfo => Some(plan.to_report(symbol_map)),
            };
            rule_reports
                .entry(description.clone())
                .or_default()
                .push(RuleReport {
                    plan,
                    search_and_apply_time: validation_times[run_index] + apply_times[run_index],
                    num_matches: action_matches[run_index],
                });
        }

        let pre_merge_elapsed = pre_merge_timer.elapsed();
        let unattributed =
            pre_merge_elapsed.saturating_sub(total_validation_time + total_apply_time);
        let merge_timer = Instant::now();
        let changed = self.merge_all();
        let merge_time = merge_timer.elapsed();
        Ok(GuardedRuleSetBatchRunOutcome::Applied {
            observed_matches: vec![1; runs.len()],
            report: RuleSetReport {
                changed,
                rule_reports,
                pre_merge: PreMergeTiming::Split {
                    search: total_validation_time,
                    apply: total_apply_time,
                    unattributed,
                },
                merge_time,
            },
        })
    }
}

fn prepare_exact_row_run(
    db: &Database,
    rule_set: &RuleSet,
    premises: &[(AtomId, &[Value])],
) -> Result<Option<(ActionId, Bindings)>, GuardedRuleSetRunError> {
    if rule_set.plans.len() > 1 {
        return Err(GuardedRuleSetRunError::MultipleExecutablePlans {
            plan_count: rule_set.plans.len(),
        });
    }
    let Some((plan, _, _)) = rule_set.plans.values().next() else {
        return Ok(None);
    };
    let action = plan.actions();
    let action_info = &rule_set.actions[action];
    if action_info.head_start > action_info.instrs.len() {
        return Err(GuardedRuleSetRunError::InvalidQueryHeadBoundary);
    }
    if action_info.head_start != 0 {
        return Err(GuardedRuleSetRunError::UnsupportedQueryPrefix);
    }

    let atoms = plan.atoms();
    if premises.len() != atoms.len() {
        return Ok(None);
    }
    let mut seen_atoms = HashSet::default();
    let mut values = HashMap::<Variable, Value>::default();
    for (atom_id, expected_row) in premises {
        if !seen_atoms.insert(*atom_id) {
            return Ok(None);
        }
        let Some(atom) = atoms.get(*atom_id) else {
            return Ok(None);
        };
        let table_info = db.get_table_info(atom.table);
        if expected_row.len() != table_info.spec().arity() {
            return Ok(None);
        }
        let table = table_info.table();
        let Some(actual_row) = table.get_row(&expected_row[..table_info.spec().n_keys]) else {
            return Ok(None);
        };
        if actual_row.vals.as_slice() != *expected_row {
            return Ok(None);
        }

        // Reuse the table's native constraint implementation on this one row;
        // exact replay must not invent a second query/filter evaluator.
        let singleton = Subset::Dense(OffsetRange::new(actual_row.id, actual_row.id.inc()));
        let constrained = table.refine(singleton, &atom.constraints.fast);
        let mut constrained = table.refine(constrained, &atom.constraints.slow);
        for header in plan
            .header()
            .iter()
            .filter(|header| header.atom == *atom_id)
        {
            constrained = table.refine(constrained, &header.constraints);
        }
        if constrained.size() != 1 {
            return Ok(None);
        }

        for (column, variable) in atom.var_columns.iter() {
            let value = expected_row[column.index()];
            if values
                .insert(variable, value)
                .is_some_and(|old| old != value)
            {
                return Ok(None);
            }
        }
    }
    if seen_atoms.len() != atoms.len()
        || action_info
            .used_vars
            .iter()
            .any(|variable| !values.contains_key(variable))
    {
        return Ok(None);
    }

    let mut bindings = Bindings::new(1);
    for variable in &action_info.used_vars {
        bindings.insert(*variable, &[values[variable]]);
    }
    Ok(Some((action, bindings)))
}

#[cfg(test)]
mod tests {
    use std::iter;

    use egglog_reports::ReportLevel;

    use crate::{
        Database, GuardedRuleSetBatchRunOutcome, RuleSet, RuleSetBuilder, SortedWritesTable,
        TableId, table_shortcuts::v,
    };

    fn relation() -> SortedWritesTable {
        SortedWritesTable::new(1, 1, None, vec![], Box::new(|_, _, _, _| false))
    }

    fn copy_rule(
        db: &mut Database,
        input: TableId,
        output: TableId,
        description: &str,
    ) -> (RuleSet, crate::AtomId) {
        let mut rules = RuleSetBuilder::new(db);
        let mut query = rules.new_rule();
        query.set_no_decomp(true);
        let value = query.new_var_named("value");
        let atom = query.add_atom(input, &[value.into()], &[]).unwrap();
        let mut rule = query.build();
        rule.finish_query();
        rule.insert(output, &[value.into()]).unwrap();
        rule.build_with_description(description);
        (rules.build(), atom)
    }

    #[test]
    fn exact_rows_validate_atomically_before_replaying_compiled_heads() {
        let mut db = Database::default();
        let input = db.add_table(relation(), iter::empty(), iter::empty());
        let first_output = db.add_table(relation(), iter::empty(), iter::empty());
        let second_output = db.add_table(relation(), iter::empty(), iter::empty());
        {
            let mut buffer = db.new_buffer(input);
            buffer.stage_insert(&[v(7)]);
            buffer.stage_insert(&[v(9)]);
        }
        db.merge_all();

        let (first_rule, first_atom) = copy_rule(&mut db, input, first_output, "exact-row-first");
        let (second_rule, second_atom) =
            copy_rule(&mut db, input, second_output, "exact-row-second");
        let first_row = [v(7)];
        let second_row = [v(9)];
        let altered_row = [v(8)];
        let first_premises = [(first_atom, first_row.as_slice())];
        let second_premises = [(second_atom, second_row.as_slice())];
        let altered_premises = [(second_atom, altered_row.as_slice())];

        let missing = db
            .run_rule_sets_exact_rows_batch(
                &[
                    (&first_rule, first_premises.as_slice()),
                    (&second_rule, &[]),
                ],
                ReportLevel::TimeOnly,
            )
            .unwrap();
        assert!(matches!(
            missing,
            GuardedRuleSetBatchRunOutcome::MatchCountMismatch {
                run_index: 1,
                expected_matches: 1,
                observed_matches: 0,
            }
        ));
        assert!(!db.merge_all(), "a rejected batch left a staged head");
        assert!(db.get_table(first_output).get_row(&first_row).is_none());
        assert!(db.get_table(second_output).get_row(&second_row).is_none());

        let altered = db
            .run_rule_sets_exact_rows_batch(
                &[
                    (&first_rule, first_premises.as_slice()),
                    (&second_rule, altered_premises.as_slice()),
                ],
                ReportLevel::TimeOnly,
            )
            .unwrap();
        assert!(matches!(
            altered,
            GuardedRuleSetBatchRunOutcome::MatchCountMismatch {
                run_index: 1,
                expected_matches: 1,
                observed_matches: 0,
            }
        ));
        assert!(!db.merge_all(), "a rejected batch left a staged head");
        assert!(db.get_table(first_output).get_row(&first_row).is_none());
        assert!(db.get_table(second_output).get_row(&second_row).is_none());

        let applied = db
            .run_rule_sets_exact_rows_batch(
                &[
                    (&first_rule, first_premises.as_slice()),
                    (&second_rule, second_premises.as_slice()),
                ],
                ReportLevel::TimeOnly,
            )
            .unwrap();
        assert!(matches!(
            applied,
            GuardedRuleSetBatchRunOutcome::Applied {
                observed_matches,
                report,
            } if observed_matches == [1, 1] && report.changed
        ));
        assert!(db.get_table(first_output).get_row(&first_row).is_some());
        assert!(db.get_table(second_output).get_row(&second_row).is_some());
    }
}

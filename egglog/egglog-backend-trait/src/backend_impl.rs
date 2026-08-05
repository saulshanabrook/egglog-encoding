//! `impl Backend for egglog_bridge::EGraph` — the in-memory reference backend.
//!
//! Every method is a thin passthrough to an inherent method on the bridge
//! `EGraph`. Lives in this crate (not in `egglog-bridge`) so the bridge stays
//! free of any dependency on the trait; the orphan rule permits it because the
//! [`Backend`] trait is local here.

use std::any::Any;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Arc, RwLock};

use anyhow::{Result, bail, ensure};
use egglog_bridge::{ActionRegistry, EGraph, QueryEntry, RuleBuilder};

use egglog_ast::core::{GenericAtomTerm, GenericCoreAction};

use crate::{
    Backend, BaseValues, ColumnTy, ContainerValues, ExecutionState, ExternalFunction,
    ExternalFunctionId, FunctionConfig, FunctionId, IterationReport, NativeInputValue, ReportLevel,
    RuleActionCall, RuleBodyCall, RuleId, RuleSetRun, RuleSpec, RuleValue, RuleVar, ScanEntry,
    Value,
};

fn rule_entry(
    builder: &mut RuleBuilder<'_>,
    variables: &mut BTreeMap<u32, QueryEntry>,
    term: &GenericAtomTerm<RuleVar, RuleValue>,
) -> Result<QueryEntry> {
    match term {
        GenericAtomTerm::Var(_, variable) => Ok(variables
            .entry(variable.id)
            .or_insert_with(|| builder.new_var_named(variable.ty, &variable.name))
            .clone()),
        GenericAtomTerm::Literal(_, constant) => Ok(QueryEntry::Const {
            val: constant.value,
            ty: constant.ty,
        }),
        GenericAtomTerm::Global(..) => bail!("globals must be desugared before backend lowering"),
    }
}

fn rule_entries(
    builder: &mut RuleBuilder<'_>,
    variables: &mut BTreeMap<u32, QueryEntry>,
    terms: &[GenericAtomTerm<RuleVar, RuleValue>],
) -> Result<Vec<QueryEntry>> {
    terms
        .iter()
        .map(|term| rule_entry(builder, variables, term))
        .collect()
}

fn term_ty(term: &GenericAtomTerm<RuleVar, RuleValue>) -> ColumnTy {
    match term {
        GenericAtomTerm::Var(_, variable) | GenericAtomTerm::Global(_, variable) => variable.ty,
        GenericAtomTerm::Literal(_, value) => value.ty,
    }
}

#[derive(Default)]
struct IndexValidation {
    self_binding_columns: BTreeMap<usize, usize>,
}

fn validate_index_atoms(egraph: &EGraph, rule: &RuleSpec) -> Result<IndexValidation> {
    if !rule
        .core
        .body
        .atoms
        .iter()
        .any(|atom| matches!(&atom.head, RuleBodyCall::IndexTable { .. }))
    {
        return Ok(IndexValidation::default());
    }
    let unit_ty = ColumnTy::Base(egraph.base_values().get_ty::<()>());
    let unit = egraph.base_values().get(());
    for atom in &rule.core.body.atoms {
        let RuleBodyCall::IndexTable { id, any_of, .. } = &atom.head else {
            continue;
        };
        let schema = egraph.function_schema(*id).ok_or_else(|| {
            anyhow::anyhow!(
                "reference backend cannot add rule {:?}: unregistered index target {:?}",
                rule.name,
                id
            )
        })?;
        ensure!(
            atom.args.len() == schema.len() + 2,
            "reference backend cannot add rule {:?}: index atom has {}, expected {} arguments",
            rule.name,
            atom.args.len(),
            schema.len() + 2
        );
        ensure!(
            !any_of.is_empty(),
            "reference backend cannot add rule {:?}: index atom lists no occurrence columns",
            rule.name
        );
        ensure!(
            any_of.iter().all(|&column| column < schema.len()),
            "reference backend cannot add rule {:?}: index atom has an out-of-range occurrence column",
            rule.name
        );
        let probe = &atom.args[0];
        for &column in any_of {
            ensure!(
                term_ty(probe) == schema[column],
                "reference backend cannot add rule {:?}: index probe type disagrees with occurrence column {column}",
                rule.name
            );
        }
        for (term, &expected) in atom.args[1..=schema.len()].iter().zip(schema) {
            ensure!(
                term_ty(term) == expected,
                "reference backend cannot add rule {:?}: index row has a mistyped column",
                rule.name
            );
        }
        let Some(GenericAtomTerm::Literal(_, output)) = atom.args.last() else {
            bail!(
                "reference backend cannot add rule {:?}: index output must be canonical Unit",
                rule.name
            )
        };
        ensure!(
            output.ty == unit_ty && output.value == unit,
            "reference backend cannot add rule {:?}: index output must be canonical Unit",
            rule.name
        );
    }

    let mut reachable = BTreeSet::<u32>::new();
    for atom in &rule.core.body.atoms {
        if !matches!(&atom.head, RuleBodyCall::Table { .. }) {
            continue;
        }
        for term in &atom.args {
            if let GenericAtomTerm::Var(_, variable) = term {
                reachable.insert(variable.id);
            }
        }
    }
    let mut admitted_indices = BTreeSet::<usize>::new();
    let mut self_binding_columns = BTreeMap::<usize, usize>::new();
    loop {
        let mut changed = false;
        for (atom_index, atom) in rule.core.body.atoms.iter().enumerate() {
            let RuleBodyCall::IndexTable { id, any_of, .. } = &atom.head else {
                continue;
            };
            if admitted_indices.contains(&atom_index) {
                continue;
            }
            let schema = egraph.function_schema(*id).ok_or_else(|| {
                anyhow::anyhow!(
                    "reference backend cannot add rule {:?}: unregistered index target {:?}",
                    rule.name,
                    id
                )
            })?;
            let any_of = any_of.iter().copied().collect::<BTreeSet<_>>();
            let probe = &atom.args[0];
            let row = &atom.args[1..=schema.len()];
            let bind_column = match probe {
                GenericAtomTerm::Literal(..) => None,
                GenericAtomTerm::Var(_, variable) if reachable.contains(&variable.id) => None,
                GenericAtomTerm::Var(_, variable) => row
                    .iter()
                    .enumerate()
                    .find_map(|(column, term)| {
                        (any_of.contains(&column)
                            && matches!(term, GenericAtomTerm::Var(_, row) if row.id == variable.id))
                        .then_some(column)
                    })
                    .or_else(|| {
                        (any_of.len() == 1)
                            .then(|| any_of.iter().next().copied())
                            .flatten()
                    }),
                GenericAtomTerm::Global(..) => continue,
            };
            let ready = matches!(probe, GenericAtomTerm::Literal(..))
                || matches!(probe, GenericAtomTerm::Var(_, variable) if reachable.contains(&variable.id))
                || bind_column.is_some();
            if !ready {
                continue;
            }
            if let GenericAtomTerm::Var(_, variable) = probe {
                if let Some(column) = bind_column {
                    self_binding_columns.insert(atom_index, column);
                }
                reachable.insert(variable.id);
            }
            for term in row {
                if let GenericAtomTerm::Var(_, variable) = term {
                    reachable.insert(variable.id);
                }
            }
            admitted_indices.insert(atom_index);
            changed = true;
        }
        if !changed {
            break;
        }
    }
    for (atom_index, atom) in rule.core.body.atoms.iter().enumerate() {
        if !matches!(&atom.head, RuleBodyCall::IndexTable { .. })
            || admitted_indices.contains(&atom_index)
        {
            continue;
        }
        let probe = atom.args.first().and_then(|term| match term {
            GenericAtomTerm::Var(_, variable) | GenericAtomTerm::Global(_, variable) => {
                Some(variable.id)
            }
            GenericAtomTerm::Literal(..) => None,
        });
        bail!(
            "reference backend cannot add rule {:?}: index probe variable {:?} is not reachable from a row binder",
            rule.name,
            probe
        );
    }
    Ok(IndexValidation {
        self_binding_columns,
    })
}

fn build_rule(egraph: &mut EGraph, rule: RuleSpec) -> Result<RuleId> {
    let index_validation = validate_index_atoms(egraph, &rule)?;
    let RuleSpec {
        name,
        seminaive,
        no_decomp,
        core,
    } = rule;
    let mut builder = egraph.new_rule(&name, seminaive);
    builder.set_no_decomp(no_decomp);
    let mut variables = BTreeMap::new();

    // A self-binding occurrence is an ordinary row scan: the selected column
    // supplies the probe, making the disjunction tautological. Alias both rule
    // variables before lowering any atom so source order cannot split them.
    for (&atom_index, &column) in &index_validation.self_binding_columns {
        let atom = &core.body.atoms[atom_index];
        let GenericAtomTerm::Var(_, probe) = &atom.args[0] else {
            continue;
        };
        let row_term = &atom.args[column + 1];
        let entry = rule_entry(&mut builder, &mut variables, row_term)?;
        variables.insert(probe.id, entry);
    }

    for (atom_index, atom) in core.body.atoms.iter().enumerate() {
        let entries = rule_entries(&mut builder, &mut variables, &atom.args)?;
        match &atom.head {
            RuleBodyCall::Table { id, read } => {
                builder.query_table(*id, &entries, read.is_subsumed())?;
            }
            RuleBodyCall::IndexTable { id, any_of, read } => {
                // An index is declared as the relation `(value, row…) -> Unit`, so
                // its atom carries the occurring value, the indexed function's row,
                // and the relation's own unit output. Only the row belongs to the
                // underlying function.
                let (indexed, rest) = entries.split_first().ok_or_else(|| {
                    anyhow::anyhow!("validated index atom unexpectedly has no probe")
                })?;
                let (_unit, row) = rest.split_last().ok_or_else(|| {
                    anyhow::anyhow!("validated index atom unexpectedly has no Unit output")
                })?;
                if index_validation
                    .self_binding_columns
                    .contains_key(&atom_index)
                {
                    builder.query_table(*id, row, read.is_subsumed())?;
                } else {
                    let any_of = any_of
                        .iter()
                        .copied()
                        .collect::<std::collections::BTreeSet<_>>()
                        .into_iter()
                        .collect::<Vec<_>>();
                    builder.query_table_by_occurrence(
                        *id,
                        row,
                        indexed.clone(),
                        &any_of,
                        read.is_subsumed(),
                    )?;
                }
            }
            RuleBodyCall::Primitive { id, output, .. } => {
                builder.query_prim(*id, &entries, *output)?;
            }
        }
    }

    for action in &core.head.0 {
        match action {
            GenericCoreAction::Let(span, variable, call, arguments) => {
                let entries = rule_entries(&mut builder, &mut variables, arguments)?;
                let result: QueryEntry = match call {
                    RuleActionCall::Table { id, name } => {
                        let span = span.clone();
                        let name = name.clone();
                        builder
                            .lookup(*id, &entries, move || {
                                format!("{span}: lookup of function {name} failed")
                            })
                            .into()
                    }
                    RuleActionCall::Primitive {
                        id, name, output, ..
                    } => {
                        let span = span.clone();
                        let name = name.clone();
                        builder
                            .call_external_func(*id, &entries, *output, move || {
                                format!("{span}: call of primitive {name} failed")
                            })
                            .into()
                    }
                };
                variables.insert(variable.id, result);
            }
            GenericCoreAction::LetAtomTerm(_, variable, term) => {
                let entry = rule_entry(&mut builder, &mut variables, term)?;
                variables.insert(variable.id, entry);
            }
            GenericCoreAction::Set(_, call, arguments, values) => {
                let RuleActionCall::Table { id, .. } = call else {
                    bail!("cannot set a primitive")
                };
                let mut entries = rule_entries(&mut builder, &mut variables, arguments)?;
                entries.extend(rule_entries(&mut builder, &mut variables, values)?);
                builder.set(*id, &entries);
            }
            GenericCoreAction::Change(_, change, call, arguments) => {
                let RuleActionCall::Table { id, .. } = call else {
                    bail!("cannot delete or subsume a primitive")
                };
                let entries = rule_entries(&mut builder, &mut variables, arguments)?;
                match change {
                    egglog_ast::generic_ast::Change::Delete => builder.remove(*id, &entries),
                    egglog_ast::generic_ast::Change::Subsume => builder.subsume(*id, &entries),
                }
            }
            GenericCoreAction::Union(_, lhs, rhs) => {
                let lhs = rule_entry(&mut builder, &mut variables, lhs)?;
                let rhs = rule_entry(&mut builder, &mut variables, rhs)?;
                builder.union(lhs, rhs);
            }
            GenericCoreAction::Panic(_, message) => builder.panic(message.clone()),
        }
    }

    Ok(builder.build())
}

// ---------------------------------------------------------------------------
// Backend for the bridge EGraph
// ---------------------------------------------------------------------------

impl Backend for EGraph {
    fn add_table(&mut self, config: FunctionConfig) -> FunctionId {
        EGraph::add_table(self, config)
    }

    fn peek_next_function_id(&self) -> FunctionId {
        EGraph::peek_next_function_id(self)
    }

    fn table_size(&self, table: FunctionId) -> usize {
        EGraph::table_size(self, table)
    }

    fn clear_table(&mut self, func: FunctionId) {
        EGraph::clear_table(self, func);
    }

    fn for_each_while_dyn(
        &self,
        table: FunctionId,
        f: &mut dyn for<'r> FnMut(ScanEntry<'r>) -> bool,
    ) {
        EGraph::for_each_while(self, table, f);
    }

    fn get_canon_repr(&self, val: Value, ty: ColumnTy) -> Value {
        EGraph::get_canon_repr(self, val, ty)
    }

    fn base_values(&self) -> &BaseValues {
        EGraph::base_values(self)
    }

    fn base_values_mut(&mut self) -> &mut BaseValues {
        EGraph::base_values_mut(self)
    }

    fn container_values(&self) -> &ContainerValues {
        EGraph::container_values(self)
    }

    fn lookup_row(&self, func: FunctionId, key: &[Value]) -> Option<Vec<Value>> {
        EGraph::lookup_row(self, func, key)
    }

    fn lookup_id(&self, func: FunctionId, key: &[Value]) -> Option<Value> {
        EGraph::lookup_id(self, func, key)
    }

    fn with_execution_state_tracked_dyn(&self, f: &mut dyn FnMut(&mut ExecutionState<'_>)) -> bool {
        EGraph::with_execution_state_tracked(self, |es| f(es)).1
    }

    fn add_rule(&mut self, rule: RuleSpec) -> Result<RuleId> {
        build_rule(self, rule)
    }

    fn fresh_id(&mut self) -> Value {
        EGraph::fresh_id(self)
    }

    fn add_values(&mut self, values: Vec<(FunctionId, Vec<Value>)>) -> Result<()> {
        EGraph::try_add_values(self, values)
    }

    fn add_values_with_fresh(
        &mut self,
        values: Vec<(FunctionId, Vec<NativeInputValue>)>,
    ) -> Result<()> {
        EGraph::try_add_values_with_fresh(self, values)
    }

    fn free_rule(&mut self, id: RuleId) {
        EGraph::free_rule(self, id);
    }

    fn run_rules(&mut self, run: RuleSetRun<'_>) -> Result<IterationReport> {
        EGraph::run_rules(self, run.rules)
    }

    fn flush_updates(&mut self) -> bool {
        EGraph::flush_updates(self)
    }

    fn register_external_func(
        &mut self,
        func: Box<dyn ExternalFunction + 'static>,
    ) -> ExternalFunctionId {
        EGraph::register_external_func(self, func)
    }

    fn free_external_func(&mut self, func: ExternalFunctionId) {
        EGraph::free_external_func(self, func);
    }

    fn new_panic(&mut self, message: String) -> ExternalFunctionId {
        EGraph::new_panic(self, message)
    }

    fn register_get_fresh(&mut self) -> ExternalFunctionId {
        EGraph::register_get_fresh(self)
    }

    fn register_set_if_empty(
        &mut self,
        view_name: String,
        n_keys: usize,
        out_arity: usize,
    ) -> ExternalFunctionId {
        EGraph::register_set_if_empty(self, view_name, n_keys, out_arity)
    }

    fn register_view_column_read(
        &mut self,
        view_name: String,
        n_keys: usize,
        col_idx: usize,
    ) -> ExternalFunctionId {
        EGraph::register_view_column_read(self, view_name, n_keys, col_idx)
    }

    fn set_report_level(&mut self, level: ReportLevel) {
        EGraph::set_report_level(self, level);
    }

    fn dump_debug_info(&self) {
        EGraph::dump_debug_info(self);
    }

    fn clone_boxed(&self) -> Box<dyn Backend> {
        Box::new(self.clone())
    }

    fn action_registry(&self) -> Option<&Arc<RwLock<ActionRegistry>>> {
        Some(EGraph::action_registry(self))
    }

    fn id_counter(&self) -> Option<crate::CounterId> {
        Some(EGraph::id_counter(self))
    }

    fn supports_containers(&self) -> bool {
        true
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use egglog_ast::{
        core::{GenericAtom, GenericCoreAction, GenericCoreActions, GenericCoreRule, Query},
        generic_ast::Change,
        span::Span,
    };
    use egglog_numeric_id::NumericId;

    fn index_rule(
        name: &str,
        source: FunctionId,
        any_of: Vec<usize>,
        args: Vec<GenericAtomTerm<RuleVar, RuleValue>>,
    ) -> RuleSpec {
        RuleSpec {
            name: name.into(),
            seminaive: false,
            no_decomp: false,
            core: GenericCoreRule {
                span: Span::Panic,
                body: Query {
                    atoms: vec![GenericAtom {
                        span: Span::Panic,
                        head: RuleBodyCall::IndexTable {
                            id: source,
                            any_of,
                            read: crate::ReadMode::All,
                        },
                        args,
                    }],
                },
                head: GenericCoreActions::new(vec![]),
            },
        }
    }

    #[test]
    fn malformed_index_rules_do_not_consume_reference_rule_ids() {
        let mut backend = EGraph::default();
        let unit_ty = ColumnTy::Base(backend.base_values_mut().register_type::<()>());
        let i64_ty = ColumnTy::Base(backend.base_values_mut().register_type::<i64>());
        let bool_ty = ColumnTy::Base(backend.base_values_mut().register_type::<bool>());
        let unit = backend.base_values().get(());
        let one = backend.base_values().get(1_i64);
        let yes = backend.base_values().get(true);
        let source = Backend::add_table(
            &mut backend,
            FunctionConfig {
                schema: vec![i64_ty, bool_ty],
                n_vals: 1,
                n_identity_vals: None,
                default: crate::DefaultVal::Fail,
                merge: egglog_bridge::MergeFn::Old,
                name: "reference index validation source".into(),
                can_subsume: false,
            },
        );
        let reachability_source = Backend::add_table(
            &mut backend,
            FunctionConfig {
                schema: vec![i64_ty, i64_ty, i64_ty],
                n_vals: 1,
                n_identity_vals: None,
                default: crate::DefaultVal::Fail,
                merge: egglog_bridge::MergeFn::Old,
                name: "reference index reachability source".into(),
                can_subsume: false,
            },
        );
        let literal = |value, ty| GenericAtomTerm::Literal(Span::Panic, RuleValue { value, ty });
        let variable = |id, ty| {
            GenericAtomTerm::Var(
                Span::Panic,
                RuleVar {
                    id,
                    name: format!("v{id}").into(),
                    ty,
                },
            )
        };
        let valid_args = vec![
            literal(one, i64_ty),
            literal(one, i64_ty),
            literal(yes, bool_ty),
            literal(unit, unit_ty),
        ];
        let x = variable(20, i64_ty);
        let y = variable(21, i64_ty);
        let mut cyclic = index_rule(
            "mutually cyclic probes",
            reachability_source,
            vec![0, 1],
            vec![
                x.clone(),
                y.clone(),
                literal(one, i64_ty),
                literal(one, i64_ty),
                literal(unit, unit_ty),
            ],
        );
        cyclic.core.body.atoms.push(GenericAtom {
            span: Span::Panic,
            head: RuleBodyCall::IndexTable {
                id: reachability_source,
                any_of: vec![0, 1],
                read: crate::ReadMode::All,
            },
            args: vec![
                y,
                x.clone(),
                literal(one, i64_ty),
                literal(one, i64_ty),
                literal(unit, unit_ty),
            ],
        });
        let unindexed_repeat = index_rule(
            "probe repeated only at unindexed column",
            reachability_source,
            vec![0, 1],
            vec![
                x.clone(),
                literal(one, i64_ty),
                literal(one, i64_ty),
                x,
                literal(unit, unit_ty),
            ],
        );
        let mut short = valid_args.clone();
        short.pop();
        // Registered Reference tables own rebuild rules, so compare with a clean
        // clone at this exact table state rather than assuming an absolute id.
        let expected_id = Backend::add_rule(
            &mut backend.clone(),
            index_rule(
                "clean-clone duplicate occurrence columns",
                source,
                vec![0, 0],
                valid_args.clone(),
            ),
        )
        .expect("clean baseline rule is valid");
        let malformed = vec![
            cyclic,
            unindexed_repeat,
            index_rule("short index", source, vec![0], short),
            index_rule("empty occurrence set", source, vec![], valid_args.clone()),
            index_rule(
                "out-of-range occurrence",
                source,
                vec![2],
                valid_args.clone(),
            ),
            index_rule("mixed probe types", source, vec![0, 1], valid_args.clone()),
            index_rule(
                "mistyped row",
                source,
                vec![0],
                vec![
                    literal(one, i64_ty),
                    literal(yes, bool_ty),
                    literal(yes, bool_ty),
                    literal(unit, unit_ty),
                ],
            ),
            index_rule(
                "nonliteral Unit output",
                source,
                vec![0],
                vec![
                    literal(one, i64_ty),
                    literal(one, i64_ty),
                    literal(yes, bool_ty),
                    variable(9, unit_ty),
                ],
            ),
            index_rule(
                "mistyped Unit output",
                source,
                vec![0],
                vec![
                    literal(one, i64_ty),
                    literal(one, i64_ty),
                    literal(yes, bool_ty),
                    literal(one, i64_ty),
                ],
            ),
            index_rule(
                "noncanonical Unit output",
                source,
                vec![0],
                vec![
                    literal(one, i64_ty),
                    literal(one, i64_ty),
                    literal(yes, bool_ty),
                    literal(Value::new(unit.rep() + 1), unit_ty),
                ],
            ),
            index_rule(
                "unbound probe",
                reachability_source,
                vec![0, 1],
                vec![
                    variable(10, i64_ty),
                    literal(one, i64_ty),
                    literal(one, i64_ty),
                    literal(one, i64_ty),
                    literal(unit, unit_ty),
                ],
            ),
            index_rule(
                "unregistered target",
                FunctionId::new(source.rep() + 50),
                vec![0],
                valid_args.clone(),
            ),
        ];
        for rule in malformed {
            Backend::add_rule(&mut backend, rule).expect_err("malformed index must be rejected");
        }
        let id = Backend::add_rule(
            &mut backend,
            index_rule(
                "valid duplicate occurrence columns",
                source,
                vec![0, 0],
                valid_args,
            ),
        )
        .expect("duplicates have set semantics");
        assert_eq!(id, expected_id);
    }

    #[test]
    fn subsumed_read_of_nonsubsumable_table_is_empty() -> Result<()> {
        let mut backend = EGraph::default();
        let unit_ty = ColumnTy::Base(backend.base_values_mut().register_type::<()>());
        let unit = backend.base_values().get(());
        let config = |name: &str| FunctionConfig {
            schema: vec![ColumnTy::Id, unit_ty],
            n_vals: 1,
            n_identity_vals: None,
            default: crate::DefaultVal::Fail,
            merge: egglog_bridge::MergeFn::AssertEq,
            name: name.into(),
            can_subsume: false,
        };
        let source = Backend::add_table(&mut backend, config("nonsubsumable source"));
        let token = Backend::add_table(&mut backend, config("nonsubsumable token"));
        let key_value = Backend::fresh_id(&mut backend);
        Backend::add_values(
            &mut backend,
            vec![
                (source, vec![key_value, unit]),
                (token, vec![key_value, unit]),
            ],
        )?;
        let key = RuleVar {
            id: 0,
            name: "key".into(),
            ty: ColumnTy::Id,
        };
        let key_term = GenericAtomTerm::Var(Span::Panic, key);
        let unit_term = GenericAtomTerm::Literal(
            Span::Panic,
            RuleValue {
                value: unit,
                ty: unit_ty,
            },
        );
        let id = Backend::add_rule(
            &mut backend,
            RuleSpec {
                name: "nonsubsumable Subsumed is empty".into(),
                seminaive: false,
                no_decomp: false,
                core: GenericCoreRule {
                    span: Span::Panic,
                    body: Query {
                        atoms: vec![GenericAtom {
                            span: Span::Panic,
                            head: RuleBodyCall::Table {
                                id: source,
                                read: crate::ReadMode::Subsumed,
                            },
                            args: vec![key_term.clone(), unit_term],
                        }],
                    },
                    head: GenericCoreActions::new(vec![GenericCoreAction::Change(
                        Span::Panic,
                        Change::Delete,
                        RuleActionCall::Table {
                            id: token,
                            name: "token".into(),
                        },
                        vec![key_term],
                    )]),
                },
            },
        )?;
        Backend::run_rules(
            &mut backend,
            RuleSetRun {
                name: Some("nonsubsumable Subsumed"),
                rules: &[id],
            },
        )?;
        assert_eq!(
            Backend::lookup_id(&backend, token, &[key_value]),
            Some(unit)
        );
        Ok(())
    }
}

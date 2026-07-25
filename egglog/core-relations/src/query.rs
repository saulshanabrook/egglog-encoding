//! APIs for building a query of a database.

use std::{iter::once, sync::Arc};

use crate::{
    free_join::plan::{DecomposedPlan, JoinStageBlocks, SinglePlan},
    numeric_id::{DenseIdMap, IdVec, NumericId, define_id},
};
use smallvec::SmallVec;
use thiserror::Error;

use crate::receipts::{
    ActionReceiptKind, ActionReceiptSpec, CheckEndpointSpec, CheckTermSource, PremiseOccurrence,
    PremiseSlot, ReplayBindingSource, ReplayEqualitySource, ReplayTerm, RowOriginSpec,
    TermOriginSpec, TermRecipe, TermTemplate,
};
use crate::{
    BaseValueId, CheckEndpointSource, CheckReceiptSpec, CounterId, EqualityEndpoint,
    ExternalFunctionId, PoolSet, ReplayConstructorSpec, ReplaySortId, RuleBindingSpec,
    RuleReceiptSpec, SourceReceiptSpec,
    action::{Instr, QueryEntry, WriteVal},
    common::HashMap,
    free_join::{
        ActionId, AtomId, Database, ProcessedConstraints, SubAtom, TableId, TableInfo, VarInfo,
        Variable,
        plan::{JoinHeader, JoinStages, Plan, PlanStrategy},
    },
    pool::{Pooled, with_pool_set},
    table_spec::{ColumnId, Constraint},
};

define_id!(pub RuleId, u32, "An identifier for a rule in a rule set");

/// Resolves variables and atoms in a rule to their string names.
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct SymbolMap {
    pub atoms: HashMap<AtomId, Arc<str>>,
    pub vars: HashMap<Variable, Arc<str>>,
}

/// A cached plan for a given rule.
pub struct CachedPlan {
    plan: Plan,
    desc: Arc<str>,
    symbol_map: SymbolMap,
    actions: ActionInfo,
}

/// One exact table premise used by plan-free grounded execution.
///
/// Unlike a planned atom, every key must already be bound and the complete
/// committed row is checked with one point lookup.
#[derive(Debug, Clone)]
#[doc(hidden)]
pub struct GroundedProbe {
    pub(crate) table: TableId,
    pub(crate) entries: Box<[QueryEntry]>,
    pub(crate) n_keys: usize,
}

impl GroundedProbe {
    pub fn new(table: TableId, entries: impl Into<Box<[QueryEntry]>>, n_keys: usize) -> Self {
        Self {
            table,
            entries: entries.into(),
            n_keys,
        }
    }
}

/// The specialized compiled body-guard/head tape for one grounded rule.
///
/// This deliberately contains no query plan and is not shared with ordinary
/// planned execution: grounded compilation rewires primitive-produced values
/// for dependency-driven point probing.
#[derive(Debug, Clone)]
#[doc(hidden)]
pub struct GroundedRule {
    pub(crate) action: ActionInfo,
    pub(crate) body_end: usize,
    pub(crate) probes: Arc<[GroundedProbe]>,
}

impl GroundedRule {
    pub fn with_probes(mut self, probes: impl Into<Arc<[GroundedProbe]>>) -> Self {
        self.probes = probes.into();
        self
    }
}

enum RuleBuildOutput {
    Planned(RuleId),
    Grounded(GroundedRule),
}

impl RuleBuildOutput {
    fn planned(self) -> RuleId {
        let Self::Planned(rule) = self else {
            unreachable!("planned rule build returned a grounded tape")
        };
        rule
    }

    fn grounded(self) -> GroundedRule {
        let Self::Grounded(rule) = self else {
            unreachable!("grounded rule build returned a query plan")
        };
        rule
    }
}

#[derive(Debug, Clone)]
pub(crate) struct ActionInfo {
    pub(crate) used_vars: SmallVec<[Variable; 4]>,
    pub(crate) instrs: Arc<Pooled<Vec<Instr>>>,
    pub(crate) receipt: Option<ActionReceiptSpec>,
}

/// A set of rules to run against a [`Database`].
///
/// See [`Database::new_rule_set`] for more information.
#[derive(Default)]
pub struct RuleSet {
    /// The contents of the queries (i.e. the LHS of the rules) for each rule in the set, along
    /// with a description of the rule.
    ///
    /// The action here is used to map between rule descriptions and plans, which contain ActionIds. The current
    /// accounting logic assumes that rules and actions stand in a bijection. If we relaxed that
    /// later on, most of the core logic would still work but the accounting logic could get more
    /// complex.
    pub(crate) plans: IdVec<RuleId, (Plan, Arc<str> /* description */, SymbolMap)>,
    pub(crate) actions: DenseIdMap<ActionId, ActionInfo>,
}

impl RuleSet {
    pub fn build_cached_plan(&self, rule_id: RuleId) -> CachedPlan {
        let (plan, desc, symbol_map) = self.plans.get(rule_id).expect("rule must exist");
        let actions = self
            .actions
            .get(plan.actions())
            .expect("action must exist")
            .clone();
        CachedPlan {
            plan: plan.clone(),
            desc: desc.clone(),
            symbol_map: symbol_map.clone(),
            actions,
        }
    }
}

/// Builder for a [`RuleSet`].
///
/// There are in general two ways to add rules to a rule set:
///
/// 1. Use the QueryBuilder and RuleBuilder APIs to construct a rule from scratch.
/// 2. Use a previously cached plan and add extra constraints to it.
///
/// The pattern this is used by egglog is as follows: An egglog rule is first compiled to a cached
/// plan using builder patterns at declaration time, and each time the rule is run, it is added to
/// a ruleset using the cached plan and possibly some extra constraints (e.g., timestamp).
///
/// See [`Database::new_rule_set`] for more information.
pub struct RuleSetBuilder<'outer> {
    rule_set: RuleSet,
    db: &'outer mut Database,
}

impl<'outer> RuleSetBuilder<'outer> {
    pub fn new(db: &'outer mut Database) -> Self {
        Self {
            rule_set: Default::default(),
            db,
        }
    }

    /// Estimate the size of the subset of the table matching the given
    /// constraint.
    ///
    /// This is a wrapper around the [`Database::estimate_size`] method.
    pub fn estimate_size(&self, table: TableId, c: Option<Constraint>) -> usize {
        self.db.estimate_size(table, c)
    }

    /// Add a rule to this rule set.
    pub fn new_rule<'a>(&'a mut self) -> QueryBuilder<'outer, 'a> {
        let instrs = with_pool_set(PoolSet::get);
        let recipe_draft = self
            .db
            .causal_receipts
            .is_some()
            .then(StaticRecipeDraft::default);
        QueryBuilder {
            rsb: self,
            instrs,
            recipe_draft,
            query: Query {
                var_info: Default::default(),
                atoms: Default::default(),
                // start with an invalid ActionId
                action: ActionId::new(u32::MAX),
                plan_strategy: Default::default(),
                fun_deps: Default::default(),
                no_decomp: false,
            },
        }
    }

    fn reprocess_constraints(
        &self,
        table: TableId,
        atom: AtomId,
        constraints: &[Constraint],
    ) -> Option<JoinHeader> {
        let processed = self.db.process_constraints(table, constraints);
        if !processed.slow.is_empty() {
            panic!(
                "Cached plans only support constraints with a fast pushdown. \
                 Got: {constraints:?} for table {table:?}",
            );
        }
        if processed.subset.size() == 0 {
            return None;
        }
        Some(JoinHeader {
            atom,
            constraints: processed.fast,
            subset: processed.subset,
        })
    }

    fn push_extra_constraints(
        &self,
        headers: &mut Vec<JoinHeader>,
        atoms: &Arc<DenseIdMap<AtomId, Atom>>,
        extra_constraints: &[(AtomId, Constraint)],
    ) -> Option<()> {
        for (atom_id, constraint) in extra_constraints {
            let atom_info = atoms.get(*atom_id).expect("atom must exist in plan");
            let table = atom_info.table;
            headers.push(self.reprocess_constraints(
                table,
                *atom_id,
                std::slice::from_ref(constraint),
            )?);
        }
        Some(())
    }

    fn reprocess_existing_headers(
        &self,
        headers: &mut Vec<JoinHeader>,
        atoms: &Arc<DenseIdMap<AtomId, Atom>>,
        existing: &[JoinHeader],
    ) -> Option<()> {
        for JoinHeader {
            atom, constraints, ..
        } in existing
        {
            let atom_info = atoms.get(*atom).expect("atom must exist in plan");
            let table = atom_info.table;
            headers.push(self.reprocess_constraints(table, *atom, constraints)?);
        }
        Some(())
    }

    fn get_rule_with_extra_constraints(
        &self,
        cached: &CachedPlan,
        action_id: ActionId,
        extra_constraints: &[(AtomId, Constraint)],
    ) -> Option<Plan> {
        match &cached.plan {
            Plan::SinglePlan(cached_plan) => {
                let mut headers = vec![];
                let stages = JoinStages {
                    instrs: cached_plan.stages.instrs.clone(),
                    live_vars: cached_plan.stages.live_vars.clone(),
                };
                self.push_extra_constraints(&mut headers, &cached_plan.atoms, extra_constraints)?;
                self.reprocess_existing_headers(
                    &mut headers,
                    &cached_plan.atoms,
                    &cached_plan.header,
                )?;
                Some(Plan::SinglePlan(SinglePlan {
                    atoms: cached_plan.atoms.clone(),
                    header: headers,
                    stages,
                    actions: action_id,
                }))
            }
            Plan::DecomposedPlan(cached_plan) => {
                let mut blocks = Vec::with_capacity(cached_plan.stages.blocks.len());
                let mut headers = vec![];
                self.push_extra_constraints(&mut headers, &cached_plan.atoms, extra_constraints)?;
                self.reprocess_existing_headers(
                    &mut headers,
                    &cached_plan.atoms,
                    &cached_plan.header,
                )?;
                for cached_block in cached_plan.stages.blocks.iter() {
                    let stages = JoinStages {
                        instrs: cached_block.0.instrs.clone(),
                        live_vars: cached_block.0.live_vars.clone(),
                    };
                    blocks.push((stages, cached_block.1.clone()));
                }
                let result_block = JoinStages {
                    instrs: cached_plan.result_block.instrs.clone(),
                    live_vars: cached_plan.result_block.live_vars.clone(),
                };
                Some(Plan::DecomposedPlan(DecomposedPlan {
                    atoms: cached_plan.atoms.clone(),
                    header: headers,
                    stages: JoinStageBlocks { blocks },
                    actions: action_id,
                    result_block,
                }))
            }
        }
    }

    /// Add a rule to this rule set based on a previously cached plan, optionally
    /// with additional constraints applied on top.
    ///
    /// Returns `None` if the query is provably empty given the current database
    /// state (i.e. some constraint narrows a table to zero matching rows), in
    /// which case no rule or action is allocated. Returns `Some(RuleId)` otherwise.
    ///
    /// The primary use-case is seminaive evaluation: an egglog rule is compiled
    /// once into a [`CachedPlan`] and then added to a fresh [`RuleSet`] each
    /// iteration with timestamp constraints (e.g. `GeConst` on the focus atom)
    /// that select only new tuples. If no new tuples exist for an atom, the
    /// `None` return allows the caller to skip that variant entirely.
    pub fn add_rule_from_cached_plan(
        &mut self,
        cached: &CachedPlan,
        extra_constraints: &[(AtomId, Constraint)],
    ) -> Option<RuleId> {
        // Peek at the action_id without allocating it yet, so we don't break
        // the rules<->actions bijection if the query turns out to be empty.
        let action_id = self.rule_set.actions.next_id();
        let plan = self.get_rule_with_extra_constraints(cached, action_id, extra_constraints)?;
        // The query is non-empty: now commit the action and the plan.
        let actual_action_id = self.rule_set.actions.push(cached.actions.clone());
        debug_assert_eq!(action_id, actual_action_id);
        Some(
            self.rule_set
                .plans
                .push((plan, cached.desc.clone(), cached.symbol_map.clone())),
        )
    }

    /// Build the ruleset.
    pub fn build(self) -> RuleSet {
        self.rule_set
    }
}

/// Builder for the "query" portion of the rule.
///
/// Queries specify scans or joins over the database that bind variables that
/// are accessible to rules.
pub struct QueryBuilder<'outer, 'a> {
    rsb: &'a mut RuleSetBuilder<'outer>,
    query: Query,
    instrs: Pooled<Vec<Instr>>,
    recipe_draft: Option<StaticRecipeDraft>,
}

impl<'outer, 'a> QueryBuilder<'outer, 'a> {
    /// Finish the query and start building the right-hand side of the rule.
    pub fn build(self) -> RuleBuilder<'outer, 'a> {
        RuleBuilder { qb: self }
    }

    /// Set the target plan strategy to use to execute this query.
    pub fn set_plan_strategy(&mut self, strategy: PlanStrategy) {
        self.query.plan_strategy = strategy;
    }

    /// If `true`, the query planner will skip tree-decomposition
    /// for query decomposition and always use evaluate the query as a single bag.
    pub fn set_no_decomp(&mut self, no_decomp: bool) {
        self.query.no_decomp = no_decomp;
    }

    /// Create a new variable of the given type.
    pub fn new_var(&mut self) -> Variable {
        self.query.var_info.push(VarInfo {
            occurrences: Default::default(),
            used_in_rhs: false,
            defined_in_rhs: false,
            name: None,
        })
    }

    pub fn new_var_named(&mut self, name: &str) -> Variable {
        self.query.var_info.push(VarInfo {
            occurrences: Default::default(),
            used_in_rhs: false,
            defined_in_rhs: false,
            name: Some(name.into()),
        })
    }

    fn mark_used<'b>(&mut self, entries: impl IntoIterator<Item = &'b QueryEntry>) {
        for entry in entries {
            if let QueryEntry::Var(v) = entry {
                self.query.var_info[*v].used_in_rhs = true;
            }
        }
    }

    fn mark_defined(&mut self, entry: &QueryEntry) {
        // TODO: use some of this information in query planning, e.g. dedup at match time.
        if let QueryEntry::Var(v) = entry {
            self.query.var_info[*v].defined_in_rhs = true;
        }
    }

    /// Add the given atom to the query, with the given variables and constraints.
    ///
    /// NB: it is possible to constrain two non-equal variables to be equal
    /// given this setup. Doing this will not cause any problems but
    /// nevertheless is not recommended.
    ///
    /// The returned `AtomId` can be used to refer to this atom when adding constraints in
    /// [`RuleSetBuilder::add_rule_from_cached_plan`].
    ///
    /// # Panics
    /// Like most methods that take a [`TableId`], this method will panic if the
    /// given table is not declared in the corresponding database.
    pub fn add_atom<'b>(
        &mut self,
        table_id: TableId,
        vars: &[QueryEntry],
        cs: impl IntoIterator<Item = &'b Constraint>,
    ) -> Result<AtomId, QueryError> {
        let info = &self.rsb.db.tables[table_id];
        let arity = info.spec.arity();
        let check_constraint = |c: &Constraint| {
            let process_col = |col: &ColumnId| -> Result<(), QueryError> {
                if col.index() >= arity {
                    Err(QueryError::InvalidConstraint {
                        constraint: c.clone(),
                        column: col.index(),
                        table: table_id,
                        arity,
                    })
                } else {
                    Ok(())
                }
            };
            match c {
                Constraint::Eq { l_col, r_col } => {
                    process_col(l_col)?;
                    process_col(r_col)
                }
                Constraint::EqConst { col, .. }
                | Constraint::LtConst { col, .. }
                | Constraint::GtConst { col, .. }
                | Constraint::LeConst { col, .. }
                | Constraint::GeConst { col, .. } => process_col(col),
            }
        };
        if arity != vars.len() {
            return Err(QueryError::BadArity {
                table: table_id,
                expected: arity,
                got: vars.len(),
            });
        }
        let cs = Vec::from_iter(
            cs.into_iter()
                .cloned()
                .chain(vars.iter().enumerate().filter_map(|(i, qe)| match qe {
                    QueryEntry::Var(_) => None,
                    QueryEntry::Const(c) => Some(Constraint::EqConst {
                        col: ColumnId::from_usize(i),
                        val: *c,
                    }),
                })),
        );
        cs.iter().try_fold((), |_, c| check_constraint(c))?;
        let processed = self.rsb.db.process_constraints(table_id, &cs);
        let mut atom = Atom {
            table: table_id,
            var_columns: Default::default(),
            constraints: processed,
        };
        let next_atom = AtomId::from_usize(self.query.atoms.n_ids());
        let mut subatoms = HashMap::<Variable, SubAtom>::default();
        for (i, qe) in vars.iter().enumerate() {
            let var = match qe {
                QueryEntry::Var(var) => *var,
                QueryEntry::Const(_) => {
                    continue;
                }
            };
            if var == Variable::placeholder() {
                continue;
            }
            let col = ColumnId::from_usize(i);
            if let Some(prev) = atom.var_columns.insert(var, col) {
                atom.constraints.slow.push(Constraint::Eq {
                    l_col: col,
                    r_col: prev,
                })
            };
            subatoms
                .entry(var)
                .or_insert_with(|| SubAtom::new(next_atom))
                .vars
                .push(col);
        }
        for (var, subatom) in subatoms {
            self.query
                .var_info
                .get_mut(var)
                .expect("all variables must be bound in current query")
                .occurrences
                .push(subatom);
        }

        // Add functional dependencies for this atom.
        let get_var = |qe: &QueryEntry| match qe {
            QueryEntry::Var(v) => Some(*v),
            QueryEntry::Const(_) => None,
        };
        let antecedent = vars[..info.spec().n_keys]
            .iter()
            .filter_map(get_var)
            .collect::<Vec<_>>();
        let consequent = vars[info.spec().n_keys..]
            .iter()
            .filter_map(get_var)
            .collect::<Vec<_>>();
        self.query.fun_deps.add_dependency(antecedent, consequent);

        Ok(self.query.atoms.push(atom))
    }
}

#[derive(Debug, Error)]
pub enum QueryError {
    #[error("table {table:?} has {expected:?} keys but got {got:?}")]
    KeyArityMismatch {
        table: TableId,
        expected: usize,
        got: usize,
    },
    #[error("table {table:?} has {expected:?} columns but got {got:?}")]
    TableArityMismatch {
        table: TableId,
        expected: usize,
        got: usize,
    },

    #[error(
        "counter used in column {column_id:?} of table {table:?}, which is declared as a base value"
    )]
    CounterUsedInBaseColumn {
        table: TableId,
        column_id: ColumnId,
        base: BaseValueId,
    },

    #[error("attempt to compare two groups of values, one of length {l}, another of length {r}")]
    MultiComparisonMismatch { l: usize, r: usize },

    #[error("table {table:?} expected {expected:?} columns but got {got:?}")]
    BadArity {
        table: TableId,
        expected: usize,
        got: usize,
    },

    #[error("expected {expected:?} columns in schema but got {got:?}")]
    InvalidSchema { expected: usize, got: usize },

    #[error(
        "constraint {constraint:?} on table {table:?} references column {column:?}, but the table has arity {arity:?}"
    )]
    InvalidConstraint {
        constraint: Constraint,
        column: usize,
        table: TableId,
        arity: usize,
    },
}

/// Builder for the "action" portion of the rule.
///
/// Rules can refer to the variables bound in their query to modify the database.
pub struct RuleBuilder<'outer, 'a> {
    qb: QueryBuilder<'outer, 'a>,
}

enum ReceiptBuildSpec {
    Rule(RuleReceiptSpec),
    Source(SourceReceiptSpec),
    Check { premises: Box<[AtomId]> },
}

type RecipeRoot = Arc<RecipeExpr>;

#[derive(Clone, Debug)]
enum RecipeExpr {
    Input(Variable),
    Static {
        term: crate::ReplayTermId,
        sort: ReplaySortId,
    },
    /// The value column of a zero-key table read. Source/global lookups use
    /// this leaf so cold projection can resolve the exact historical fact
    /// instead of consulting final database state.
    FactLookup {
        table: TableId,
        column: u16,
        sort: ReplaySortId,
    },
    Call {
        replay: ReplayConstructorSpec,
        children: Arc<[RecipeRoot]>,
    },
}

#[derive(Default)]
struct StaticRecipeDraft {
    value_roots: HashMap<Variable, RecipeRoot>,
}

fn atom_query_entry(atom: &Atom, column: ColumnId) -> QueryEntry {
    if let Some(variable) = atom.get_var(column) {
        return QueryEntry::Var(variable);
    }
    atom.constraints
        .fast
        .iter()
        .chain(atom.constraints.slow.iter())
        .find_map(|constraint| match constraint {
            Constraint::EqConst { col, val } if *col == column => Some(QueryEntry::Const(*val)),
            _ => None,
        })
        .unwrap_or_else(|| {
            panic!(
                "query atom column {} is neither variable nor equality constant",
                column.index()
            )
        })
}

impl StaticRecipeDraft {
    fn entry(
        &self,
        receipts: &crate::CausalReceipts,
        entry: QueryEntry,
        sort: ReplaySortId,
    ) -> RecipeRoot {
        match entry {
            QueryEntry::Var(variable) => self
                .value_roots
                .get(&variable)
                .cloned()
                .unwrap_or_else(|| Arc::new(RecipeExpr::Input(variable))),
            QueryEntry::Const(value) => {
                let term = receipts
                    .lookup_term(sort, value)
                    .expect("typed action literal has no registered replay term");
                assert!(
                    matches!(receipts.replay_term(term), Some(ReplayTerm::Literal { sort: actual, .. }) if actual == sort),
                    "typed action constant resolved through a structural alias instead of a literal"
                );
                Arc::new(RecipeExpr::Static { term, sort })
            }
        }
    }

    fn call_output(
        &mut self,
        receipts: &crate::CausalReceipts,
        dst: Variable,
        args: &[QueryEntry],
        replay: &ReplayConstructorSpec,
    ) {
        let root = Arc::new(RecipeExpr::Call {
            replay: replay.clone(),
            children: replay
                .child_sorts
                .iter()
                .copied()
                .zip(args.iter().copied())
                .map(|(sort, entry)| self.entry(receipts, entry, sort))
                .collect(),
        });
        assert!(
            self.value_roots.insert(dst, root).is_none(),
            "one action variable has multiple structural producers"
        );
    }

    fn alias_output(&mut self, source: Variable, destination: Variable) {
        let root = self
            .value_roots
            .get(&source)
            .cloned()
            .expect("replay recipe alias source has no structural producer");
        match self.value_roots.get(&destination) {
            None => {
                self.value_roots.insert(destination, root);
            }
            Some(existing) if Arc::ptr_eq(existing, &root) => {}
            // A rule may deliberately validate two pure expressions into the
            // same already-bound variable. Runtime execution retains both
            // equality guards; the recipe is naming metadata, so one exact
            // producer is sufficient and first-wins keeps lowering stable.
            Some(_) => {}
        }
    }

    fn lookup_output(
        &mut self,
        receipts: &crate::CausalReceipts,
        destination: Variable,
        table: TableId,
        column: ColumnId,
        key: &[QueryEntry],
    ) {
        // A zero-key table names one historical global cell exactly. General
        // keyed action reads would require recording the key recipe too and
        // remain deliberately unsupported by the causal replay contract.
        if !key.is_empty() {
            return;
        }
        let sort = receipts
            .table_column_sort(table, column.index())
            .expect("zero-key replay lookup has no registered result sort");
        let root = Arc::new(RecipeExpr::FactLookup {
            table,
            column: u16::try_from(column.index()).expect("table column exceeds u16"),
            sort,
        });
        assert!(
            self.value_roots.insert(destination, root).is_none(),
            "one action variable has multiple structural producers"
        );
    }

    fn lower(
        &self,
        bindings: &[RuleBindingSpec],
        binding_sources: &[ReplayBindingSource],
        binding_sorts: &[ReplaySortId],
    ) -> TermRecipe {
        let mut inputs = HashMap::default();
        for (index, ((binding, source), sort)) in bindings
            .iter()
            .zip(binding_sources)
            .zip(binding_sorts)
            .enumerate()
        {
            if let (
                RuleBindingSpec::Variable { variable, .. },
                ReplayBindingSource::Premise { .. },
            ) = (binding, source)
            {
                inputs.entry(*variable).or_insert((
                    RecipeInput::Binding(
                        u16::try_from(index).expect("one causal rule has more than u16 bindings"),
                    ),
                    *sort,
                ));
            }
        }
        let mut lowerer = RecipeLowerer {
            inputs,
            memo: HashMap::default(),
            observed_sorts: HashMap::default(),
        };
        let mut next_residual = 0u32;
        let current_roots = bindings
            .iter()
            .zip(binding_sources)
            .zip(binding_sorts)
            .filter_map(|((binding, source), sort)| match (binding, source) {
                (
                    RuleBindingSpec::Variable { variable, .. },
                    ReplayBindingSource::Current { residual, .. },
                ) => {
                    assert_eq!(*residual, next_residual);
                    next_residual += 1;
                    Some(
                        self.value_roots
                            .get(variable)
                            .and_then(|root| lowerer.try_lower(root, *sort)),
                    )
                }
                _ => None,
            })
            .collect();
        TermRecipe { current_roots }
    }

    fn lower_row_origin(
        &self,
        receipts: &crate::CausalReceipts,
        table: TableId,
        entries: &[Option<QueryEntry>],
        inputs: &HashMap<Variable, (RecipeInput, ReplaySortId)>,
    ) -> RowOriginSpec {
        let layout = receipts
            .table_replay_layout(table)
            .unwrap_or_else(|| panic!("row-origin table {table:?} has no replay layout"));
        assert_eq!(
            layout.len(),
            entries.len(),
            "row-origin input and table layout have different arities"
        );
        let mut lowerer = RecipeLowerer {
            inputs: inputs.clone(),
            memo: HashMap::default(),
            observed_sorts: HashMap::default(),
        };
        let mut cells = layout
            .iter()
            .copied()
            .zip(entries.iter().copied())
            .map(|(sort, entry)| match (sort, entry) {
                (None, _) => None,
                (Some(sort), Some(entry)) => {
                    let root = self.entry(receipts, entry, sort);
                    lowerer.try_lower(&root, sort)
                }
                (Some(_), None) => None,
            })
            .collect::<Vec<_>>();
        if let Some(constructor) = receipts.table_constructor(table) {
            let output = constructor.child_sorts.len();
            assert_eq!(
                layout.get(output).copied().flatten(),
                Some(constructor.result_sort),
                "constructor result does not match its table row layout"
            );
            let children = cells
                .iter()
                .take(output)
                .cloned()
                .collect::<Option<Vec<_>>>();
            cells[output] = children.map(|children| {
                Arc::new(TermTemplate::Call {
                    sort: constructor.result_sort,
                    op: constructor.op,
                    children: children.into(),
                })
            });
        }
        RowOriginSpec {
            table,
            cells: cells.into(),
        }
    }

    fn lower_term_origin(
        &self,
        receipts: &crate::CausalReceipts,
        entry: QueryEntry,
        sort: ReplaySortId,
        inputs: &HashMap<Variable, (RecipeInput, ReplaySortId)>,
    ) -> crate::receipts::TermOriginSiteId {
        let mut lowerer = RecipeLowerer {
            inputs: inputs.clone(),
            memo: HashMap::default(),
            observed_sorts: HashMap::default(),
        };
        let root = self.entry(receipts, entry, sort);
        let term = lowerer
            .try_lower(&root, sort)
            .unwrap_or_else(|| panic!("typed equality endpoint has no structural producer"));
        receipts.register_term_origin(TermOriginSpec { sort, term })
    }

    fn attach_row_origins(
        &self,
        receipts: &crate::CausalReceipts,
        atoms: &DenseIdMap<AtomId, Atom>,
        instrs: &mut [Instr],
        inputs: &HashMap<Variable, (RecipeInput, ReplaySortId)>,
    ) {
        for instr in instrs {
            if let Instr::PromoteReplayCall {
                dst,
                replay,
                origin,
                ..
            } = instr
            {
                *origin = Some(self.lower_term_origin(
                    receipts,
                    QueryEntry::Var(*dst),
                    replay.result_sort,
                    inputs,
                ));
                continue;
            }
            if let Instr::UnionWithReplay {
                left,
                right,
                sort,
                left_origin,
                right_origin,
                ..
            } = instr
            {
                *left_origin = Some(self.lower_term_origin(receipts, *left, *sort, inputs));
                *right_origin = Some(self.lower_term_origin(receipts, *right, *sort, inputs));
                continue;
            }
            if let Instr::RecordCheck {
                equalities,
                implicit_equalities,
                ..
            } = instr
            {
                for endpoint in equalities
                    .iter_mut()
                    .chain(implicit_equalities.iter_mut())
                    .flat_map(|(left, right)| [left, right])
                {
                    if let CheckTermSource::Constructor { atom, origin, .. } = &mut endpoint.term {
                        let atom = &atoms[*atom];
                        let replay = receipts.table_constructor(atom.table).unwrap_or_else(|| {
                            panic!(
                                "check constructor atom {:?} has no replay metadata",
                                atom.table
                            )
                        });
                        assert_eq!(
                            replay.result_sort, endpoint.sort,
                            "check constructor endpoint has the wrong replay result sort"
                        );
                        let children = replay
                            .child_sorts
                            .iter()
                            .copied()
                            .enumerate()
                            .map(|(column, sort)| {
                                self.entry(
                                    receipts,
                                    atom_query_entry(atom, ColumnId::from_usize(column)),
                                    sort,
                                )
                            })
                            .collect();
                        let root = Arc::new(RecipeExpr::Call { replay, children });
                        let mut lowerer = RecipeLowerer {
                            inputs: inputs.clone(),
                            memo: HashMap::default(),
                            observed_sorts: HashMap::default(),
                        };
                        let term = lowerer.try_lower(&root, endpoint.sort).unwrap_or_else(|| {
                            panic!("check constructor endpoint has no exact source-term recipe")
                        });
                        *origin = Some(receipts.register_term_origin(TermOriginSpec {
                            sort: endpoint.sort,
                            term,
                        }));
                    }
                }
                continue;
            }
            let (table, entries, origin) = match instr {
                Instr::Insert {
                    table,
                    vals,
                    origin,
                }
                | Instr::InsertIfEq {
                    table,
                    vals,
                    origin,
                    ..
                } => (*table, vals.iter().copied().map(Some).collect(), origin),
                Instr::LookupOrInsertDefault {
                    table,
                    args,
                    default,
                    origin,
                    ..
                } => {
                    let mut entries = args.iter().copied().map(Some).collect::<Vec<_>>();
                    for value in default.iter().copied() {
                        entries.push(match value {
                            WriteVal::QueryEntry(entry) => Some(entry),
                            WriteVal::CurrentVal(column) => entries[column],
                            WriteVal::IncCounter(_) => None,
                        });
                    }
                    (*table, entries, origin)
                }
                Instr::LookupOrInsertDefaultReplay {
                    table,
                    args,
                    default,
                    dst_col,
                    dst_var,
                    origin,
                    ..
                } => {
                    let mut entries = args.iter().copied().map(Some).collect::<Vec<_>>();
                    for value in default.iter().copied() {
                        entries.push(match value {
                            WriteVal::QueryEntry(entry) => Some(entry),
                            WriteVal::CurrentVal(column) => entries[column],
                            WriteVal::IncCounter(_) => None,
                        });
                    }
                    entries[dst_col.index()] = Some(QueryEntry::Var(*dst_var));
                    (*table, entries, origin)
                }
                _ => continue,
            };
            let spec = self.lower_row_origin(receipts, table, &entries, inputs);
            let registered = receipts.register_row_origin(spec);
            *origin = Some(registered);
        }
    }
}

struct RecipeLowerer {
    inputs: HashMap<Variable, (RecipeInput, ReplaySortId)>,
    memo: HashMap<(usize, ReplaySortId), Option<Arc<TermTemplate>>>,
    observed_sorts: HashMap<usize, ReplaySortId>,
}

#[derive(Clone, Copy)]
enum RecipeInput {
    Binding(u16),
    PremiseCell { premise: u16, column: u16 },
}

impl RecipeLowerer {
    fn try_lower(
        &mut self,
        root: &RecipeRoot,
        expected: ReplaySortId,
    ) -> Option<Arc<TermTemplate>> {
        // `entry` creates short-lived roots for plain inputs and constants.
        // Their Arc allocation may be reused by the very next column, so a
        // raw pointer is not a stable memo key once such a leaf is dropped.
        // Leaves are trivial to lower directly; only persistent call-DAG
        // nodes benefit from identity memoization.
        match root.as_ref() {
            RecipeExpr::Input(variable) => {
                let (input, sort) = self.inputs.get(variable)?;
                assert_eq!(*sort, expected, "input binding used under the wrong sort");
                let template = match input {
                    RecipeInput::Binding(binding) => TermTemplate::Binding { binding: *binding },
                    RecipeInput::PremiseCell { premise, column } => TermTemplate::PremiseCell {
                        premise: *premise,
                        column: *column,
                    },
                };
                return Some(Arc::new(template));
            }
            RecipeExpr::Static { term, sort } => {
                assert_eq!(*sort, expected);
                return Some(Arc::new(TermTemplate::Static { term: *term }));
            }
            RecipeExpr::FactLookup {
                table,
                column,
                sort,
            } => {
                assert_eq!(*sort, expected);
                return Some(Arc::new(TermTemplate::FactLookup {
                    table: *table,
                    column: *column,
                }));
            }
            RecipeExpr::Call { .. } => {}
        }
        let key = Arc::as_ptr(root) as usize;
        if let Some(prior) = self.observed_sorts.insert(key, expected) {
            assert_eq!(prior, expected, "one producer crosses logical sorts");
        }
        if let Some(term) = self.memo.get(&(key, expected)) {
            return term.clone();
        }
        let RecipeExpr::Call { replay, children } = root.as_ref() else {
            unreachable!("leaf recipes return before call-DAG memoization")
        };
        assert_eq!(replay.result_sort, expected);
        let node = TermTemplate::Call {
            sort: expected,
            op: replay.op,
            children: replay
                .child_sorts
                .iter()
                .copied()
                .zip(children.iter())
                .map(|(sort, child)| self.try_lower(child, sort))
                .collect::<Option<_>>()?,
        };
        let term = Arc::new(node);
        self.memo.insert((key, expected), Some(Arc::clone(&term)));
        Some(term)
    }
}
impl RuleBuilder<'_, '_> {
    fn table_info(&self, table: TableId) -> &TableInfo {
        self.qb.rsb.db.get_table_info(table)
    }

    /// Compile every equality that the native query enforces between
    /// replay-typed premise cells or a premise cell and a typed constant.
    /// This includes unnamed variables introduced while lowering nested
    /// source terms; it is deliberately separate from source replay bindings.
    fn receipt_equality_obligations(
        &self,
        premises: &[AtomId],
    ) -> Vec<(ReplayEqualitySource, ReplayEqualitySource)> {
        let receipts = self
            .qb
            .rsb
            .db
            .causal_receipts
            .as_ref()
            .expect("receipt equality obligations require causal receipts");
        let mut obligations = Vec::new();
        let mut push = |obligation| {
            if !obligations.contains(&obligation) {
                obligations.push(obligation);
            }
        };

        for (_, info) in self.qb.query.var_info.iter() {
            let mut occurrences = Vec::<(PremiseOccurrence, ReplaySortId)>::new();
            for (premise, atom) in premises.iter().copied().enumerate() {
                let Some(subatom) = info
                    .occurrences
                    .iter()
                    .find(|occurrence| occurrence.atom == atom)
                else {
                    continue;
                };
                let table = self.qb.query.atoms[atom].table;
                for column in subatom.vars.iter().copied() {
                    let Some(sort) = receipts.table_column_sort(table, column.index()) else {
                        continue;
                    };
                    occurrences.push((
                        PremiseOccurrence {
                            premise,
                            column: column.index(),
                        },
                        sort,
                    ));
                }
            }
            let Some((representative, sort)) = occurrences.first().copied() else {
                continue;
            };
            for (occurrence, other_sort) in occurrences.into_iter().skip(1) {
                assert_eq!(sort, other_sort, "one query variable crosses replay sorts");
                if occurrence != representative {
                    push((
                        ReplayEqualitySource::Premise(representative),
                        ReplayEqualitySource::Premise(occurrence),
                    ));
                }
            }
        }

        for (premise, atom_id) in premises.iter().copied().enumerate() {
            let atom = &self.qb.query.atoms[atom_id];
            for constraint in atom
                .constraints
                .fast
                .iter()
                .chain(atom.constraints.slow.iter())
            {
                let Constraint::EqConst { col, val } = constraint else {
                    continue;
                };
                let Some(sort) = receipts.table_column_sort(atom.table, col.index()) else {
                    continue;
                };
                let term = receipts.lookup_term(sort, *val).unwrap_or_else(|| {
                    panic!(
                        "typed query constant in table {:?} column {} has no replay term",
                        atom.table,
                        col.index()
                    )
                });
                push((
                    ReplayEqualitySource::Premise(PremiseOccurrence {
                        premise,
                        column: col.index(),
                    }),
                    ReplayEqualitySource::Constant(EqualityEndpoint {
                        sort,
                        term,
                        raw: *val,
                    }),
                ));
            }
        }
        obligations
    }

    fn receipt_occurrence_value(
        &self,
        premises: &[AtomId],
        occurrence: PremiseOccurrence,
    ) -> QueryEntry {
        let atom = &self.qb.query.atoms[premises[occurrence.premise]];
        let column = ColumnId::from_usize(occurrence.column);
        atom_query_entry(atom, column)
    }

    /// Build the finished query.
    pub fn build(self) -> RuleId {
        self.build_with_description("")
    }

    fn build_symbol_map(&self) -> SymbolMap {
        let var_info = &self.qb.query.var_info;
        SymbolMap {
            atoms: self
                .qb
                .query
                .atoms
                .iter()
                .filter_map(|(id, atom)| {
                    let name = self.table_info(atom.table).name.clone();
                    name.map(|name| (id, name))
                })
                .collect(),
            vars: var_info
                .iter()
                .filter_map(|(id, info)| info.name.as_ref().map(|name| (id, name.clone())))
                .collect(),
        }
    }

    pub fn build_with_description(self, desc: impl Into<String>) -> RuleId {
        self.build_impl(desc, None, None).planned()
    }

    /// Build a rule together with the fixed receipt layout preserved from the
    /// source-level rule. Runtime capture copies only FactId/ReplayTermId
    /// handles according to this layout.
    pub fn build_with_receipts(self, desc: impl Into<String>, spec: RuleReceiptSpec) -> RuleId {
        self.build_impl(desc, Some(ReceiptBuildSpec::Rule(spec)), None)
            .planned()
    }

    /// Build a source action whose effective lanes cite one stable source
    /// identity directly, without allocating synthetic rule matches.
    pub fn build_source_with_receipts(
        self,
        desc: impl Into<String>,
        spec: SourceReceiptSpec,
    ) -> RuleId {
        assert!(
            self.qb.rsb.db.causal_receipts.is_some(),
            "source receipt actions require causal receipts"
        );
        assert!(
            self.qb.query.atoms.is_empty(),
            "source receipt actions require an empty query"
        );
        self.build_impl(desc, Some(ReceiptBuildSpec::Source(spec)), None)
            .planned()
    }

    /// Append an exact positive-check root action and build its native premise
    /// witness layout. The recorder runs after every previously-added guard.
    pub fn build_check_with_receipts(
        mut self,
        desc: impl Into<String>,
        spec: CheckReceiptSpec,
    ) -> RuleId {
        assert!(
            self.qb.rsb.db.causal_receipts.is_some(),
            "check receipt actions require causal receipts"
        );
        let implicit_equalities = self.receipt_equality_obligations(&spec.premises);
        for (left, right) in &spec.equalities {
            self.qb.mark_used([left.value(), right.value()]);
        }
        let CheckReceiptSpec {
            check,
            premises,
            equalities,
        } = spec;
        let receipts = self.qb.rsb.db.causal_receipts.as_ref().unwrap();
        let as_of_edges = receipts
            .equality_edge_count()
            .unwrap_or_else(|error| panic!("cannot capture exact check cutoff: {error}"));
        let compile = |endpoint| match endpoint {
            CheckEndpointSource::Premise {
                premise,
                column,
                value,
                constructor,
            } => {
                let atom = *premises
                    .get(premise)
                    .unwrap_or_else(|| panic!("check endpoint cites missing premise {premise}"));
                let table = self.qb.query.atoms[atom].table;
                let sort = receipts
                    .table_column_sort(table, column)
                    .unwrap_or_else(|| {
                        panic!(
                            "check endpoint premise {premise} column {column} has no replay sort"
                        )
                    });
                let term = if let Some((constructor_sort, op)) = constructor {
                    assert_eq!(
                        sort, constructor_sort,
                        "check constructor result sort differs from its producer column"
                    );
                    CheckTermSource::Constructor {
                        premise,
                        atom,
                        input_columns: column,
                        op,
                        origin: None,
                    }
                } else {
                    CheckTermSource::Premise { premise, column }
                };
                CheckEndpointSpec { value, sort, term }
            }
            CheckEndpointSource::Current { value, sort } => CheckEndpointSpec {
                value,
                sort,
                term: CheckTermSource::Current,
            },
        };
        let equalities = equalities
            .into_vec()
            .into_iter()
            .map(|(left, right)| {
                let left = compile(left);
                let right = compile(right);
                assert_eq!(
                    left.sort, right.sort,
                    "one check equality cannot cross logical sorts"
                );
                (left, right)
            })
            .collect::<Vec<_>>();
        let compile_implicit = |source| match source {
            ReplayEqualitySource::Premise(occurrence) => {
                let atom = premises[occurrence.premise];
                let table = self.qb.query.atoms[atom].table;
                let sort = receipts
                    .table_column_sort(table, occurrence.column)
                    .expect("receipt equality premise has no replay sort");
                CheckEndpointSpec {
                    value: self.receipt_occurrence_value(&premises, occurrence),
                    sort,
                    term: CheckTermSource::Premise {
                        premise: occurrence.premise,
                        column: occurrence.column,
                    },
                }
            }
            ReplayEqualitySource::Constant(endpoint) => CheckEndpointSpec {
                value: QueryEntry::Const(endpoint.raw),
                sort: endpoint.sort,
                term: CheckTermSource::Constant {
                    term: endpoint.term,
                },
            },
        };
        let implicit_equalities = implicit_equalities
            .into_iter()
            .map(|(left, right)| (compile_implicit(left), compile_implicit(right)))
            .collect::<Vec<_>>();
        for (left, right) in &implicit_equalities {
            self.qb.mark_used([&left.value, &right.value]);
        }
        self.qb.instrs.push(Instr::RecordCheck {
            check,
            equalities: equalities.into_boxed_slice(),
            implicit_equalities: implicit_equalities.into_boxed_slice(),
            as_of_edges,
        });
        self.build_impl(desc, Some(ReceiptBuildSpec::Check { premises }), None)
            .planned()
    }

    /// Return the current instruction boundary without planning the query.
    #[doc(hidden)]
    pub fn instruction_count(&self) -> usize {
        self.qb.instrs.len()
    }

    /// Finish a plan-free rule tape. `body_end` must be the boundary captured
    /// after all body computations/guards and before the first head action.
    #[doc(hidden)]
    pub fn build_grounded(self, body_end: usize) -> GroundedRule {
        self.build_impl("", None, Some(body_end)).grounded()
    }

    fn build_impl(
        mut self,
        desc: impl Into<String>,
        receipt: Option<ReceiptBuildSpec>,
        grounded_body_end: Option<usize>,
    ) -> RuleBuildOutput {
        let var_info = &self.qb.query.var_info;
        let symbol_map = self.build_symbol_map();
        // Generate an id for our actions and slot them in.
        let used_vars = SmallVec::from_iter(var_info.iter().filter_map(|(v, info)| {
            if info.used_in_rhs && !info.defined_in_rhs {
                Some(v)
            } else {
                None
            }
        }));
        let mut row_origin_inputs = HashMap::default();
        let receipt = receipt.map(|spec| match spec {
            ReceiptBuildSpec::Rule(spec) => {
                let equality_obligations = self.receipt_equality_obligations(&spec.premises);
                let premise_count = spec.premises.len();
                let premise_slots = Arc::new(
                    spec.premises
                        .iter()
                        .enumerate()
                        .map(|(slot, atom)| (*atom, PremiseSlot::from_usize(slot)))
                        .collect(),
                );
                let mut binding_sources = Vec::with_capacity(spec.bindings.len());
                let mut binding_sorts = Vec::with_capacity(spec.bindings.len());
                let mut next_residual = 0u32;
                for binding in &spec.bindings {
                    let RuleBindingSpec::Variable {
                        variable: var,
                        current_sort,
                    } = binding
                    else {
                        let RuleBindingSpec::Constant { term, sort } = binding else {
                            unreachable!()
                        };
                        assert!(!term.is_missing(), "receipt constant binding is missing");
                        let node = self
                            .qb
                            .rsb
                            .db
                            .causal_receipts
                            .as_ref()
                            .and_then(|receipts| receipts.replay_term(*term))
                            .unwrap_or_else(|| {
                                panic!("receipt constant binding has an unknown ReplayTermId")
                            });
                        assert_eq!(
                            node.sort(),
                            *sort,
                            "receipt constant binding has the wrong replay sort"
                        );
                        binding_sources.push(ReplayBindingSource::Constant { term: *term });
                        binding_sorts.push(*sort);
                        continue;
                    };
                    let mut occurrences = Vec::new();
                    let mut occurrence_sort = None;
                    for (premise, atom) in spec.premises.iter().copied().enumerate() {
                        let Some(subatom) = var_info[*var]
                            .occurrences
                            .iter()
                            .find(|occurrence| occurrence.atom == atom)
                        else {
                            continue;
                        };
                        let table = self.qb.query.atoms[atom].table;
                        for column in subatom.vars.iter().copied() {
                            let sort = self.qb.rsb.db.causal_receipts.as_ref().and_then(|receipts| {
                                receipts.table_column_sort(table, column.index())
                            }).unwrap_or_else(|| {
                                panic!(
                                    "receipt variable {var:?} selects non-replayable table column {}",
                                    column.index()
                                )
                            });
                            if let Some(prior) = occurrence_sort {
                                assert_eq!(prior, sort, "one receipt variable crosses replay sorts");
                            } else {
                                occurrence_sort = Some(sort);
                            }
                            occurrences.push(PremiseOccurrence {
                                premise,
                                column: column.index(),
                            });
                        }
                    }
                    let (source, sort) = if !occurrences.is_empty() {
                        let first_premise = occurrences[0].premise;
                        let representative = occurrences
                            .iter()
                            .copied()
                            .take_while(|occurrence| occurrence.premise == first_premise)
                            .last()
                            .expect("nonempty premise occurrences have a representative");
                        (
                            ReplayBindingSource::Premise {
                                representative,
                                occurrences: occurrences.into(),
                            },
                            occurrence_sort.unwrap(),
                        )
                    } else {
                        let sort = current_sort.unwrap_or_else(|| {
                                panic!(
                                    "receipt variable {var:?} has neither a retained premise nor a typed current-value producer"
                                )
                            });
                        (
                            ReplayBindingSource::Current {
                                variable: *var,
                                sort,
                                residual: {
                                    let residual = next_residual;
                                    next_residual += 1;
                                    residual
                                },
                            },
                            sort,
                        )
                    };
                    if matches!(source, ReplayBindingSource::Premise { .. }) {
                        row_origin_inputs.entry(*var).or_insert((
                            RecipeInput::Binding(
                                u16::try_from(binding_sources.len())
                                    .expect("one causal rule has more than u16 bindings"),
                            ),
                            sort,
                        ));
                    }
                    binding_sources.push(source);
                    binding_sorts.push(sort);
                }
                // Generated body variables are not part of the source-level
                // replay binding catalog, but their exact premise cell is
                // already present in the match witness. Let static action
                // recipes cite that fact directly instead of capturing a
                // runtime term or falling back to a by-value lookup.
                for (variable, info) in var_info.iter() {
                    if row_origin_inputs.contains_key(&variable) {
                        continue;
                    }
                    for (premise, atom) in spec.premises.iter().copied().enumerate() {
                        let Some(subatom) = info
                            .occurrences
                            .iter()
                            .find(|occurrence| occurrence.atom == atom)
                        else {
                            continue;
                        };
                        let Some(column) = subatom.vars.last().copied() else {
                            continue;
                        };
                        let table = self.qb.query.atoms[atom].table;
                        let Some(sort) = self
                            .qb
                            .rsb
                            .db
                            .causal_receipts
                            .as_ref()
                            .and_then(|receipts| {
                                receipts.table_column_sort(table, column.index())
                            })
                        else {
                            continue;
                        };
                        row_origin_inputs.insert(
                            variable,
                            (
                                RecipeInput::PremiseCell {
                                    premise: u16::try_from(premise)
                                        .expect("one causal rule has more than u16 premises"),
                                    column: u16::try_from(column.index())
                                        .expect("one causal premise has more than u16 columns"),
                                },
                                sort,
                            ),
                        );
                        break;
                    }
                }
                let binding_sources = self
                    .qb
                    .rsb
                    .db
                    .causal_receipts
                    .as_ref()
                    .expect("rule receipt actions require causal receipts")
                    .register_rule_binding_recipe(spec.rule, &binding_sources);
                let receipts = self.qb.rsb.db.causal_receipts.as_ref().unwrap();
                receipts.register_rule_equality_recipe(spec.rule, &equality_obligations);
                let term_recipe = self
                    .qb
                    .recipe_draft
                    .as_ref()
                    .expect("rule receipt actions require a static recipe draft")
                    .lower(&spec.bindings, &binding_sources, &binding_sorts);
                receipts.register_rule_term_recipe(spec.rule, term_recipe);
                ActionReceiptSpec {
                    kind: ActionReceiptKind::Rule(spec.rule),
                    premise_count,
                    premise_slots,
                    binding_sources,
                }
            }
            ReceiptBuildSpec::Source(spec) => ActionReceiptSpec {
                kind: ActionReceiptKind::Source(spec.source),
                premise_count: 0,
                premise_slots: Arc::new(DenseIdMap::new()),
                binding_sources: Arc::from([]),
            },
            ReceiptBuildSpec::Check { premises } => {
                let premise_count = premises.len();
                let premise_slots = Arc::new(
                    premises
                        .iter()
                        .enumerate()
                        .map(|(slot, atom)| (*atom, PremiseSlot::from_usize(slot)))
                        .collect(),
                );
                // Check actions may construct replay-safe values (notably
                // nested Vec/Pair terms) before RecordCheck. Their variables
                // are not rule replay bindings, but every query variable has
                // an exact premise occurrence in the selected witness. Feed
                // those cells into the same static recipe lowering used by
                // rules so check construction never falls back to a runtime
                // by-value lookup.
                for (variable, info) in var_info.iter() {
                    for (premise, atom) in premises.iter().copied().enumerate() {
                        let Some(subatom) = info
                            .occurrences
                            .iter()
                            .find(|occurrence| occurrence.atom == atom)
                        else {
                            continue;
                        };
                        let Some(column) = subatom.vars.last().copied() else {
                            continue;
                        };
                        let table = self.qb.query.atoms[atom].table;
                        let Some(sort) = self
                            .qb
                            .rsb
                            .db
                            .causal_receipts
                            .as_ref()
                            .and_then(|receipts| {
                                receipts.table_column_sort(table, column.index())
                            })
                        else {
                            continue;
                        };
                        row_origin_inputs.insert(
                            variable,
                            (
                                RecipeInput::PremiseCell {
                                    premise: u16::try_from(premise)
                                        .expect("one causal check has more than u16 premises"),
                                    column: u16::try_from(column.index()).expect(
                                        "one causal check premise has more than u16 columns",
                                    ),
                                },
                                sort,
                            ),
                        );
                        break;
                    }
                }
                ActionReceiptSpec {
                    kind: ActionReceiptKind::Check,
                    premise_count,
                    premise_slots,
                    binding_sources: Arc::from([]),
                }
            }
        });
        if receipt.is_some() {
            let receipts = self
                .qb
                .rsb
                .db
                .causal_receipts
                .as_ref()
                .expect("receipt action has no causal arena");
            self.qb
                .recipe_draft
                .as_ref()
                .expect("receipt action has no static term recipe draft")
                .attach_row_origins(
                    receipts,
                    &self.qb.query.atoms,
                    &mut self.qb.instrs,
                    &row_origin_inputs,
                );
        }
        let action = ActionInfo {
            instrs: Arc::new(self.qb.instrs),
            used_vars,
            receipt,
        };
        if let Some(body_end) = grounded_body_end {
            assert!(body_end <= action.instrs.len());
            return RuleBuildOutput::Grounded(GroundedRule {
                action,
                body_end,
                probes: Arc::from([]),
            });
        }
        let action_id = self.qb.rsb.rule_set.actions.push(action);
        self.qb.query.action = action_id;
        // Plan the query
        let plan = self.qb.rsb.db.plan_query(self.qb.query);
        let desc: String = desc.into();
        // Add it to the ruleset.
        RuleBuildOutput::Planned(
            self.qb
                .rsb
                .rule_set
                .plans
                .push((plan, desc.into(), symbol_map)),
        )
    }

    /// Return a variable containing the result of reading the specified counter.
    pub fn read_counter(&mut self, counter: CounterId) -> Variable {
        let dst = self.qb.new_var();
        self.qb.instrs.push(Instr::ReadCounter { counter, dst });
        self.qb.mark_defined(&dst.into());
        dst
    }

    /// Return a variable containing the result of looking up the specified
    /// column from the row corresponding to given keys in the given
    /// table.
    ///
    /// If the key does not currently have a mapping in the table, the values
    /// specified by `default_vals` will be inserted.
    pub fn lookup_or_insert(
        &mut self,
        table: TableId,
        args: &[QueryEntry],
        default_vals: &[WriteVal],
        dst_col: ColumnId,
    ) -> Result<Variable, QueryError> {
        let table_info = self.table_info(table);
        self.validate_keys(table, table_info, args)?;
        self.validate_vals(table, table_info, default_vals.iter())?;
        let res = self.qb.new_var();
        self.qb.instrs.push(Instr::LookupOrInsertDefault {
            table,
            args: args.to_vec(),
            default: default_vals.to_vec(),
            dst_col,
            dst_var: res,
            origin: None,
        });
        self.qb.mark_used(args);
        self.qb
            .mark_used(default_vals.iter().filter_map(|x| match x {
                WriteVal::QueryEntry(qe) => Some(qe),
                WriteVal::IncCounter(_) | WriteVal::CurrentVal(_) => None,
            }));
        self.qb.mark_defined(&res.into());
        Ok(res)
    }

    /// Receipt-only constructor lookup/insert with one typed structural
    /// producer. This is a distinct instruction so the ordinary hot path does
    /// not branch on replay metadata.
    pub fn lookup_or_insert_with_replay(
        &mut self,
        table: TableId,
        args: &[QueryEntry],
        default_vals: &[WriteVal],
        dst_col: ColumnId,
        replay: ReplayConstructorSpec,
    ) -> Result<Variable, QueryError> {
        let table_info = self.table_info(table);
        self.validate_keys(table, table_info, args)?;
        self.validate_vals(table, table_info, default_vals.iter())?;
        assert_eq!(
            replay.child_sorts.len(),
            args.len(),
            "constructor replay metadata needs one sort per key argument"
        );
        let receipts = self
            .qb
            .rsb
            .db
            .causal_receipts
            .as_ref()
            .expect("constructor replay metadata requires causal receipts")
            .clone();
        for (column, sort) in replay.child_sorts.iter().copied().enumerate() {
            assert_eq!(
                receipts.table_column_sort(table, column),
                Some(sort),
                "constructor replay child sort does not match its table column"
            );
        }
        assert_eq!(
            receipts.table_column_sort(table, dst_col.index()),
            Some(replay.result_sort),
            "constructor replay result sort does not match its table column"
        );
        for column in args.len()..table_info.spec.arity() {
            if column != dst_col.index() {
                assert!(
                    receipts.table_column_sort(table, column).is_none(),
                    "constructor replay has an unsupported typed default column {column}"
                );
            }
        }
        receipts
            .register_table_constructor(table, replay.clone())
            .unwrap_or_else(|error| {
                panic!("cannot register constructor replay metadata for {table:?}: {error}")
            });
        let res = self.qb.new_var();
        if let Some(draft) = self.qb.recipe_draft.as_mut() {
            draft.call_output(&receipts, res, args, &replay);
        }
        self.qb.instrs.push(Instr::LookupOrInsertDefaultReplay {
            table,
            args: args.to_vec(),
            default: default_vals.to_vec(),
            dst_col,
            dst_var: res,
            origin: None,
        });
        self.qb.mark_used(args);
        self.qb
            .mark_used(default_vals.iter().filter_map(|x| match x {
                WriteVal::QueryEntry(qe) => Some(qe),
                WriteVal::IncCounter(_) | WriteVal::CurrentVal(_) => None,
            }));
        self.qb.mark_defined(&res.into());
        Ok(res)
    }

    /// Return a variable containing the result of looking up the specified
    /// column from the row corresponding to given keys in the given
    /// table.
    ///
    /// If the key does not currently have a mapping in the table, the variable
    /// takes the value of `default`.
    pub fn lookup_with_default(
        &mut self,
        table: TableId,
        args: &[QueryEntry],
        default: QueryEntry,
        dst_col: ColumnId,
    ) -> Result<Variable, QueryError> {
        let table_info = self.table_info(table);
        self.validate_keys(table, table_info, args)?;
        let res = self.qb.new_var();
        self.qb.instrs.push(Instr::LookupWithDefault {
            table,
            args: args.to_vec(),
            dst_col,
            dst_var: res,
            default,
        });
        self.qb.mark_used(args);
        self.qb.mark_used(&[default]);
        self.qb.mark_defined(&res.into());
        Ok(res)
    }

    /// Return a variable containing the result of looking up the specified
    /// column from the row corresponding to given keys in the given
    /// table.
    ///
    /// If the key does not currently have a mapping in the table, execution of
    /// the rule is halted.
    pub fn lookup(
        &mut self,
        table: TableId,
        args: &[QueryEntry],
        dst_col: ColumnId,
    ) -> Result<Variable, QueryError> {
        let table_info = self.table_info(table);
        self.validate_keys(table, table_info, args)?;
        let res = self.qb.new_var();
        self.qb.instrs.push(Instr::Lookup {
            table,
            args: args.to_vec(),
            dst_col,
            dst_var: res,
        });
        self.qb.mark_used(args);
        self.qb.mark_defined(&res.into());
        Ok(res)
    }

    /// Insert the specified values into the given table.
    pub fn insert(&mut self, table: TableId, vals: &[QueryEntry]) -> Result<(), QueryError> {
        let table_info = self.table_info(table);
        self.validate_row(table, table_info, vals)?;
        self.qb.instrs.push(Instr::Insert {
            table,
            vals: vals.to_vec(),
            origin: None,
        });
        self.qb.mark_used(vals);
        Ok(())
    }

    /// Stage a receipt-only union whose two endpoints belong to the explicit
    /// logical equality sort.
    pub fn union_with_replay(
        &mut self,
        table: TableId,
        left: QueryEntry,
        right: QueryEntry,
        timestamp: QueryEntry,
        sort: ReplaySortId,
    ) -> Result<(), QueryError> {
        assert!(
            self.qb.rsb.db.causal_receipts.is_some(),
            "typed union actions require causal receipts"
        );
        self.validate_row(table, self.table_info(table), &[left, right, timestamp])?;
        self.qb.instrs.push(Instr::UnionWithReplay {
            table,
            left,
            right,
            timestamp,
            sort,
            left_origin: None,
            right_origin: None,
        });
        self.qb.mark_used(&[left, right, timestamp]);
        Ok(())
    }

    /// Insert the specified values into the given table if `l` and `r` are equal.
    pub fn insert_if_eq(
        &mut self,
        table: TableId,
        l: QueryEntry,
        r: QueryEntry,
        vals: &[QueryEntry],
    ) -> Result<(), QueryError> {
        let table_info = self.table_info(table);
        self.validate_row(table, table_info, vals)?;
        self.qb.instrs.push(Instr::InsertIfEq {
            table,
            l,
            r,
            vals: vals.to_vec(),
            origin: None,
        });
        self.qb
            .mark_used(vals.iter().chain(once(&l)).chain(once(&r)));
        Ok(())
    }

    /// Remove the specified entry from the given table, if it is there.
    pub fn remove(&mut self, table: TableId, args: &[QueryEntry]) -> Result<(), QueryError> {
        let table_info = self.table_info(table);
        self.validate_keys(table, table_info, args)?;
        self.qb.instrs.push(Instr::Remove {
            table,
            args: args.to_vec(),
        });
        self.qb.mark_used(args);
        Ok(())
    }

    /// Apply the given external function to the specified arguments.
    pub fn call_external(
        &mut self,
        func: ExternalFunctionId,
        args: &[QueryEntry],
    ) -> Result<Variable, QueryError> {
        self.call_external_with_replay(func, args, None)
    }

    /// Apply an external function, optionally registering a static structural
    /// recipe for its successful result. Runtime execution records no terms.
    pub fn call_external_with_replay(
        &mut self,
        func: ExternalFunctionId,
        args: &[QueryEntry],
        replay: Option<ReplayConstructorSpec>,
    ) -> Result<Variable, QueryError> {
        let res = self.qb.new_var();
        self.qb.instrs.push(Instr::External {
            func,
            args: args.to_vec(),
            dst: res,
        });
        self.qb.mark_used(args);
        self.qb.mark_defined(&res.into());
        self.promote_replay_call(args, res, replay);
        Ok(res)
    }

    /// Apply a primitive into an existing grounded variable slot. The runtime
    /// assigns an absent slot or validates an existing value for equality.
    #[doc(hidden)]
    pub fn call_external_assign_or_validate(
        &mut self,
        func: ExternalFunctionId,
        args: &[QueryEntry],
        dst: Variable,
    ) -> Result<(), QueryError> {
        self.qb.instrs.push(Instr::ExternalAssignOrValidate {
            func,
            args: args.to_vec(),
            dst,
        });
        self.qb.mark_used(args);
        self.qb.mark_defined(&dst.into());
        Ok(())
    }

    pub fn promote_replay_call(
        &mut self,
        args: &[QueryEntry],
        dst: Variable,
        replay: Option<ReplayConstructorSpec>,
    ) {
        if let Some(replay) = replay {
            assert_eq!(
                replay.child_sorts.len(),
                args.len(),
                "primitive replay metadata needs one sort per argument"
            );
            assert!(
                self.qb.rsb.db.causal_receipts.is_some(),
                "primitive replay metadata requires causal receipts"
            );
            let receipts = self
                .qb
                .rsb
                .db
                .causal_receipts
                .as_ref()
                .expect("causal recipe draft requires causal receipts")
                .clone();
            if let Some(draft) = self.qb.recipe_draft.as_mut() {
                draft.call_output(&receipts, dst, args, &replay);
            }
            if replay.promote_immediately {
                self.qb.instrs.push(Instr::PromoteReplayCall {
                    args: args.to_vec(),
                    dst,
                    replay: Box::new(replay),
                    origin: None,
                });
            }
        }
    }

    /// Copy one already-registered structural recipe onto the query variable
    /// whose runtime value a guard-only primitive validated. This is metadata
    /// only: it emits no instruction and performs no runtime term work.
    pub fn alias_replay_recipe(&mut self, source: Variable, destination: Variable) {
        self.qb
            .recipe_draft
            .as_mut()
            .expect("replay recipe alias requires causal receipts")
            .alias_output(source, destination);
    }

    /// Look up the given key in the given table. If the lookup fails, then call the given external
    /// function with the given arguments. Bind the result to the returned variable. If the
    /// external function returns None (and the lookup fails) then the execution of the rule halts.
    pub fn lookup_with_fallback(
        &mut self,
        table: TableId,
        key: &[QueryEntry],
        dst_col: ColumnId,
        func: ExternalFunctionId,
        func_args: &[QueryEntry],
    ) -> Result<Variable, QueryError> {
        self.lookup_with_fallback_inner(table, key, dst_col, func, func_args, false)
    }

    /// Look up a value that must already exist; `func` is only the native
    /// error path. Unlike a general fallback, a successful result is
    /// certified to come from the table and may therefore name a historical
    /// zero-key global in a causal replay recipe.
    pub fn lookup_required(
        &mut self,
        table: TableId,
        key: &[QueryEntry],
        dst_col: ColumnId,
        func: ExternalFunctionId,
        func_args: &[QueryEntry],
    ) -> Result<Variable, QueryError> {
        self.lookup_with_fallback_inner(table, key, dst_col, func, func_args, true)
    }

    fn lookup_with_fallback_inner(
        &mut self,
        table: TableId,
        key: &[QueryEntry],
        dst_col: ColumnId,
        func: ExternalFunctionId,
        func_args: &[QueryEntry],
        existing_required: bool,
    ) -> Result<Variable, QueryError> {
        let table_info = self.table_info(table);
        self.validate_keys(table, table_info, key)?;
        let res = self.qb.new_var();
        if existing_required
            && let (Some(receipts), Some(draft)) = (
                self.qb.rsb.db.causal_receipts.as_ref(),
                self.qb.recipe_draft.as_mut(),
            )
        {
            draft.lookup_output(receipts, res, table, dst_col, key);
        }
        self.qb.instrs.push(Instr::LookupWithFallback {
            table,
            table_key: key.to_vec(),
            func,
            func_args: func_args.to_vec(),
            dst_var: res,
            dst_col,
        });
        self.qb.mark_used(key);
        self.qb.mark_used(func_args);
        self.qb.mark_defined(&res.into());
        Ok(res)
    }

    pub fn call_external_with_fallback(
        &mut self,
        f1: ExternalFunctionId,
        args1: &[QueryEntry],
        f2: ExternalFunctionId,
        args2: &[QueryEntry],
    ) -> Result<Variable, QueryError> {
        self.call_external_with_fallback_replay(f1, args1, f2, args2, None)
    }

    /// Call a primitive with a fallback. A single static structural recipe
    /// cannot distinguish which branch produced each lane, so replay metadata
    /// is deliberately not registered for this operation. If a retained fact
    /// needs such a current value, cold projection fails closed.
    pub fn call_external_with_fallback_replay(
        &mut self,
        f1: ExternalFunctionId,
        args1: &[QueryEntry],
        f2: ExternalFunctionId,
        args2: &[QueryEntry],
        replay: Option<ReplayConstructorSpec>,
    ) -> Result<Variable, QueryError> {
        let res = self.qb.new_var();
        if let Some(replay) = replay.as_ref() {
            assert_eq!(
                replay.child_sorts.len(),
                args1.len(),
                "primitive replay metadata needs one sort per argument"
            );
            assert!(
                self.qb.rsb.db.causal_receipts.is_some(),
                "primitive replay metadata requires causal receipts"
            );
        }
        self.qb.instrs.push(Instr::ExternalWithFallback {
            f1,
            args1: args1.to_vec(),
            f2,
            args2: args2.to_vec(),
            dst: res,
        });
        self.qb.mark_used(args1);
        self.qb.mark_used(args2);
        self.qb.mark_defined(&res.into());
        Ok(res)
    }

    /// Continue execution iff the two arguments are equal.
    pub fn assert_eq(&mut self, l: QueryEntry, r: QueryEntry) {
        self.qb.instrs.push(Instr::AssertEq(l, r));
        self.qb.mark_used(&[l, r]);
    }

    /// Continue execution iff the two arguments are not equal.
    pub fn assert_ne(&mut self, l: QueryEntry, r: QueryEntry) -> Result<(), QueryError> {
        self.qb.instrs.push(Instr::AssertNe(l, r));
        self.qb.mark_used(&[l, r]);
        Ok(())
    }

    /// Continue execution iff there is some `i` such that `l[i] != r[i]`.
    ///
    /// This is useful when doing egglog-style rebuilding.
    pub fn assert_any_ne(&mut self, l: &[QueryEntry], r: &[QueryEntry]) -> Result<(), QueryError> {
        if l.len() != r.len() {
            return Err(QueryError::MultiComparisonMismatch {
                l: l.len(),
                r: r.len(),
            });
        }

        let mut ops = Vec::with_capacity(l.len() + r.len());
        ops.extend_from_slice(l);
        ops.extend_from_slice(r);
        self.qb.instrs.push(Instr::AssertAnyNe {
            ops,
            divider: l.len(),
        });
        self.qb.mark_used(l);
        self.qb.mark_used(r);
        Ok(())
    }

    fn validate_row(
        &self,
        table: TableId,
        info: &TableInfo,
        vals: &[QueryEntry],
    ) -> Result<(), QueryError> {
        if vals.len() != info.spec.arity() {
            Err(QueryError::TableArityMismatch {
                table,
                expected: info.spec.arity(),
                got: vals.len(),
            })
        } else {
            Ok(())
        }
    }

    fn validate_keys(
        &self,
        table: TableId,
        info: &TableInfo,
        keys: &[QueryEntry],
    ) -> Result<(), QueryError> {
        if keys.len() != info.spec.n_keys {
            Err(QueryError::KeyArityMismatch {
                table,
                expected: info.spec.n_keys,
                got: keys.len(),
            })
        } else {
            Ok(())
        }
    }

    fn validate_vals<'b>(
        &self,
        table: TableId,
        info: &TableInfo,
        vals: impl Iterator<Item = &'b WriteVal>,
    ) -> Result<(), QueryError> {
        for (i, _) in vals.enumerate() {
            let col = i + info.spec.n_keys;
            if col >= info.spec.arity() {
                return Err(QueryError::TableArityMismatch {
                    table,
                    expected: info.spec.arity(),
                    got: col,
                });
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub(crate) struct Atom {
    pub(crate) table: TableId,
    pub(crate) var_columns: VarColumnMap,
    /// These constraints are an initial take at processing "fast" constraints as well as a
    /// potential list of "slow" constraints.
    ///
    /// Fast constraints get re-computed when queries are executed. In particular, this makes it
    /// possible to cache plans and add new fast constraints to them without re-planning.
    pub(crate) constraints: ProcessedConstraints,
}

impl Atom {
    pub(crate) fn vars(&self) -> impl Iterator<Item = Variable> + '_ {
        self.var_columns.vars()
    }

    pub(crate) fn get_var(&self, col: ColumnId) -> Option<Variable> {
        self.var_columns.get_var(col)
    }

    pub(crate) fn get_col(&self, var: Variable) -> Option<ColumnId> {
        self.var_columns.get_col(var)
    }
}

#[derive(Clone, Default)]
pub(crate) struct VarColumnMap {
    var_to_column: DenseIdMap<Variable, ColumnId>,
    column_to_var: DenseIdMap<ColumnId, Variable>,
}

impl std::fmt::Debug for VarColumnMap {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut entries: Vec<_> = self.column_to_var.iter().collect();
        entries.sort_by_key(|(col, _)| col.index());

        f.write_str("VarColumnMap(")?;
        for (i, (col, var)) in entries.iter().enumerate() {
            if i > 0 {
                f.write_str(", ")?;
            }
            write!(f, "{col:?} -> {var:?}")?;
        }
        f.write_str(")")
    }
}

impl VarColumnMap {
    pub(crate) fn insert(&mut self, var: Variable, col: ColumnId) -> Option<ColumnId> {
        let prev = self.var_to_column.insert(var, col);
        self.column_to_var.insert(col, var);
        prev
    }

    pub(crate) fn get_col(&self, var: Variable) -> Option<ColumnId> {
        self.var_to_column.get(var).copied()
    }

    pub(crate) fn get_var(&self, col: ColumnId) -> Option<Variable> {
        self.column_to_var.get(col).copied()
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = (ColumnId, Variable)> + '_ {
        self.column_to_var.iter().map(|(col, var)| (col, *var))
    }

    pub(crate) fn vars(&self) -> impl Iterator<Item = Variable> + '_ {
        self.iter().map(|(_, var)| var)
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.var_to_column.len() == 0
    }
}

/// A functional dependency inferencer.
///
/// A functional dependency (x, y, ...) -> (u, v, ...) means that if we know
/// the values of x, y, ..., then we can determine u, v, ...
///
/// This data structure can compute the closure of a set of variables under
/// a set of functional dependencies.
#[derive(Clone, Default)]
pub(crate) struct FunDeps {
    /// List of functional dependencies (antecedent -> consequent)
    dependencies: Vec<(Vec<Variable>, Vec<Variable>)>,
}

impl FunDeps {
    /// Add a functional dependency: antecedent -> consequent.
    pub fn add_dependency(&mut self, antecedent: Vec<Variable>, consequent: Vec<Variable>) {
        // Don't add trivial dependencies.
        if !antecedent.is_empty() {
            self.dependencies.push((antecedent, consequent));
        }
    }

    /// Returns all variables that can be determined from the input variables
    /// using the functional dependencies.
    pub fn closure(
        &self,
        variables: impl IntoIterator<Item = Variable>,
    ) -> DenseIdMap<Variable, ()> {
        let mut result: DenseIdMap<Variable, ()> =
            DenseIdMap::from_iter(variables.into_iter().map(|v| (v, ())));
        let mut changed = true;

        while changed {
            changed = false;
            for (antecedent, consequent) in &self.dependencies {
                // If all variables in the antecedent are in the result,
                // add all variables in the consequent.
                if antecedent.iter().all(|v| result.contains_key(*v)) {
                    for v in consequent {
                        if !result.contains_key(*v) {
                            result.insert(*v, ());
                            changed = true;
                        }
                    }
                }
            }
        }

        result
    }
}

impl std::fmt::Debug for FunDeps {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use std::fmt::Write;

        let mut deps = String::new();

        for (i, (ant, cons)) in self.dependencies.iter().enumerate() {
            if i > 0 {
                deps.push_str("; ");
            }

            deps.push('{');
            for (j, v) in ant.iter().enumerate() {
                if j > 0 {
                    deps.push_str(", ");
                }
                write!(&mut deps, "{v:?}")?;
            }
            deps.push('}');

            deps.push_str(" -> ");

            deps.push('{');
            for (j, v) in cons.iter().enumerate() {
                if j > 0 {
                    deps.push_str(", ");
                }
                write!(&mut deps, "{v:?}")?;
            }
            deps.push('}');
        }

        write!(f, "FunDeps {{ {deps} }}")
    }
}

pub(crate) struct Query {
    pub(crate) var_info: DenseIdMap<Variable, VarInfo>,
    pub(crate) atoms: DenseIdMap<AtomId, Atom>,
    pub(crate) action: ActionId,
    pub(crate) plan_strategy: PlanStrategy,
    pub(crate) fun_deps: FunDeps,
    /// If `true`, skip tree-decomposition during query planning and
    /// always use the single-bag fast path in
    /// [`crate::free_join::plan::tree_decompose_and_plan`]. Set via
    /// [`QueryBuilder::set_no_decomp`].
    pub(crate) no_decomp: bool,
}

#[cfg(test)]
mod recipe_lowerer_tests {
    use super::*;

    #[test]
    fn ephemeral_recipe_leaves_do_not_enter_pointer_memo() {
        let first = Variable::new(0);
        let second = Variable::new(1);
        let sort = ReplaySortId::new(0);
        let mut inputs = HashMap::default();
        inputs.insert(first, (RecipeInput::Binding(0), sort));
        inputs.insert(second, (RecipeInput::Binding(1), sort));
        let mut lowerer = RecipeLowerer {
            inputs,
            memo: HashMap::default(),
            observed_sorts: HashMap::default(),
        };

        for (variable, expected_binding) in [(first, 0), (second, 1)] {
            let root = Arc::new(RecipeExpr::Input(variable));
            assert!(matches!(
                lowerer.try_lower(&root, sort).as_deref(),
                Some(TermTemplate::Binding { binding }) if *binding == expected_binding
            ));
            assert!(
                lowerer.memo.is_empty() && lowerer.observed_sorts.is_empty(),
                "short-lived leaves must not be keyed by their reusable allocation address"
            );
        }
    }
}

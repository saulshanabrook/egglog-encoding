//! Replacement rule and action execution; no native query/action interpreter.

use egglog_core_relations::{
    ActionInstruction as Op, BackendTable, Constraint, ExecutionState, MatchBackend, MatchRelation,
    QueryEntry as Entry, RelationalBackend, RelationalRule, Value, Variable, WrappedTable,
    WriteVal,
};
use egglog_numeric_id::NumericId;
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    },
};

use crate::columns::{GpuOps, JoinPlan, Matrix};
use crate::{
    AdapterMode, Matcher,
    storage::{Store, matches},
};

/// A complete replacement for relational storage, queries, and action bytecode.
/// Frontend scheduling and opaque host primitive callbacks keep their existing ABI.
pub struct Backend {
    device: Option<Arc<GpuOps>>,
    matcher: Matcher,
    rules: AtomicUsize,
    actions: AtomicUsize,
    tables: AtomicUsize,
}

#[derive(Debug)]
pub struct BackendStatistics {
    pub rules: usize,
    pub actions: usize,
    pub tables: usize,
    pub device_dispatches: usize,
    pub device_submissions: usize,
    pub device_readbacks: usize,
    pub device_sorts: usize,
    pub sort_cache_hits: usize,
}

impl Backend {
    pub fn simulated(max_rows: usize) -> Self {
        Self::new(Matcher::simulated(max_rows))
    }
    pub fn vulkan(mode: AdapterMode, max_rows: usize) -> anyhow::Result<Self> {
        Ok(Self::new(Matcher::vulkan(mode, max_rows)?))
    }
    fn new(matcher: Matcher) -> Self {
        assert!(
            matcher.max_rows > 0 && matcher.max_rows < u32::MAX as usize,
            "row limit must fit the device index space"
        );
        let device = matcher
            .device
            .as_ref()
            .map(|d| Arc::new(GpuOps::new(d.clone(), matcher.max_rows)));
        Self {
            device,
            matcher,
            rules: AtomicUsize::new(0),
            actions: AtomicUsize::new(0),
            tables: AtomicUsize::new(0),
        }
    }
    pub fn adapter(&self) -> &str {
        self.matcher.adapter()
    }
    pub fn statistics(&self) -> BackendStatistics {
        BackendStatistics {
            rules: self.rules.load(Ordering::Relaxed),
            actions: self.actions.load(Ordering::Relaxed),
            tables: self.tables.load(Ordering::Relaxed),
            device_dispatches: self
                .device
                .as_ref()
                .map_or(0, |d| d.dispatches.load(Ordering::Relaxed)),
            device_submissions: self
                .device
                .as_ref()
                .map_or(0, |d| d.submissions.load(Ordering::Relaxed)),
            device_readbacks: self
                .device
                .as_ref()
                .map_or(0, |d| d.readbacks.load(Ordering::Relaxed)),
            device_sorts: self
                .device
                .as_ref()
                .map_or(0, |d| d.sorts.load(Ordering::Relaxed)),
            sort_cache_hits: self
                .device
                .as_ref()
                .map_or(0, |d| d.sort_cache_hits.load(Ordering::Relaxed)),
        }
    }
    pub fn egraph(self: &Arc<Self>) -> egglog::EGraph {
        let mut graph = egglog_experimental::new_experimental_egraph_with_term_encoding();
        graph.set_relational_backend(self.clone());
        graph
    }

    fn query(
        &self,
        rule: &RelationalRule,
        state: &ExecutionState,
    ) -> Result<MatchRelation, String> {
        let mut uses = BTreeMap::<Variable, usize>::new();
        for atom in &rule.atoms {
            let mut vars: BTreeSet<_> = atom.columns.iter().map(|&(_, v)| v).collect();
            if let Some((Entry::Var(v), _)) = &atom.occurrence {
                vars.insert(*v);
            }
            for v in vars {
                *uses.entry(v).or_default() += 1;
            }
        }
        let needed = |v: &Variable| rule.inputs.contains(v) || uses[v] > 1;
        let atoms: Vec<_> = rule
            .atoms
            .iter()
            .map(|atom| {
                let store = state
                    .get_table(atom.table)
                    .as_any()
                    .downcast_ref::<Store>()
                    .expect("replacement encountered native storage");
                let columns: Vec<_> = atom
                    .columns
                    .iter()
                    .copied()
                    .filter(|(_, v)| needed(v))
                    .collect();
                let mut variables: Vec<_> = columns.iter().map(|&(_, v)| v).collect();
                if let Some((Entry::Var(v), _)) = &atom.occurrence
                    && needed(v)
                    && !variables.contains(v)
                {
                    variables.push(*v);
                }
                let mut rows = Vec::new();
                for (row, &live) in store.rows.iter().zip(&store.live) {
                    if !live || !atom.constraints.iter().all(|c| matches(row, c)) {
                        continue;
                    }
                    let values: Vec<_> = columns.iter().map(|(c, _)| row[c.index()]).collect();
                    match &atom.occurrence {
                        None => rows.push(values),
                        Some((key, cols)) => {
                            let keys: BTreeSet<_> = cols.iter().map(|c| row[c.index()]).collect();
                            match key {
                                Entry::Const(c) => {
                                    if keys.contains(c) {
                                        rows.push(values);
                                    }
                                }
                                Entry::Var(v) => {
                                    if let Some((col, _)) =
                                        atom.columns.iter().find(|(_, w)| v == w)
                                    {
                                        if keys.contains(&row[col.index()]) {
                                            rows.push(values);
                                        }
                                    } else if needed(v) {
                                        for key in keys {
                                            let mut row = values.clone();
                                            row.push(key);
                                            rows.push(row);
                                        }
                                    } else if !keys.is_empty() {
                                        rows.push(values);
                                    }
                                }
                            }
                        }
                    }
                }
                rows.sort_unstable();
                rows.dedup();
                MatchRelation { variables, rows }
            })
            .collect();
        self.matcher.evaluate(atoms)
    }

    fn device_query(
        &self,
        rule: &RelationalRule,
        state: &ExecutionState,
        device: &GpuOps,
    ) -> Result<(Vec<Variable>, Matrix), String> {
        let mut uses = BTreeMap::<Variable, usize>::new();
        for atom in &rule.atoms {
            let store = state
                .get_table(atom.table)
                .as_any()
                .downcast_ref::<Store>()
                .expect("replacement storage");
            if store.rows.is_empty() {
                return Ok((Vec::new(), device.upload(&[], 0)?));
            }
            let mut vars: BTreeSet<_> = atom.columns.iter().map(|&(_, v)| v).collect();
            if let Some((Entry::Var(v), _)) = &atom.occurrence {
                vars.insert(*v);
            }
            for v in vars {
                *uses.entry(v).or_default() += 1;
            }
        }
        let mut atoms = Vec::new();
        for atom in &rule.atoms {
            let store = state
                .get_table(atom.table)
                .as_any()
                .downcast_ref::<Store>()
                .expect("replacement storage");
            let (matrix, live) = store.resident.as_ref().expect("resident table");
            let columns: Vec<_> = atom
                .columns
                .iter()
                .copied()
                .filter(|(_, v)| rule.inputs.contains(v) || uses[v] > 1)
                .collect();
            let mut vars: Vec<_> = columns.iter().map(|&(_, v)| v).collect();
            let mut projection: Vec<_> = columns.iter().map(|(c, _)| c.rep()).collect();
            let mut occurrence_cols = Vec::new();
            let (mode, key) = match &atom.occurrence {
                None => (0, 0),
                Some((entry, cols)) => {
                    occurrence_cols.extend(cols.iter().map(|c| c.rep()));
                    match entry {
                        Entry::Const(v) => (1, v.rep()),
                        Entry::Var(v) => {
                            if let Some((c, _)) = atom.columns.iter().find(|(_, w)| w == v) {
                                (3, c.rep())
                            } else {
                                if rule.inputs.contains(v) || uses[v] > 1 {
                                    vars.push(*v);
                                    projection.push(u32::MAX);
                                }
                                (2, 0)
                            }
                        }
                    }
                }
            };
            let preserves_key = projection_preserves_key(
                store.keys(),
                &projection,
                &atom.constraints,
                mode == 2 && !projection.contains(&u32::MAX),
            );
            let selected = device.select(
                matrix,
                live,
                &atom.constraints,
                &projection,
                (mode, key, &occurrence_cols),
                preserves_key,
            )?;
            if selected.rows == 0 {
                return Ok((vars, selected));
            }
            atoms.push((vars, selected));
        }
        atoms.sort_by_key(|(_, m)| m.rows);
        if atoms.is_empty() {
            return Ok((Vec::new(), device.upload(&[Vec::new()], 0)?));
        }
        let (mut vars, mut result) = atoms.remove(0);
        while !atoms.is_empty() {
            let connected = atoms
                .iter()
                .any(|(v, _)| v.iter().any(|v| vars.contains(v)));
            let mut best: Option<(usize, Vec<usize>, JoinPlan)> = None;
            for (i, (right_vars, right)) in atoms.iter().enumerate() {
                let keys: Vec<_> = vars
                    .iter()
                    .enumerate()
                    .filter_map(|(l, v)| right_vars.iter().position(|r| r == v).map(|r| (l, r)))
                    .collect();
                if connected && keys.is_empty() {
                    continue;
                }
                let extra: Vec<_> = right_vars
                    .iter()
                    .enumerate()
                    .filter(|(_, v)| !vars.contains(v))
                    .map(|(i, _)| i)
                    .collect();
                let plan = device.plan_join(&result, right, &keys, &extra)?;
                if best.as_ref().is_none_or(|(_, _, old)| plan.rows < old.rows) {
                    best = Some((i, extra, plan));
                }
                if best.as_ref().is_some_and(|(_, _, plan)| plan.rows == 0) {
                    break;
                }
            }
            let (next, extra, plan) = best.unwrap();
            let (right_vars, right) = atoms.remove(next);
            result = device.join(plan).map_err(|error| {
                format!(
                    "{error}; joining {} rows {:?} with {} rows {:?}",
                    result.rows, vars, right.rows, right_vars
                )
            })?;
            vars.extend(extra.iter().map(|&i| right_vars[i]));
            if result.rows == 0 {
                break;
            }
        }
        Ok((vars, result))
    }
}

// Selected rows remain distinct when their FD key is determined by projected
// values and constant/equality filters. An unprojected occurrence expansion can
// still emit one row multiple times, so it needs duplicate elimination.
fn projection_preserves_key(
    keys: Option<usize>,
    projection: &[u32],
    constraints: &[Constraint],
    unprojected_occurrence: bool,
) -> bool {
    let Some(keys) = keys.filter(|_| !unprojected_occurrence) else {
        return false;
    };
    let mut known: BTreeSet<_> = projection.iter().copied().collect();
    for c in constraints {
        if let Constraint::EqConst { col, .. } = c {
            known.insert(col.rep());
        }
    }
    loop {
        let before = known.len();
        for c in constraints {
            if let Constraint::Eq { l_col, r_col } = c
                && (known.contains(&l_col.rep()) || known.contains(&r_col.rep()))
            {
                known.extend([l_col.rep(), r_col.rep()]);
            }
        }
        if known.len() == before {
            break;
        }
    }
    (0..keys as u32).all(|key| known.contains(&key))
}

impl RelationalBackend for Backend {
    fn create_table(&self, definition: BackendTable) -> WrappedTable {
        self.tables.fetch_add(1, Ordering::Relaxed);
        WrappedTable::new(Store::new(definition, self.device.clone()))
    }
    fn check_tables(&self, state: &ExecutionState) -> Result<(), String> {
        if let Some(device) = &self.device {
            device.flush();
        }
        for id in state.table_ids() {
            let store = state
                .get_table(id)
                .as_any()
                .downcast_ref::<Store>()
                .ok_or("replacement encountered native storage")?;
            if let Some(error) = &store.error {
                return Err(error.clone());
            }
        }
        Ok(())
    }
    fn execute(
        &self,
        rules: &[RelationalRule],
        state: &mut ExecutionState,
    ) -> Result<Vec<usize>, String> {
        let mut counts = vec![0; rules.len()];
        for (i, rule) in rules.iter().enumerate() {
            if state.should_stop() {
                break;
            }
            self.rules.fetch_add(1, Ordering::Relaxed);
            if let Some(device) = &self.device {
                let (vars, matrix) = self
                    .device_query(rule, state, device)
                    .map_err(|error| format!("rule {}: {error}", rule.description))?;
                counts[i] =
                    crate::device_actions::run(device, &rule.instructions, vars, matrix, state)
                        .map_err(|error| format!("rule {} actions: {error}", rule.description))?;
                self.actions.fetch_add(counts[i], Ordering::Relaxed);
                continue;
            }
            let matched = self
                .query(rule, state)
                .map_err(|error| format!("rule {}: {error}", rule.description))?;
            let columns: Vec<_> = rule
                .inputs
                .iter()
                .map(|v| matched.variables.iter().position(|w| v == w).unwrap())
                .collect();
            let mut vars = rule.inputs.clone();
            let mut bindings: Vec<Vec<Value>> = matched
                .rows
                .into_iter()
                .map(|row| columns.iter().map(|&c| row[c]).collect())
                .collect();
            // Match the device's instruction-major batches, including partial
            // effects from rows filtered out by a later instruction.
            for op in &rule.instructions {
                let mut next_vars = vars.clone();
                if let Some(dst) = action_destination(op)
                    && !next_vars.contains(&dst)
                {
                    next_vars.push(dst);
                }
                // Keep compact row payloads, not a heap-allocated tree for
                // every match. One scratch map serves the instruction's rows.
                let mut mapped = BTreeMap::new();
                let mut survivors = Vec::new();
                for mut row in bindings {
                    if state.should_stop() {
                        break;
                    }
                    mapped.extend(vars.iter().copied().zip(row.iter().copied()));
                    if run_actions(std::slice::from_ref(op), &mut mapped, state)? {
                        row.clear();
                        row.extend(next_vars.iter().map(|v| mapped[v]));
                        survivors.push(row);
                    }
                }
                bindings = survivors;
                vars = next_vars;
            }
            counts[i] = if state.should_stop() {
                0
            } else {
                bindings.len()
            };
            self.actions.fetch_add(counts[i], Ordering::Relaxed);
        }
        Ok(counts)
    }
}

fn action_destination(op: &Op) -> Option<Variable> {
    match op {
        Op::ReadCounter { dst, .. }
        | Op::External { dst, .. }
        | Op::ExternalWithFallback { dst, .. } => Some(*dst),
        Op::Insert { bind, .. } => bind.map(|(_, v)| v),
        Op::LookupOrInsertDefault { dst_var, .. }
        | Op::Lookup { dst_var, .. }
        | Op::LookupWithDefault { dst_var, .. }
        | Op::LookupWithFallback { dst_var, .. } => Some(*dst_var),
        Op::Remove { .. }
        | Op::InsertIfEq { .. }
        | Op::AssertEq(..)
        | Op::AssertNe(..)
        | Op::AssertAnyNe { .. } => None,
    }
}

fn value(entry: Entry, vars: &BTreeMap<Variable, Value>) -> Value {
    match entry {
        Entry::Const(v) => v,
        Entry::Var(v) => vars[&v],
    }
}
fn values(entries: &[Entry], vars: &BTreeMap<Variable, Value>) -> Vec<Value> {
    entries.iter().map(|&e| value(e, vars)).collect()
}
fn write(
    vals: &[WriteVal],
    mut row: Vec<Value>,
    vars: &BTreeMap<Variable, Value>,
    state: &mut ExecutionState,
) -> Result<Vec<Value>, String> {
    for val in vals {
        row.push(match *val {
            WriteVal::QueryEntry(e) => value(e, vars),
            WriteVal::IncCounter(c) => Value::from_usize(state.reserve_counter(c, 1)?.start),
            WriteVal::CurrentVal(i) => row[i],
        });
    }
    Ok(row)
}

pub(crate) fn run_actions(
    ops: &[Op],
    vars: &mut BTreeMap<Variable, Value>,
    state: &mut ExecutionState,
) -> Result<bool, String> {
    for op in ops {
        match op {
            Op::ReadCounter { counter, dst } => {
                vars.insert(*dst, Value::from_usize(state.read_counter(*counter)));
            }
            Op::AssertEq(a, b) => {
                if value(*a, vars) != value(*b, vars) {
                    return Ok(false);
                }
            }
            Op::AssertNe(a, b) => {
                if value(*a, vars) == value(*b, vars) {
                    return Ok(false);
                }
            }
            Op::AssertAnyNe { ops, divider } => {
                let vals = values(ops, vars);
                if vals[..*divider] == vals[*divider..] {
                    return Ok(false);
                }
            }
            Op::Insert { table, vals, bind } => {
                let row = write(vals, Vec::new(), vars, state)?;
                state.stage_insert(*table, &row);
                if let Some((col, dst)) = bind {
                    vars.insert(*dst, row[col.index()]);
                }
            }
            Op::InsertIfEq { table, l, r, vals } => {
                if value(*l, vars) == value(*r, vars) {
                    state.stage_insert(*table, &values(vals, vars));
                }
            }
            Op::Remove { table, args } => state.stage_remove(*table, &values(args, vars)),
            Op::Lookup {
                table,
                args,
                dst_col,
                dst_var,
            } => {
                let Some(v) = state
                    .get_table(*table)
                    .get_row_column(&values(args, vars), *dst_col)
                else {
                    return Ok(false);
                };
                vars.insert(*dst_var, v);
            }
            Op::LookupWithDefault {
                table,
                args,
                dst_col,
                dst_var,
                default,
            } => {
                let v = state
                    .get_table(*table)
                    .get_row_column(&values(args, vars), *dst_col)
                    .unwrap_or_else(|| value(*default, vars));
                vars.insert(*dst_var, v);
            }
            Op::LookupOrInsertDefault {
                table,
                args,
                default,
                dst_col,
                dst_var,
            } => {
                let key = values(args, vars);
                // Use the primitive ABI's shared prediction cache so opaque
                // callbacks and lowered intern operations agree within a run.
                let row = if let Some(row) = state.predicted_row(*table, &key) {
                    row
                } else {
                    let row = write(default, key.clone(), vars, state)?;
                    state.publish_prediction(*table, &key, &row)
                };
                let v = row[dst_col.index()];
                vars.insert(*dst_var, v);
            }
            Op::LookupWithFallback {
                table,
                table_key,
                func,
                func_args,
                dst_col,
                dst_var,
            } => {
                let v = state
                    .get_table(*table)
                    .get_row_column(&values(table_key, vars), *dst_col)
                    .or_else(|| state.call_external_func(*func, &values(func_args, vars)));
                let Some(v) = v else {
                    return Ok(false);
                };
                vars.insert(*dst_var, v);
            }
            Op::External { func, args, dst } => {
                let Some(v) = state.call_external_func(*func, &values(args, vars)) else {
                    return Ok(false);
                };
                vars.insert(*dst, v);
            }
            Op::ExternalWithFallback {
                f1,
                args1,
                f2,
                args2,
                dst,
            } => {
                let v = state
                    .call_external_func(*f1, &values(args1, vars))
                    .or_else(|| state.call_external_func(*f2, &values(args2, vars)));
                let Some(v) = v else {
                    return Ok(false);
                };
                vars.insert(*dst, v);
            }
        }
        if state.should_stop() {
            return Ok(false);
        }
    }
    Ok(true)
}

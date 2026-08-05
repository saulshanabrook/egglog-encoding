//! Backend merge programs and their compiled reference-backend evaluator.
//!
//! A merge program performs ordered actions once, then evaluates one result expression per
//! physical value column against the same prior and incoming rows. Exact repeat rows and collisions
//! covered by an identity-prefix guard skip the complete program. Result expressions are not
//! necessarily pure: [`MergeExpr::UnionId`] stages a union, while [`MergeExpr::Function`] may
//! construct a missing row. For a conflict that does run the program, the `actions` list executes
//! once rather than once per result. Trace-enabled execution accepts a function call only for the
//! certified binary constructor shape `Constructor(old, new)`, whose hit or insertion is retained
//! exactly. It rejects other table reads and reached actionful programs before their effects because
//! check-directed replay has one computed-result carrier and does not retain ordered merge-block
//! effects or multiple results.
//!
//! A failed action or result rejects the owner row before publication. Effects completed before a
//! later failure are not rolled back.

use super::{
    ColumnId, DefaultVal, EGraph, ExecutionState, ExternalFunctionId, FunctionId, IndexSet,
    MergeResultShape, NumericId, RowVals, SchemaMath, SmallVec, TableAction, TableId, TableKind,
    Value, combine_subsumed, core_relations,
};

/// An FD-conflict program: run `actions` in order, then compute one result per value column.
///
/// The source language has one result expression. Tuple-valued results are normalized here into
/// one expression per physical value column, so `results.len()` must equal the function's value
/// arity.
pub struct MergeProgram {
    /// Effects performed once, in source order, before any result is evaluated.
    pub actions: Vec<MergeAction>,
    /// One result expression per physical value column.
    pub results: Vec<MergeExpr>,
}

/// Which side of an FD conflict a merge expression reads.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum MergeInputSide {
    /// The row currently retained by the table.
    Prior,
    /// The newly proposed row.
    Incoming,
}

/// A value-column index within the output portion of a function row.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct MergeValueColumn(usize);

impl MergeValueColumn {
    /// Address value column `index`, excluding leading key columns.
    pub const fn new(index: usize) -> Self {
        Self(index)
    }

    /// Return the zero-based value-column index.
    pub const fn index(self) -> usize {
        self.0
    }
}

/// The slot assigned to a preceding merge-local `let` binding.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct MergeBindingId(usize);

impl MergeBindingId {
    /// Address the binding created by the `index`th merge-local `let`.
    pub const fn new(index: usize) -> Self {
        Self(index)
    }

    /// Return the zero-based binding index.
    pub const fn index(self) -> usize {
        self.0
    }
}

/// A value expression evaluated by a [`MergeProgram`].
pub enum MergeExpr {
    /// Panic unless this value column agrees in the prior and incoming rows, then retain it.
    AssertEq { column: MergeValueColumn },
    /// Union this value column's prior and incoming ids and return the native representative.
    UnionId { column: MergeValueColumn },
    /// Invoke an external primitive on the evaluated arguments.
    Primitive {
        function: ExternalFunctionId,
        arguments: Vec<MergeExpr>,
    },
    /// Look up or construct a single-output table-backed function call.
    ///
    /// On a miss, the target's configured default supplies and inserts an output; a target with
    /// [`crate::DefaultVal::Fail`] fails the merge.
    Function {
        function: FunctionId,
        /// The target function's key columns, in schema order. The target must have one output.
        arguments: Vec<MergeExpr>,
    },
    /// Read one value column from the prior or incoming row.
    Input {
        side: MergeInputSide,
        column: MergeValueColumn,
    },
    /// Read the value produced by a preceding merge-local `let` action.
    Binding(MergeBindingId),
    /// Produce a constant value.
    Const(Value),
}

/// A side effect performed by a [`MergeProgram`] before its results are evaluated.
pub enum MergeAction {
    /// Stage a complete logical row into a table, respecting that table's merge.
    Set {
        function: FunctionId,
        /// Every key followed by every value column, each in the target function's schema order.
        arguments: Vec<MergeExpr>,
    },
    /// Evaluate `value` once and bind it for later actions and results.
    Let {
        binding: MergeBindingId,
        value: MergeExpr,
    },
    /// Stage a union of two eclass values.
    Union { left: MergeExpr, right: MergeExpr },
}

impl MergeProgram {
    /// Classify the scalar, action-free result shape that can be named by one
    /// post-merge table lookup. The only table-backed result admitted here is a
    /// binary fresh-id constructor over value column zero in exact
    /// prior/incoming order. Replay registration separately validates that
    /// constructor's logical signature.
    pub(super) fn scalar_replay_result_shape(&self, egraph: &EGraph) -> MergeResultShape {
        if !self.actions.is_empty() || self.results.len() != 1 {
            return MergeResultShape::Unsupported;
        }
        match &self.results[0] {
            MergeExpr::Function {
                function,
                arguments,
            } if egraph.funcs.get(*function).is_some_and(|info| {
                matches!(info.default_val, DefaultVal::FreshId)
                    && info.n_keys == 2
                    && info.schema.len() - info.n_keys == 1
                    && matches!(arguments.as_slice(),
                        [MergeExpr::Input { side: MergeInputSide::Prior, column: prior },
                         MergeExpr::Input { side: MergeInputSide::Incoming, column: incoming }]
                            if prior.index() == 0 && incoming.index() == 0)
            }) =>
            {
                MergeResultShape::DirectConstructor(*function)
            }
            result if !result.requires_table_read_or_binding() => MergeResultShape::NoTableRead,
            _ => MergeResultShape::Unsupported,
        }
    }
}

impl MergeExpr {
    fn requires_table_read_or_binding(&self) -> bool {
        match self {
            Self::Function { .. } | Self::Binding(..) => true,
            Self::Primitive { arguments, .. } => {
                arguments.iter().any(Self::requires_table_read_or_binding)
            }
            Self::AssertEq { .. } | Self::UnionId { .. } | Self::Input { .. } | Self::Const(..) => {
                false
            }
        }
    }

    fn fill_deps(
        &self,
        egraph: &EGraph,
        read_deps: &mut IndexSet<TableId>,
        write_deps: &mut IndexSet<TableId>,
    ) {
        match self {
            MergeExpr::Primitive { arguments, .. } => {
                arguments
                    .iter()
                    .for_each(|arg| arg.fill_deps(egraph, read_deps, write_deps));
                write_deps.insert(egraph.uf_table);
            }
            MergeExpr::Function {
                function,
                arguments,
            } => {
                read_deps.insert(egraph.funcs[*function].table);
                write_deps.insert(egraph.funcs[*function].table);
                arguments
                    .iter()
                    .for_each(|arg| arg.fill_deps(egraph, read_deps, write_deps));
            }
            MergeExpr::UnionId { .. } => {
                write_deps.insert(egraph.uf_table);
            }
            MergeExpr::AssertEq { .. }
            | MergeExpr::Input { .. }
            | MergeExpr::Binding(..)
            | MergeExpr::Const(..) => {}
        }
    }

    /// Validate value-column and merge-local binding references.
    fn check_references(&self, n_vals: usize, available_bindings: usize, name: &str) {
        let check = |i: usize, kind: &str| {
            assert!(
                i < n_vals,
                "merge for `{name}` references {kind}({i}), but the function has only {n_vals} value column(s)"
            );
        };
        match self {
            MergeExpr::AssertEq { column }
            | MergeExpr::UnionId { column }
            | MergeExpr::Input { column, .. } => check(column.index(), "value column"),
            MergeExpr::Primitive { arguments, .. } | MergeExpr::Function { arguments, .. } => {
                arguments.iter().for_each(|argument| {
                    argument.check_references(n_vals, available_bindings, name)
                })
            }
            MergeExpr::Binding(binding) => assert!(
                binding.index() < available_bindings,
                "merge for `{name}` references let binding {} before it is bound",
                binding.index()
            ),
            MergeExpr::Const(..) => {}
        }
    }

    fn resolve(&self, function_name: &str, egraph: &mut EGraph) -> CompiledMergeExpr {
        match self {
            MergeExpr::Const(value) => CompiledMergeExpr::Const(*value),
            MergeExpr::Input { side, column } => CompiledMergeExpr::Input {
                side: *side,
                column: *column,
            },
            MergeExpr::Binding(binding) => CompiledMergeExpr::Binding(*binding),
            MergeExpr::AssertEq { column } => CompiledMergeExpr::AssertEq {
                column: *column,
                panic: egraph.new_panic(format!(
                    "Illegal merge attempted for function {function_name}"
                )),
            },
            MergeExpr::UnionId { column } => CompiledMergeExpr::UnionId {
                column: *column,
                uf_table: egraph.uf_table,
            },
            MergeExpr::Primitive {
                function,
                arguments,
            } => CompiledMergeExpr::Primitive {
                prim: *function,
                args: arguments
                    .iter()
                    .map(|argument| argument.resolve(function_name, egraph))
                    .collect(),
                panic: egraph.new_panic(format!(
                    "Merge function for {function_name} primitive call failed"
                )),
            },
            MergeExpr::Function {
                function,
                arguments,
            } => {
                let function_info = &egraph.funcs[*function];
                let target_n_vals = function_info.schema.len() - function_info.n_keys;
                assert_eq!(
                    target_n_vals, 1,
                    "Merge function for {function_name} calls {}, which has {target_n_vals} output columns; merge function calls require exactly one",
                    function_info.name
                );
                assert_eq!(
                    arguments.len(),
                    function_info.n_keys,
                    "Merge function for {function_name} calls {} with {} key arguments, expected {}",
                    function_info.name,
                    arguments.len(),
                    function_info.n_keys
                );
                CompiledMergeExpr::Function {
                    func: TableAction::new(egraph, *function),
                    panic: egraph.new_panic(format!(
                        "Lookup on {} failed in the merge function for {function_name}",
                        function_info.name
                    )),
                    args: arguments
                        .iter()
                        .map(|argument| argument.resolve(function_name, egraph))
                        .collect(),
                }
            }
        }
    }
}

impl MergeProgram {
    pub(super) fn fill_deps(
        &self,
        egraph: &EGraph,
        read_deps: &mut IndexSet<TableId>,
        write_deps: &mut IndexSet<TableId>,
    ) {
        self.actions
            .iter()
            .for_each(|action| action.fill_deps(egraph, read_deps, write_deps));
        self.results
            .iter()
            .for_each(|result| result.fill_deps(egraph, read_deps, write_deps));
    }

    pub(super) fn check_references(&self, n_vals: usize, name: &str) {
        assert_eq!(
            self.results.len(),
            n_vals,
            "merge for {name} must have one result per value column"
        );
        let mut available_bindings = 0;
        for action in &self.actions {
            action.check_references(n_vals, &mut available_bindings, name);
        }
        self.results
            .iter()
            .for_each(|result| result.check_references(n_vals, available_bindings, name));
    }

    pub(super) fn to_callback(
        &self,
        schema_math: SchemaMath,
        function_name: &str,
        merge_table: TableId,
        egraph: &mut EGraph,
    ) -> Box<core_relations::MergeCallback> {
        let actions: Vec<CompiledMergeAction> = self
            .actions
            .iter()
            .map(|action| action.resolve(function_name, egraph))
            .collect();
        let results: Vec<CompiledMergeExpr> = self
            .results
            .iter()
            .map(|result| result.resolve(function_name, egraph))
            .collect();
        assert_eq!(
            results.len(),
            schema_math.n_vals(),
            "merge for {function_name} must have one entry per value column"
        );

        Box::new(move |state, cur, new, out| {
            let values = schema_math.n_keys..schema_math.n_keys + schema_math.n_vals();
            let values_unchanged = cur[values.clone()] == new[values];

            // Identity/payload columns: when a collision leaves every identity value column
            // unchanged it is not a real value conflict, so keep the existing value columns (and
            // skip the actions) instead of running the merge — which would, e.g., stage a spurious
            // union. A subsume-flag change is still applied below, so this stays correct for
            // subsumable functions. Inert unless the function declares payload columns.
            let identity_unchanged = match schema_math.n_identity_vals {
                Some(k) => {
                    let id_lo = schema_math.n_keys;
                    cur[id_lo..id_lo + k] == new[id_lo..id_lo + k]
                }
                None => false,
            };
            let skip_merge = values_unchanged || identity_unchanged;

            let timestamp = new[schema_math.ts_col()];

            // Environment for merge-local `let` bindings. Empty (no allocation) unless used.
            let mut env = SmallVec::<[Value; 4]>::new();

            // Run the program's side effects once, before computing any result column.
            if !skip_merge {
                for action in &actions {
                    if action
                        .run(
                            state,
                            cur,
                            new,
                            schema_math.n_keys,
                            timestamp,
                            &mut env,
                            merge_table,
                        )
                        .is_none()
                    {
                        return false;
                    }
                }
            }

            let mut changed = false;

            // Every result reads the same complete prior/incoming rows and post-action bindings.
            let mut merged_vals = SmallVec::<[Value; 4]>::new();
            for (i, result) in results.iter().enumerate() {
                let out_val = if skip_merge {
                    Some(cur[schema_math.val_col(i)])
                } else {
                    result.run(
                        state,
                        cur,
                        new,
                        schema_math.n_keys,
                        timestamp,
                        &env,
                        merge_table,
                    )
                };
                let Some(out_val) = out_val else {
                    return false;
                };
                changed |= cur[schema_math.val_col(i)] != out_val;
                merged_vals.push(out_val);
            }

            let subsume = schema_math.subsume.then(|| {
                let cur = cur[schema_math.subsume_col()];
                let new = new[schema_math.subsume_col()];
                let out = combine_subsumed(cur, new);
                changed |= cur != out;
                out
            });
            if changed {
                out.extend_from_slice(new);
                for (i, val) in merged_vals.iter().enumerate() {
                    out[schema_math.val_col(i)] = *val;
                }
                schema_math.write_table_row(
                    out,
                    RowVals {
                        timestamp,
                        subsume,
                        ret_val: None,
                    },
                );
            }

            changed
        })
    }
}

/// An owned, executable merge expression compiled from [`MergeExpr`].
///
/// Runtime IDs and table actions replace frontend references so the expression can move into the
/// merge callback without borrowing the [`EGraph`].
enum CompiledMergeExpr {
    Const(Value),
    Input {
        side: MergeInputSide,
        column: MergeValueColumn,
    },
    Binding(MergeBindingId),
    AssertEq {
        column: MergeValueColumn,
        panic: ExternalFunctionId,
    },
    UnionId {
        column: MergeValueColumn,
        uf_table: TableId,
    },
    Primitive {
        prim: ExternalFunctionId,
        args: Vec<CompiledMergeExpr>,
        panic: ExternalFunctionId,
    },
    Function {
        func: TableAction,
        args: Vec<CompiledMergeExpr>,
        panic: ExternalFunctionId,
    },
}

/// A resolved side effect run before a merge program's results are evaluated.
enum CompiledMergeAction {
    /// `(set (f keys...) vals...)`: stage the full row `args` into `table`, respecting its merge.
    Set {
        table: TableAction,
        args: Vec<CompiledMergeExpr>,
    },
    /// `(let x <value>)`: evaluate `value` and push it onto the environment (its slot equals the
    /// current environment length, since `let`s run in slot order).
    Let {
        binding: MergeBindingId,
        value: CompiledMergeExpr,
    },
    /// `(union a b)`: stage a union of the two eclasses into the union-find.
    Union {
        a: CompiledMergeExpr,
        b: CompiledMergeExpr,
        uf_table: TableId,
    },
}

impl MergeAction {
    fn fill_deps(
        &self,
        egraph: &EGraph,
        read_deps: &mut IndexSet<TableId>,
        write_deps: &mut IndexSet<TableId>,
    ) {
        match self {
            MergeAction::Set {
                function,
                arguments,
            } => {
                write_deps.insert(egraph.funcs[*function].table);
                arguments
                    .iter()
                    .for_each(|arg| arg.fill_deps(egraph, read_deps, write_deps));
            }
            MergeAction::Let { value, .. } => value.fill_deps(egraph, read_deps, write_deps),
            MergeAction::Union { left, right } => {
                left.fill_deps(egraph, read_deps, write_deps);
                right.fill_deps(egraph, read_deps, write_deps);
                write_deps.insert(egraph.uf_table);
            }
        }
    }

    fn check_references(&self, n_vals: usize, available_bindings: &mut usize, name: &str) {
        match self {
            MergeAction::Set { arguments, .. } => arguments
                .iter()
                .for_each(|argument| argument.check_references(n_vals, *available_bindings, name)),
            MergeAction::Let { binding, value } => {
                assert_eq!(
                    binding.index(),
                    *available_bindings,
                    "merge for `{name}` declares let binding {}, expected {}",
                    binding.index(),
                    *available_bindings
                );
                value.check_references(n_vals, *available_bindings, name);
                *available_bindings += 1;
            }
            MergeAction::Union { left, right } => {
                left.check_references(n_vals, *available_bindings, name);
                right.check_references(n_vals, *available_bindings, name);
            }
        }
    }

    fn resolve(&self, function_name: &str, egraph: &mut EGraph) -> CompiledMergeAction {
        match self {
            MergeAction::Set {
                function,
                arguments,
            } => CompiledMergeAction::Set {
                table: TableAction::new(egraph, *function),
                args: arguments
                    .iter()
                    .map(|arg| arg.resolve(function_name, egraph))
                    .collect(),
            },
            MergeAction::Let { binding, value } => CompiledMergeAction::Let {
                binding: *binding,
                value: value.resolve(function_name, egraph),
            },
            MergeAction::Union { left, right } => CompiledMergeAction::Union {
                a: left.resolve(function_name, egraph),
                b: right.resolve(function_name, egraph),
                uf_table: egraph.uf_table,
            },
        }
    }
}

impl CompiledMergeAction {
    #[allow(clippy::too_many_arguments)]
    fn run(
        &self,
        state: &mut ExecutionState,
        cur: &[Value],
        new: &[Value],
        n_keys: usize,
        ts: Value,
        env: &mut SmallVec<[Value; 4]>,
        merge_table: TableId,
    ) -> Option<()> {
        match self {
            CompiledMergeAction::Set { table, args } => {
                // `insert` respects the target table's own merge.
                let row = args
                    .iter()
                    .map(|arg| arg.run(state, cur, new, n_keys, ts, env, merge_table))
                    .collect::<Option<Vec<_>>>()?;
                table.insert(state, row.into_iter());
            }
            CompiledMergeAction::Let { binding, value } => {
                let v = value.run(state, cur, new, n_keys, ts, env, merge_table)?;
                debug_assert_eq!(binding.index(), env.len());
                env.push(v);
            }
            CompiledMergeAction::Union { a, b, uf_table } => {
                let av = a.run(state, cur, new, n_keys, ts, env, merge_table)?;
                let bv = b.run(state, cur, new, n_keys, ts, env, merge_table)?;
                if av != bv {
                    assert!(
                        !state.trace_enabled(),
                        "trace capture does not support union effects inside merge blocks"
                    );
                    state.stage_insert(*uf_table, &[av, bv, ts]);
                }
            }
        }
        Some(())
    }
}

impl CompiledMergeExpr {
    /// Compute an expression, returning `None` after reporting a merge failure.
    ///
    /// `cur` and `new` are the full conflicting rows. `n_keys` is the number of key columns, so
    /// value column `i` lives at `cur[n_keys + i]`. Inputs carry explicit columns.
    #[allow(clippy::too_many_arguments)]
    fn run(
        &self,
        state: &mut ExecutionState,
        cur: &[Value],
        new: &[Value],
        n_keys: usize,
        ts: Value,
        env: &[Value],
        merge_table: TableId,
    ) -> Option<Value> {
        match self {
            CompiledMergeExpr::Const(v) => Some(*v),
            CompiledMergeExpr::Input { side, column } => match side {
                MergeInputSide::Prior => Some(cur[n_keys + column.index()]),
                MergeInputSide::Incoming => Some(new[n_keys + column.index()]),
            },
            CompiledMergeExpr::Binding(binding) => Some(env[binding.index()]),
            CompiledMergeExpr::AssertEq { column, panic } => {
                let index = n_keys + column.index();
                let (prior, incoming) = (cur[index], new[index]);
                if prior != incoming {
                    let res = state.call_external_func(*panic, &[]);
                    assert_eq!(res, None);
                    return None;
                }
                Some(prior)
            }
            CompiledMergeExpr::UnionId { column, uf_table } => {
                let physical_column = n_keys + column.index();
                let (prior, incoming) = (cur[physical_column], new[physical_column]);
                if prior != incoming {
                    if state.trace_enabled() {
                        let sort = state
                            .replay_sort(merge_table, ColumnId::from_usize(physical_column))
                            .expect(
                                "capture-enabled merge is missing its logical replay-sort layout",
                            );
                        state.stage_merge_union_with_replay(
                            *uf_table,
                            merge_table,
                            ColumnId::from_usize(physical_column),
                            prior,
                            incoming,
                            ts,
                            sort,
                        );
                    } else {
                        state.stage_insert(*uf_table, &[prior, incoming, ts]);
                    }
                    // We pick the minimum when unioning. This matches the original egglog
                    // behavior. THIS MUST MATCH THE UNION-FIND IMPLEMENTATION!
                    Some(std::cmp::min(prior, incoming))
                } else {
                    Some(prior)
                }
            }
            CompiledMergeExpr::Primitive { prim, args, panic } => {
                let args = args
                    .iter()
                    .map(|arg| arg.run(state, cur, new, n_keys, ts, env, merge_table))
                    .collect::<Option<Vec<_>>>()?;

                match state.call_external_func(*prim, &args) {
                    Some(result) => Some(result),
                    None => {
                        let res = state.call_external_func(*panic, &[]);
                        assert_eq!(res, None);
                        None
                    }
                }
            }
            CompiledMergeExpr::Function { func, args, panic } => {
                let args = args
                    .iter()
                    .map(|arg| arg.run(state, cur, new, n_keys, ts, env, merge_table))
                    .collect::<Option<Vec<_>>>()?;

                // Respect the target's configured default on a miss: insert its fresh/constant
                // output when present, or report merge failure for `DefaultVal::Fail`.
                let result = if state.trace_enabled() && func.kind() == TableKind::Constructor {
                    let input_column = self.constructor_input_column(n_keys).expect(
                        "capture-enabled constructor merge call is not a direct input call",
                    );
                    func.lookup_or_insert_merge_constructor(state, &args, merge_table, input_column)
                } else {
                    func.lookup_or_insert(state, &args)
                };
                match result {
                    Some(result) => Some(result),
                    None => {
                        let res = state.call_external_func(*panic, &[]);
                        assert_eq!(res, None);
                        None
                    }
                }
            }
        }
    }

    fn constructor_input_column(&self, n_keys: usize) -> Option<ColumnId> {
        let Self::Function { args, .. } = self else {
            return None;
        };
        let [
            Self::Input {
                side: MergeInputSide::Prior,
                column: prior,
            },
            Self::Input {
                side: MergeInputSide::Incoming,
                column: incoming,
            },
        ] = args.as_slice()
        else {
            return None;
        };
        (prior == incoming).then(|| ColumnId::from_usize(n_keys + prior.index()))
    }
}

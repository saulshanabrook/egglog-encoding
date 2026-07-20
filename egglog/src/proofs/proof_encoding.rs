#[doc = include_str!("proof_encoding.md")]
use crate::proofs::proof_checker::is_container_side_condition;
use crate::proofs::proof_encoding_helpers::{EncodingNames, Justification};
use crate::typechecking::FuncType;
use crate::*;

/// A materialized rebuild index on a view, keyed on a referenced term of one
/// eq-sort. The index table is `(ref, <all view key columns>) -> Unit`; for
/// every view row it holds one entry per key column of `sort_name` (with that
/// column's term as `ref`). `positions` are those key-column indices. The
/// single-rule rebuild driven by an `@UF_<sort>` delta looks up the rows
/// containing a term via `ref` (a key prefix).
#[derive(Clone)]
pub(crate) struct ViewIndex {
    pub name: String,
    pub sort_name: String,
    pub positions: Vec<usize>,
}

// TODO refactor so that encoding state is optional on the e-graph, ProofNames not optional on EncodingState. Then we don't have to clone proof names everywhere.
#[derive(Clone)]
pub(crate) struct EncodingState {
    pub uf_parent: HashMap<String, String>,
    /// Maps sort name -> proof function name (set from :internal-proof-func annotation).
    pub proof_func_parent: HashMap<String, String>,
    /// Maps container sort name -> the name of its registered container-rebuild
    /// primitive (`ContainerRebuild`). Cached so each container sort gets
    /// a single rebuild primitive shared across all functions using it.
    pub container_rebuild_name: HashMap<String, String>,
    /// Maps container sort name -> the name of its registered proof-producing
    /// container-rebuild primitive (`ContainerRebuildProof`). Proof mode only.
    pub container_rebuild_proof_name: HashMap<String, String>,
    /// Function name -> (hidden current-value function, input arity). The
    /// current function uses the original eager backend merge, so cleanup can
    /// discard stale proof-view candidates whenever the current value already
    /// has a proof witness.
    pub merge_current: HashMap<String, (String, usize)>,
    /// Function name -> materialized rebuild indexes on its view, one per
    /// distinct eq-sort among the view's key columns. The single-rule rebuild is
    /// driven by an `@UF` delta on a term joined against these indexes (see
    /// `proof_encoding.md`).
    pub view_index: HashMap<String, Vec<ViewIndex>>,
    pub term_header_added: bool,
    // TODO this is very ugly- we should separate out a typechecking struct
    // since we didn't need an entire e-graph
    // When Some term encoding is enabled.
    pub original_typechecking: Option<Box<EGraph>>,
    pub proofs_enabled: bool,
    pub proof_testing: bool,
    pub proof_names: EncodingNames,
    /// Test-only knob: annotate RHS-reading rules `:naive` (the safe
    /// whole-database baseline) instead of `:unsafe-seminaive`, so tests can
    /// assert the two produce the same database.
    pub force_proof_naive: bool,
}

impl EncodingState {
    pub(crate) fn new(symbol_gen: &mut SymbolGen) -> Self {
        Self {
            uf_parent: HashMap::default(),
            proof_func_parent: HashMap::default(),
            container_rebuild_name: HashMap::default(),
            container_rebuild_proof_name: HashMap::default(),
            merge_current: HashMap::default(),
            view_index: HashMap::default(),
            term_header_added: false,
            original_typechecking: None,
            proofs_enabled: false,
            proof_names: EncodingNames::new(symbol_gen),
            proof_testing: false,
            force_proof_naive: false,
        }
    }
}

/// Thin wrapper around an [`EGraph`] for the term encoding
pub(crate) struct ProofInstrumentor<'a> {
    pub(crate) egraph: &'a mut EGraph,
}

impl<'a> ProofInstrumentor<'a> {
    /// Make a term state and use it to instrument the code.
    pub(crate) fn add_term_encoding(
        egraph: &'a mut EGraph,
        program: Vec<ResolvedNCommand>,
    ) -> Result<Vec<Command>, Error> {
        Self { egraph }.add_term_encoding_helper(program)
    }

    pub(crate) fn lower_inputs(
        egraph: &EGraph,
        program: Vec<ResolvedNCommand>,
    ) -> Result<Vec<ResolvedNCommand>, Error> {
        let mut lowered = Vec::with_capacity(program.len());
        for command in program {
            if let ResolvedNCommand::Input { span, name, file } = &command {
                lowered.extend(
                    Self::input_actions(egraph, span, name, file)?
                        .into_iter()
                        .map(ResolvedNCommand::CoreAction),
                );
            } else {
                lowered.push(command);
            }
        }
        Ok(lowered)
    }

    /// Mark two things as equal, adding proof if proofs are enabled.
    pub(crate) fn union(
        &mut self,
        type_name: &str,
        lhs: &str,
        rhs: &str,
        justification: &Justification,
    ) -> String {
        let uf_name = self.uf_name(type_name);
        let smaller = format!("(ordering-min {lhs} {rhs})");
        let larger = format!("(ordering-max {lhs} {rhs})");
        // `@UF : (S) -> (S, {Unit|Proof})` is keyed by the larger endpoint; its
        // `:merge` resolves conflicting parents. The second column carries a proof
        // `larger = smaller` (`()` in term mode).
        let proof = if !self.egraph.proof_state.proofs_enabled {
            "()".to_string()
        } else {
            let to_ast_constructor = self
                .proof_names()
                .sort_to_ast_constructor
                .get(type_name)
                .unwrap();
            let rule_constructor = &self.proof_names().rule_constructor;
            let fiat_constructor = &self.proof_names().fiat_constructor;
            match justification {
                Justification::Rule(rule_name, proof_list) => format!(
                    "({rule_constructor} {rule_name} {proof_list} ({to_ast_constructor} {larger}) ({to_ast_constructor} {smaller}))"
                ),
                Justification::Fiat => format!(
                    "({fiat_constructor} ({to_ast_constructor} {larger}) ({to_ast_constructor} {smaller}))"
                ),
                Justification::Merge(_func_name, _proof1, _proof2) => panic!(
                    "Merge functions do not include union actions, so proof should not be by merge"
                ),
            }
        };
        format!("(set ({uf_name} {larger}) (values {smaller} {proof}))")
    }

    /// The parent table is the database representation of a union-find datastructure.
    /// When one term has two parents, those parents are unioned in the merge action.
    /// Also, we have a rule that maintains the invariant that each term points to its
    /// canonical representative.
    fn declare_sort(&mut self, sort_name: &str, is_container: bool) -> Vec<Command> {
        // Containers are canonicalized structurally, not unioned directly.
        // Proof mode still needs the container's reflexive proof table and AST wrapper.
        if is_container {
            if self.egraph.proof_state.proofs_enabled {
                let term_proof_name = self.term_proof_name(sort_name);
                let add_to_ast_code = self.add_to_ast(sort_name);
                let proof_type = self.proof_type_str().to_string();
                return self.parse_program(&format!(
                    "{add_to_ast_code}
                     (function {term_proof_name} ({sort_name}) {proof_type} :merge old :internal-hidden)"
                ));
            }
            return vec![];
        }
        self.declare_sort_eq(sort_name)
    }

    /// Declare a sort's union-find `@UF : (S) -> (S, {Unit|Proof})`, mapping each
    /// term to its parent plus a proof `key = parent` (`()` in term mode). Its
    /// `:merge` resolves conflicting parents (see `proof_encoding.md`). Also emits
    /// the `path_compress` rule and, in proof mode, the per-sort `term_proof`
    /// table and AST constructor.
    fn declare_sort_eq(&mut self, sort_name: &str) -> Vec<Command> {
        let proofs = self.proofs_enabled();
        let uf_name = self.uf_name(sort_name);
        let proof_type = self.proof_type_str().to_string();
        let fresh_name = self.egraph.parser.symbol_gen.fresh("uf_path_compress");
        let path_compress_ruleset_name = self.proof_names().path_compress_ruleset_name.clone();

        let a = self.egraph.parser.symbol_gen.fresh("uf_a");
        let b = self.egraph.parser.symbol_gen.fresh("uf_b");
        let c = self.egraph.parser.symbol_gen.fresh("uf_c");
        let pb = self.egraph.parser.symbol_gen.fresh("uf_pb");
        let pc = self.egraph.parser.symbol_gen.fresh("uf_pc");

        let proof_tables = if proofs {
            let term_proof_name = self.term_proof_name(sort_name);
            let add_to_ast_code = self.add_to_ast(sort_name);
            format!(
                "{add_to_ast_code}
                 (function {term_proof_name} ({sort_name}) {proof_type} :merge old :internal-hidden)"
            )
        } else {
            String::new()
        };
        // On a conflict, keep the smaller parent and union the displaced parent back
        // into `@UF`. In proof mode the proofs ride along: `hi_pf_`/`lo_pf_` prove
        // `key = larger parent` / `key = smaller parent`, so the displaced edge's
        // proof is `Trans (Sym hi_pf_) lo_pf_ : larger = smaller`.
        let uf_merge = if proofs {
            let trans = self.proof_names().eq_trans_constructor.clone();
            let sym = self.proof_names().eq_sym_constructor.clone();
            format!(
                "((let hi_pf_ (proof-of-max old0 old1 new0 new1))
                  (let lo_pf_ (proof-of-min old0 old1 new0 new1))
                  (set ({uf_name} (ordering-max old0 new0))
                       (values (ordering-min old0 new0) ({trans} ({sym} hi_pf_) lo_pf_)))
                  (values (ordering-min old0 new0) lo_pf_))"
            )
        } else {
            format!(
                "((set ({uf_name} (ordering-max old0 new0)) (values (ordering-min old0 new0) ()))
                  (values (ordering-min old0 new0) ()))"
            )
        };
        // path compression: a->b (pb: a=b), b->c (pc: b=c)  =>  a->c (Trans pb pc: a=c)
        let compressed_proof = if proofs {
            let trans = self.proof_names().eq_trans_constructor.clone();
            format!("({trans} {pb} {pc})")
        } else {
            "()".to_string()
        };

        let code = format!(
            "{proof_tables}
             (function {uf_name} ({sort_name}) ({sort_name} {proof_type}) :merge {uf_merge} :unextractable :internal-hidden :internal-identity-vals 1)
             (rule ((= (values {b} {pb}) ({uf_name} {a}))
                    (= (values {c} {pc}) ({uf_name} {b}))
                    (!= {b} {c}))
                  ((set ({uf_name} {a}) (values {c} {compressed_proof})))
                   :ruleset {path_compress_ruleset_name}
                   :name \"{fresh_name}\")
                   "
        );

        self.parse_program(&code)
    }

    /// Rules that execute deletion and subsumption based on the tables requesting the deletion/subsumption.
    fn delete_and_subsume(&mut self, fdecl: &ResolvedFunctionDecl) -> String {
        let child_vars: Vec<String> = (0..fdecl.schema.input.len())
            .map(|i| format!("c{i}_"))
            .collect();
        let child_names = child_vars.join(" ");
        let to_delete_name = self.delete_name(&fdecl.name);
        let subsumed_name = self.subsumed_name(&fdecl.name);
        let view_name = self.view_name(&fdecl.name);
        let delete_subsume_ruleset = self.proof_names().delete_subsume_ruleset_name.clone();
        let fresh_name = self.egraph.parser.symbol_gen.fresh("delete_rule");

        // A constructor's FD tuple view is keyed by children only, so match its value
        // tuple to delete/subsume by key (the bridge re-reads every value column when
        // subsuming a tuple-output view). Subsumption keeps the row, so it leaves the
        // rebuild indexes untouched; deletion drops the row's index entries with it.
        if fdecl.subtype == FunctionSubtype::Constructor {
            let e = self.fresh_var();
            let pf = self.fresh_var();
            let e2 = self.fresh_var();
            let pf2 = self.fresh_var();
            let index_deletes = self.view_index_deletes(&fdecl.name, &child_vars);
            // Deletion removes the row by key; subsumption marks it subsumed (kept for size/proofs
            // but excluded from matching).
            return format!(
                "(rule (({to_delete_name} {child_names})
                        (= (values {e} {pf}) ({view_name} {child_names})))
                       ((delete ({view_name} {child_names}))
                        {index_deletes}
                        (delete ({to_delete_name} {child_names})))
                        :ruleset {delete_subsume_ruleset}
                        :name \"{fresh_name}\")
                 (rule (({subsumed_name} {child_names})
                        (= (values {e2} {pf2}) ({view_name} {child_names})))
                       ((subsume ({view_name} {child_names})))
                        :ruleset {delete_subsume_ruleset}
                        :name \"{fresh_name}_subsume\")"
            );
        }

        // Custom function views are keyed by every column, so the deleted row's key is
        // the children plus the output.
        let mut all_keys = child_vars.clone();
        all_keys.push("out".to_string());
        let index_deletes = self.view_index_deletes(&fdecl.name, &all_keys);
        format!(
            "(rule (({to_delete_name} {child_names})
                    ({view_name} {child_names} out))
                   ((delete ({view_name} {child_names} out))
                    {index_deletes}
                    (delete ({to_delete_name} {child_names})))
                    :ruleset {delete_subsume_ruleset}
                    :name \"{fresh_name}\")
             (rule (({subsumed_name} {child_names})
                    ({view_name} {child_names} out))
                   ((subsume ({view_name} {child_names} out)))
                    :ruleset {delete_subsume_ruleset}
                    :name \"{fresh_name}_subsume\")"
        )
    }

    /// Generate rules that run a merge function for a custom function.
    /// One rule runs the merge function when two different values are present for the same children.
    /// Another rule cleans up old values, necessary because the newly merged value may be equal to one of the old values.
    fn handle_merge_fn(
        &mut self,
        fdecl: &ResolvedFunctionDecl,
        child_names: &[String],
        child_names_str: &str,
        _view_name: &str,
        rebuilding_ruleset: &str,
    ) -> String {
        let name = &fdecl.name;

        let merge_fn = &fdecl
            .merge
            .as_ref()
            .unwrap_or_else(|| panic!("Proofs don't support :no-merge"));

        let current_name = self
            .egraph
            .parser
            .symbol_gen
            .fresh(&format!("{name}Current"));
        self.egraph
            .proof_state
            .merge_current
            .insert(name.clone(), (current_name.clone(), child_names.len()));

        let fresh_name = self.egraph.parser.symbol_gen.fresh("merge_rule");
        let cleanup_name = self.egraph.parser.symbol_gen.fresh("merge_cleanup");
        let current_cleanup_name = self.egraph.parser.symbol_gen.fresh("merge_current_cleanup");

        let p1_fresh = self.egraph.parser.symbol_gen.fresh("p1");
        let p2_fresh = self.egraph.parser.symbol_gen.fresh("p2");
        let view_name = self.view_name(&fdecl.name);
        let rebuilding_cleanup_ruleset = self.proof_names().rebuilding_cleanup_ruleset_name.clone();
        let input_sorts = ListDisplay(&fdecl.schema.input, " ");
        let proof_query = if self.egraph.proof_state.proofs_enabled {
            // View is a function with proof output; bind proof variables
            format!(
                "(= {p1_fresh} ({view_name} {child_names_str} old))
                     (= {p2_fresh} ({view_name} {child_names_str} new))
                    "
            )
        } else {
            // View is a function with Unit output; no need to bind the output
            "".to_string()
        };
        let proof_var = if self.egraph.proof_state.proofs_enabled {
            self.fresh_var()
        } else {
            "()".to_string()
        };
        let mut merge_fn_code = vec![];
        // Proof instrumentation tracks the merged *value*; a `:merge` action block's effects are
        // not proof-tracked (action-block merges under proofs are unsupported).
        let merge_fn_var = self.instrument_action_expr(
            &merge_fn.result,
            &mut merge_fn_code,
            &Justification::Merge(name.clone(), p1_fresh.clone(), p2_fresh.clone()),
        );
        let merge_fn_code_str = merge_fn_code.join("\n");
        let mut updated = child_names.to_vec();
        updated.push(merge_fn_var.clone());
        let term = format!("({name} {child_names_str} {merge_fn_var})");

        let rule_proof = if self.egraph.proof_state.proofs_enabled {
            let to_ast = self.fname_to_ast_name(name);
            let merge_fn_constructor = self.proof_names().merge_fn_constructor.clone();
            format!(
                "(let {proof_var}
                            ({merge_fn_constructor} \"{name}\"
                                  {p1_fresh}
                                  {p2_fresh}
                                  ({to_ast} {term})))"
            )
        } else {
            "".to_string()
        };
        let term_and_proof = self.update_view(name, &updated, &proof_var);
        let cleanup_constructor = self.egraph.parser.symbol_gen.fresh("mergecleanup");
        let fresh_sort = self.egraph.parser.symbol_gen.fresh("mergecleanupsort");
        let output_sort = fdecl.schema.output().clone();
        // Both cleanup rules delete the stale row keyed by `(children old)`, so
        // its rebuild-index entries are removed alongside it.
        let mut old_key = child_names.to_vec();
        old_key.push("old".to_string());
        let index_deletes_old = self.view_index_deletes(name, &old_key);

        // The first runs the merge function adding a new row.
        // The second deletes rows with old values for the old variable, while the third deletes rows with new values for the new variable.
        format!(
            "(function {current_name} ({input_sorts}) {output_sort}
                    :merge {merge_fn}
                    :unextractable
                    :internal-hidden)
                 (sort {fresh_sort})
                 (constructor {cleanup_constructor} ({output_sort} {output_sort}) {fresh_sort} :internal-hidden)
                 (rule (({view_name} {child_names_str} old)
                        ({view_name} {child_names_str} new)
                        (!= old new)
                        (= (ordering-max old new) new)
                        {proof_query})
                       (
                        {merge_fn_code_str}
                        {rule_proof}
                        {term_and_proof}
                        ({cleanup_constructor} {merge_fn_var} old)
                        ({cleanup_constructor} {merge_fn_var} new)
                       )
                        :ruleset {rebuilding_ruleset}
                        :name \"{fresh_name}\")
                 (rule (({cleanup_constructor} merged old)
                        ({view_name} {child_names_str} merged)
                        ({view_name} {child_names_str} old)
                        (!= merged old))
                       ((delete ({view_name} {child_names_str} old))
                        {index_deletes_old})
                        :ruleset {rebuilding_cleanup_ruleset}
                        :name \"{cleanup_name}\")
                 (rule ((= selected ({current_name} {child_names_str}))
                        ({view_name} {child_names_str} selected)
                        ({view_name} {child_names_str} old)
                        (!= selected old))
                       ((delete ({view_name} {child_names_str} old))
                        {index_deletes_old})
                        :ruleset {rebuilding_cleanup_ruleset}
                        :name \"{current_cleanup_name}\")
                ",
        )
    }

    /// Use native `:no-merge` for primitive outputs and compare UF leaders for eq-sort outputs.
    fn handle_no_merge_fn(
        &mut self,
        fdecl: &ResolvedFunctionDecl,
        child_names: &[String],
        child_names_str: &str,
        rebuilding_ruleset: &str,
    ) -> String {
        let name = &fdecl.name;
        let output_is_eq_sort = fdecl.resolved_schema.output().is_eq_sort();

        if !output_is_eq_sort {
            let input_sorts = ListDisplay(&fdecl.schema.input, " ");
            let output_sort = fdecl.schema.output();
            let current_name = self
                .egraph
                .parser
                .symbol_gen
                .fresh(&format!("{name}Current"));
            self.egraph
                .proof_state
                .merge_current
                .insert(name.clone(), (current_name.clone(), child_names.len()));
            return format!(
                "(function {current_name} ({input_sorts}) {output_sort}
                    :no-merge
                    :unextractable
                    :internal-hidden)"
            );
        }

        // Distinct encoded values can already belong to the same e-class. Wait
        // for their encoded UF leaders before deciding whether the conflict is real.
        let view_name = self.view_name(name);
        let fresh_name = self.egraph.parser.symbol_gen.fresh("no_merge_rule");
        let uf_name = self.uf_name(fdecl.resolved_schema.output().name());

        format!(
            "(rule (({view_name} {child_names_str} old)
                    ({view_name} {child_names_str} new)
                    (= (values old_leader_ old_proof_) ({uf_name} old))
                    (= (values new_leader_ new_proof_) ({uf_name} new))
                    (!= old_leader_ new_leader_)
                    (= (ordering-max old new) new))
                   ((panic \"Illegal merge attempted for function {name}\"))
                    :ruleset {rebuilding_ruleset}
                    :name \"{fresh_name}\")"
        )
    }

    /// Generate rules that handle merge functions.
    /// For custom functions, we generate rules that run the merge function.
    /// Constructors need no rule: congruence is resolved by their view's `:merge`.
    fn handle_merge_or_congruence(&mut self, fdecl: &ResolvedFunctionDecl) -> String {
        let child_names = fdecl
            .schema
            .input
            .iter()
            .enumerate()
            .map(|(i, _)| format!("c{i}_"))
            .collect::<Vec<_>>();
        let child_names_str = child_names.join(" ");
        let rebuilding_ruleset = self.proof_names().rebuilding_ruleset_name.clone();
        let view_name = self.view_name(&fdecl.name);
        if fdecl.subtype == FunctionSubtype::Custom {
            if fdecl.merge.is_some() {
                self.handle_merge_fn(
                    fdecl,
                    &child_names,
                    &child_names_str,
                    &view_name,
                    &rebuilding_ruleset,
                )
            } else {
                self.handle_no_merge_fn(fdecl, &child_names, &child_names_str, &rebuilding_ruleset)
            }
        } else {
            // Congruence is resolved by the constructor view's `:merge`; no rule needed.
            String::new()
        }
    }

    /// Declare a materialized rebuild index for each non-first eq-sort key column
    /// of a view, register it in [`EncodingState::view_index`], and return the
    /// declarations. Each index `(col_i, other key columns…) -> carrier` mirrors
    /// the view keyed on `col_i` first, so the rebuild query looks up the rows
    /// containing a term in that column by key instead of scanning the view (see
    /// `proof_encoding.md`). It is maintained by [`Self::view_index_inserts`] /
    /// [`Self::view_index_deletes`] wherever the view is written or deleted.
    ///
    /// Must run before any view write for this function is instrumented (i.e.
    /// before the merge/congruence handling below), so the metadata is present.
    fn declare_view_indexes(&mut self, fdecl: &ResolvedFunctionDecl) -> String {
        let types = fdecl.resolved_schema.view_types();
        let n_keys = Self::view_n_keys(fdecl, types.len());
        // The index tables' trailing columns are all the view's key columns, in
        // order; the leading column is the referenced term. Group the eq-sort key
        // columns by sort — one index table each.
        let key_sorts = types[..n_keys]
            .iter()
            .map(|t| t.name().to_string())
            .collect::<Vec<_>>()
            .join(" ");
        let mut by_sort: Vec<(String, Vec<usize>)> = Vec::new();
        for i in Self::view_index_positions(&types, n_keys) {
            let sort = types[i].name().to_string();
            match by_sort.iter_mut().find(|(s, _)| *s == sort) {
                Some((_, positions)) => positions.push(i),
                None => by_sort.push((sort, vec![i])),
            }
        }
        let mut decls = String::new();
        let mut entries = Vec::new();
        for (sort_name, positions) in by_sort {
            let index_name = self
                .egraph
                .parser
                .symbol_gen
                .fresh(&format!("{}Index_{sort_name}", fdecl.name));
            decls.push_str(&format!(
                "(function {index_name} ({sort_name} {key_sorts}) Unit :merge old :internal-hidden :unextractable)\n"
            ));
            entries.push(ViewIndex {
                name: index_name,
                sort_name,
                positions,
            });
        }
        self.egraph
            .proof_state
            .view_index
            .insert(fdecl.name.clone(), entries);
        decls
    }

    /// Names of the eq-sort canonicalization primitives (registered in
    /// typechecking, see `proof_container_rebuild::register_uf_canon`).
    fn uf_canon_name(&mut self, sort: &str) -> String {
        crate::proofs::proof_container_rebuild::uf_canon_prim_name(&self.uf_name(sort))
    }
    fn uf_canon_proof_name(&mut self, sort: &str) -> String {
        crate::proofs::proof_container_rebuild::uf_canon_proof_prim_name(&self.uf_name(sort))
    }

    /// Number of key columns of a view: children only for a constructor's FD
    /// view, every column for a custom function's all-key view.
    fn view_n_keys(fdecl: &ResolvedFunctionDecl, n: usize) -> usize {
        if fdecl.subtype == FunctionSubtype::Constructor {
            n - 1
        } else {
            n
        }
    }

    /// Each function/constructor gets a term table and a view table.
    /// The term table stores underlying representative terms.
    /// The view table stores child terms and their eclass.
    /// The view table is mutated using delete, but we never delete from term tables.
    /// We re-use the original name of the function for the term table.
    fn term_and_view(&mut self, fdecl: &ResolvedFunctionDecl) -> Vec<Command> {
        let schema = &fdecl.schema;
        let out_type = schema.output().clone();

        let name = &fdecl.name;
        let view_name = self.view_name(&fdecl.name);
        let in_sorts = ListDisplay(schema.input.clone(), " ");
        let fresh_sort = self.egraph.parser.symbol_gen.fresh("view");
        // Declare and register rebuild indexes before instrumenting any view
        // write for this function (the merge/congruence handling below writes
        // the view and must emit index maintenance).
        let index_decls = self.declare_view_indexes(fdecl);
        let delete_rule = self.delete_and_subsume(fdecl);
        let to_delete_name = self.delete_name(&fdecl.name);
        let subsumed_name = self.subsumed_name(&fdecl.name);
        let term_sorts = format!(
            "{in_sorts} {}",
            if fdecl.subtype == FunctionSubtype::Constructor {
                "".to_string()
            } else {
                schema.output().to_string()
            }
        );
        let view_sorts = format!("{in_sorts} {out_type}");
        let proof_constructors = self.proof_functions(fdecl, &view_sorts);

        let view_sort = if fdecl.subtype == FunctionSubtype::Constructor {
            schema.output().clone()
        } else {
            fresh_sort.clone()
        };
        let to_ast_view_sort = self.add_to_ast(&view_sort);

        if self.egraph.proof_state.proofs_enabled {
            self.egraph
                .proof_state
                .proof_names
                .fn_to_term_sort
                .insert(name.clone(), view_sort.clone());
        }
        let merge_rule = self.handle_merge_or_congruence(fdecl);
        // the term table has child_sorts as inputs
        // the view table has child_sorts + the leader term for the eclass
        // Propagate cost, unextractable, hidden, and internal_let flags from the original function
        let mut term_flags = String::new();
        if let Some(cost) = fdecl.cost {
            term_flags.push_str(&format!(" :cost {cost}"));
        }
        // View is always a function (returning Proof or Unit), with :merge old
        let proof_type = self.proof_type_str().to_string();
        let mut view_flags = String::new();
        if fdecl.unextractable {
            view_flags.push_str(" :unextractable");
        }
        if fdecl.internal_hidden {
            view_flags.push_str(" :internal-hidden");
        }
        if fdecl.internal_let {
            view_flags.push_str(" :internal-let");
        }
        // A constructor's view is a functional-dependency tuple
        // `(children) -> (eclass, {Unit|Proof})` whose `:merge` resolves congruence:
        // it keeps the smaller eclass and unions the two eclasses in the sort's
        // `@UF`. Custom functions keep the `(children eclass) -> {Unit|Proof}` form
        // with a merge rule.
        let fd_view = fdecl.subtype == FunctionSubtype::Constructor;
        let view_decl = if fd_view {
            // Two rows conflicting on the same children are congruent: keep the
            // smaller eclass and union the two eclasses in the sort's `@UF`. In
            // proof mode the view proofs (`eclass = f(children)`) compose into the
            // union edge's proof `Trans hi_pf_ (Sym lo_pf_) : larger = smaller`.
            let congruence_merge = if self.proofs_enabled() {
                let uf_name = self.uf_name(schema.output());
                let trans = self.proof_names().eq_trans_constructor.clone();
                let sym = self.proof_names().eq_sym_constructor.clone();
                format!(
                    "((let hi_pf_ (proof-of-max old0 old1 new0 new1))
                      (let lo_pf_ (proof-of-min old0 old1 new0 new1))
                      (set ({uf_name} (ordering-max old0 new0))
                           (values (ordering-min old0 new0) ({trans} hi_pf_ ({sym} lo_pf_))))
                      (values (ordering-min old0 new0) lo_pf_))"
                )
            } else {
                let uf_name = self.uf_name(schema.output());
                format!(
                    "((set ({uf_name} (ordering-max old0 new0)) (values (ordering-min old0 new0) ()))
                      (values (ordering-min old0 new0) ()))"
                )
            };
            format!(
                "(function {view_name} ({in_sorts}) ({out_type} {proof_type}) :merge {congruence_merge} :internal-term-constructor {name}{view_flags} :internal-identity-vals 1)"
            )
        } else {
            format!(
                "(function {view_name} ({view_sorts}) {proof_type} :merge old :internal-term-constructor {name}{view_flags})"
            )
        };
        self.parse_program(&format!(
            "
            (sort {fresh_sort})
            {to_ast_view_sort}
            (constructor {name} ({term_sorts}) {view_sort}{term_flags} :internal-hidden :unextractable)
            {view_decl}
            (constructor {to_delete_name} ({in_sorts}) {fresh_sort} :internal-hidden)
            (constructor {subsumed_name} ({in_sorts}) {fresh_sort} :internal-hidden)
            {index_decls}
            {proof_constructors}
            {merge_rule}
            {delete_rule}",
        ))
    }

    fn proof_functions(&mut self, _fdecl: &ResolvedFunctionDecl, _view_sorts: &str) -> String {
        // ViewProof is now merged into the view table as its output column
        "".to_string()
    }

    /// Rebuild rules that keep a view canonical. Eq-sort key columns are
    /// canonicalized by a single rule per distinct child eq-sort, driven by an
    /// `@UF` delta joined against that sort's term→row index: the rule looks up
    /// the referencing rows by key and re-canonicalizes every eq-sort key column
    /// in its action with the `uf_canon` primitive (leader-or-self), so it
    /// replaces the old per-column fan-out. Container key columns keep a
    /// per-column `:naive` rule (their rebuild primitive reads `@UF` tables the
    /// rule doesn't join on, and a container term has no `@UF` delta to drive a
    /// seminaive rule). A constructor's FD view additionally gets one rule for
    /// its eclass value. In proof mode each rule composes the updated view proof.
    fn rebuilding_rules(&mut self, fdecl: &ResolvedFunctionDecl) -> Vec<Command> {
        let fd = fdecl.subtype == FunctionSubtype::Constructor;
        let types = fdecl.resolved_schema.view_types();
        let n = types.len();
        let n_keys = Self::view_n_keys(fdecl, n);
        let child = |i: usize| format!("c{i}_");
        let key_vars: Vec<String> = (0..n_keys).map(child).collect();

        let mut rules = String::new();
        // Container key columns: per-column `:naive` re-key (see doc above).
        for (i, ty) in types[..n_keys].iter().enumerate() {
            if ty.is_eq_container_sort() {
                rules.push_str(&self.container_rebuild_rule(fdecl, &key_vars, i, ty, fd));
            }
        }
        // Eq-sort key columns: one recanon rule per distinct child eq-sort.
        let indexes = self
            .egraph
            .proof_state
            .view_index
            .get(&fdecl.name)
            .cloned()
            .unwrap_or_default();
        for vi in &indexes {
            rules.push_str(&self.eq_sort_rebuild_rule(fdecl, &key_vars, &types, vi, fd));
        }
        // FD views: one rule for the eclass value (same key, `set` only; the view
        // merge keeps the min).
        if fd {
            rules.push_str(&self.fd_eclass_rebuild_rule(fdecl, &key_vars, &types));
        }
        self.parse_program(&rules)
    }

    /// The `:naive` per-column rebuild for a container key column `i`: rebuild
    /// the container with its primitive and re-key the row (`set` new, `delete`
    /// old), maintaining the row's index entries alongside.
    fn container_rebuild_rule(
        &mut self,
        fdecl: &ResolvedFunctionDecl,
        key_vars: &[String],
        i: usize,
        ty: &ArcSort,
        fd: bool,
    ) -> String {
        let proofs = self.proofs_enabled();
        let view_name = self.view_name(&fdecl.name);
        let keys_str = format!("{}", ListDisplay(key_vars, " "));
        let rebuilding_ruleset = self.proof_names().rebuilding_ruleset_name.clone();
        let index_deletes_key = self.view_index_deletes(&fdecl.name, key_vars);
        let ci = &key_vars[i];
        let canon = format!("c{i}_canon_");
        let (query_view, eclass_var, view_prf) = if fd {
            let (q, e, p) = self.query_fd_view(&fdecl.name, key_vars);
            (q, Some(e), p)
        } else {
            let (q, p) = self.query_view_and_get_proof(&fdecl.name, key_vars);
            (q, None, p)
        };
        let value_prim = self.ensure_container_rebuild(ty);
        let canon_fact = format!("(= {canon} ({value_prim} {ci}))");
        let (proof_lets, pf_arg, cproof_set) = if proofs {
            let congr = self.proof_names().congr_constructor.clone();
            let trans = self.proof_names().eq_trans_constructor.clone();
            let sym = self.proof_names().eq_sym_constructor.clone();
            let proof_prim = self.ensure_container_rebuild_proof(ty);
            let rebuild_pf = self.fresh_var();
            let new_pf = self.fresh_var();
            let cproof = self.term_proof_name(ty.name());
            (
                format!(
                    "(let {rebuild_pf} ({proof_prim} {ci}))
                     (let {new_pf} ({congr} {view_prf} {i} {rebuild_pf}))"
                ),
                new_pf,
                format!("(set ({cproof} {canon}) ({trans} ({sym} {rebuild_pf}) {rebuild_pf}))"),
            )
        } else {
            (String::new(), "()".to_string(), String::new())
        };
        let mut updated = key_vars.to_vec();
        updated[i] = canon.clone();
        let updated_view = match &eclass_var {
            Some(eclass) => self.update_fd_view(&fdecl.name, &updated, eclass, &pf_arg),
            None => self.update_view(&fdecl.name, &updated, &pf_arg),
        };
        let fresh_name = self.egraph.parser.symbol_gen.fresh("rebuild_rule");
        format!(
            "(rule ({query_view}
                    {canon_fact}
                    (!= {ci} {canon}))
                 (
                  {proof_lets}
                  {updated_view}
                  {cproof_set}
                  (delete ({view_name} {keys_str}))
                  {index_deletes_key}
                 )
                  :ruleset {rebuilding_ruleset} :naive :name \"{fresh_name}\" :internal-include-subsumed)\n"
        )
    }

    /// The single-rule rebuild for a view's eq-sort key columns of one sort
    /// (`vi`). Driven by an `@UF_<S>` delta on some referenced term joined
    /// against `vi`'s term→row index (a key lookup, not a scan), it
    /// re-canonicalizes *every* eq-sort key column of the row with `uf_canon` in
    /// its action, re-keys the row, and (proof mode) folds one `@Congr` per
    /// eq-sort column onto the view proof — reflexive (unchanged) columns drop in
    /// the simplifier. The `uf_canon` action reads `@UF` tables, so the rule is
    /// `:unsafe-seminaive`; the `@UF`/index body delta makes that read sound.
    fn eq_sort_rebuild_rule(
        &mut self,
        fdecl: &ResolvedFunctionDecl,
        key_vars: &[String],
        types: &[ArcSort],
        vi: &ViewIndex,
        fd: bool,
    ) -> String {
        let proofs = self.proofs_enabled();
        let view_name = self.view_name(&fdecl.name);
        let keys_str = format!("{}", ListDisplay(key_vars, " "));
        let rebuilding_ruleset = self.proof_names().rebuilding_ruleset_name.clone();
        let index_deletes_key = self.view_index_deletes(&fdecl.name, key_vars);
        let n_keys = key_vars.len();

        // Body: `@UF_<S>` delta on the referenced term, its term→row index entry,
        // and the view row (a key lookup for the eclass/proof).
        let follower = self.fresh_var();
        let leader = self.fresh_var();
        let leader_pf = self.fresh_var();
        let uf_name = self.uf_name(&vi.sort_name);
        let index_atom = format!("({} {follower} {keys_str})", vi.name);
        let uf_atom = format!("(= (values {leader} {leader_pf}) ({uf_name} {follower}))");
        // For FD views, read the eclass/proof value columns on the RHS (via the
        // per-column read primitives) instead of joining the tuple view in the
        // body — the body then only searches the `@UF` delta and the index.
        let (body_view, rhs_view_read, eclass_var, view_prf) = if fd {
            use crate::proofs::proof_container_rebuild::view_col_prim_name;
            let e = self.fresh_var();
            let col0 = view_col_prim_name(&view_name, 0);
            if proofs {
                let vp = self.fresh_var();
                let col1 = view_col_prim_name(&view_name, 1);
                let read =
                    format!("(let {e} ({col0} {keys_str}))\n(let {vp} ({col1} {keys_str}))\n");
                (String::new(), read, Some(e), vp)
            } else {
                (
                    String::new(),
                    format!("(let {e} ({col0} {keys_str}))\n"),
                    Some(e),
                    "()".to_string(),
                )
            }
        } else {
            let (q, p) = self.query_view_and_get_proof(&fdecl.name, key_vars);
            (q, String::new(), None, p)
        };

        // Action: canonicalize every eq-sort key column and fold its congruence
        // proof; non-eq-sort columns are carried over unchanged.
        let mut lets = String::new();
        let mut updated = key_vars.to_vec();
        let mut proof_acc = view_prf.clone();
        for j in 0..n_keys {
            if types[j].is_eq_container_sort() || !types[j].is_eq_sort() {
                continue;
            }
            let canon = format!("c{j}_canon_");
            let canon_prim = self.uf_canon_name(types[j].name());
            lets.push_str(&format!("(let {canon} ({canon_prim} {}))\n", key_vars[j]));
            if proofs {
                let proof_prim = self.uf_canon_proof_name(types[j].name());
                let congr = self.proof_names().congr_constructor.clone();
                let step_pf = self.fresh_var();
                let new_acc = self.fresh_var();
                lets.push_str(&format!(
                    "(let {step_pf} ({proof_prim} {}))\n(let {new_acc} ({congr} {proof_acc} {j} {step_pf}))\n",
                    key_vars[j]
                ));
                proof_acc = new_acc;
            }
            updated[j] = canon;
        }
        let pf_arg = if proofs { proof_acc } else { "()".to_string() };
        let updated_view = match &eclass_var {
            Some(eclass) => self.update_fd_view(&fdecl.name, &updated, eclass, &pf_arg),
            None => self.update_view(&fdecl.name, &updated, &pf_arg),
        };
        let fresh_name = self.egraph.parser.symbol_gen.fresh("rebuild_rule");
        format!(
            "(rule ({uf_atom}
                    (!= {follower} {leader})
                    {index_atom}
                    {body_view})
                 (
                  {rhs_view_read}
                  {lets}
                  {updated_view}
                  (delete ({view_name} {keys_str}))
                  {index_deletes_key}
                 )
                  :ruleset {rebuilding_ruleset} :unsafe-seminaive :name \"{fresh_name}\" :internal-include-subsumed)\n"
        )
    }

    /// A constructor FD view's eclass-value rebuild: when the eclass has a
    /// leader, re-`set` the same key with the leader (the view `:merge` keeps the
    /// min). Same key, so the index is untouched.
    fn fd_eclass_rebuild_rule(
        &mut self,
        fdecl: &ResolvedFunctionDecl,
        key_vars: &[String],
        types: &[ArcSort],
    ) -> String {
        let proofs = self.proofs_enabled();
        let rebuilding_ruleset = self.proof_names().rebuilding_ruleset_name.clone();
        let eclass_uf_name = self.uf_name(types[types.len() - 1].name());
        let (query_view, eclass_var, view_prf) = self.query_fd_view(&fdecl.name, key_vars);
        let eclass_canon = self.fresh_var();
        let uf_prf = self.fresh_var();
        let (proof_lets, pf_arg) = if proofs {
            let trans = self.proof_names().eq_trans_constructor.clone();
            let sym = self.proof_names().eq_sym_constructor.clone();
            let new_pf = self.fresh_var();
            (
                format!("(let {new_pf} ({trans} ({sym} {uf_prf}) {view_prf}))"),
                new_pf,
            )
        } else {
            (String::new(), "()".to_string())
        };
        let updated_view = self.update_fd_view(&fdecl.name, key_vars, &eclass_canon, &pf_arg);
        let fresh_name = self.egraph.parser.symbol_gen.fresh("rebuild_rule");
        format!(
            "(rule ({query_view}
                    (= (values {eclass_canon} {uf_prf}) ({eclass_uf_name} {eclass_var}))
                    (!= {eclass_var} {eclass_canon}))
                 (
                  {proof_lets}
                  {updated_view}
                 )
                  :ruleset {rebuilding_ruleset} :name \"{fresh_name}\" :internal-include-subsumed)\n"
        )
    }

    /// Rules that update the to_subsume tables when children change. One rule per
    /// eq-sort child (no proof needed for subsumed rows).
    fn rebuilding_subsumed_rules(&mut self, fdecl: &ResolvedFunctionDecl) -> Vec<Command> {
        let ResolvedCall::Func(FuncType { input, .. }) = &fdecl.resolved_schema else {
            panic!("cannot create subsumed rules for primitives")
        };

        // Check if there are any eq-sort columns at all; if not, no rebuild rule needed.
        if !input.iter().any(|t| t.is_eq_sort()) {
            return vec![];
        }

        self.rebuilding_subsumed_rules_fanout(fdecl, input.clone())
    }

    /// Subsumed-table rebuild: one rule per eq-sort column, mirroring
    /// [`Self::rebuilding_rules`] (the single-key `@UF` has no row for a
    /// canonical node, so a per-column lookup only fires when there is work).
    /// The `@UF` proof column is unused for subsumed rows.
    fn rebuilding_subsumed_rules_fanout(
        &mut self,
        fdecl: &ResolvedFunctionDecl,
        input: Vec<ArcSort>,
    ) -> Vec<Command> {
        let subsumed_name = self.subsumed_name(&fdecl.name);
        let child = |i: usize| format!("c{i}_");
        let children_vec: Vec<String> = (0..input.len()).map(child).collect();
        let children = format!("{}", ListDisplay(&children_vec, " "));
        let rebuilding_ruleset = self.proof_names().rebuilding_ruleset_name.clone();

        let mut rules = String::new();
        for (i, ty) in input.iter().enumerate() {
            if !ty.is_eq_sort() {
                continue;
            }
            let ci = child(i);
            let leader = format!("c{i}_leader_");
            let uf_name = self.uf_name(ty.name());
            let uf_lookup = {
                let proof_var = self.fresh_var();
                format!("(= (values {leader} {proof_var}) ({uf_name} {ci}))")
            };
            let mut updated = children_vec.clone();
            updated[i] = leader.clone();
            let updated_view = ListDisplay(&updated, " ");
            let fresh_name = self
                .egraph
                .parser
                .symbol_gen
                .fresh("rebuild_to_subsume_rule");
            rules.push_str(&format!(
                "(rule (({subsumed_name} {children})
                        {uf_lookup}
                        (!= {ci} {leader}))
                     (
                      ({subsumed_name} {updated_view})
                      (delete ({subsumed_name} {children}))
                     )
                      :ruleset {rebuilding_ruleset} :name \"{fresh_name}\" :internal-include-subsumed)\n"
            ));
        }
        self.parse_program(&rules)
    }

    /// Instrument fact replaces terms with looking up
    /// canonical versions in the view.
    /// It also needs to look up references to globals.
    /// Adds the instrumented fact to `res` and returns a proof that the fact matched.
    fn instrument_fact(
        &mut self,
        fact: &ResolvedFact,
        res: &mut Vec<String>,
        action_lookups: &mut Vec<String>,
    ) -> String {
        // A container side condition: a fact that builds a container with a
        // primitive (`(= xs (vec-of e))`, `(= (set-of a) (set-of b))`, or a bare
        // `(vec-of e)` guard). The container has no carryable proof — emit the
        // fact as-is so the e-graph computes it (its arguments are already
        // bound), with the `Eval` marker as its proof; the checker verifies it
        // by re-evaluation (see `check_side_condition`, which shares this gate).
        if is_container_side_condition(fact) {
            res.push(fact.to_string());
            return format!("({})", self.proof_names().eval_constructor);
        }
        match fact {
            // In proof normal form, this is the only way that function calls appear.
            ResolvedFact::Eq(
                _span,
                ResolvedExpr::Call(
                    _span2,
                    head @ ResolvedCall::Func(FuncType {
                        subtype: FunctionSubtype::Custom,
                        ..
                    }),
                    args,
                ),
                // TODO this could actually be arbitrary pretty easily, it's just nested functions that are hard.
                ResolvedExpr::Var(_span3, v),
            ) => {
                let mut new_args = vec![];
                let mut arg_proofs = vec![];
                for arg in args {
                    let (var, proof) = self.instrument_fact_expr(arg, res, action_lookups);
                    new_args.push(var);
                    arg_proofs.push(proof);
                }
                new_args.push(v.to_string());

                let view_name = self.view_name(head.name());
                let args_str = ListDisplay(new_args, " ");

                // View is always a function; query it and bind the output
                let proof_var = self.fresh_var();
                res.push(format!("(= {proof_var} ({view_name} {args_str}))"));

                if self.egraph.proof_state.proofs_enabled {
                    let mut proof = proof_var;
                    for (i, arg_proof) in arg_proofs.into_iter().enumerate() {
                        let congr = &self.proof_names().congr_constructor;
                        proof = format!(
                            "
                            ({congr} {proof} {i} {arg_proof})
                            "
                        );
                    }
                    proof
                } else {
                    "()".to_string()
                }
            }
            ResolvedFact::Eq(_span, left_expr, right_expr) => {
                let (v1, p1) = self.instrument_fact_expr(left_expr, res, action_lookups);
                let (v2, p2) = self.instrument_fact_expr(right_expr, res, action_lookups);
                res.push(format!("(= {v1} {v2})"));
                let sym = &self.proof_names().eq_sym_constructor;
                let trans = &self.proof_names().eq_trans_constructor;

                format!("({trans} ({sym} {p1}) {p2})",)
            }
            ResolvedFact::Fact(generic_expr) => {
                let (_, proof) = self.instrument_fact_expr(generic_expr, res, action_lookups);
                if self.proofs_enabled()
                    && matches!(
                        generic_expr,
                        ResolvedExpr::Call(_, ResolvedCall::Primitive(p), _)
                            if p.output().is_eq_container_sort()
                    )
                {
                    format!("({})", self.proof_names().eval_constructor)
                } else {
                    proof
                }
            }
        }
    }

    /// Instruments a fact expression to use the view tables.
    /// Assumes there are no function lookups in the term.
    /// Returns a variable representing the expression and a proof that the expression was matched.
    /// Proves a ground equality t1 = t2 where t1 is the eclass representative and t2 matches `expr` syntactically.
    fn instrument_fact_expr(
        &mut self,
        expr: &ResolvedExpr,
        res: &mut Vec<String>,
        action_lookups: &mut Vec<String>,
    ) -> (String, String) {
        match expr {
            ResolvedExpr::Lit(_, lit) => {
                let proof_code = if self.egraph.proof_state.proofs_enabled {
                    let fiat_constructor = &self.proof_names().fiat_constructor;
                    let lit_sort = literal_sort(lit);
                    let to_ast = self
                        .proof_names()
                        .sort_to_ast_constructor
                        .get(lit_sort.name())
                        .unwrap();
                    format!("({fiat_constructor} ({to_ast} {lit}) ({to_ast} {lit}))")
                } else {
                    "()".to_string()
                };

                (format!("{lit}"), proof_code)
            }
            ResolvedExpr::Var(_, resolved_var) => {
                let var = &resolved_var.name;
                (
                    resolved_var.name.clone(),
                    if !self.egraph.proof_state.proofs_enabled {
                        "()".to_string()
                    } else if resolved_var.sort.is_eq_sort()
                        || resolved_var.sort.is_eq_container_sort()
                    {
                        let term_proof_name = self.term_proof_name(resolved_var.sort.name());
                        let fresh_proof = self.fresh_var();
                        // Every eq-sort term has its term_proof set at
                        // constructor-creation time, so this proof is guaranteed
                        // present when the rule fires. Fetch it directly in the
                        // action (the rule is then `:unsafe-seminaive`, see
                        // instrument_rule) instead of as a body join — one fewer
                        // join per eq-sort body variable. Callers that don't
                        // build a proof (run :until, check) discard these.
                        action_lookups
                            .push(format!("(let {fresh_proof} ({term_proof_name} {var}))"));
                        fresh_proof
                    } else {
                        let fiat_constructor = &self.proof_names().fiat_constructor;
                        let lit_sort = resolved_var.sort.name();
                        let to_ast = self
                            .proof_names()
                            .sort_to_ast_constructor
                            .get(lit_sort)
                            .unwrap();
                        format!("({fiat_constructor} ({to_ast} {var}) ({to_ast} {var}))")
                    },
                )
            }
            ResolvedExpr::Call(_, resolved_call, args) => {
                let mut new_args = vec![];
                // Variables and constants don't need subproofs, but constructor calls do.
                let mut arg_proofs: Vec<Option<String>> = vec![];
                for arg in args {
                    if matches!(arg, ResolvedExpr::Var(_, _) | ResolvedExpr::Lit(_, _)) {
                        new_args.push(arg.to_string());
                        arg_proofs.push(None);
                    } else {
                        let (arg_str, proof) = self.instrument_fact_expr(arg, res, action_lookups);
                        new_args.push(arg_str);
                        arg_proofs.push(Some(proof));
                    }
                }
                match resolved_call {
                    ResolvedCall::Func(func_type) => {
                        assert!(
                            func_type.subtype == FunctionSubtype::Constructor,
                            "Only constructor function calls are allowed in fact expressions due to proof normal form. Got {func_type:?}",
                        );

                        let fv = self.fresh_var();
                        let view_name = self.view_name(&func_type.name);
                        let args_str = ListDisplay(new_args, " ");

                        let proof = {
                            let view_proof_var = self.fresh_var();
                            // A constructor view is the FD tuple
                            // `(children) -> (eclass, {Unit|Proof})`: bind the eclass (`fv`)
                            // and proof from the tuple.
                            res.push(format!(
                                "(= (values {fv} {view_proof_var}) ({view_name} {args_str}))"
                            ));
                            if self.proofs_enabled() {
                                let mut proof = view_proof_var;
                                for (i, arg_proof) in arg_proofs.into_iter().enumerate() {
                                    if let Some(arg_proof) = arg_proof {
                                        let congr = &self.proof_names().congr_constructor;
                                        proof = format!(
                                            "
                            ({congr} {proof} {i} {arg_proof})
                            "
                                        );
                                    }
                                }
                                proof
                            } else {
                                "()".to_string()
                            }
                        };
                        (fv, proof)
                    }
                    ResolvedCall::Primitive(specialized_primitive) => {
                        let fv = self.fresh_var();
                        res.push(format!(
                            "(= {fv} ({} {}))",
                            specialized_primitive.name(),
                            ListDisplay(new_args, " ")
                        ));

                        let proof = if !self.proofs_enabled() {
                            "()".to_string()
                        } else if specialized_primitive.output().is_eq_container_sort() {
                            // A container computed in the query/rule body has no
                            // carryable proof. It only ever appears in a container
                            // side condition, whose proof is the `Eval` marker
                            // emitted at the fact level (see `instrument_fact`);
                            // this per-expression proof is unused.
                            "()".to_string()
                        } else if specialized_primitive.output().is_eq_sort() {
                            // An eq-sort (datatype) result is an existing anchored
                            // term (e.g. an identity primitive returning its
                            // input); reuse its term-proof, fetched in the action.
                            let term_proof_name =
                                self.term_proof_name(specialized_primitive.output().name());
                            let fresh_proof = self.fresh_var();
                            action_lookups
                                .push(format!("(let {fresh_proof} ({term_proof_name} {fv}))"));
                            fresh_proof
                        } else {
                            // Base primitives produce a literal result; a
                            // reflexive `Fiat` over a literal is checker-valid.
                            let fiat_constructor = &self.proof_names().fiat_constructor;
                            let to_ast = self
                                .proof_names()
                                .sort_to_ast_constructor
                                .get(specialized_primitive.output().name())
                                .unwrap();
                            format!("({fiat_constructor} ({to_ast} {fv}) ({to_ast} {fv}))")
                        };

                        (fv.clone(), proof)
                    }
                    ResolvedCall::Values(_) => {
                        panic!("tuple-output (`values`) functions are not supported in proofs")
                    }
                }
            }
        }
    }

    /// Return the instrumented query and a proof that it matched.
    /// Returns `(body_facts, action_lookups, proof)`. Eq-sort variables'
    /// `term_proof` fetches are emitted into `action_lookups` as
    /// `(let p (term_proof v))` lines for the caller to splice into the
    /// rule's actions (the rule is then `:unsafe-seminaive`). Callers
    /// that don't build a proof (`run :until`, `check`) discard the
    /// lookups and the proof.
    fn instrument_facts(&mut self, facts: &[ResolvedFact]) -> (Vec<String>, Vec<String>, String) {
        let mut res = vec![];
        let mut action_lookups = vec![];
        let mut proof = vec![];

        for fact in facts.iter() {
            let f_proof = self.instrument_fact(fact, &mut res, &mut action_lookups);
            proof.push(f_proof);
        }

        (res, action_lookups, self.format_prooflist(&proof))
    }

    // Actions need to be instrumented to add to the view
    // as well as to the terms tables.
    fn instrument_action(
        &mut self,
        action: &ResolvedAction,
        justification: &Justification,
    ) -> Vec<String> {
        let mut res = vec![];

        match action {
            ResolvedAction::Let(_span, v, generic_expr) => {
                let v2 = self.instrument_action_expr(generic_expr, &mut res, justification);
                res.push(format!("(let {} {})", v.name, v2));
            }
            ResolvedAction::Set(_span, h, generic_exprs, generic_expr) => {
                let mut exprs = vec![];
                for e in generic_exprs.iter().chain(std::iter::once(generic_expr)) {
                    exprs.push(self.instrument_action_expr(e, &mut res, justification));
                }

                let ResolvedCall::Func(func_type) = h else {
                    panic!(
                        "Set action on non-function, should have been prevented by typechecking"
                    );
                };

                let (add_code, _fv) = self.add_term_and_view(func_type, &exprs, justification);
                res.extend(add_code);
            }
            ResolvedAction::Change(_span, change, h, generic_exprs) => {
                if let ResolvedCall::Func(func_type) = h {
                    let symbol = match change {
                        Change::Delete => self.delete_name(&func_type.name),
                        Change::Subsume => self.subsumed_name(&func_type.name),
                    };
                    let children = generic_exprs
                        .iter()
                        .map(|e| self.instrument_action_expr(e, &mut res, justification))
                        .collect::<Vec<_>>();

                    res.push(format!("({symbol} {})", ListDisplay(children, " ")));
                } else {
                    panic!(
                        "Delete action on non-function, should have been prevented by typechecking"
                    );
                }
            }
            ResolvedAction::Union(_span, generic_expr, generic_expr1) => {
                let v1 = self.instrument_action_expr(generic_expr, &mut res, justification);
                let v2 = self.instrument_action_expr(generic_expr1, &mut res, justification);
                let ot = generic_expr.output_type();
                let type_name = ot.name();
                let unioned = self.union(type_name, &v1, &v2, justification);
                res.push(unioned);
            }
            ResolvedAction::Panic(..) => {
                res.push(format!("{action}"));
            }
            ResolvedAction::Expr(_span, generic_expr) => {
                self.instrument_action_expr(generic_expr, &mut res, justification);
            }
        }

        res
    }

    /// Build the proof term that justifies a freshly-created term `fv`
    /// (wrapped by the AST constructor `to_ast`) proving `fv = fv`, from the
    /// surrounding [`Justification`]. Shared by constructor creation
    /// (`add_term_and_view`) and container creation.
    fn term_proof_for_justification(
        &self,
        fv: &str,
        to_ast: &str,
        justification: &Justification,
    ) -> String {
        let rule_constructor = &self.proof_names().rule_constructor;
        let fiat_constructor = &self.proof_names().fiat_constructor;
        match justification {
            Justification::Rule(rule_name, rule_proof) => format!(
                "({rule_constructor} {rule_name} {rule_proof} ({to_ast} {fv}) ({to_ast} {fv}))"
            ),
            Justification::Fiat => {
                format!("({fiat_constructor} ({to_ast} {fv}) ({to_ast} {fv}))")
            }
            Justification::Merge(fn_name, p1, p2) => {
                let merge_constructor = &self.proof_names().merge_fn_constructor;
                format!("({merge_constructor} \"{fn_name}\" {p1} {p2} ({to_ast} {fv}))")
            }
        }
    }

    /// Update the view with the given arguments.
    /// The arguments include the eclass for constructors.
    /// View is always a function (returning Proof or Unit).
    fn update_view(&mut self, fname: &str, args: &[String], proof: &str) -> String {
        let view_name = self.view_name(fname);
        let view_update = format!("(set ({view_name} {}) {proof})", ListDisplay(args, " "));
        // Custom function views are keyed by every column, so `args` are the key.
        let index_update = self.view_index_inserts(fname, args);
        if let Some((current_name, input_arity)) =
            self.egraph.proof_state.merge_current.get(fname).cloned()
            && args.len() == input_arity + 1
        {
            let inputs = ListDisplay(&args[..input_arity], " ");
            let output = &args[input_arity];
            return format!(
                "{view_update}\n(set ({current_name} {inputs}) {output})\n{index_update}"
            );
        }
        format!("{view_update}\n{index_update}")
    }

    /// Write a row into a constructor's functional-dependency view
    /// `(set (@FView children) (values eclass proof))`. Re-setting an existing `children` key with a
    /// different `eclass` triggers the view's native congruence `:merge`.
    fn update_fd_view(
        &mut self,
        fname: &str,
        children: &[String],
        eclass: &str,
        proof: &str,
    ) -> String {
        let view_name = self.view_name(fname);
        // FD views are keyed by their children, so `children` are the key.
        let index_update = self.view_index_inserts(fname, children);
        format!(
            "(set ({view_name} {}) (values {eclass} {proof}))\n{index_update}",
            ListDisplay(children, " ")
        )
    }

    /// Key positions of a view that get a materialized rebuild index: every
    /// non-container eq-sort key column (containers rebuild structurally, not via
    /// `@UF`). All such positions are indexed — including the first — because the
    /// single-rule rebuild is driven by a `@UF` delta on any child and finds its
    /// rows through the index.
    fn view_index_positions(types: &[ArcSort], n_keys: usize) -> Vec<usize> {
        (0..n_keys)
            .filter(|&i| !types[i].is_eq_container_sort() && types[i].is_eq_sort())
            .collect()
    }

    /// Insert this view row into each of its rebuild indexes: one entry per
    /// indexed key column, `(set (<index> key[pos] <full key>) ())` — the
    /// referenced term first, then the whole key. `key` is the view's key
    /// columns (children for FD views, all columns otherwise).
    fn view_index_inserts(&mut self, fname: &str, key: &[String]) -> String {
        self.view_index_ops(fname, key, |name, r, full| {
            format!("(set ({name} {r} {full}) ())")
        })
    }

    /// Delete this view row from each of its rebuild indexes, mirroring
    /// [`Self::view_index_inserts`]. Emitted wherever a view row is deleted.
    fn view_index_deletes(&mut self, fname: &str, key: &[String]) -> String {
        self.view_index_ops(fname, key, |name, r, full| {
            format!("(delete ({name} {r} {full}))")
        })
    }

    fn view_index_ops(
        &mut self,
        fname: &str,
        key: &[String],
        op: impl Fn(&str, &str, &str) -> String,
    ) -> String {
        let Some(indexes) = self.egraph.proof_state.view_index.get(fname).cloned() else {
            return String::new();
        };
        let full = format!("{}", ListDisplay(key, " "));
        let mut out = Vec::new();
        for vi in &indexes {
            for &pos in &vi.positions {
                out.push(op(&vi.name, &key[pos], &full));
            }
        }
        out.join("\n")
    }

    /// Return some code adding to the view and term tables.
    /// For constructors, `args` should not include the eclass of the resulting term (since it may not exist yet).
    /// For custom functions, `args` should include all arguments (including the output for the function).
    ///
    /// Returns a vector of strings representing code to add and a variable for the created term.
    /// We could return the term itself, but this might make the encoding blow up the code.
    fn add_term_and_view(
        &mut self,
        func_type: &FuncType,
        args: &[String],
        justification: &Justification,
    ) -> (Vec<String>, String) {
        // A fresh variable for the new term.
        let fv = self.fresh_var();
        let mut res = vec![];
        // TODO might be able to get rid of this intermediate variable in encoding
        res.push(format!(
            "(let {fv} ({} {}))",
            func_type.name,
            ListDisplay(args, " ")
        ));

        let (proof_str, view_proof_var) = if self.egraph.proof_state.proofs_enabled {
            let to_ast = self.fname_to_ast_name(&func_type.name);
            let proof = self.term_proof_for_justification(&fv, to_ast, justification);

            let proof_var = self.fresh_var();
            // add a proof for the constructor if needed
            let term_proof = if func_type.subtype == FunctionSubtype::Constructor {
                let term_proof_constructor = self.term_proof_name(func_type.output().name());
                format!("(set ({term_proof_constructor} {fv}) {proof_var})")
            } else {
                "".to_string()
            };

            (
                format!(
                    "(let {proof_var} {proof})
                     {term_proof}"
                ),
                proof_var,
            )
        } else {
            ("".to_string(), "()".to_string())
        };

        res.push(proof_str);
        if func_type.subtype == FunctionSubtype::Constructor {
            // FD view: children are the key, the fresh term is the eclass value.
            res.push(self.update_fd_view(&func_type.name, args, &fv, &view_proof_var));
        } else {
            // Custom function: `args` already includes the output column.
            res.push(self.update_view(&func_type.name, args, &view_proof_var));
        }

        // No self-loop seed: the single-key `@UF` needs none — a root term simply has
        // no `@UF` row (identity-on-miss), in both term and proof mode.

        (res, fv)
    }

    /// Returns a query for (fname args) and a variable for the proof (or Unit) output.
    /// View is always a function, so we always use `(= var (view ...))` form.
    fn query_view_and_get_proof(&mut self, fname: &str, args: &[String]) -> (String, String) {
        let view_name = self.view_name(fname);
        let pf_var = self.fresh_var();
        let query = format!("(= {pf_var} ({view_name} {}))", ListDisplay(args, " "));
        (query, pf_var)
    }

    /// Query a constructor's functional-dependency view by its `children` key, binding fresh
    /// variables for the `eclass` and `proof` output columns: `(= (values e pf) (@FView children))`.
    /// Returns `(query, eclass_var, proof_var)`.
    fn query_fd_view(&mut self, fname: &str, children: &[String]) -> (String, String, String) {
        let view_name = self.view_name(fname);
        let eclass_var = self.fresh_var();
        let pf_var = self.fresh_var();
        let query = format!(
            "(= (values {eclass_var} {pf_var}) ({view_name} {}))",
            ListDisplay(children, " ")
        );
        (query, eclass_var, pf_var)
    }

    // Add to view and term tables, returning a variable for the created term.
    fn instrument_action_expr(
        &mut self,
        expr: &ResolvedExpr,
        res: &mut Vec<String>,
        proof: &Justification,
    ) -> String {
        match expr {
            ResolvedExpr::Lit(_, lit) => format!("{lit}"),
            ResolvedExpr::Var(_, resolved_var) => resolved_var.name.clone(),
            ResolvedExpr::Call(_, resolved_call, args) => {
                let args = args
                    .iter()
                    .map(|arg| self.instrument_action_expr(arg, res, proof))
                    .collect::<Vec<_>>();
                match resolved_call {
                    ResolvedCall::Func(func_type) => {
                        if func_type.subtype == FunctionSubtype::Custom {
                            // Globals are desugared to no-arg functions (in non-proof mode)
                            // They're allowed, in proof mode they are constructors.
                            if self.egraph.type_info.is_global(&func_type.name) {
                                return format!("({} {})", func_type.name, ListDisplay(&args, " "));
                            }
                            panic!(
                                "Found a function lookup in actions, should have been prevented by typechecking"
                            );
                        }
                        let (add_code, fv) = self.add_term_and_view(func_type, &args, proof);
                        res.extend(add_code);

                        fv
                    }
                    ResolvedCall::Primitive(specialized_primitive) => {
                        let fv = self.fresh_var();
                        res.push(format!(
                            "(let {} ({} {}))",
                            fv,
                            specialized_primitive.name(),
                            ListDisplay(&args, " ")
                        ));
                        // In proof mode, a primitive that builds a container
                        // value records a reflexive term-proof in `<CSort>Proof`.
                        // This is the anchor for the container's rebuild
                        // congruence proofs (see `rebuilding_rules`).
                        if self.egraph.proof_state.proofs_enabled {
                            let out = specialized_primitive.output();
                            if out.is_eq_container_sort() {
                                let csort = out.name().to_string();
                                let to_ast = self
                                    .proof_names()
                                    .sort_to_ast_constructor
                                    .get(&csort)
                                    .unwrap()
                                    .clone();
                                let proof_str =
                                    self.term_proof_for_justification(&fv, &to_ast, proof);
                                let cproof = self.term_proof_name(&csort);
                                res.push(format!("(set ({cproof} {fv}) {proof_str})"));
                            }
                        }
                        fv
                    }
                    ResolvedCall::Values(_) => {
                        panic!("tuple-output (`values`) functions are not supported in proofs")
                    }
                }
            }
        }
    }

    /// In proof mode, rule_proof justifies the actions taken.
    fn instrument_actions(
        &mut self,
        actions: &[ResolvedAction],
        justification: &Justification,
    ) -> Vec<String> {
        let mut res = vec![];
        for action in actions {
            res.extend(self.instrument_action(action, justification));
        }
        res
    }

    /// Instrument a rule to use term encoding. This involves using the view tables in facts,
    /// adding to term and view tables in actions.
    /// When proofs are enabled we query proof tables, then build a proof for the rule in the actions.
    /// Finally, each view update also updates the proof tables.
    fn instrument_rule(&mut self, rule: &ResolvedRule) -> Vec<Command> {
        // term_proofs are fetched as action-side lookups (see instrument_facts),
        // so a rule with any needs a Read/Full action context (`eval_opt` below).
        let (facts, action_lookups, proof_str) = self.instrument_facts(&rule.body);
        let proof_var = self.fresh_var();
        let rule_name_var = if self.egraph.proof_state.proofs_enabled {
            self.egraph.parser.symbol_gen.fresh("rule_name")
        } else {
            "()".to_string()
        };
        let proof = Justification::Rule(rule_name_var.clone(), proof_var.clone());
        let reads_in_rhs = !action_lookups.is_empty();
        // The looked-up proofs feed `proof_str`, so bind them before the proof list.
        let action_lookups_str = ListDisplay(&action_lookups, "\n                    ");
        let proof_var_binding = if self.egraph.proof_state.proofs_enabled {
            format!(
                "(let {rule_name_var} \"{}\")
                 {action_lookups_str}
                 (let {proof_var}
                          {proof_str})",
                rule.name
            )
        } else {
            "".to_string()
        };

        let actions = self.instrument_actions(&rule.head.0, &proof);
        let name = &rule.name;
        let ruleset_opt = if rule.ruleset.is_empty() {
            "".to_string()
        } else {
            format!(":ruleset {}", rule.ruleset)
        };
        // Preserve a user `:naive` (else it silently reverts to seminaive).
        // Otherwise an RHS-reading rule needs `:unsafe-seminaive` (or `:naive`
        // under the test knob).
        let eval_opt = if rule.eval_mode.is_naive() {
            ":naive"
        } else if reads_in_rhs {
            if self.egraph.proof_state.force_proof_naive {
                ":naive"
            } else {
                ":unsafe-seminaive"
            }
        } else {
            ""
        };
        let instrumented = format!(
            "(rule ({})
                   ({proof_var_binding}
                    {})
                    {ruleset_opt} {eval_opt}
                    :name \"{name}\")",
            ListDisplay(facts, " "),
            ListDisplay(actions, " "),
        );
        self.parse_program(&instrumented)
    }

    /// Any schedule should be sound as long as we saturate.
    fn rebuild(&mut self) -> Schedule {
        let path_compress_ruleset = self.proof_names().path_compress_ruleset_name.clone();
        let rebuilding_cleanup_ruleset = self.proof_names().rebuilding_cleanup_ruleset_name.clone();
        let rebuilding_ruleset = self.proof_names().rebuilding_ruleset_name.clone();
        let delete_ruleset = self.proof_names().delete_subsume_ruleset_name.clone();
        // The `@UF` `:merge` resolves conflicting parents itself, so only
        // `path_compress` (flattening chains) remains as UF maintenance.
        self.parse_schedule(format!(
            "(seq
              (saturate
                  {rebuilding_cleanup_ruleset}
                  (saturate {path_compress_ruleset})
                  {rebuilding_ruleset})
              {delete_ruleset})"
        ))
    }

    fn instrument_schedule(&mut self, schedule: &ResolvedSchedule) -> Schedule {
        match schedule {
            ResolvedSchedule::Run(span, config) => {
                let new_run = match config.until {
                    Some(ref facts) => {
                        let (instrumented, _lookups, _proof) = self.instrument_facts(facts);
                        let instrumented_facts = self.parse_facts(&instrumented);
                        Schedule::Run(
                            span.clone(),
                            RunConfig {
                                ruleset: config.ruleset.clone(),
                                until: Some(instrumented_facts),
                            },
                        )
                    }
                    None => Schedule::Run(
                        span.clone(),
                        RunConfig {
                            ruleset: config.ruleset.clone(),
                            until: None,
                        },
                    ),
                };
                Schedule::Sequence(span.clone(), vec![new_run, self.rebuild()])
            }
            ResolvedSchedule::Sequence(span, schedules) => Schedule::Sequence(
                span.clone(),
                schedules
                    .iter()
                    .map(|s| self.instrument_schedule(s))
                    .collect(),
            ),
            ResolvedSchedule::Saturate(span, schedule) => {
                Schedule::Saturate(span.clone(), Box::new(self.instrument_schedule(schedule)))
            }
            GenericSchedule::Repeat(span, n, schedule) => Schedule::Repeat(
                span.clone(),
                *n,
                Box::new(self.instrument_schedule(schedule)),
            ),
        }
    }

    fn input_actions(
        egraph: &EGraph,
        span: &Span,
        name: &str,
        file: &str,
    ) -> Result<Vec<ResolvedAction>, Error> {
        let function_type = egraph
            .proof_state
            .original_typechecking
            .as_ref()
            .and_then(|typechecker| typechecker.type_info.get_func_type(name))
            .unwrap_or_else(|| panic!("Unrecognized function name {name}"))
            .clone();
        let rows =
            EGraph::read_input_file(egraph.fact_directory.as_deref(), &function_type, span, file)?;
        let mut actions = vec![];
        for row in rows {
            let mut expressions = row
                .into_iter()
                .map(|literal| ResolvedExpr::Lit(span.clone(), literal));
            let inputs = expressions
                .by_ref()
                .take(function_type.input.len())
                .collect::<Vec<_>>();
            actions.push(if function_type.subtype == FunctionSubtype::Constructor {
                ResolvedAction::Expr(
                    span.clone(),
                    ResolvedExpr::Call(
                        span.clone(),
                        ResolvedCall::Func(function_type.clone()),
                        inputs,
                    ),
                )
            } else {
                let output = expressions
                    .next()
                    .expect("custom input row must contain its output value");
                ResolvedAction::Set(
                    span.clone(),
                    ResolvedCall::Func(function_type.clone()),
                    inputs,
                    output,
                )
            });
        }
        Ok(actions)
    }

    fn term_encode_command(
        &mut self,
        command: &ResolvedNCommand,
        res: &mut Vec<Command>,
    ) -> Result<(), Error> {
        log::trace!("Term encoding for {command}");
        match &command {
            ResolvedNCommand::Sort {
                span,
                name,
                presort_and_args,
                unionable,
                ..
            } => {
                // After the proof-encoding gate, any sort carrying a presort
                // is one of the supported container sorts. Containers have no
                // per-sort union-find (they are canonicalized structurally),
                // so they get `uf: None` and `find_canonical` leaves their
                // value unchanged during extraction.
                let is_container = presort_and_args.is_some();
                let uf_name = if is_container {
                    None
                } else {
                    Some((self.uf_name(name), None))
                };
                // Every sort (containers included) records its `<Sort>Proof`
                // table via `:internal-proof-func` so container rebuild can
                // recover the per-container proof tables without a per-container
                // list. (The table itself is declared in `declare_sort`.)
                let proof_func = if self.egraph.proof_state.proofs_enabled {
                    Some(self.term_proof_name(name))
                } else {
                    None
                };
                // For container sorts, build the rebuild-primitive spec now (it
                // generates and caches the fresh primitive names used by the
                // rebuild rules below) and attach it as an annotation so the
                // primitives can be re-registered when this desugared Sort
                // command is typechecked / re-parsed.
                let container_rebuild = if is_container {
                    let container_sort = self
                        .egraph
                        .proof_state
                        .original_typechecking
                        .as_ref()
                        .and_then(|tc| tc.get_sort_by_name(name).cloned())
                        .unwrap_or_else(|| {
                            panic!("container sort {name} not found while term-encoding")
                        });
                    Some(self.build_container_rebuild_spec(&container_sort))
                } else {
                    None
                };
                res.push(Command::Sort {
                    span: span.clone(),
                    name: name.clone(),
                    presort_and_args: presort_and_args.clone(),
                    uf: uf_name,
                    proof_func,
                    unionable: *unionable,
                    container_rebuild,
                    // The Proof sort (which carries :internal-proof-names) is
                    // emitted as source by the proof header, not here.
                    proof_constructors: None,
                });
                res.extend(self.declare_sort(name, is_container));
            }
            ResolvedNCommand::Function(fdecl) => {
                res.extend(self.term_and_view(fdecl));
                res.extend(self.rebuilding_rules(fdecl));
                res.extend(self.rebuilding_subsumed_rules(fdecl));
            }
            ResolvedNCommand::NormRule { rule } => {
                res.extend(self.instrument_rule(rule));
            }
            ResolvedNCommand::CoreAction(action) => {
                let instrumented = self
                    .instrument_action(action, &Justification::Fiat)
                    .join("\n");
                res.extend(self.parse_program(&instrumented));
            }
            ResolvedNCommand::Check(span, facts) => {
                let (instrumented, _lookups, _proof) = self.instrument_facts(facts);
                res.push(Command::Check(
                    span.clone(),
                    self.parse_facts(&instrumented),
                ));
            }
            ResolvedNCommand::RunSchedule(schedule) => {
                res.push(Command::RunSchedule(self.instrument_schedule(schedule)));
            }
            ResolvedNCommand::Fail(span, cmd) => {
                let mut encoded = vec![];
                self.term_encode_command(cmd, &mut encoded)?;
                if encoded.len() != 1 {
                    return Err(Error::UnsupportedProofCommand {
                        command: cmd.to_command().to_string(),
                        reason: ProofEncodingUnsupportedReason::FailNonAtomicCommand,
                    });
                }
                res.push(Command::Fail(
                    span.clone(),
                    Box::new(encoded.pop().unwrap()),
                ));
            }
            ResolvedNCommand::Input { .. } => {
                unreachable!("inputs should be lowered before term/proof instrumentation")
            }
            ResolvedNCommand::Extract(span, expr, variants) => {
                // Instrument the expressions to use view tables (like actions, not facts)
                let mut action_stmts = vec![];
                let instrumented_expr =
                    self.instrument_action_expr(expr, &mut action_stmts, &Justification::Fiat);
                let instrumented_variants =
                    self.instrument_action_expr(variants, &mut action_stmts, &Justification::Fiat);

                // Add any action statements needed to set up the expressions
                for stmt in action_stmts {
                    res.extend(self.parse_program(&stmt));
                }
                // Rebuild before extract; we may have added new view rows that need canonicalization
                res.push(Command::RunSchedule(self.rebuild()));
                res.push(Command::Extract(
                    span.clone(),
                    self.parse_expr(&instrumented_expr),
                    self.parse_expr(&instrumented_variants),
                ));
            }
            ResolvedNCommand::PrintSize(span, name) => {
                // In proof mode, print the size of the view table for constructors
                let new_name = name.as_ref().map(|n| {
                    if self
                        .egraph
                        .type_info
                        .get_func_type(n)
                        .is_some_and(|f| f.subtype == FunctionSubtype::Constructor)
                    {
                        self.view_name(n)
                    } else {
                        n.clone()
                    }
                });
                res.push(Command::PrintSize(span.clone(), new_name));
            }
            ResolvedNCommand::Pop(..)
            | ResolvedNCommand::Push(..)
            | ResolvedNCommand::AddRuleset(..)
            | ResolvedNCommand::Output { .. }
            | ResolvedNCommand::UnstableCombinedRuleset(..)
            | ResolvedNCommand::PrintOverallStatistics(..)
            | ResolvedNCommand::PrintFunction(..)
            | ResolvedNCommand::ProveExists(..) => {
                res.push(command.to_command().make_unresolved());
            }
            ResolvedNCommand::UserDefined(..) => {
                panic!("User defined commands unsupported in term encoding");
            }
        }
        Ok(())
    }

    pub(crate) fn add_term_encoding_helper(
        &mut self,
        program: Vec<ResolvedNCommand>,
    ) -> Result<Vec<Command>, Error> {
        let mut res = vec![];

        if !self.egraph.proof_state.term_header_added {
            res.extend(self.term_header());
            if self.egraph.proof_state.proofs_enabled {
                let proof_header = self.proof_header();
                res.extend(self.parse_program(&proof_header));
            }
            self.egraph.proof_state.term_header_added = true;
        }

        for command in program {
            self.term_encode_command(&command, &mut res)?;

            // run rebuilding after every command except a few
            if let ResolvedNCommand::Function(..)
            | ResolvedNCommand::NormRule { .. }
            | ResolvedNCommand::Sort { .. } = &command
            {
            } else {
                res.push(Command::RunSchedule(self.rebuild()));
            }
        }

        Ok(res)
    }

    /// Build the [`ContainerRebuildSpec`] for a container sort: mint and cache
    /// the fresh rebuild-primitive names. The primitives themselves are
    /// registered from the spec when the Sort is typechecked (see
    /// [`crate::proofs::proof_container_rebuild::register_container_rebuild_from_spec`]).
    fn build_container_rebuild_spec(&mut self, container_sort: &ArcSort) -> ContainerRebuildSpec {
        let sort_name = container_sort.name().to_string();
        let proof_mode = self.egraph.proof_state.proofs_enabled;

        let internal_rebuild_prim = self.egraph.parser.symbol_gen.fresh("container_rebuild");
        self.egraph
            .proof_state
            .container_rebuild_name
            .insert(sort_name.clone(), internal_rebuild_prim.clone());

        let internal_rebuild_proof_prim = proof_mode.then(|| {
            let proof_prim = self
                .egraph
                .parser
                .symbol_gen
                .fresh("container_rebuild_proof");
            self.egraph
                .proof_state
                .container_rebuild_proof_name
                .insert(sort_name, proof_prim.clone());
            proof_prim
        });

        ContainerRebuildSpec {
            internal_rebuild_prim,
            internal_rebuild_proof_prim,
        }
    }

    /// The (already-built) container value-rebuild primitive name for a sort.
    fn ensure_container_rebuild(&mut self, container_sort: &ArcSort) -> String {
        self.egraph
            .proof_state
            .container_rebuild_name
            .get(container_sort.name())
            .cloned()
            .unwrap_or_else(|| {
                panic!(
                    "container rebuild primitive not built for sort {}",
                    container_sort.name()
                )
            })
    }

    /// The (already-built) container proof-rebuild primitive name for a sort.
    fn ensure_container_rebuild_proof(&mut self, container_sort: &ArcSort) -> String {
        self.egraph
            .proof_state
            .container_rebuild_proof_name
            .get(container_sort.name())
            .cloned()
            .unwrap_or_else(|| {
                panic!(
                    "container rebuild proof primitive not built for sort {}",
                    container_sort.name()
                )
            })
    }
}

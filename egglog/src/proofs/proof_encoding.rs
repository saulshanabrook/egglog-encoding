#[doc = include_str!("proof_encoding.md")]
use crate::proofs::proof_encoding_helpers::{EncodingNames, Justification};
use crate::typechecking::FuncType;
use crate::*;

// TODO refactor so that encoding state is optional on the e-graph, ProofNames not optional on EncodingState. Then we don't have to clone proof names everywhere.
#[derive(Clone)]
pub(crate) struct EncodingState {
    pub uf_parent: HashMap<String, String>,
    /// Maps sort name -> proof function name (set from :internal-proof-func annotation).
    pub proof_func_parent: HashMap<String, String>,
    /// Function name -> (hidden current-value function, input arity). The
    /// current function uses the original eager backend merge, so cleanup can
    /// discard stale proof-view candidates whenever the current value already
    /// has a proof witness.
    pub merge_current: HashMap<String, (String, usize)>,
    pub term_header_added: bool,
    // TODO this is very ugly- we should separate out a typechecking struct
    // since we didn't need an entire e-graph
    // When Some term encoding is enabled.
    pub original_typechecking: Option<Box<EGraph>>,
    pub proofs_enabled: bool,
    pub proof_testing: bool,
    /// Non-proof term encoding: the per-sort single self-referential union-find
    /// function names (`@UF : (S) -> S`). `declare_function` (lib.rs) attaches
    /// the native self-referential `:merge` (see `EGraph::build_uf_self_merge`)
    /// to these, overriding their placeholder source `:merge`.
    pub self_merge_uf_functions: HashSet<String>,
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
            merge_current: HashMap::default(),
            term_header_added: false,
            original_typechecking: None,
            proofs_enabled: false,
            proof_names: EncodingNames::new(symbol_gen),
            proof_testing: false,
            self_merge_uf_functions: HashSet::default(),
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
    ) -> Vec<Command> {
        Self { egraph }.add_term_encoding_helper(program)
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
        // Non-proof: the union-find is a single self-referential function
        // `@UF : (S) -> S` keyed by the larger endpoint; the native `:merge`
        // resolves conflicts (keeps the min, unions the displaced parent).
        if !self.egraph.proof_state.proofs_enabled {
            return format!("(set ({uf_name} {larger}) {smaller})");
        }
        let proof = if self.egraph.proof_state.proofs_enabled {
            let to_ast_constructor = self
                .proof_names()
                .sort_to_ast_constructor
                .get(type_name)
                .unwrap();
            let rule_constructor = &self.proof_names().rule_constructor;
            let fiat_constructor = &self.proof_names().fiat_constructor;
            match justification {
                Justification::Rule(rule_name, proof_list) => format!(
                    "({rule_constructor} \"{rule_name}\" {proof_list} ({to_ast_constructor} {larger}) ({to_ast_constructor} {smaller}))"
                ),
                Justification::Fiat => format!(
                    "({fiat_constructor} ({to_ast_constructor} {larger}) ({to_ast_constructor} {smaller}))"
                ),
                Justification::Merge(_func_name, _proof1, _proof2) => panic!(
                    "Merge functions do not include union actions, so proof should not be by merge"
                ),
                Justification::Proof(existing_proof) => existing_proof.clone(),
            }
        } else {
            "()".to_string()
        };
        // Single self-referential UF `@UF : (S) -> (S, Proof)` keyed by the larger
        // endpoint; value column 0 = smaller parent, column 1 = `proof` (larger = smaller).
        format!("(set ({uf_name} {larger}) (values {smaller} {proof}))")
    }

    /// The parent table is the database representation of a union-find datastructure.
    /// When one term has two parents, those parents are unioned in the merge action.
    /// Also, we have a rule that maintains the invariant that each term points to its
    /// canonical representative.
    fn declare_sort(&mut self, sort_name: &str) -> Vec<Command> {
        if self.egraph.proof_state.proofs_enabled {
            self.declare_sort_proof(sort_name)
        } else {
            self.declare_sort_non_proof(sort_name)
        }
    }

    /// Proof-mode `declare_sort`: the union-find is a SINGLE self-referential
    /// function `@UF : (S) -> (S, Proof)` (native tuple, reusing `uf_name`). Value
    /// column 0 is the parent, column 1 a proof `key = parent`. Union `a, b` writes
    /// `(set (@UF (ordering-max a b)) (values (ordering-min a b) proof))`;
    /// `declare_function` attaches the native self-referential `:merge` (see
    /// [`EGraph::build_uf_self_merge`]), overriding the `:merge (values old0 old1)`
    /// placeholder. A proof-composing `path_compress` rule flattens cross-key chains
    /// via `Trans`. Also emits the per-sort `term_proof` table and AST constructor.
    fn declare_sort_proof(&mut self, sort_name: &str) -> Vec<Command> {
        let uf_name = self.uf_name(sort_name);
        let proof_type = self.proof_type_str().to_string();
        let term_proof_name = self.term_proof_name(sort_name);
        let add_to_ast_code = self.add_to_ast(sort_name);
        let fresh_name = self.egraph.parser.symbol_gen.fresh("uf_path_compress");
        let path_compress_ruleset_name = self.proof_names().path_compress_ruleset_name.clone();
        let trans = self.proof_names().eq_trans_constructor.clone();

        // Mark `@UF` so `declare_function` attaches the native self-referential proof merge.
        self.egraph
            .proof_state
            .self_merge_uf_functions
            .insert(uf_name.clone());

        let code = format!(
            "{add_to_ast_code}
             (function {term_proof_name} ({sort_name}) {proof_type} :merge old :internal-hidden)
             (function {uf_name} ({sort_name}) ({sort_name} {proof_type}) :merge (values old0 old1) :unextractable :internal-hidden)
             ;; path compression: a->b (pb: a=b), b->c (pc: b=c)  =>  a->c (Trans pb pc: a=c)
             (rule ((= (values b pb) ({uf_name} a))
                    (= (values c pc) ({uf_name} b))
                    (!= b c))
                  ((set ({uf_name} a) (values c ({trans} pb pc))))
                   :ruleset {path_compress_ruleset_name}
                   :name \"{fresh_name}\")
                   "
        );

        self.parse_program(&code)
    }

    /// Non-proof `declare_sort`: the whole union-find is a SINGLE
    /// self-referential function `@UF : (S) -> S` (reusing `uf_name`), with a
    /// native `:merge` (built in [`EGraph::build_uf_self_merge`], attached in
    /// `declare_function`). Union `a, b` writes `(set (@UF (ordering-max a b))
    /// (ordering-min a b))`; on an FD conflict the merge keeps the min and unions
    /// the displaced parent back into `@UF`, so the `single_parent` /
    /// `uf_function_index` rulesets are unnecessary. `path_compress` is kept to
    /// flatten cross-key chains (the encoder reads `@UF` as a single
    /// identity-on-miss lookup).
    fn declare_sort_non_proof(&mut self, sort_name: &str) -> Vec<Command> {
        let uf_name = self.uf_name(sort_name);
        let fresh_name = self.egraph.parser.symbol_gen.fresh("uf_path_compress");
        let path_compress_ruleset_name = self.proof_names().path_compress_ruleset_name.clone();

        // Mark `@UF` so `declare_function` attaches the native self-referential
        // merge instead of lowering the placeholder `:merge (ordering-min old new)`.
        self.egraph
            .proof_state
            .self_merge_uf_functions
            .insert(uf_name.clone());

        // The source `:merge (ordering-min old new)` is a valid placeholder so the
        // function typechecks; `declare_function` overrides it with the native
        // self-referential merge (recursive parent-union).
        let code = format!(
            "(function {uf_name} ({sort_name}) {sort_name} :merge (ordering-min old new) :unextractable :internal-hidden)
             (rule ((= b ({uf_name} a))
                    (= c ({uf_name} b))
                    (!= b c))
                  ((set ({uf_name} a) c))
                   :ruleset {path_compress_ruleset_name}
                   :name \"{fresh_name}\")
                   "
        );

        self.parse_program(&code)
    }

    /// Rules that execute deletion and subsumption based on the tables requesting the deletion/subsumption.
    fn delete_and_subsume(&mut self, fdecl: &ResolvedFunctionDecl) -> String {
        let child_names = fdecl
            .schema
            .input
            .iter()
            .enumerate()
            .map(|(i, _)| format!("c{i}_"))
            .collect::<Vec<_>>()
            .join(" ");
        let to_delete_name = self.delete_name(&fdecl.name);
        let subsumed_name = self.subsumed_name(&fdecl.name);
        let view_name = self.view_name(&fdecl.name);
        let delete_subsume_ruleset = self.proof_names().delete_subsume_ruleset_name.clone();
        let fresh_name = self.egraph.parser.symbol_gen.fresh("delete_rule");

        // The FD tuple view is keyed by children only, so match its value tuple to delete/subsume
        // by key (the bridge re-reads every value column when subsuming a tuple-output view).
        if self.native_merge_view(fdecl) {
            let e = self.fresh_var();
            let pf = self.fresh_var();
            let e2 = self.fresh_var();
            let pf2 = self.fresh_var();
            // Deletion removes the row by key; subsumption marks it subsumed (kept for size/proofs
            // but excluded from matching).
            return format!(
                "(rule (({to_delete_name} {child_names})
                        (= (values {e} {pf}) ({view_name} {child_names})))
                       ((delete ({view_name} {child_names}))
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

        format!(
            "(rule (({to_delete_name} {child_names})
                    ({view_name} {child_names} out))
                   ((delete ({view_name} {child_names} out))
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
        let merge_fn_var = self.instrument_action_expr(
            merge_fn,
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
                       ((delete ({view_name} {child_names_str} old)))
                        :ruleset {rebuilding_cleanup_ruleset}
                        :name \"{cleanup_name}\")
                 (rule ((= selected ({current_name} {child_names_str}))
                        ({view_name} {child_names_str} selected)
                        ({view_name} {child_names_str} old)
                        (!= selected old))
                       ((delete ({view_name} {child_names_str} old)))
                        :ruleset {rebuilding_cleanup_ruleset}
                        :name \"{current_cleanup_name}\")
                ",
        )
    }

    /// Generate a rule that handles congruence for constructors.
    /// When two different values are present for the same children,
    /// we union those two values together.
    fn handle_congruence(
        &mut self,
        fdecl: &ResolvedFunctionDecl,
        child_names: &[String],
        rebuilding_ruleset: &str,
    ) -> String {
        // Congruence rule
        let fresh_name = self.egraph.parser.symbol_gen.fresh("congruence_rule");
        let mut child_names_new = child_names.to_vec();
        child_names_new.push("new".to_string());
        let mut child_names_old = child_names.to_vec();
        child_names_old.push("old".to_string());
        let (query1, prf1) = self.query_view_and_get_proof(&fdecl.name, &child_names_new);
        let (query2, prf2) = self.query_view_and_get_proof(&fdecl.name, &child_names_old);
        let sym = &self.proof_names().eq_sym_constructor;
        let trans = &self.proof_names().eq_trans_constructor;

        // Proof is by transitivity. A view proof gives a proof that
        // representative r_1 = f(c_1,...,c_n).
        // We also have a proof that other eclass representative r_2 = f(c_1,...,c_n), the same term.
        // We want a proof that r1 = r2, which we get by transitivity.
        let union_code = self.union(
            fdecl.schema.output(),
            "new",
            "old",
            &Justification::Proof(format!("({trans} {prf1} ({sym} {prf2}))",)),
        );
        // Action-side term construction can create a fresh visible view row for
        // child tuples that were already subsumed. Congruence maintenance still
        // has to see those subsumed rows so it can union the old and new outputs.
        format!(
            "(rule ({query1}
                        {query2}
                        (!= old new)
                        (= (ordering-max old new) new))
                       ({union_code})
                        :ruleset {rebuilding_ruleset}
                        :internal-include-subsumed
                        :name \"{fresh_name}\")"
        )
    }

    /// Generate rules that handle merge functions or congruence.
    /// For custom functions, we generate rules that run the merge function.
    /// For constructors, we generate congruence rules.
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
            self.handle_merge_fn(
                fdecl,
                &child_names,
                &child_names_str,
                &view_name,
                &rebuilding_ruleset,
            )
        } else if self.native_merge_view(fdecl) {
            // Congruence is resolved by the view's native `:merge`; no rule needed.
            String::new()
        } else {
            self.handle_congruence(fdecl, &child_names, &rebuilding_ruleset)
        }
    }

    /// Each function/constructor gets a term table and a view table.
    /// The term table stores underlying representative terms.
    /// The view table stores child terms and their eclass.
    /// The view table is mutated using delete, but we never delete from term tables.
    /// We re-use the original name of the function for the term table.
    /// Whether this function's view is the proof-mode functional-dependency tuple view
    /// `(children) -> (eclass, proof)` whose native `:merge` resolves congruence.
    fn native_merge_view(&self, fdecl: &ResolvedFunctionDecl) -> bool {
        fdecl.subtype == FunctionSubtype::Constructor && self.egraph.proof_state.proofs_enabled
    }

    fn term_and_view(&mut self, fdecl: &ResolvedFunctionDecl) -> Vec<Command> {
        let schema = &fdecl.schema;
        let out_type = schema.output().clone();

        let name = &fdecl.name;
        let view_name = self.view_name(&fdecl.name);
        let in_sorts = ListDisplay(schema.input.clone(), " ");
        let fresh_sort = self.egraph.parser.symbol_gen.fresh("view");
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
        // In proof mode, a constructor's view is a functional-dependency tuple
        // `(children) -> (eclass, proof)` whose native `:merge` resolves congruence (see
        // `EGraph::native_congruence_merge`). Other functions keep the `(children eclass) -> proof`
        // form with a congruence/merge rule.
        let fd_view = self.native_merge_view(fdecl);
        let view_decl = if fd_view {
            format!(
                "(function {view_name} ({in_sorts}) ({out_type} {proof_type}) :merge (values old0 old1) :internal-term-constructor {name}{view_flags})"
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
            {proof_constructors}
            {merge_rule}
            {delete_rule}",
        ))
    }

    fn proof_functions(&mut self, _fdecl: &ResolvedFunctionDecl, _view_sorts: &str) -> String {
        // ViewProof is now merged into the view table as its output column
        "".to_string()
    }

    /// Rules that update the views when children change.
    fn rebuilding_rules(&mut self, fdecl: &ResolvedFunctionDecl) -> Vec<Command> {
        if self.native_merge_view(fdecl) {
            return self.rebuilding_rules_fd(fdecl);
        }
        if !self.egraph.proof_state.proofs_enabled {
            return self.rebuilding_rules_fanout(fdecl);
        }
        let types = fdecl.resolved_schema.view_types();

        // Check if there are any eq-sort columns at all; if not, no rebuild rule needed.
        if !types.iter().any(|t| t.is_eq_sort()) {
            return vec![];
        }

        // Proof-mode fanout: the single-key `@UF` has no row for a canonical column
        // (identity-on-miss), so a combined all-columns join would stall whenever any
        // column is already canonical. Emit one rule per eq-sort view column, each with a
        // single `@UF` lookup, mirroring [`Self::rebuilding_rules_fanout`] but composing a
        // proof: `Congr` for a child update, `Trans(Sym uf_pf, view_prf)` for the
        // representative (last) column of a constructor view.
        let view_name = self.view_name(&fdecl.name);
        let child = |i: usize| format!("c{i}_");
        let children_vec: Vec<String> = (0..types.len()).map(child).collect();
        let children = format!("{}", ListDisplay(&children_vec, " "));
        let rebuilding_ruleset = self.proof_names().rebuilding_ruleset_name.clone();
        let trans = self.proof_names().eq_trans_constructor.clone();
        let sym = self.proof_names().eq_sym_constructor.clone();
        let congr = self.proof_names().congr_constructor.clone();

        let mut rules = String::new();
        for (i, ty) in types.iter().enumerate() {
            if !ty.is_eq_sort() {
                continue;
            }
            let ci = child(i);
            let leader = format!("c{i}_leader_");
            let uf_name = self.uf_name(ty.name());
            let (query_view, view_prf) = self.query_view_and_get_proof(&fdecl.name, &children_vec);
            let uf_prf = self.fresh_var();
            let new_pf = self.fresh_var();
            let proof_code =
                if fdecl.subtype == FunctionSubtype::Constructor && i == types.len() - 1 {
                    format!("(let {new_pf} ({trans} ({sym} {uf_prf}) {view_prf}))")
                } else {
                    format!("(let {new_pf} ({congr} {view_prf} {i} {uf_prf}))")
                };
            let mut updated = children_vec.clone();
            updated[i] = leader.clone();
            let updated_view = self.update_view(&fdecl.name, &updated, &new_pf);
            let fresh_name = self.egraph.parser.symbol_gen.fresh("rebuild_rule");
            rules.push_str(&format!(
                "(rule ({query_view}
                        (= (values {leader} {uf_prf}) ({uf_name} {ci}))
                        (!= {ci} {leader}))
                     (
                      {proof_code}
                      {updated_view}
                      (delete ({view_name} {children}))
                     )
                      :ruleset {rebuilding_ruleset} :name \"{fresh_name}\" :internal-include-subsumed)\n"
            ));
        }
        self.parse_program(&rules)
    }

    /// Non-proof rebuild: one rule per eq-sort view column (children and the
    /// constructor's eclass/output column alike). The single-key `@UF` has no row
    /// for a canonical (root) node, so a column that is already canonical simply
    /// doesn't match — no self-loops or default-lookups needed. Each rule replaces
    /// ONE column with its leader, re-setting the view row and deleting the stale
    /// one; a row with several stale columns is canonicalized across rebuild
    /// iterations.
    fn rebuilding_rules_fanout(&mut self, fdecl: &ResolvedFunctionDecl) -> Vec<Command> {
        let types = fdecl.resolved_schema.view_types();
        if !types.iter().any(|t| t.is_eq_sort()) {
            return vec![];
        }
        let view_name = self.view_name(&fdecl.name);
        let child = |i: usize| format!("c{i}_");
        let children_vec: Vec<String> = (0..types.len()).map(child).collect();
        let children = format!("{}", ListDisplay(&children_vec, " "));
        let rebuilding_ruleset = self.proof_names().rebuilding_ruleset_name.clone();

        let mut rules = String::new();
        for (i, ty) in types.iter().enumerate() {
            if !ty.is_eq_sort() {
                continue;
            }
            let ci = child(i);
            let leader = format!("c{i}_leader_");
            let uf_name = self.uf_name(ty.name());
            let (query_view, _pf) = self.query_view_and_get_proof(&fdecl.name, &children_vec);
            let mut updated = children_vec.clone();
            updated[i] = leader.clone();
            let updated_view = self.update_view(&fdecl.name, &updated, "()");
            let fresh_name = self.egraph.parser.symbol_gen.fresh("rebuild_rule");
            rules.push_str(&format!(
                "(rule ({query_view}
                        (= {leader} ({uf_name} {ci}))
                        (!= {ci} {leader}))
                     (
                      {updated_view}
                      (delete ({view_name} {children}))
                     )
                      :ruleset {rebuilding_ruleset} :name \"{fresh_name}\" :internal-include-subsumed)\n"
            ));
        }
        self.parse_program(&rules)
    }

    /// Rebuild rules for a proof-mode functional-dependency constructor view
    /// `(children) -> (eclass, proof)`, fanned out per eq-sort column (like the term
    /// path): the single-key `@UF` has no row for a canonical column, so a combined
    /// all-columns join would stall when any column is already canonical.
    ///
    /// - A CHILD update (`ci -> leader`, `uf_pf : ci = leader`) re-keys the row: `set`
    ///   at the canonicalized children (triggering the congruence `:merge` on collision)
    ///   and `delete` the stale row, with proof `Congr(view_prf, i, uf_pf)`.
    /// - The ECLASS value update (`eclass -> leader`, `uf_pf : eclass = leader`) keeps
    ///   the same key, so it just `set`s the smaller eclass (the view `:merge` keeps the
    ///   min) with proof `Trans(Sym uf_pf, view_prf) : leader = f(children)` — no delete.
    fn rebuilding_rules_fd(&mut self, fdecl: &ResolvedFunctionDecl) -> Vec<Command> {
        let types = fdecl.resolved_schema.view_types();
        // The last column is the eclass (output); the rest are children (keys).
        let n = types.len();
        let child = |i: usize| format!("c{i}_");
        let children_vars: Vec<String> = (0..n - 1).map(child).collect();
        let child_types = &types[..n - 1];
        let eclass_type = &types[n - 1];

        let view_name = self.view_name(&fdecl.name);
        let children_str = ListDisplay(&children_vars, " ");
        let rebuilding_ruleset = self.proof_names().rebuilding_ruleset_name.clone();
        let trans = self.proof_names().eq_trans_constructor.clone();
        let congr = self.proof_names().congr_constructor.clone();
        let sym = self.proof_names().eq_sym_constructor.clone();

        let mut rules = String::new();
        // One rule per eq-sort child (re-keys the row via delete + set).
        for (i, ty) in child_types.iter().enumerate() {
            if !ty.is_eq_sort() {
                continue;
            }
            let ci = child(i);
            let leader = format!("c{i}_leader_");
            let uf_name = self.uf_name(ty.name());
            let (query_view, eclass_var, view_prf) =
                self.query_fd_view(&fdecl.name, &children_vars);
            let uf_prf = self.fresh_var();
            let new_pf = self.fresh_var();
            let mut updated = children_vars.clone();
            updated[i] = leader.clone();
            let updated_view = self.update_fd_view(&fdecl.name, &updated, &eclass_var, &new_pf);
            let fresh_name = self.egraph.parser.symbol_gen.fresh("rebuild_rule");
            rules.push_str(&format!(
                "(rule ({query_view}
                        (= (values {leader} {uf_prf}) ({uf_name} {ci}))
                        (!= {ci} {leader}))
                     (
                      (let {new_pf} ({congr} {view_prf} {i} {uf_prf}))
                      {updated_view}
                      (delete ({view_name} {children_str}))
                     )
                      :ruleset {rebuilding_ruleset} :name \"{fresh_name}\" :internal-include-subsumed)\n"
            ));
        }
        // One rule for the eclass value (same key, `set` only; the view merge keeps the min).
        let eclass_uf_name = self.uf_name(eclass_type.name());
        let (query_view, eclass_var, view_prf) = self.query_fd_view(&fdecl.name, &children_vars);
        let eclass_leader = self.fresh_var();
        let uf_prf = self.fresh_var();
        let new_pf = self.fresh_var();
        let updated_view =
            self.update_fd_view(&fdecl.name, &children_vars, &eclass_leader, &new_pf);
        let fresh_name = self.egraph.parser.symbol_gen.fresh("rebuild_rule");
        rules.push_str(&format!(
            "(rule ({query_view}
                    (= (values {eclass_leader} {uf_prf}) ({eclass_uf_name} {eclass_var}))
                    (!= {eclass_var} {eclass_leader}))
                 (
                  (let {new_pf} ({trans} ({sym} {uf_prf}) {view_prf}))
                  {updated_view}
                 )
                  :ruleset {rebuilding_ruleset} :name \"{fresh_name}\" :internal-include-subsumed)\n"
        ));
        self.parse_program(&rules)
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
    /// [`Self::rebuilding_rules_fanout`] (the single-key `@UF` has no row for a
    /// canonical node, so a per-column lookup only fires when there is work). In proof
    /// mode `@UF` is a `(S) -> (S, Proof)` tuple; its proof is unused for subsumed rows.
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
        let proofs_enabled = self.egraph.proof_state.proofs_enabled;

        let mut rules = String::new();
        for (i, ty) in input.iter().enumerate() {
            if !ty.is_eq_sort() {
                continue;
            }
            let ci = child(i);
            let leader = format!("c{i}_leader_");
            let uf_name = self.uf_name(ty.name());
            let uf_lookup = if proofs_enabled {
                let proof_var = self.fresh_var();
                format!("(= (values {leader} {proof_var}) ({uf_name} {ci}))")
            } else {
                format!("(= {leader} ({uf_name} {ci}))")
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
                proof
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
                            // In proof mode a constructor view is the FD tuple
                            // `(children) -> (eclass, proof)`: bind the eclass (`fv`) and proof from
                            // the tuple. Without proofs it's the `(children eclass) -> Unit` form.
                            if self.egraph.proof_state.proofs_enabled {
                                res.push(format!(
                                    "(= (values {fv} {view_proof_var}) ({view_name} {args_str}))"
                                ));
                            } else {
                                res.push(format!(
                                    "(= {view_proof_var} ({view_name} {args_str} {fv}))"
                                ));
                            }
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
                        } else if specialized_primitive.output().is_eq_sort()
                            || specialized_primitive.output().is_eq_container_sort()
                        {
                            let term_proof_name =
                                self.term_proof_name(specialized_primitive.output().name());
                            let fresh_proof = self.fresh_var();
                            action_lookups
                                .push(format!("(let {fresh_proof} ({term_proof_name} {fv}))"));
                            fresh_proof
                        } else {
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

    /// Update the view with the given arguments.
    /// The arguments include the eclass for constructors.
    /// View is always a function (returning Proof or Unit).
    fn update_view(&mut self, fname: &str, args: &[String], proof: &str) -> String {
        let view_name = self.view_name(fname);
        let view_update = format!("(set ({view_name} {}) {proof})", ListDisplay(args, " "));
        if let Some((current_name, input_arity)) =
            self.egraph.proof_state.merge_current.get(fname).cloned()
            && args.len() == input_arity + 1
        {
            let inputs = ListDisplay(&args[..input_arity], " ");
            let output = &args[input_arity];
            return format!("{view_update}\n(set ({current_name} {inputs}) {output})");
        }
        view_update
    }

    /// Write a row into the proof-mode functional-dependency view
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
        format!(
            "(set ({view_name} {}) (values {eclass} {proof}))",
            ListDisplay(children, " ")
        )
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

        let args_with_fv = if func_type.subtype == FunctionSubtype::Constructor {
            let mut a = args.to_vec();
            a.push(fv.clone());
            a
        } else {
            args.to_vec()
        };

        let (proof_str, view_proof_var) = if self.egraph.proof_state.proofs_enabled {
            let to_ast = self.fname_to_ast_name(&func_type.name);
            let rule_constructor = &self.proof_names().rule_constructor;
            let fiat_constructor = &self.proof_names().fiat_constructor;

            let proof = match justification {
                Justification::Rule(rule_name, rule_proof) => {
                    format!(
                        "({rule_constructor} \"{rule_name}\" {rule_proof} ({to_ast} {fv}) ({to_ast} {fv}))",
                    )
                }
                Justification::Fiat => {
                    format!("({fiat_constructor} ({to_ast} {fv}) ({to_ast} {fv}))",)
                }
                Justification::Merge(fn_name, p1, p2) => {
                    let merge_constructor = &self.proof_names().merge_fn_constructor;
                    format!("({merge_constructor} \"{fn_name}\" {p1} {p2} ({to_ast} {fv}))",)
                }
                Justification::Proof(existing_proof) => existing_proof.clone(),
            };

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
        if func_type.subtype == FunctionSubtype::Constructor
            && self.egraph.proof_state.proofs_enabled
        {
            // FD view: children are the key, the fresh term is the eclass value.
            res.push(self.update_fd_view(&func_type.name, args, &fv, &view_proof_var));
        } else {
            res.push(self.update_view(&func_type.name, &args_with_fv, &view_proof_var));
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

    /// Query the proof-mode functional-dependency view by its `children` key, binding fresh
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
                            ListDisplay(args, " ")
                        ));
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
        let proof = Justification::Rule(rule.name.clone(), proof_var.clone());
        let reads_in_rhs = !action_lookups.is_empty();
        // The looked-up proofs feed `proof_str`, so bind them first.
        let action_lookups_str = ListDisplay(&action_lookups, "\n                    ");
        let proof_var_binding = if self.egraph.proof_state.proofs_enabled {
            format!(
                "{action_lookups_str}
                 (let {proof_var}
                          {proof_str})"
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
        // Both term and proof modes use a single self-referential `@UF` whose native
        // `:merge` subsumes `single_parent` and makes `uf_function_index` dead, so only
        // `path_compress` (flattening cross-key chains) remains as UF maintenance.
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

    fn term_encode_command(&mut self, command: &ResolvedNCommand, res: &mut Vec<Command>) {
        log::trace!("Term encoding for {command}");
        match &command {
            ResolvedNCommand::Sort {
                span,
                name,
                presort_and_args,
                unionable,
                ..
            } => {
                let uf_name = self.uf_name(name);
                let proof_func = if self.egraph.proof_state.proofs_enabled {
                    Some(self.term_proof_name(name))
                } else {
                    None
                };
                res.push(Command::Sort {
                    span: span.clone(),
                    name: name.clone(),
                    presort_and_args: presort_and_args.clone(),
                    uf: Some(uf_name),
                    proof_func,
                    proof_ctors: None,
                    unionable: *unionable,
                });
                res.extend(self.declare_sort(name));
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
                self.term_encode_command(cmd, res);
                let last = res.pop().unwrap();
                res.push(Command::Fail(span.clone(), Box::new(last)));
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
            | ResolvedNCommand::Input { .. }
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
    }

    pub(crate) fn add_term_encoding_helper(
        &mut self,
        program: Vec<ResolvedNCommand>,
    ) -> Vec<Command> {
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
            self.term_encode_command(&command, &mut res);

            // run rebuilding after every command except a few
            if let ResolvedNCommand::Function(..)
            | ResolvedNCommand::NormRule { .. }
            | ResolvedNCommand::Sort { .. } = &command
            {
            } else {
                res.push(Command::RunSchedule(self.rebuild()));
            }
        }

        res
    }
}

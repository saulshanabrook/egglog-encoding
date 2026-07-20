#[doc = include_str!("proof_encoding.md")]
use crate::proofs::proof_checker::is_container_side_condition;
use crate::proofs::proof_encoding_helpers::{EncodingNames, Justification};
use crate::typechecking::FuncType;
use crate::*;

/// Deterministic name of a sort's auxiliary union-find `@UF-Aux-<Sort>`, which
/// maps a *natural* (as-built) e-class id to its canonical dedup id plus the
/// connector proof `natural = canonical`. Used only for container elements: a
/// container is built over natural element ids (so its term-proof extracts the
/// syntactic shape), and the container rebuild reads `UF-Aux` (in addition to
/// the main `UF`) to canonicalize those elements and thread the connector proof.
/// Deterministic (not a fresh symbol) so the rebuild can recompute it.
pub(crate) fn uf_aux_name(sort: &str) -> String {
    format!("@UF-Aux-{sort}")
}

/// Term-construction side channel (proof mode): maps a built term's canonical
/// e-class var to `(natural e-class var, connector proof var)`, where the
/// connector proves `natural = canonical`. A parent term reads its children's
/// entries to build the natural term and its `Congr` connector; the root `union`
/// and a global's `global_value_proof` read it to anchor on the natural form.
///
/// Scoped to a single generated program — a rule, a top-level action, or a
/// custom function's merge body — so each such scope threads a fresh, local map
/// through the action/term builders rather than sharing one long-lived field.
pub(crate) type NatConn = HashMap<String, (String, Option<String>)>;

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
    /// Names of custom (non-constructor) functions that have a `:merge`, so their
    /// encoded view takes the FD pair-valued shape `(children) -> (eclass, proof)`
    /// (the user merge runs in that view's own `:merge`).
    ///
    /// Needed only because query/action sites see a [`FuncType`] (name, subtype,
    /// sorts) that reveals a constructor but *not* whether a `Custom` function has
    /// a `:merge`. We record the merge-having customs here when their view is
    /// declared, so [`Self::func_type_is_fd_view`] can route them as FD from the
    /// name alone. Constructors are always FD (known from the subtype) and so are
    /// not recorded here.
    pub fd_custom_funcs: HashSet<String>,
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
            fd_custom_funcs: HashSet::default(),
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
    /// Emits any proof-relation mints onto `stmts` and returns the `(set @UF ...)`
    /// action; the caller must push the mints (already on `stmts`) before it.
    pub(crate) fn union(
        &mut self,
        stmts: &mut Vec<String>,
        type_name: &str,
        lhs: &str,
        rhs: &str,
        justification: &Justification,
        nat_conn: &NatConn,
    ) -> String {
        let uf_name = self.uf_name(type_name);
        let smaller = format!("(ordering-min {lhs} {rhs})");
        let larger = format!("(ordering-max {lhs} {rhs})");
        // `@UF : (S) -> (S, {Unit|Proof})` is keyed by the larger endpoint; its
        // `:merge` resolves conflicting parents. The second column carries a proof
        // `larger = smaller` (`()` in term mode).
        if !self.egraph.proof_state.proofs_enabled {
            return format!("(set ({uf_name} {larger}) (values {smaller} ()))");
        }

        let to_ast_constructor = self
            .proof_names()
            .sort_to_ast_constructor
            .get(type_name)
            .unwrap()
            .clone();
        let proof_sort = self.proof_sort();
        let ast_sort = self.proof_names().ast_sort.clone();
        let rule_constructor = self.proof_names().rule_constructor.clone();
        let fiat_constructor = self.proof_names().fiat_constructor.clone();

        // Natural id + connector (`natural = deduped`) for each operand, if it was
        // a canonicalized constructor term. Leaves / body matches have neither.
        let lhs_info = nat_conn.get(lhs).cloned();
        let rhs_info = nat_conn.get(rhs).cloned();
        let lhs_conn = lhs_info.as_ref().and_then(|(_, c)| c.clone());
        let rhs_conn = rhs_info.as_ref().and_then(|(_, c)| c.clone());

        // No canonicalized side: build the edge proof directly over the deduped
        // e-classes (their ASTs are stable here) — the original behaviour.
        if lhs_conn.is_none() && rhs_conn.is_none() {
            let proof = match justification {
                Justification::Rule(rule_name, proof_list) => {
                    let a_larger = self.mint(stmts, &to_ast_constructor, &larger, &ast_sort);
                    let a_smaller = self.mint(stmts, &to_ast_constructor, &smaller, &ast_sort);
                    self.mint(
                        stmts,
                        &rule_constructor,
                        &format!("{rule_name} {proof_list} {a_larger} {a_smaller}"),
                        &proof_sort,
                    )
                }
                Justification::Fiat => {
                    let a_larger = self.mint(stmts, &to_ast_constructor, &larger, &ast_sort);
                    let a_smaller = self.mint(stmts, &to_ast_constructor, &smaller, &ast_sort);
                    self.mint(
                        stmts,
                        &fiat_constructor,
                        &format!("{a_larger} {a_smaller}"),
                        &proof_sort,
                    )
                }
                Justification::MergeIdx(..) | Justification::MergeRow(..) => panic!(
                    "Merge functions do not include union actions, so proof should not be by merge"
                ),
            };
            return format!("(set ({uf_name} {larger}) (values {smaller} {proof}))");
        }

        // A canonicalized operand's deduped e-class may already be unioned with a
        // differently-shaped term, so its AST floats. Build the base equality over
        // the *natural* forms (ASTs pinned to the enode the rule built), then route
        // each deduped e-class to a shared natural form and orient the edge to
        // `larger = smaller` with proof-of-max/min.
        let nat_of = |info: &Option<(String, Option<String>)>, dedup: &str| {
            info.as_ref()
                .map(|(n, _)| n.clone())
                .unwrap_or_else(|| dedup.to_string())
        };
        let lhs_nat = nat_of(&lhs_info, lhs);
        let rhs_nat = nat_of(&rhs_info, rhs);

        let base_proof = {
            let a_lhs = self.mint(stmts, &to_ast_constructor, &lhs_nat, &ast_sort);
            let a_rhs = self.mint(stmts, &to_ast_constructor, &rhs_nat, &ast_sort);
            match justification {
                Justification::Rule(rule_name, proof_list) => self.mint(
                    stmts,
                    &rule_constructor,
                    &format!("{rule_name} {proof_list} {a_lhs} {a_rhs}"),
                    &proof_sort,
                ),
                Justification::Fiat => self.mint(
                    stmts,
                    &fiat_constructor,
                    &format!("{a_lhs} {a_rhs}"),
                    &proof_sort,
                ),
                Justification::MergeIdx(..) | Justification::MergeRow(..) => panic!(
                    "Merge functions do not include union actions, so proof should not be by merge"
                ),
            }
        };

        let sym = self.proof_names().eq_sym_constructor.clone();
        let trans = self.proof_names().eq_trans_constructor.clone();
        // Route both operands to a shared *natural* form, then orient to the
        // `larger = smaller` UF edge with proof-of-max/min. The shared form is the
        // canonicalized side's natural (pinned AST), so the Trans goes through it
        // rather than through the deduped e-class.
        let (lhs_to_shared, rhs_to_shared) = if let Some(rc) = &rhs_conn {
            let lhs_to = if let Some(lc) = &lhs_conn {
                let sym_lc = self.mint(stmts, &sym, lc, &proof_sort);
                self.mint(
                    stmts,
                    &trans,
                    &format!("{sym_lc} {base_proof}"),
                    &proof_sort,
                )
            } else {
                base_proof.clone()
            };
            let rhs_to = self.mint(stmts, &sym, rc, &proof_sort);
            (lhs_to, rhs_to)
        } else {
            let lc = lhs_conn.as_ref().unwrap();
            let lhs_to = self.mint(stmts, &sym, lc, &proof_sort);
            let rhs_to = self.mint(stmts, &sym, &base_proof, &proof_sort);
            (lhs_to, rhs_to)
        };
        let max_pf = self.fresh_var();
        stmts.push(format!(
            "(let {max_pf} (proof-of-max {lhs} {lhs_to_shared} {rhs} {rhs_to_shared}))"
        ));
        let min_pf = self.fresh_var();
        stmts.push(format!(
            "(let {min_pf} (proof-of-min {lhs} {lhs_to_shared} {rhs} {rhs_to_shared}))"
        ));
        let sym_min = self.mint(stmts, &sym, &min_pf, &proof_sort);
        let edge = self.mint(stmts, &trans, &format!("{max_pf} {sym_min}"), &proof_sort);
        format!("(set ({uf_name} {larger}) (values {smaller} {edge}))")
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
            // `@UF-Aux-<Sort>`: natural -> (canonical, connector proof). Written
            // only for container elements; the container rebuild reads it. `:merge
            // old` keeps the first edge (each natural is minted once).
            let aux_name = uf_aux_name(sort_name);
            format!(
                "{add_to_ast_code}
                 (function {term_proof_name} ({sort_name}) {proof_type} :merge old :internal-hidden)
                 (function {aux_name} ({sort_name}) ({sort_name} {proof_type}) :merge (values old0 old1) :internal-hidden)"
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
            let proof_sort = self.proof_sort();
            let mut mints = vec![];
            let sym_pf = self.mint(&mut mints, &sym, "hi_pf_", &proof_sort);
            let displaced_pf =
                self.mint(&mut mints, &trans, &format!("{sym_pf} lo_pf_"), &proof_sort);
            let mints_str = mints.join("\n                  ");
            format!(
                "((let hi_pf_ (proof-of-max old0 old1 new0 new1))
                  (let lo_pf_ (proof-of-min old0 old1 new0 new1))
                  {mints_str}
                  (set ({uf_name} (ordering-max old0 new0))
                       (values (ordering-min old0 new0) {displaced_pf}))
                  (values (ordering-min old0 new0) lo_pf_))"
            )
        } else {
            format!(
                "((set ({uf_name} (ordering-max old0 new0)) (values (ordering-min old0 new0) ()))
                  (values (ordering-min old0 new0) ()))"
            )
        };
        // path compression: a->b (pb: a=b), b->c (pc: b=c)  =>  a->c (Trans pb pc: a=c)
        let (compressed_proof_lets, compressed_proof) = if proofs {
            let trans = self.proof_names().eq_trans_constructor.clone();
            let proof_sort = self.proof_sort();
            let mut mints = vec![];
            let pf = self.mint(&mut mints, &trans, &format!("{pb} {pc}"), &proof_sort);
            (mints.join("\n                    "), pf)
        } else {
            (String::new(), "()".to_string())
        };

        let code = format!(
            "{proof_tables}
             (function {uf_name} ({sort_name}) ({sort_name} {proof_type}) :merge {uf_merge} :unextractable :internal-hidden :internal-identity-vals 1)
             (rule ((= (values {b} {pb}) ({uf_name} {a}))
                    (= (values {c} {pc}) ({uf_name} {b}))
                    (!= {b} {c}))
                  ({compressed_proof_lets}
                   (set ({uf_name} {a}) (values {c} {compressed_proof})))
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

        // An FD tuple view (constructors + custom functions with a `:merge`) is keyed
        // by children only, so match its value tuple to delete/subsume by key (the
        // bridge re-reads every value column when subsuming a tuple-output view).
        if self.is_fd_view(fdecl) {
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

    /// Whether `fdecl`'s view uses the FD pair-valued shape `(children) ->
    /// (values output proof)`, keyed on children only. Constructors always do; a
    /// custom function does iff it has a `:merge` (its user merge runs in the
    /// view's own `:merge`). `:no-merge` customs keep the all-column view.
    fn is_fd_view(&self, fdecl: &ResolvedFunctionDecl) -> bool {
        fdecl.subtype == FunctionSubtype::Constructor
            || (fdecl.subtype == FunctionSubtype::Custom && fdecl.merge.is_some())
            // Globals (`:internal-let` no-arg functions): use the FD pair-valued
            // view `() -> (val, proof)` (like a constructor) so a global can be read
            // as `(@xView)` in queries and actions. The default `:no-merge`
            // all-column view is keyed by the value and can't be read in an action.
            || self.is_encoded_global(fdecl)
    }

    /// A global is a `:internal-let` function; in the encoding it is treated like a
    /// nullary constructor (FD view, congruence merge, readable value+proof) rather
    /// than a `:no-merge` custom function.
    fn is_encoded_global(&self, fdecl: &ResolvedFunctionDecl) -> bool {
        fdecl.internal_let
    }

    /// Whether the function's output value *is* its e-class, so the term relation
    /// needs no separate output column and the view is the congruence FD
    /// `(children) -> (eclass, proof)`. Holds for constructors and encoded globals.
    fn output_is_eclass(&self, fdecl: &ResolvedFunctionDecl) -> bool {
        fdecl.subtype == FunctionSubtype::Constructor || self.is_encoded_global(fdecl)
    }

    /// Like [`Self::is_fd_view`], for a resolved [`FuncType`] at an action/query
    /// site. Constructors are always FD; custom FD functions are recorded in
    /// `fd_custom_funcs` when their view is declared.
    fn func_type_is_fd_view(&self, func_type: &FuncType) -> bool {
        func_type.subtype == FunctionSubtype::Constructor
            || self
                .egraph
                .proof_state
                .fd_custom_funcs
                .contains(&func_type.name)
    }

    /// The `:merge` expression for a custom function's FD pair-valued view
    /// `(children) -> (values output proof)`. On a children-key collision it runs
    /// the user's merge body ONCE (unlike a constructor's congruence, it performs
    /// no `@UF` union): `old`/`new` bind to the two colliding output columns
    /// (`old0`/`new0`) and the carried view proofs to `old1`/`new1`. The result is
    /// `(values merged rowproof)`, where `merged` is the (canonically-minted) merge
    /// body and `rowproof` is a children-free `MergeRow` (`()` in term mode).
    ///
    /// Doing the merge here, rather than in a separate rule + `current` helper,
    /// avoids computing it twice (which minted over-merged extra term rows).
    fn custom_view_merge(&mut self, fdecl: &ResolvedFunctionDecl) -> String {
        // `nat_conn` is scoped to this merge body; the body mints subterms via
        // `add_term_and_view`, which threads it.
        let mut nat_conn = NatConn::default();
        let name = fdecl.name.clone();
        let merge = fdecl
            .merge
            .as_ref()
            .expect("custom FD view requires a :merge");

        let mut body_code = vec![];
        let mut idx = 0usize;
        let merged = self.instrument_merge_body(
            &merge.result,
            &mut body_code,
            &name,
            &mut idx,
            &mut nat_conn,
        );
        let row_proof = if self.egraph.proof_state.proofs_enabled {
            let fresh = self.term_proof_for_justification(
                &mut body_code,
                "",
                "",
                &Justification::MergeRow(name.clone(), "old1".to_string(), "new1".to_string()),
            );
            // Keep the proof column stable: when the merged output equals a
            // colliding premise's output (as with idempotent `min`/`max`/... merges
            // that keep one input), reuse that premise's existing proof so the row
            // stays value-identical and the merge saturates. Otherwise the fresh
            // `MergeRow` justifies the newly-computed output. (`old0`/`new0` are the
            // premise outputs, `old1`/`new1` their carried view proofs.)
            format!("(select-eq {merged} old0 old1 (select-eq {merged} new0 new1 {fresh}))")
        } else {
            "()".to_string()
        };
        let value = format!("(values {merged} {row_proof})");
        if body_code.is_empty() {
            value
        } else {
            format!("({}\n{value})", body_code.join("\n"))
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
        let delete_rule = self.delete_and_subsume(fdecl);
        let to_delete_name = self.delete_name(&fdecl.name);
        let subsumed_name = self.subsumed_name(&fdecl.name);
        // True when the function's output value *is* its eclass, so the term
        // relation needs no separate output column and the view is the
        // congruence FD `(children) -> (eclass, proof)`. Holds for constructors
        // (output is the built term) and for encoded globals (a nullary Custom
        // `:internal-let` function whose output is the term it aliases): both
        // give term row `(children eclass)`. A Custom function returning a
        // distinct value (e.g. `-> i64`) is false — it keeps an output column
        // plus a fresh eclass column.
        let output_is_eclass = self.output_is_eclass(fdecl);
        let term_sorts = format!(
            "{in_sorts} {}",
            if output_is_eclass {
                "".to_string()
            } else {
                schema.output().to_string()
            }
        );

        let view_sort = if output_is_eclass {
            schema.output().clone()
        } else {
            fresh_sort.clone()
        };
        let to_ast_view_sort = self.add_to_ast(&view_sort);

        // Record the term's eclass sort (its `view_sort`) so the creation site
        // in `add_term_and_view` knows which `get-fresh!` to mint from. Needed in
        // both term and proof mode now that terms are minted, not constructed.
        self.egraph
            .proof_state
            .proof_names
            .fn_to_term_sort
            .insert(name.clone(), view_sort.clone());
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
        // The view carries the user operation's extraction cost (the term table
        // is a relation and can't carry `:cost`); the extractor reads it here.
        if let Some(cost) = fdecl.cost {
            view_flags.push_str(&format!(" :internal-cost {cost}"));
        }
        // An FD view is a functional-dependency tuple `(children) -> (output,
        // {Unit|Proof})` keyed on children only. Constructors always use it (their
        // `:merge` resolves congruence: keep the smaller eclass, union the two in
        // the sort's `@UF`). Custom functions with a `:merge` also use it (their
        // `:merge` runs the user merge — no union). `:no-merge` functions never
        // reach here: they are rejected up front by `command_supports_proof_encoding`.
        let fd_view = self.is_fd_view(fdecl);
        if fd_view && fdecl.subtype == FunctionSubtype::Custom {
            self.egraph.proof_state.fd_custom_funcs.insert(name.clone());
        }
        let view_decl = if output_is_eclass {
            // Two rows conflicting on the same children are congruent: keep the
            // smaller eclass and union the two eclasses in the sort's `@UF`. In
            // proof mode the view proofs (`eclass = f(children)`) compose into the
            // union edge's proof `Trans hi_pf_ (Sym lo_pf_) : larger = smaller`.
            let congruence_merge = if self.proofs_enabled() {
                let uf_name = self.uf_name(schema.output());
                let trans = self.proof_names().eq_trans_constructor.clone();
                let sym = self.proof_names().eq_sym_constructor.clone();
                let proof_sort = self.proof_sort();
                let mut mints = vec![];
                let sym_pf = self.mint(&mut mints, &sym, "lo_pf_", &proof_sort);
                let union_pf =
                    self.mint(&mut mints, &trans, &format!("hi_pf_ {sym_pf}"), &proof_sort);
                let mints_str = mints.join("\n                      ");
                format!(
                    "((let hi_pf_ (proof-of-max old0 old1 new0 new1))
                      (let lo_pf_ (proof-of-min old0 old1 new0 new1))
                      {mints_str}
                      (set ({uf_name} (ordering-max old0 new0))
                           (values (ordering-min old0 new0) {union_pf}))
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
        } else if fd_view {
            // Custom function with a `:merge`: FD pair-valued view keyed on children;
            // the value is `(output {Unit|Proof})` and the `:merge` runs the user
            // merge once (see `custom_view_merge`). No `@UF` union.
            let custom_merge = self.custom_view_merge(fdecl);
            format!(
                "(function {view_name} ({in_sorts}) ({out_type} {proof_type}) :merge {custom_merge} :internal-term-constructor {name}{view_flags} :internal-identity-vals 1)"
            )
        } else {
            // The only remaining case is a `:no-merge` function, which
            // `command_supports_proof_encoding` rejects before encoding.
            unreachable!("`:no-merge` functions are not encoded (rejected up front)")
        };
        self.parse_program(&format!(
            "
            (sort {fresh_sort})
            {to_ast_view_sort}
            (function {name} ({term_sorts} {view_sort}) Unit :no-merge :internal-hidden)
            {view_decl}
            (constructor {to_delete_name} ({in_sorts}) {fresh_sort} :internal-hidden)
            (constructor {subsumed_name} ({in_sorts}) {fresh_sort} :internal-hidden)
            {delete_rule}",
        ))
    }

    /// Rebuild rules that keep a table's view canonical, fanned out one rule per
    /// rebuildable column (a canonical column has no `@UF` row, so it simply
    /// doesn't match). A stale column is replaced by its `@UF` leader (eq-sorts)
    /// or its rebuilt container.
    ///
    /// An FD view `(children) -> (output, {Unit|Proof})` (constructors and custom
    /// functions with a `:merge`) re-keys the row for a child update — `set` at the
    /// canonicalized children, then `delete`. A collision on the new children key
    /// runs the view's `:merge` (congruence for constructors, the user merge for
    /// customs — the correct semantics for two applications whose children became
    /// equal). For a constructor's eclass column we additionally re-`set` the same
    /// key with the canonicalized eclass (congruence keeps the min); a custom
    /// function's output column is NOT canonicalized this way — re-setting it would
    /// wrongly re-run the user merge — so that block is constructor-only. A
    /// `:no-merge` custom's all-key view re-keys every column. In proof mode each
    /// rule composes the updated view proof, and a container update records the
    /// rebuilt container's `<CSort>Proof`.
    fn rebuilding_rules(&mut self, fdecl: &ResolvedFunctionDecl) -> Vec<Command> {
        // FD views (constructors + custom-with-merge) key by children; `:no-merge`
        // customs use the all-key view.
        let fd = self.is_fd_view(fdecl);
        let proofs = self.proofs_enabled();
        // A global's output *is* its e-class (like a constructor's), so it takes the
        // e-class rebuild below (union-tracking) — not the custom-output rebuild
        // (congruence), which would emit a nonsensical `Congr` on its nullary term.
        let output_is_eclass = self.output_is_eclass(fdecl);
        let types = fdecl.resolved_schema.view_types();
        let n = types.len();
        let child = |i: usize| format!("c{i}_");
        // Key columns of the view row: children for FD views, every column otherwise.
        let n_keys = if fd { n - 1 } else { n };
        let key_vars: Vec<String> = (0..n_keys).map(child).collect();
        let view_name = self.view_name(&fdecl.name);
        let keys_str = format!("{}", ListDisplay(&key_vars, " "));
        let rebuilding_ruleset = self.proof_names().rebuilding_ruleset_name.clone();

        let mut rules = String::new();
        // One rule per rebuildable key column (re-keys the row via set + delete).
        for (i, ty) in types[..n_keys].iter().enumerate() {
            let is_container = ty.is_eq_container_sort();
            if !is_container && !ty.is_eq_sort() {
                continue;
            }
            let ci = child(i);
            let canon = format!("c{i}_canon_");
            let (query_view, eclass_var, view_prf) = if fd {
                let (q, e, p) = self.query_fd_view(&fdecl.name, &key_vars);
                (q, Some(e), p)
            } else {
                let (q, p) = self.query_view_and_get_proof(&fdecl.name, &key_vars);
                (q, None, p)
            };
            // Canonicalize the column with the container rebuild primitive or a `@UF`
            // lookup, and build the proof pieces. Container-reading rules are `:naive`
            // (the primitive reads `@UF` tables the rule doesn't join on).
            let (canon_fact, naive, proof_lets, pf_arg, cproof_set) = if is_container {
                let value_prim = self.ensure_container_rebuild(ty);
                let canon_fact = format!("(= {canon} ({value_prim} {ci}))");
                if proofs {
                    let congr = self.proof_names().congr_constructor.clone();
                    let trans = self.proof_names().eq_trans_constructor.clone();
                    let sym = self.proof_names().eq_sym_constructor.clone();
                    let proof_sort = self.proof_sort();
                    let proof_prim = self.ensure_container_rebuild_proof(ty);
                    let rebuild_pf = self.fresh_var();
                    let cproof = self.term_proof_name(ty.name());
                    // proof_lets: bind the container rebuild proof, then mint the congr proof.
                    let mut lets = vec![format!("(let {rebuild_pf} ({proof_prim} {ci}))")];
                    let new_pf = self.mint(
                        &mut lets,
                        &congr,
                        &format!("{view_prf} {i} {rebuild_pf}"),
                        &proof_sort,
                    );
                    // cproof_set: mint (Sym rebuild_pf), (Trans .. rebuild_pf), then record it.
                    let mut cproof_stmts = vec![];
                    let sym_pf = self.mint(&mut cproof_stmts, &sym, &rebuild_pf, &proof_sort);
                    let trans_pf = self.mint(
                        &mut cproof_stmts,
                        &trans,
                        &format!("{sym_pf} {rebuild_pf}"),
                        &proof_sort,
                    );
                    cproof_stmts.push(format!("(set ({cproof} {canon}) {trans_pf})"));
                    (
                        canon_fact,
                        ":naive ",
                        lets.join("\n                             "),
                        new_pf,
                        cproof_stmts.join("\n                             "),
                    )
                } else {
                    (
                        canon_fact,
                        ":naive ",
                        String::new(),
                        "()".to_string(),
                        String::new(),
                    )
                }
            } else {
                let uf_name = self.uf_name(ty.name());
                let uf_prf = self.fresh_var();
                let canon_fact = format!("(= (values {canon} {uf_prf}) ({uf_name} {ci}))");
                if proofs {
                    let congr = self.proof_names().congr_constructor.clone();
                    let proof_sort = self.proof_sort();
                    let mut lets = vec![];
                    let new_pf = self.mint(
                        &mut lets,
                        &congr,
                        &format!("{view_prf} {i} {uf_prf}"),
                        &proof_sort,
                    );
                    (
                        canon_fact,
                        "",
                        lets.join("\n                             "),
                        new_pf,
                        String::new(),
                    )
                } else {
                    (
                        canon_fact,
                        "",
                        String::new(),
                        "()".to_string(),
                        String::new(),
                    )
                }
            };
            let mut updated = key_vars.clone();
            updated[i] = canon.clone();
            let updated_view = match &eclass_var {
                Some(eclass) => self.update_fd_view(&fdecl.name, &updated, eclass, &pf_arg),
                None => self.update_view(&fdecl.name, &updated, &pf_arg),
            };
            let fresh_name = self.egraph.parser.symbol_gen.fresh("rebuild_rule");
            rules.push_str(&format!(
                "(rule ({query_view}
                        {canon_fact}
                        (!= {ci} {canon}))
                     (
                      {proof_lets}
                      {updated_view}
                      {cproof_set}
                      (delete ({view_name} {keys_str}))
                     )
                      :ruleset {rebuilding_ruleset} {naive}:name \"{fresh_name}\" :internal-include-subsumed)\n"
            ));
        }
        // Constructor FD views: one rule for the eclass value (same key, `set` only;
        // the congruence `:merge` keeps the min). This is NOT done for custom-with-
        // merge FD views — their output column is not a unioned eclass to keep
        // canonical, and re-`set`ting it would wrongly re-run the user merge. A stale
        // custom output is resolved instead by `find_canonical` during extraction.
        if fd && output_is_eclass {
            let eclass_uf_name = self.uf_name(types[n - 1].name());
            let (query_view, eclass_var, view_prf) = self.query_fd_view(&fdecl.name, &key_vars);
            let eclass_canon = self.fresh_var();
            let uf_prf = self.fresh_var();
            let (proof_lets, pf_arg) = if proofs {
                let trans = self.proof_names().eq_trans_constructor.clone();
                let sym = self.proof_names().eq_sym_constructor.clone();
                let proof_sort = self.proof_sort();
                let mut lets = vec![];
                let sym_pf = self.mint(&mut lets, &sym, &uf_prf, &proof_sort);
                let new_pf = self.mint(
                    &mut lets,
                    &trans,
                    &format!("{sym_pf} {view_prf}"),
                    &proof_sort,
                );
                (lets.join("\n                      "), new_pf)
            } else {
                (String::new(), "()".to_string())
            };
            let updated_view = self.update_fd_view(&fdecl.name, &key_vars, &eclass_canon, &pf_arg);
            let fresh_name = self.egraph.parser.symbol_gen.fresh("rebuild_rule");
            rules.push_str(&format!(
                "(rule ({query_view}
                        (= (values {eclass_canon} {uf_prf}) ({eclass_uf_name} {eclass_var}))
                        (!= {eclass_var} {eclass_canon}))
                     (
                      {proof_lets}
                      {updated_view}
                     )
                      :ruleset {rebuilding_ruleset} :name \"{fresh_name}\" :internal-include-subsumed)\n"
            ));
        }
        // Custom-with-merge FD views with an eq-sort output: canonicalize the output
        // value when it is unioned to a smaller leader. We must NOT re-`set` the same
        // key (that would re-run the user merge on `(out, out_canon)`); instead
        // `delete` the stale row and `set` the canonical one, so the re-`set` sees an
        // empty key and inserts without merging. The row proof is rewritten by
        // congruence at the output position.
        if fd
            && fdecl.subtype == FunctionSubtype::Custom
            && !self.is_encoded_global(fdecl)
            && types[n - 1].is_eq_sort()
            && n_keys == n - 1
        {
            let out_idx = n - 1;
            let out_uf_name = self.uf_name(types[out_idx].name());
            let (query_view, out_var, view_prf) = self.query_fd_view(&fdecl.name, &key_vars);
            let out_canon = self.fresh_var();
            let uf_prf = self.fresh_var();
            let (proof_lets, pf_arg) = if proofs {
                let congr = self.proof_names().congr_constructor.clone();
                let proof_sort = self.proof_sort();
                let mut lets = vec![];
                let new_pf = self.mint(
                    &mut lets,
                    &congr,
                    &format!("{view_prf} {out_idx} {uf_prf}"),
                    &proof_sort,
                );
                (lets.join("\n                      "), new_pf)
            } else {
                (String::new(), "()".to_string())
            };
            let set_canon = self.update_fd_view(&fdecl.name, &key_vars, &out_canon, &pf_arg);
            let fresh_name = self.egraph.parser.symbol_gen.fresh("rebuild_rule");
            rules.push_str(&format!(
                "(rule ({query_view}
                        (= (values {out_canon} {uf_prf}) ({out_uf_name} {out_var}))
                        (!= {out_var} {out_canon}))
                     (
                      {proof_lets}
                      (delete ({view_name} {keys_str}))
                      {set_canon}
                     )
                      :ruleset {rebuilding_ruleset} :name \"{fresh_name}\" :internal-include-subsumed)\n"
            ));
        }
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
            if self.egraph.proof_state.proofs_enabled {
                let eval_constructor = self.proof_names().eval_constructor.clone();
                let proof_sort = self.proof_sort();
                return self.mint(action_lookups, &eval_constructor, "", &proof_sort);
            }
            return "()".to_string();
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

                let view_name = self.view_name(head.name());
                let is_fd = self
                    .egraph
                    .proof_state
                    .fd_custom_funcs
                    .contains(head.name());

                // Query the view and bind the row's existence proof (`proof_var`).
                // A custom-with-merge FD view is keyed by children with value
                // `(output {Unit|Proof})`: bind the output `v` (pair-first) and the
                // proof (pair-second). A `:no-merge` custom's all-key view takes `v`
                // in the key with the proof as its (sole) value.
                let proof_var = self.fresh_var();
                if is_fd {
                    let children_str = ListDisplay(&new_args, " ");
                    res.push(format!(
                        "(= (values {v} {proof_var}) ({view_name} {children_str}))"
                    ));
                } else {
                    let mut all_args = new_args;
                    all_args.push(v.to_string());
                    let args_str = ListDisplay(all_args, " ");
                    res.push(format!("(= {proof_var} ({view_name} {args_str}))"));
                }

                if self.egraph.proof_state.proofs_enabled {
                    let congr = self.proof_names().congr_constructor.clone();
                    let proof_sort = self.proof_sort();
                    let mut proof = proof_var;
                    for (i, arg_proof) in arg_proofs.into_iter().enumerate() {
                        proof = self.mint(
                            action_lookups,
                            &congr,
                            &format!("{proof} {i} {arg_proof}"),
                            &proof_sort,
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
                if self.egraph.proof_state.proofs_enabled {
                    let sym = self.proof_names().eq_sym_constructor.clone();
                    let trans = self.proof_names().eq_trans_constructor.clone();
                    let proof_sort = self.proof_sort();
                    let sym_pf = self.mint(action_lookups, &sym, &p1, &proof_sort);
                    self.mint(
                        action_lookups,
                        &trans,
                        &format!("{sym_pf} {p2}"),
                        &proof_sort,
                    )
                } else {
                    "()".to_string()
                }
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
                    let eval_constructor = self.proof_names().eval_constructor.clone();
                    let proof_sort = self.proof_sort();
                    self.mint(action_lookups, &eval_constructor, "", &proof_sort)
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
                    let lit_sort = literal_sort(lit);
                    let to_ast = self
                        .proof_names()
                        .sort_to_ast_constructor
                        .get(lit_sort.name())
                        .unwrap()
                        .clone();
                    let fiat_constructor = self.proof_names().fiat_constructor.clone();
                    let proof_sort = self.proof_sort();
                    let ast_sort = self.proof_names().ast_sort.clone();
                    let lit_str = format!("{lit}");
                    let a1 = self.mint(action_lookups, &to_ast, &lit_str, &ast_sort);
                    let a2 = self.mint(action_lookups, &to_ast, &lit_str, &ast_sort);
                    self.mint(
                        action_lookups,
                        &fiat_constructor,
                        &format!("{a1} {a2}"),
                        &proof_sort,
                    )
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
                        let lit_sort = resolved_var.sort.name();
                        let to_ast = self
                            .proof_names()
                            .sort_to_ast_constructor
                            .get(lit_sort)
                            .unwrap()
                            .clone();
                        let fiat_constructor = self.proof_names().fiat_constructor.clone();
                        let proof_sort = self.proof_sort();
                        let ast_sort = self.proof_names().ast_sort.clone();
                        let a1 = self.mint(action_lookups, &to_ast, var, &ast_sort);
                        let a2 = self.mint(action_lookups, &to_ast, var, &ast_sort);
                        self.mint(
                            action_lookups,
                            &fiat_constructor,
                            &format!("{a1} {a2}"),
                            &proof_sort,
                        )
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
                        // Constructors and encoded globals both have the FD view
                        // `(children) -> (eclass, proof)`, so the same view read binds
                        // the e-class + proof. Other custom lookups are banned here by
                        // proof normal form.
                        assert!(
                            func_type.subtype == FunctionSubtype::Constructor
                                || self.egraph.type_info.is_global(&func_type.name),
                            "Only constructor (or global) function calls are allowed in fact expressions due to proof normal form. Got {func_type:?}",
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
                                let congr = self.proof_names().congr_constructor.clone();
                                let proof_sort = self.proof_sort();
                                let mut proof = view_proof_var;
                                for (i, arg_proof) in arg_proofs.into_iter().enumerate() {
                                    if let Some(arg_proof) = arg_proof {
                                        proof = self.mint(
                                            action_lookups,
                                            &congr,
                                            &format!("{proof} {i} {arg_proof}"),
                                            &proof_sort,
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
                            let to_ast = self
                                .proof_names()
                                .sort_to_ast_constructor
                                .get(specialized_primitive.output().name())
                                .unwrap()
                                .clone();
                            let fiat_constructor = self.proof_names().fiat_constructor.clone();
                            let proof_sort = self.proof_sort();
                            let ast_sort = self.proof_names().ast_sort.clone();
                            let a1 = self.mint(action_lookups, &to_ast, &fv, &ast_sort);
                            let a2 = self.mint(action_lookups, &to_ast, &fv, &ast_sort);
                            self.mint(
                                action_lookups,
                                &fiat_constructor,
                                &format!("{a1} {a2}"),
                                &proof_sort,
                            )
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

        // The prooflist mints are actions (emitted into `action_lookups` before
        // the proof binding). Only proof mode consumes the prooflist; in term
        // mode it is discarded, so skip the mints to keep `action_lookups` empty.
        let proof_list = if self.proofs_enabled() {
            self.format_prooflist(&mut action_lookups, &proof)
        } else {
            String::new()
        };
        (res, action_lookups, proof_list)
    }

    // Actions need to be instrumented to add to the view
    // as well as to the terms tables.
    fn instrument_action(
        &mut self,
        action: &ResolvedAction,
        justification: &Justification,
        nat_conn: &mut NatConn,
    ) -> Vec<String> {
        let mut res = vec![];

        match action {
            ResolvedAction::Let(_span, v, generic_expr) => {
                let v2 =
                    self.instrument_action_expr(generic_expr, &mut res, justification, nat_conn);
                // Carry the canonicalization info onto the let-bound name. `v2` is
                // the built term's deduped e-class var, keyed in `nat_conn` by that
                // fresh var; without this, a later reference to `v.name` (e.g. the
                // `new-e` in `(let new-e (Bop …)) (union e new-e)`) misses in
                // `nat_conn` and `union` falls into the no-connector branch, whose
                // bare `@Rule` endpoint extracts the deduped (canonicalized) shape
                // instead of the natural one the rule head produced.
                if let Some(info) = nat_conn.get(&v2).cloned() {
                    nat_conn.insert(v.name.clone(), info);
                }
                res.push(format!("(let {} {})", v.name, v2));
            }
            ResolvedAction::Set(_span, h, generic_exprs, generic_expr) => {
                let ResolvedCall::Func(func_type) = h else {
                    panic!(
                        "Set action on non-function, should have been prevented by typechecking"
                    );
                };

                // Global definition `(set (x) e)`: x is a nullary `:internal-let`
                // function aliasing e. Store e's value+proof directly in x's FD view
                // (x's e-class *is* e's) — no term mint, which would use the wrong
                // arity for x's term relation (its output is the eclass, so it has
                // no separate output column).
                if generic_exprs.is_empty() && self.egraph.type_info.is_global(&func_type.name) {
                    let e_value = self.instrument_action_expr(
                        generic_expr,
                        &mut res,
                        justification,
                        nat_conn,
                    );
                    let proof = if self.proofs_enabled() {
                        self.global_value_proof(
                            &mut res,
                            func_type,
                            &e_value,
                            justification,
                            nat_conn,
                        )
                    } else {
                        "()".to_string()
                    };
                    // Term row (`x`'s e-class is e's) + the FD view `() -> (val, proof)`.
                    res.push(format!("(set ({} {e_value}) ())", func_type.name));
                    res.push(self.update_fd_view(&func_type.name, &[], &e_value, &proof));
                    return res;
                }

                let mut exprs = vec![];
                for e in generic_exprs.iter().chain(std::iter::once(generic_expr)) {
                    exprs.push(self.instrument_action_expr(e, &mut res, justification, nat_conn));
                }

                let (add_code, _fv) =
                    self.add_term_and_view(func_type, &exprs, justification, nat_conn);
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
                        .map(|e| self.instrument_action_expr(e, &mut res, justification, nat_conn))
                        .collect::<Vec<_>>();

                    res.push(format!("({symbol} {})", ListDisplay(children, " ")));
                } else {
                    panic!(
                        "Delete action on non-function, should have been prevented by typechecking"
                    );
                }
            }
            ResolvedAction::Union(_span, generic_expr, generic_expr1) => {
                let v1 =
                    self.instrument_action_expr(generic_expr, &mut res, justification, nat_conn);
                let v2 =
                    self.instrument_action_expr(generic_expr1, &mut res, justification, nat_conn);
                let ot = generic_expr.output_type();
                let type_name = ot.name();
                let unioned = self.union(&mut res, type_name, &v1, &v2, justification, nat_conn);
                res.push(unioned);
            }
            ResolvedAction::Panic(..) => {
                res.push(format!("{action}"));
            }
            ResolvedAction::Expr(_span, generic_expr) => {
                self.instrument_action_expr(generic_expr, &mut res, justification, nat_conn);
            }
        }

        res
    }

    /// Build the proof term that justifies a freshly-created term `fv`
    /// (wrapped by the AST constructor `to_ast`) proving `fv = fv`, from the
    /// surrounding [`Justification`]. Shared by constructor creation
    /// (`add_term_and_view`) and container creation.
    /// Build the `t = t` (or merge/fiat) proof for a freshly created term `fv`,
    /// emitting the proof-relation mints onto `stmts` and returning the proof var.
    fn term_proof_for_justification(
        &mut self,
        stmts: &mut Vec<String>,
        fv: &str,
        to_ast: &str,
        justification: &Justification,
    ) -> String {
        let ast_sort = self.proof_names().ast_sort.clone();
        let proof_sort = self.proof_sort();
        match justification {
            Justification::Rule(rule_name, rule_proof) => {
                let a1 = self.mint(stmts, to_ast, fv, &ast_sort);
                let a2 = self.mint(stmts, to_ast, fv, &ast_sort);
                let rule = self.proof_names().rule_constructor.clone();
                self.mint(
                    stmts,
                    &rule,
                    &format!("{rule_name} {rule_proof} {a1} {a2}"),
                    &proof_sort,
                )
            }
            Justification::Fiat => {
                let a1 = self.mint(stmts, to_ast, fv, &ast_sort);
                let a2 = self.mint(stmts, to_ast, fv, &ast_sort);
                let fiat = self.proof_names().fiat_constructor.clone();
                self.mint(stmts, &fiat, &format!("{a1} {a2}"), &proof_sort)
            }
            // Term-free: no AST minted (`fv`/`to_ast` unused). The checker
            // reconstructs the conclusion from the merge body + premise outputs.
            Justification::MergeIdx(fn_name, p1, p2, idx) => {
                let merge_idx = self.proof_names().merge_fn_idx_constructor.clone();
                self.mint(
                    stmts,
                    &merge_idx,
                    &format!("\"{fn_name}\" {p1} {p2} {idx}"),
                    &proof_sort,
                )
            }
            Justification::MergeRow(fn_name, p1, p2) => {
                let merge_row = self.proof_names().merge_fn_row_constructor.clone();
                self.mint(
                    stmts,
                    &merge_row,
                    &format!("\"{fn_name}\" {p1} {p2}"),
                    &proof_sort,
                )
            }
        }
    }

    /// Proof stored in a global's FD view for the value `e` it aliases.
    ///
    /// When `e` is a built term (e.g. `(Plus …)`), `add_term_and_view` has already
    /// proved its *natural* form — the literal term the checker reconstructs from
    /// the global's `(let x e)` — and recorded a `connector : natural = e_value` in
    /// `nat_conn`. Anchor the global's proof on that natural form (a reflexive
    /// `e_value = e_value` routed through it) instead of fiat-ing the canonical
    /// `e_value` directly: `e_value`'s shape may be a rewritten (canonicalized)
    /// child the checker cannot establish, whereas the natural form is exactly the
    /// global definition it can. An atomic value (a literal, or a bare reference to
    /// another global) has no connector and is fiat-ed directly — a literal is
    /// self-justifying and a global alias is already established.
    fn global_value_proof(
        &mut self,
        res: &mut Vec<String>,
        func_type: &FuncType,
        e_value: &str,
        justification: &Justification,
        nat_conn: &NatConn,
    ) -> String {
        if let Some((_nat, Some(connector))) = nat_conn.get(e_value).cloned() {
            let proof_sort = self.proof_sort();
            let sym = self.proof_names().eq_sym_constructor.clone();
            let trans = self.proof_names().eq_trans_constructor.clone();
            let sym_conn = self.mint(res, &sym, &connector, &proof_sort);
            self.mint(res, &trans, &format!("{sym_conn} {connector}"), &proof_sort)
        } else {
            let to_ast = self.fname_to_ast_name(&func_type.name).to_string();
            self.term_proof_for_justification(res, e_value, &to_ast, justification)
        }
    }

    /// Update a non-FD (all-key) view with the given arguments (children + output).
    /// View is always a function (returning Proof or Unit).
    fn update_view(&mut self, fname: &str, args: &[String], proof: &str) -> String {
        let view_name = self.view_name(fname);
        format!("(set ({view_name} {}) {proof})", ListDisplay(args, " "))
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
    /// Mint a fresh id of `out_sort` and assert the relation row
    /// `({name} {args_joined} <fresh>)`, appending the `let`/`set` onto `stmts`
    /// and returning the fresh variable. Terms and proofs are relations rather
    /// than constructors, so an id is minted explicitly here rather than by a
    /// constructor call; every minted id keeps its row (nothing is merged away).
    pub(crate) fn mint(
        &mut self,
        stmts: &mut Vec<String>,
        name: &str,
        args_joined: &str,
        out_sort: &str,
    ) -> String {
        let v = self.fresh_var();
        // The generic `get-fresh!` takes the target sort as a string literal so it
        // types its output without per-sort primitives (its runtime ignores the arg).
        let get_fresh = crate::proofs::proof_fresh::GET_FRESH_PRIM_NAME;
        stmts.push(format!("(let {v} ({get_fresh} \"{out_sort}\"))"));
        stmts.push(format!("(set ({name} {args_joined} {v}) ())"));
        v
    }

    /// Read an encoded global's value from its FD view `() -> (val, proof)`, for a
    /// global reference `(x)` appearing in an action. `set-if-empty` returns the
    /// stored e-class (a global is `set` before it is used, so the fresh fallback is
    /// dead code that only fires on a malformed program). The value read is already
    /// the view's canonical e-class, so no natural/deduped connector is recorded.
    fn lookup_global(&mut self, name: &str, res: &mut Vec<String>) -> String {
        let view = self.view_name(name);
        let set_if_empty = crate::proofs::proof_fresh::set_if_empty_prim_name(&view);
        let get_fresh = crate::proofs::proof_fresh::GET_FRESH_PRIM_NAME;
        let view_sort = self
            .proof_names()
            .fn_to_term_sort
            .get(name)
            .expect("term sort recorded in term_and_view")
            .clone();
        let fresh_e = self.fresh_var();
        res.push(format!("(let {fresh_e} ({get_fresh} \"{view_sort}\"))"));
        let vx = self.fresh_var();
        let fallback_proof = if self.proofs_enabled() {
            let to_ast = self.fname_to_ast_name(name).to_string();
            self.term_proof_for_justification(res, &fresh_e, &to_ast, &Justification::Fiat)
        } else {
            "()".to_string()
        };
        res.push(format!(
            "(let {vx} ({set_if_empty} {fresh_e} {fallback_proof}))"
        ));
        vx
    }

    /// The `Proof` datatype's sort name (mint target for proof relations).
    pub(crate) fn proof_sort(&self) -> String {
        self.proof_names().proof_datatype.clone()
    }

    fn add_term_and_view(
        &mut self,
        func_type: &FuncType,
        args: &[String],
        justification: &Justification,
        nat_conn: &mut NatConn,
    ) -> (Vec<String>, String) {
        let mut res = vec![];
        let view_sort = self
            .egraph
            .proof_state
            .proof_names
            .fn_to_term_sort
            .get(&func_type.name)
            .expect("term sort recorded in term_and_view")
            .clone();
        let proofs = self.egraph.proof_state.proofs_enabled;

        // Custom functions (and globals-as-constructors): mint the term-relation
        // row and record its term proof. No canonicalization threading.
        if func_type.subtype != FunctionSubtype::Constructor {
            let fv = self.mint(
                &mut res,
                &func_type.name,
                &ListDisplay(args, " ").to_string(),
                &view_sort,
            );
            let view_proof_var = if proofs {
                let to_ast = self.fname_to_ast_name(&func_type.name).to_string();
                self.term_proof_for_justification(&mut res, &fv, &to_ast, justification)
            } else {
                "()".to_string()
            };
            if self.func_type_is_fd_view(func_type) {
                // Custom-with-merge FD view: key on the children, value
                // `(output {Unit|Proof})`. `args` ends with the output value (from
                // the `(set (f c..) v)` action). `view_proof_var` proves the row's
                // f-application term `f(children, output)` (what `fv` extracts to),
                // exactly the premise that `MergeRow`/`MergeIdx` reconstruct their
                // conclusion from. A children-key collision runs the user merge (see
                // `custom_view_merge`).
                let (output, children) = args.split_last().expect("custom set needs an output");
                res.push(self.update_fd_view(&func_type.name, children, output, &view_proof_var));
            } else {
                res.push(self.update_view(&func_type.name, args, &view_proof_var));
            }
            return (res, fv);
        }

        let view = self.view_name(&func_type.name);
        let set_if_empty = crate::proofs::proof_fresh::set_if_empty_prim_name(&view);

        // Term-only: build the term with canonical children and canonicalize it to
        // the view's e-class via `set-if-empty`; return that canonical id so
        // parents build with canonical children (views stay canonical).
        if !proofs {
            let fv = self.mint(
                &mut res,
                &func_type.name,
                &ListDisplay(args, " ").to_string(),
                &view_sort,
            );
            let canon = self.fresh_var();
            res.push(format!(
                "(let {canon} ({set_if_empty} {} {fv} ()))",
                ListDisplay(args, " ")
            ));
            return (res, canon);
        }

        // Proof mode (the flatten-canonicalize-thread plan): build the *natural*
        // term (children at their as-built ids) and the *canonical* term (children
        // at their view-deduped ids), connect them with a `Congr` chain over the
        // changed children, then `set-if-empty` to the view's deduped e-class and
        // stitch on the view-dedup edge. Return the deduped e-class (so parents and
        // views stay canonical) and record `(natural, connector : natural =
        // deduped)` in `nat_conn` for the parent's `Congr` and the root `union`.
        let to_ast = self.fname_to_ast_name(&func_type.name).to_string();
        let proof_sort = self.proof_sort();
        let congr = self.proof_names().congr_constructor.clone();
        let trans = self.proof_names().eq_trans_constructor.clone();
        let sym = self.proof_names().eq_sym_constructor.clone();
        let term_proof_constructor = self.term_proof_name(func_type.output().name());

        // Each arg is a child's deduped id; look up its natural id + connector.
        let children: Vec<(String, String, Option<String>)> = args
            .iter()
            .map(|a| match nat_conn.get(a) {
                Some((nat, conn)) => (a.clone(), nat.clone(), conn.clone()),
                None => (a.clone(), a.clone(), None),
            })
            .collect();
        let nat_args: Vec<String> = children.iter().map(|(_, n, _)| n.clone()).collect();
        let dedup_args: Vec<String> = children.iter().map(|(d, _, _)| d.clone()).collect();

        // Natural term + its (rule-justified) term proof. `fv_nat` stays *unseeded*
        // (only the canonical node below is written to the view), so it is never
        // pulled into the view's congruence `:merge` and stays as-built — hence its
        // `@Rule` endpoint extracts the syntactic shape the rule head produced, and
        // recording it as `fv_nat`'s existence proof is valid (and required, since
        // proof-testing can enumerate the natural row as a witness).
        let fv_nat = self.mint(
            &mut res,
            &func_type.name,
            &ListDisplay(&nat_args, " ").to_string(),
            &view_sort,
        );
        let nat_prf = self.term_proof_for_justification(&mut res, &fv_nat, &to_ast, justification);
        res.push(format!(
            "(set ({term_proof_constructor} {fv_nat}) {nat_prf})"
        ));

        // `Congr` chain: `fv_nat = f(deduped children)` (rewrite each changed child).
        let mut nat_to_dedup_term = nat_prf.clone();
        for (i, (_, _, conn)) in children.iter().enumerate() {
            if let Some(conn) = conn {
                nat_to_dedup_term = self.mint(
                    &mut res,
                    &congr,
                    &format!("{nat_to_dedup_term} {i} {conn}"),
                    &proof_sort,
                );
            }
        }

        // Canonical-children term that seeds the view — always a *separate* node
        // from `fv_nat`, even when no child changed (`nat_args == dedup_args`).
        // The natural node must stay unseeded so it is never pulled into the view's
        // congruence `:merge` (which natively unions e-classes): if `fv_nat` were
        // the seed, a birewrite that re-keys this view to a differently-shaped
        // partner (e.g. `(IntImm32 x) <-> (IntImm 32 x)`) would natively merge
        // `fv_nat` into that partner, and the natural `@Rule` endpoint threaded up
        // through the Congr chain would then extract the partner's shape instead of
        // the as-built one the rule head produced. `fv_can`'s proof is the
        // *reflexive* `fv_can = fv_can` from the Congr chain (`Trans (Sym e-to-e')
        // e-to-e'`), exempt from the rule-head check.
        let fv_can = self.mint(
            &mut res,
            &func_type.name,
            &ListDisplay(&dedup_args, " ").to_string(),
            &view_sort,
        );
        let sym_ntd = self.mint(&mut res, &sym, &nat_to_dedup_term, &proof_sort);
        let can_prf = self.mint(
            &mut res,
            &trans,
            &format!("{sym_ntd} {nat_to_dedup_term}"),
            &proof_sort,
        );
        res.push(format!(
            "(set ({term_proof_constructor} {fv_can}) {can_prf})"
        ));

        // Dedup to the view e-class; read its stored proof (`dedup = f(children)`).
        let dedup = self.fresh_var();
        res.push(format!(
            "(let {dedup} ({set_if_empty} {} {fv_can} {can_prf}))",
            ListDisplay(&dedup_args, " ")
        ));
        let view_proof = crate::proofs::proof_fresh::view_proof_prim_name(&view);
        let vprf = self.fresh_var();
        res.push(format!(
            "(let {vprf} ({view_proof} {} {can_prf}))",
            ListDisplay(&dedup_args, " ")
        ));

        // connector: `fv_nat = dedup` = Trans(fv_nat = f(children), Sym(dedup = f(children))).
        let sym_vprf = self.mint(&mut res, &sym, &vprf, &proof_sort);
        let connector = self.mint(
            &mut res,
            &trans,
            &format!("{nat_to_dedup_term} {sym_vprf}"),
            &proof_sort,
        );

        nat_conn.insert(dedup.clone(), (fv_nat, Some(connector)));
        (res, dedup)
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
    /// Rebuild a custom function's merge body inside the pair-valued `current`
    /// helper's `:merge`, minting each constructor subterm via `add_term_and_view`
    /// (so canonical ids are used, like every other term site) with a term-free
    /// `MergeIdx` proof. `idx` is threaded pre-order (incremented once per node,
    /// leaves included) to match the checker's `subexpr_at_index`, so subexpr `idx`
    /// evaluated on the premise outputs reconstructs exactly this node's term.
    /// `old`/`new` in the body map to the `:merge` output columns `old0`/`new0`;
    /// the carried view proofs are `old1`/`new1`.
    fn instrument_merge_body(
        &mut self,
        expr: &ResolvedExpr,
        res: &mut Vec<String>,
        fname: &str,
        idx: &mut usize,
        nat_conn: &mut NatConn,
    ) -> String {
        let my_idx = *idx;
        *idx += 1;
        match expr {
            ResolvedExpr::Lit(_, lit) => format!("{lit}"),
            ResolvedExpr::Var(_, resolved_var) => match resolved_var.name.as_str() {
                "old" => "old0".to_string(),
                "new" => "new0".to_string(),
                other => other.to_string(),
            },
            ResolvedExpr::Call(_, ResolvedCall::Func(func_type), args) => {
                let arg_vars = args
                    .iter()
                    .map(|a| self.instrument_merge_body(a, res, fname, idx, nat_conn))
                    .collect::<Vec<_>>();
                let just = Justification::MergeIdx(
                    fname.to_string(),
                    "old1".to_string(),
                    "new1".to_string(),
                    my_idx,
                );
                let (code, fv) = self.add_term_and_view(func_type, &arg_vars, &just, nat_conn);
                res.extend(code);
                fv
            }
            // A container-producing primitive (e.g. `set-intersect`): build the
            // container over the recursively-built args and anchor a term-free
            // `MergeIdx` container proof in `<CSort>Proof` (the container rebuild's
            // anchor). No AST/children needed.
            ResolvedExpr::Call(_, ResolvedCall::Primitive(sp), args) => {
                let arg_vars = args
                    .iter()
                    .map(|a| self.instrument_merge_body(a, res, fname, idx, nat_conn))
                    .collect::<Vec<_>>();
                let prim_name = sp.name().to_string();
                let out = sp.output();
                let fv = self.fresh_var();
                res.push(format!(
                    "(let {fv} ({prim_name} {}))",
                    ListDisplay(&arg_vars, " ")
                ));
                if self.egraph.proof_state.proofs_enabled && out.is_eq_container_sort() {
                    let csort = out.name().to_string();
                    let to_ast = self
                        .proof_names()
                        .sort_to_ast_constructor
                        .get(&csort)
                        .unwrap()
                        .clone();
                    let just = Justification::MergeIdx(
                        fname.to_string(),
                        "old1".to_string(),
                        "new1".to_string(),
                        my_idx,
                    );
                    let proof_var = self.term_proof_for_justification(res, &fv, &to_ast, &just);
                    let cproof = self.term_proof_name(&csort);
                    res.push(format!("(set ({cproof} {fv}) {proof_var})"));
                }
                fv
            }
            ResolvedExpr::Call(_, _, _) => {
                panic!("proof-mode merge body for `{fname}` contains an unsupported call form")
            }
        }
    }

    fn instrument_action_expr(
        &mut self,
        expr: &ResolvedExpr,
        res: &mut Vec<String>,
        proof: &Justification,
        nat_conn: &mut NatConn,
    ) -> String {
        match expr {
            ResolvedExpr::Lit(_, lit) => format!("{lit}"),
            ResolvedExpr::Var(_, resolved_var) => resolved_var.name.clone(),
            ResolvedExpr::Call(_, resolved_call, args) => {
                let args = args
                    .iter()
                    .map(|arg| self.instrument_action_expr(arg, res, proof, nat_conn))
                    .collect::<Vec<_>>();
                match resolved_call {
                    ResolvedCall::Func(func_type) => {
                        if func_type.subtype == FunctionSubtype::Custom {
                            // Proof normal form bans looking up custom functions in
                            // actions — EXCEPT encoded globals. A global is a nullary
                            // `:internal-let` function with the FD view
                            // `() -> (val, proof)`; read its value+proof from the view
                            // (`set-if-empty` returns the stored e-class, `view-proof`
                            // its proof). This is the only custom lookup allowed here.
                            if self.egraph.type_info.is_global(&func_type.name) {
                                return self.lookup_global(&func_type.name, res);
                            }
                            panic!(
                                "Found a function lookup in actions, should have been prevented by typechecking"
                            );
                        }
                        let (add_code, fv) =
                            self.add_term_and_view(func_type, &args, proof, nat_conn);
                        res.extend(add_code);

                        fv
                    }
                    ResolvedCall::Primitive(specialized_primitive) => {
                        let prim_name = specialized_primitive.name().to_string();
                        let out = specialized_primitive.output();
                        let container_proof =
                            self.egraph.proof_state.proofs_enabled && out.is_eq_container_sort();
                        let csort = out.name().to_string();
                        // Element eq-sort for `vec-of` (an ordered, element-wise
                        // container constructor), if it's over a single eq-sort.
                        // Building over natural element ids makes the container's
                        // elements *change* during rebuild (natural -> canonical),
                        // which triggers the rebuild's per-element `@Congr` fold.
                        // That fold is positional, so it is only sound when element
                        // order is stable — i.e. an ordered container. Sets/maps
                        // reorder, so they keep the deduped path (a birewrite-
                        // canonicalized element of an unordered container would need
                        // an order-independent rebuild proof — a follow-up).
                        let elem_sort: Option<String> = if container_proof && prim_name == "vec-of"
                        {
                            match out.inner_sorts().as_slice() {
                                [s] if s.is_eq_sort() => Some(s.name().to_string()),
                                _ => None,
                            }
                        } else {
                            None
                        };
                        // Build over *natural* element ids where we have them (so
                        // the container's term-proof extracts the syntactic shape),
                        // and record each `natural -> (canonical, connector)` edge in
                        // `UF-Aux` so the container rebuild canonicalizes the element
                        // and threads the connector — the container-general analog of
                        // the constructor connector, order-independent.
                        let mut build_args = Vec::with_capacity(args.len());
                        for a in &args {
                            match (&elem_sort, nat_conn.get(a).cloned()) {
                                (Some(es), Some((nat, Some(conn)))) => {
                                    res.push(format!(
                                        "(set ({} {nat}) (values {a} {conn}))",
                                        uf_aux_name(es)
                                    ));
                                    build_args.push(nat);
                                }
                                _ => build_args.push(a.clone()),
                            }
                        }
                        let fv = self.fresh_var();
                        res.push(format!(
                            "(let {fv} ({prim_name} {}))",
                            ListDisplay(&build_args, " ")
                        ));
                        // A container-producing primitive records a term-proof in
                        // `<CSort>Proof`, the anchor for the container rebuild.
                        if container_proof {
                            let to_ast = self
                                .proof_names()
                                .sort_to_ast_constructor
                                .get(&csort)
                                .unwrap()
                                .clone();
                            let proof_var =
                                self.term_proof_for_justification(res, &fv, &to_ast, proof);
                            let cproof = self.term_proof_name(&csort);
                            res.push(format!("(set ({cproof} {fv}) {proof_var})"));
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
        nat_conn: &mut NatConn,
    ) -> Vec<String> {
        let mut res = vec![];
        for action in actions {
            res.extend(self.instrument_action(action, justification, nat_conn));
        }
        res
    }

    /// Instrument a rule to use term encoding. This involves using the view tables in facts,
    /// adding to term and view tables in actions.
    /// When proofs are enabled we query proof tables, then build a proof for the rule in the actions.
    /// Finally, each view update also updates the proof tables.
    fn instrument_rule(&mut self, rule: &ResolvedRule) -> Vec<Command> {
        // `nat_conn` maps this rule's freshly-minted vars (and let-bound names) to
        // their natural/connector; it is scoped to this generated program, so it is
        // a fresh local map threaded through the action builders below. (A shared
        // field would leak stale entries keyed by repeated user let names — e.g.
        // `new-e` — from earlier rules/merges, referencing out-of-scope vars.)
        let mut nat_conn = NatConn::default();
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

        let actions = self.instrument_actions(&rule.head.0, &proof, &mut nat_conn);
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
                // Each top-level action is its own generated program, so naturals do
                // not carry across commands; scope `nat_conn` to a fresh local map.
                let mut nat_conn = NatConn::default();
                let instrumented = self
                    .instrument_action(action, &Justification::Fiat, &mut nat_conn)
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
            ResolvedNCommand::Fail(span, cmds) => {
                // Encode every wrapped command and keep the whole flattened result
                // inside one `fail` (a single command can encode to several).
                let mut encoded = vec![];
                for cmd in cmds {
                    self.term_encode_command(cmd, &mut encoded)?;
                }
                res.push(Command::Fail(span.clone(), encoded));
            }
            ResolvedNCommand::Input { .. } => {
                // Loaded natively at run time (see `EGraph::native_input`), inserting
                // straight into the encoded tables. Pass the command through so
                // `run_command` dispatches it.
                res.push(command.to_command().make_unresolved());
            }
            ResolvedNCommand::Extract(span, expr, variants) => {
                // Instrument the expressions to use view tables (like actions, not facts)
                let mut action_stmts = vec![];
                let mut nat_conn = NatConn::default();
                let instrumented_expr = self.instrument_action_expr(
                    expr,
                    &mut action_stmts,
                    &Justification::Fiat,
                    &mut nat_conn,
                );
                let instrumented_variants = self.instrument_action_expr(
                    variants,
                    &mut action_stmts,
                    &Justification::Fiat,
                    &mut nat_conn,
                );

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

            // A `set` (including a global-let's `(set (g) e)`) or a top-level
            // expression over non-container sorts builds and dedups terms via
            // `set-if-empty` without merging e-classes or deferring work, so no
            // maintenance rebuild is needed after it — this is what stops N
            // global-let `set`s from each triggering a rebuild (quadratic). We still
            // rebuild after everything else: `union` merges e-classes, `delete`/
            // `subsume` defer work to the maintenance ruleset, and a container-valued
            // action needs the (`:naive`) container rebuild to recanonicalize it —
            // all need the following rebuild to run.
            fn touches_container(e: &ResolvedExpr) -> bool {
                e.output_type().is_eq_container_sort()
                    || matches!(e, ResolvedExpr::Call(_, _, args) if args.iter().any(touches_container))
            }
            let is_set_or_expr = match &command {
                ResolvedNCommand::CoreAction(ResolvedAction::Expr(_, e)) => !touches_container(e),
                ResolvedNCommand::CoreAction(ResolvedAction::Set(_, _, args, rhs)) => !args
                    .iter()
                    .chain(std::iter::once(rhs))
                    .any(touches_container),
                _ => false,
            };
            if !matches!(
                &command,
                ResolvedNCommand::Function(..)
                    | ResolvedNCommand::NormRule { .. }
                    | ResolvedNCommand::Sort { .. }
            ) && !is_set_or_expr
            {
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

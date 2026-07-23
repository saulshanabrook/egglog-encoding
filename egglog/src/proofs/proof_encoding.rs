#[doc = include_str!("proof_encoding.md")]
use crate::proofs::proof_encoding_helpers::{EncodingNames, Justification};
use crate::typechecking::FuncType;
use crate::util::HashSet;
use crate::*;
use egglog_ast::generic_ast::GenericExpr;

/// Term-construction side channel (proof mode): maps a built term's canonical
/// e-class var to `(natural e-class var, connector proof var)`, where the
/// connector proves `natural = canonical`. A parent term reads its children's
/// entries to build the natural term and its `Congr` connector; the root `union`
/// and a global's `global_value_proof` read it to anchor on the natural form.
///
/// Scoped to a single generated program — a rule, a top-level action, or a
/// custom function's merge body — so each such scope threads a fresh, local map
/// through the action/term builders.
pub(crate) type NatConn = HashMap<String, NatEntry>;

/// A [`NatConn`] entry: a built term's natural (as-built) id and the connector
/// proof `natural = canonical` (`None` when the term needed no
/// canonicalization).
#[derive(Clone)]
pub(crate) struct NatEntry {
    pub natural: String,
    pub connector: Option<String>,
}

/// Constructor applications the current rule's body already matched, keyed by
/// `(constructor, instrumented children)`. When the head rebuilds the same
/// application, its e-class is already interned, so the encoding reuses the
/// body's binding instead of minting a fresh id and re-`set-if-empty`-ing it
/// (see proof_encoding.md, "Reusing a body term").
pub(crate) type QueryTermBindings = HashMap<(String, Vec<String>), QueryTermBinding>;

/// A [`QueryTermBindings`] entry: the body view read's e-class variable and its
/// raw view proof `eclass = f(children)`. Both are bound by the body query, so
/// both are in scope in the rule's actions.
#[derive(Clone)]
pub(crate) struct QueryTermBinding {
    pub eclass: String,
    pub proof: String,
}

/// Which way a pair-valued table's carried proofs point, selecting the
/// displaced-edge composition in [`ProofInstrumentor::ordered_union_merge`].
enum CarriedProofs {
    /// `@UF` rows: the carried proof proves `key = parent`.
    KeyToParent,
    /// Congruence views: the carried proof proves `eclass = f(children)`.
    EclassToTerm,
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
    pub term_header_added: bool,
    // TODO this is very ugly- we should separate out a typechecking struct
    // since we didn't need an entire e-graph
    // When Some term encoding is enabled.
    pub original_typechecking: Option<Box<EGraph>>,
    pub proofs_enabled: bool,
    pub proof_testing: bool,
    /// Whether extracted proofs are verified.
    pub verify_proofs: bool,
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
            term_header_added: false,
            original_typechecking: None,
            proofs_enabled: false,
            proof_names: EncodingNames::new(symbol_gen),
            proof_testing: false,
            verify_proofs: true,
            force_proof_naive: false,
        }
    }
}

/// Thin wrapper around an [`EGraph`] for the term encoding
pub(crate) struct ProofInstrumentor<'a> {
    pub(crate) egraph: &'a mut EGraph,
    /// Constructor applications matched by the rule body currently being
    /// instrumented. Empty outside a rule's action instrumentation (top-level
    /// actions and merge bodies have no body query to reuse).
    pub(crate) query_term_bindings: QueryTermBindings,
}

impl<'a> ProofInstrumentor<'a> {
    /// Make a term state and use it to instrument the code.
    pub(crate) fn add_term_encoding(
        egraph: &'a mut EGraph,
        program: Vec<ResolvedNCommand>,
    ) -> Result<Vec<Command>, Error> {
        Self {
            egraph,
            query_term_bindings: QueryTermBindings::default(),
        }
        .add_term_encoding_helper(program)
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

    /// Mint a `Rule` or `Fiat` proof of the equality `a = b` over the two
    /// endpoints' ASTs, appending the mints to `stmts`. Panics on merge
    /// justifications (merge bodies contain no `union` actions).
    fn edge_proof(
        &mut self,
        stmts: &mut Vec<String>,
        to_ast: &str,
        a: &str,
        b: &str,
        justification: &Justification,
    ) -> String {
        let ast_sort = self.proof_names().ast_sort.clone();
        let proof_sort = self.proof_sort();
        let a1 = self.mint(stmts, to_ast, a, &ast_sort);
        let a2 = self.mint(stmts, to_ast, b, &ast_sort);
        match justification {
            Justification::Rule(rule_name, proof_list) => {
                let rule = self.proof_names().rule_constructor.clone();
                self.mint(
                    stmts,
                    &rule,
                    &format!("{rule_name} {proof_list} {a1} {a2}"),
                    &proof_sort,
                )
            }
            Justification::Fiat => {
                let fiat = self.proof_names().fiat_constructor.clone();
                self.mint(stmts, &fiat, &format!("{a1} {a2}"), &proof_sort)
            }
            Justification::MergeIdx(..) | Justification::MergeRow(..) => panic!(
                "Merge functions do not include union actions, so proof should not be by merge"
            ),
        }
    }

    /// Mark two things as equal, adding proof if proofs are enabled.
    /// Emits any proof-relation mints onto `stmts` and returns the `(set @UF ...)`
    /// action, which the caller must emit after `stmts`.
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

        // Natural id + connector (`natural = deduped`) for each operand, if it was
        // a canonicalized constructor term. Leaves / body matches have neither.
        let lhs_info = nat_conn.get(lhs).cloned();
        let rhs_info = nat_conn.get(rhs).cloned();
        let lhs_conn = lhs_info.as_ref().and_then(|e| e.connector.clone());
        let rhs_conn = rhs_info.as_ref().and_then(|e| e.connector.clone());

        // Neither operand was a canonicalized constructor term (no connector), so
        // both e-classes' ASTs are stable: build the edge proof directly over them.
        if lhs_conn.is_none() && rhs_conn.is_none() {
            let proof =
                self.edge_proof(stmts, &to_ast_constructor, &larger, &smaller, justification);
            return format!("(set ({uf_name} {larger}) (values {smaller} {proof}))");
        }

        // A canonicalized operand's deduped e-class may already be unioned with a
        // differently-shaped term, so its AST floats. Build the base equality over
        // the *natural* forms (ASTs pinned to the enode the rule built), then route
        // each deduped e-class to a shared natural form and orient the edge to
        // `larger = smaller` with proof-of-max/min.
        let nat_of = |info: &Option<NatEntry>, dedup: &str| {
            info.as_ref()
                .map(|e| e.natural.clone())
                .unwrap_or_else(|| dedup.to_string())
        };
        let lhs_nat = nat_of(&lhs_info, lhs);
        let rhs_nat = nat_of(&rhs_info, rhs);

        let base_proof = self.edge_proof(
            stmts,
            &to_ast_constructor,
            &lhs_nat,
            &rhs_nat,
            justification,
        );

        let sym = self.proof_names().eq_sym_constructor.clone();
        let trans = self.proof_names().eq_trans_constructor.clone();
        // The shared natural form is the canonicalized side's natural (pinned
        // AST), so the Trans goes through it rather than through the deduped
        // e-class.
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

    /// The `(FuncType, args)` of a constructor-application expression, else `None`.
    fn constructor_operand(expr: &ResolvedExpr) -> Option<(&FuncType, &[ResolvedExpr])> {
        match expr {
            ResolvedExpr::Call(_, ResolvedCall::Func(func_type), args)
                if func_type.subtype == FunctionSubtype::Constructor =>
            {
                Some((func_type, args.as_slice()))
            }
            _ => None,
        }
    }

    /// Lift each constructor-application `union` operand into a preceding `let`,
    /// so every union operand is a variable and the inline and let-bound shapes
    /// coincide before [`Self::plan_construct_into`] runs.
    fn normalize_union_operands(&mut self, actions: &[ResolvedAction]) -> Vec<ResolvedAction> {
        let mut out = vec![];
        for action in actions {
            match action {
                ResolvedAction::Union(span, lhs, rhs) => {
                    let lhs = self.lift_union_operand(lhs.clone(), &mut out);
                    let rhs = self.lift_union_operand(rhs.clone(), &mut out);
                    out.push(ResolvedAction::Union(span.clone(), lhs, rhs));
                }
                other => out.push(other.clone()),
            }
        }
        out
    }

    /// If `operand` is a constructor application, bind it to a fresh `let`
    /// (pushed onto `out`) and return a variable referencing it; otherwise
    /// return `operand` unchanged.
    fn lift_union_operand(
        &mut self,
        operand: ResolvedExpr,
        out: &mut Vec<ResolvedAction>,
    ) -> ResolvedExpr {
        if Self::constructor_operand(&operand).is_none() {
            return operand;
        }
        let span = operand.span();
        let var = ResolvedVar {
            name: self.egraph.parser.symbol_gen.fresh("union_operand"),
            sort: operand.output_type(),
            is_global_ref: false,
        };
        out.push(ResolvedAction::Let(span.clone(), var.clone(), operand));
        GenericExpr::Var(span, var)
    }

    /// Plan the construct-into optimization over normalized actions (union
    /// operands are variables). Returns a map `guest -> target` — the guest's
    /// constructor is built into the target's e-class instead of a fresh one —
    /// and the set of union action indices it makes redundant.
    ///
    /// Conservative: only a `union` of two distinct, not-yet-touched variables
    /// where at least one is a constructor-`let` is optimized. The guest is the
    /// later-defined constructor operand (so the target's e-class is already
    /// bound where the guest is built); a matched (un-`let`) variable is always
    /// an eligible target.
    fn plan_construct_into(
        actions: &[ResolvedAction],
    ) -> (HashMap<String, String>, HashSet<usize>) {
        let mut all_def: HashMap<String, usize> = HashMap::default();
        let mut ctor_def: HashMap<String, usize> = HashMap::default();
        for (i, action) in actions.iter().enumerate() {
            if let ResolvedAction::Let(_, v, expr) = action {
                all_def.insert(v.name.clone(), i);
                if Self::constructor_operand(expr).is_some() {
                    ctor_def.insert(v.name.clone(), i);
                }
            }
        }

        let mut construct_into: HashMap<String, String> = HashMap::default();
        let mut dropped: HashSet<usize> = HashSet::default();
        let mut used: HashSet<String> = HashSet::default();
        for (i, action) in actions.iter().enumerate() {
            let ResolvedAction::Union(_, lhs, rhs) = action else {
                continue;
            };
            let (GenericExpr::Var(_, va), GenericExpr::Var(_, vb)) = (lhs, rhs) else {
                continue;
            };
            let (a, b) = (va.name.clone(), vb.name.clone());
            if a == b {
                // Union of a variable with itself is a no-op.
                dropped.insert(i);
                continue;
            }
            if used.contains(&a) || used.contains(&b) {
                // Keep chains of optimized unions out of scope for now.
                continue;
            }
            let (guest, target) = match (ctor_def.get(&a), ctor_def.get(&b)) {
                (Some(&ia), Some(&ib)) => {
                    if ia >= ib {
                        (a, b)
                    } else {
                        (b, a)
                    }
                }
                (Some(_), None) => (a, b),
                (None, Some(_)) => (b, a),
                (None, None) => continue,
            };
            // The target's e-class must be bound where the guest is built: a
            // matched variable always is; a `let` must precede the guest's.
            let guest_idx = ctor_def[&guest];
            if let Some(&target_idx) = all_def.get(&target)
                && target_idx >= guest_idx
            {
                continue;
            }
            used.insert(guest.clone());
            used.insert(target.clone());
            construct_into.insert(guest, target);
            dropped.insert(i);
        }
        (construct_into, dropped)
    }

    /// Lower a construct-into guest `(let guest (F args))`: point its view value
    /// at `target`'s e-class with a plain `set` (a collision with an existing
    /// `F(args)` unions the two via the view's `:merge`), and bind `guest` to
    /// `target` so later uses share the representative. In proof mode the view
    /// row also carries the proof `target = F(args)`.
    fn instrument_construct_into(
        &mut self,
        res: &mut Vec<String>,
        expr: &ResolvedExpr,
        target: &str,
        guest: &str,
        justification: &Justification,
        nat_conn: &mut NatConn,
    ) {
        let (func_type, args) = Self::constructor_operand(expr)
            .expect("construct-into guest must be a constructor application");
        let ctor_name = func_type.name.clone();
        let child_vals: Vec<String> = args
            .iter()
            .map(|arg| self.instrument_action_expr(arg, res, justification, nat_conn))
            .collect();

        if !self.proofs_enabled() {
            res.push(format!(
                "(set ({ctor_name} {} {target}) ())",
                ListDisplay(&child_vals, " ")
            ));
            res.push(self.update_fd_view(&ctor_name, &child_vals, target, "()"));
            res.push(format!("(let {guest} {target})"));
            return;
        }

        let sort_name = func_type.output().name().to_string();
        let view_sort = self
            .egraph
            .proof_state
            .proof_names
            .fn_to_term_sort
            .get(&ctor_name)
            .expect("term sort")
            .clone();
        let sort_ast = self
            .proof_names()
            .sort_to_ast_constructor
            .get(&sort_name)
            .expect("sort AST")
            .clone();
        let proof_sort = self.proof_sort();
        let trans = self.proof_names().eq_trans_constructor.clone();
        let sym = self.proof_names().eq_sym_constructor.clone();
        let view = self.view_name(&ctor_name);
        let (dedup_args, fv_nat, nat_prf, nat_to_dedup) = self.build_natural_with_congr(
            res,
            &ctor_name,
            &view_sort,
            &child_vals,
            justification,
            nat_conn,
        );
        let term_proof_ctor = self.term_proof_name(&sort_name);
        res.push(format!("(set ({term_proof_ctor} {fv_nat}) {nat_prf})"));
        let target_entry = nat_conn.get(target).cloned();
        let target_nat = target_entry
            .as_ref()
            .map(|e| e.natural.clone())
            .unwrap_or_else(|| target.to_string());
        let edge = self.edge_proof(res, &sort_ast, &target_nat, &fv_nat, justification);
        let to_dedup = self.mint(res, &trans, &format!("{edge} {nat_to_dedup}"), &proof_sort);
        let view_proof = match target_entry.as_ref().and_then(|e| e.connector.clone()) {
            Some(conn) => {
                let sc = self.mint(res, &sym, &conn, &proof_sort);
                self.mint(res, &trans, &format!("{sc} {to_dedup}"), &proof_sort)
            }
            None => to_dedup,
        };
        // The guest's term keeps its own id (`fv_nat`); only the view VALUE uses
        // the target. Emitting `(F dedup_args target)` would add the guest's
        // shape to `target`'s term relation, making `target`'s `@Ast` ambiguous
        // during proof reconstruction (which reads term rows, not views).
        let dedup_disp = ListDisplay(&dedup_args, " ").to_string();
        res.push(format!(
            "(set ({view} {dedup_disp}) (values {target} {view_proof}))"
        ));
        res.push(format!("(let {guest} {target})"));
        let sv = self.mint(res, &sym, &view_proof, &proof_sort);
        let guest_conn = self.mint(res, &trans, &format!("{nat_to_dedup} {sv}"), &proof_sort);
        nat_conn.insert(
            guest.to_string(),
            NatEntry {
                natural: fv_nat,
                connector: Some(guest_conn),
            },
        );
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

    /// The shared `:merge` block for a collision that unions two members of one
    /// e-class: keep `(ordering-min old0 new0)` with the smaller side's carried
    /// proof, and `set` the displaced larger side's `@UF` edge to the smaller
    /// with a composed proof of `larger = smaller`. The composition depends on
    /// which way the two carried proofs point (see [`CarriedProofs`]):
    /// `key = parent` proofs compose as `Trans (Sym hi_pf_) lo_pf_`,
    /// `eclass = f(children)` proofs as `Trans hi_pf_ (Sym lo_pf_)`.
    fn ordered_union_merge(&mut self, uf_name: &str, carried: CarriedProofs) -> String {
        if !self.proofs_enabled() {
            return format!(
                "((set ({uf_name} (ordering-max old0 new0)) (values (ordering-min old0 new0) ()))
                  (values (ordering-min old0 new0) ()))"
            );
        }
        let trans = self.proof_names().eq_trans_constructor.clone();
        let sym = self.proof_names().eq_sym_constructor.clone();
        let proof_sort = self.proof_sort();
        let mut mints = vec![];
        let displaced_pf = match carried {
            CarriedProofs::KeyToParent => {
                let sym_pf = self.mint(&mut mints, &sym, "hi_pf_", &proof_sort);
                self.mint(&mut mints, &trans, &format!("{sym_pf} lo_pf_"), &proof_sort)
            }
            CarriedProofs::EclassToTerm => {
                let sym_pf = self.mint(&mut mints, &sym, "lo_pf_", &proof_sort);
                self.mint(&mut mints, &trans, &format!("hi_pf_ {sym_pf}"), &proof_sort)
            }
        };
        let mints_str = mints.join("\n                  ");
        format!(
            "((let hi_pf_ (proof-of-max old0 old1 new0 new1))
              (let lo_pf_ (proof-of-min old0 old1 new0 new1))
              {mints_str}
              (set ({uf_name} (ordering-max old0 new0))
                   (values (ordering-min old0 new0) {displaced_pf}))
              (values (ordering-min old0 new0) lo_pf_))"
        )
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
        let uf_merge = self.ordered_union_merge(&uf_name, CarriedProofs::KeyToParent);
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

    /// A global is a `:internal-let` function; in the encoding it is treated like a
    /// nullary constructor (FD view, congruence merge, readable value+proof) rather
    /// than a `:no-merge` custom function.
    pub(super) fn is_encoded_global(&self, fdecl: &ResolvedFunctionDecl) -> bool {
        fdecl.internal_let
    }

    /// Whether the function's output value *is* its e-class, so the term relation
    /// needs no separate output column and the view is the congruence FD
    /// `(children) -> (eclass, proof)`. Holds for constructors and encoded globals.
    pub(super) fn output_is_eclass(&self, fdecl: &ResolvedFunctionDecl) -> bool {
        fdecl.subtype == FunctionSubtype::Constructor || self.is_encoded_global(fdecl)
    }

    /// The `:merge` expression for a custom function's FD pair-valued view
    /// `(children) -> (values output proof)`. On a children-key collision it runs
    /// the user's merge body once (unlike a constructor's congruence, it performs
    /// no `@UF` union): `old`/`new` bind to the two colliding output columns
    /// (`old0`/`new0`) and the carried view proofs to `old1`/`new1`. The result is
    /// `(values merged rowproof)`, where `merged` is the (canonically-minted) merge
    /// body and `rowproof` is a children-free `MergeRow` (`()` in term mode).
    ///
    /// Running the merge inside the view's `:merge` computes the body exactly
    /// once; computing it twice mints extra, over-merged term rows.
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
            // `MergeRow` justifies the newly-computed output.
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
        // Constructors and encoded globals give the term row `(children eclass)`;
        // a Custom function returning a distinct value (e.g. `-> i64`) keeps an
        // output column plus a fresh eclass column.
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
        // in `add_term_and_view` knows which `get-fresh!` to mint from, in both
        // term and proof mode.
        self.egraph
            .proof_state
            .proof_names
            .fn_to_term_sort
            .insert(name.clone(), view_sort.clone());
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
        // Every encoded function uses the FD pair-valued view `(children) ->
        // (output, {Unit|Proof})` keyed on children only; the branches below
        // differ in how the `:merge` resolves a children-key collision.
        let view_decl = if output_is_eclass {
            // Two rows conflicting on the same children are congruent: keep the
            // smaller eclass and union the two eclasses in the sort's `@UF`.
            let uf_name = self.uf_name(schema.output());
            let congruence_merge = self.ordered_union_merge(&uf_name, CarriedProofs::EclassToTerm);
            format!(
                "(function {view_name} ({in_sorts}) ({out_type} {proof_type}) :merge {congruence_merge} :internal-term-constructor {name}{view_flags} :internal-identity-vals 1)"
            )
        } else if fdecl.merge.is_some() {
            // Custom function with a `:merge`: the view `:merge` runs the user
            // merge once (see `custom_view_merge`). No `@UF` union.
            let custom_merge = self.custom_view_merge(fdecl);
            format!(
                "(function {view_name} ({in_sorts}) ({out_type} {proof_type}) :merge {custom_merge} :internal-term-constructor {name}{view_flags} :internal-identity-vals 1)"
            )
        } else {
            // Primitive/`Unit`-output `:no-merge` custom: the view is declared native
            // `:no-merge` with `:internal-identity-vals 1` — a children collision
            // keeps the old row when value column 0 (the output) is unchanged (raw
            // equality is equality for a primitive output) and panics when it
            // differs. The proof column (value column 1) is a payload the identity
            // guard ignores.
            debug_assert!(
                !fdecl.resolved_schema.output().is_eq_sort(),
                "eq-sort `:no-merge` must be rejected by command_supports_proof_encoding"
            );
            format!(
                "(function {view_name} ({in_sorts}) ({out_type} {proof_type}) :no-merge :internal-term-constructor {name}{view_flags} :internal-identity-vals 1)"
            )
        };
        // `fresh_sort` is the term's e-class sort only for a custom function whose
        // output is a distinct value (see `view_sort` above); a constructor/global
        // reuses its output sort, leaving `fresh_sort` unused.
        let fresh_sort_decl = if output_is_eclass {
            String::new()
        } else {
            format!("(sort {fresh_sort})")
        };
        // The term relation is a term node (`:internal-term-node`): its rows are
        // reconstructed by proof extraction, with the minted id as the last input.
        // The deferred delete/subsume markers are keyed on children with no output,
        // so they are plain `Unit` relations (not term nodes) — the encoding mints
        // no e-class there and extraction never reads them as terms.
        self.parse_program(&format!(
            "
            {fresh_sort_decl}
            {to_ast_view_sort}
            (function {name} ({term_sorts} {view_sort}) Unit :no-merge :internal-hidden :internal-term-node)
            {view_decl}
            (function {to_delete_name} ({in_sorts}) Unit :no-merge :internal-hidden)
            (function {subsumed_name} ({in_sorts}) Unit :no-merge :internal-hidden)
            {delete_rule}",
        ))
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

                    // The marker is a `Unit` relation, so insert a row keyed on the
                    // children with `set` (rather than a constructor application).
                    res.push(format!(
                        "(set ({symbol} {}) ())",
                        ListDisplay(children, " ")
                    ));
                } else {
                    panic!(
                        "Delete action on non-function, should have been prevented by typechecking"
                    );
                }
            }
            ResolvedAction::Union(_span, generic_expr, generic_expr1) => {
                // A union whose operand is a freshly-built constructor term is
                // optimized upstream in `instrument_actions`; this arm handles
                // the remaining general unions.
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
    /// surrounding [`Justification`], emitting the proof-relation mints onto
    /// `stmts` and returning the proof var.
    /// Anchor a container's term-proof: mint a proof of `fv = fv` under
    /// `justification` and record it in the container sort's `<CSort>Proof`
    /// table (the base the container rebuild composes from).
    fn anchor_container_term_proof(
        &mut self,
        stmts: &mut Vec<String>,
        fv: &str,
        csort: &str,
        justification: &Justification,
    ) {
        let to_ast = self
            .proof_names()
            .sort_to_ast_constructor
            .get(csort)
            .unwrap()
            .clone();
        let proof_var = self.term_proof_for_justification(stmts, fv, &to_ast, justification);
        let cproof = self.term_proof_name(csort);
        stmts.push(format!("(set ({cproof} {fv}) {proof_var})"));
    }

    pub(super) fn term_proof_for_justification(
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
        if let Some(NatEntry {
            connector: Some(connector),
            ..
        }) = nat_conn.get(e_value).cloned()
        {
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

    /// Write a row into a functional-dependency view
    /// `(set (@FView children) (values eclass proof))`. Re-setting an existing `children` key with a
    /// different `eclass` triggers the view's `:merge`.
    pub(super) fn update_fd_view(
        &mut self,
        fname: &str,
        children: &[String],
        value: &str,
        proof: &str,
    ) -> String {
        let view_name = self.view_name(fname);
        format!(
            "(set ({view_name} {}) (values {value} {proof}))",
            ListDisplay(children, " ")
        )
    }

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

    /// Return some code adding to the term and view tables, and a variable for
    /// the created term. For constructors, `args` excludes the eclass of the
    /// resulting term (it may not exist yet); for custom functions, `args`
    /// includes all arguments, output included.
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

        let is_constructor = func_type.subtype == FunctionSubtype::Constructor;
        // A constructor application the current rule's body already matched is
        // interned with a known e-class; reuse it rather than minting a fresh id
        // and re-`set-if-empty`-ing (see proof_encoding.md, "Reusing a body term").
        let reuse = is_constructor
            .then(|| {
                self.query_term_bindings
                    .get(&(func_type.name.to_string(), args.to_vec()))
                    .cloned()
            })
            .flatten();

        let var = if !is_constructor {
            self.add_custom_row(&mut res, func_type, args, justification, &view_sort)
        } else if let Some(binding) = reuse {
            if self.egraph.proof_state.proofs_enabled {
                self.reuse_query_term_with_proof(
                    &mut res,
                    func_type,
                    args,
                    justification,
                    nat_conn,
                    &view_sort,
                    &binding,
                )
            } else {
                // The body already interned this application; alias its e-class.
                binding.eclass
            }
        } else if !self.egraph.proof_state.proofs_enabled {
            self.add_constructor_term_only(&mut res, func_type, args, &view_sort)
        } else {
            self.add_constructor_with_proof(
                &mut res,
                func_type,
                args,
                justification,
                nat_conn,
                &view_sort,
            )
        };
        (res, var)
    }

    /// Custom functions: mint the term-relation row and record its term proof.
    /// No canonicalization threading.
    fn add_custom_row(
        &mut self,
        res: &mut Vec<String>,
        func_type: &FuncType,
        args: &[String],
        justification: &Justification,
        view_sort: &str,
    ) -> String {
        let fv = self.mint(
            res,
            &func_type.name,
            &ListDisplay(args, " ").to_string(),
            view_sort,
        );
        let view_proof_var = if self.egraph.proof_state.proofs_enabled {
            let to_ast = self.fname_to_ast_name(&func_type.name).to_string();
            self.term_proof_for_justification(res, &fv, &to_ast, justification)
        } else {
            "()".to_string()
        };
        // `args` ends with the output value (from the `(set (f c..) v)` action);
        // the FD view is keyed on the children. `view_proof_var` proves the row's
        // f-application term `f(children, output)` (what `fv` extracts to) — the
        // premise `MergeRow`/`MergeIdx` reconstruct their conclusion from.
        let (output, children) = args.split_last().expect("custom set needs an output");
        let update = self.update_fd_view(&func_type.name, children, output, &view_proof_var);
        res.push(update);
        fv
    }

    /// Term-only constructors: build the term with canonical children and
    /// canonicalize it to the view's e-class via `set-if-empty`; return that
    /// canonical id so parents build with canonical children (views stay
    /// canonical).
    fn add_constructor_term_only(
        &mut self,
        res: &mut Vec<String>,
        func_type: &FuncType,
        args: &[String],
        view_sort: &str,
    ) -> String {
        let view = self.view_name(&func_type.name);
        let set_if_empty = crate::proofs::proof_fresh::set_if_empty_prim_name(&view);
        let fv = self.mint(
            res,
            &func_type.name,
            &ListDisplay(args, " ").to_string(),
            view_sort,
        );
        let canon = self.fresh_var();
        res.push(format!(
            "(let {canon} ({set_if_empty} {} {fv} ()))",
            ListDisplay(args, " ")
        ));
        canon
    }

    /// Mint a constructor's *natural* node (children at their as-built ids) and
    /// build a `Congr` chain proving `fv_nat = f(deduped children)`. Returns
    /// `(deduped children, fv_nat, nat_prf, nat_to_dedup)`, where `nat_prf` is
    /// `fv_nat`'s term proof (the caller anchors it) and `nat_to_dedup` is the
    /// chain. Shared by [`Self::add_constructor_with_proof`] and
    /// [`Self::instrument_construct_into`].
    fn build_natural_with_congr(
        &mut self,
        res: &mut Vec<String>,
        fname: &str,
        view_sort: &str,
        args: &[String],
        justification: &Justification,
        nat_conn: &NatConn,
    ) -> (Vec<String>, String, String, String) {
        let to_ast = self.fname_to_ast_name(fname).to_string();
        let congr = self.proof_names().congr_constructor.clone();
        let proof_sort = self.proof_sort();
        // Each arg is a child's deduped id; look up its natural id + connector.
        let children: Vec<(String, String, Option<String>)> = args
            .iter()
            .map(|a| match nat_conn.get(a) {
                Some(e) => (a.clone(), e.natural.clone(), e.connector.clone()),
                None => (a.clone(), a.clone(), None),
            })
            .collect();
        let nat_args: Vec<String> = children.iter().map(|(_, n, _)| n.clone()).collect();
        let dedup_args: Vec<String> = children.iter().map(|(d, _, _)| d.clone()).collect();
        let fv_nat = self.mint(
            res,
            fname,
            &ListDisplay(&nat_args, " ").to_string(),
            view_sort,
        );
        let nat_prf = self.term_proof_for_justification(res, &fv_nat, &to_ast, justification);
        let mut nat_to_dedup = nat_prf.clone();
        for (i, (_, _, conn)) in children.iter().enumerate() {
            if let Some(conn) = conn {
                nat_to_dedup = self.mint(
                    res,
                    &congr,
                    &format!("{nat_to_dedup} {i} {conn}"),
                    &proof_sort,
                );
            }
        }
        (dedup_args, fv_nat, nat_prf, nat_to_dedup)
    }

    /// Proof-mode constructors: build the *natural* term (children at their
    /// as-built ids) and the *canonical* term (children at their view-deduped
    /// ids), connect them with a `Congr` chain over the changed children, then
    /// `set-if-empty` to the view's deduped e-class and stitch on the view-dedup
    /// edge. Return the deduped e-class (so parents and views stay canonical)
    /// and record `(natural, connector : natural = deduped)` in `nat_conn` for
    /// the parent's `Congr` and the root `union`.
    fn add_constructor_with_proof(
        &mut self,
        res: &mut Vec<String>,
        func_type: &FuncType,
        args: &[String],
        justification: &Justification,
        nat_conn: &mut NatConn,
        view_sort: &str,
    ) -> String {
        let view = self.view_name(&func_type.name);
        let set_if_empty = crate::proofs::proof_fresh::set_if_empty_prim_name(&view);
        let proof_sort = self.proof_sort();
        let trans = self.proof_names().eq_trans_constructor.clone();
        let sym = self.proof_names().eq_sym_constructor.clone();
        let term_proof_constructor = self.term_proof_name(func_type.output().name());

        // `fv_nat` stays *unseeded* (only `fv_can` is written to the view) so it is
        // never pulled into the view's congruence `:merge`; its `@Rule` endpoint
        // therefore keeps the as-built shape the rule head produced. `fv_can` is
        // always a separate node (even when no child changed) with the reflexive
        // proof `fv_can = fv_can`, exempt from the rule-head check.
        let (dedup_args, fv_nat, nat_prf, nat_to_dedup_term) = self.build_natural_with_congr(
            res,
            &func_type.name,
            view_sort,
            args,
            justification,
            nat_conn,
        );
        let fv_can = self.mint(
            res,
            &func_type.name,
            &ListDisplay(&dedup_args, " ").to_string(),
            view_sort,
        );
        let sym_ntd = self.mint(res, &sym, &nat_to_dedup_term, &proof_sort);
        let can_prf = self.mint(
            res,
            &trans,
            &format!("{sym_ntd} {nat_to_dedup_term}"),
            &proof_sort,
        );

        // Anchor both term proofs, dedup `fv_can` to the view e-class, and read the
        // view's stored proof (`dedup = f(children)`).
        let dedup = self.fresh_var();
        let vprf = self.fresh_var();
        let view_proof = crate::proofs::proof_fresh::view_proof_prim_name(&view);
        let dedup_args = ListDisplay(&dedup_args, " ");
        res.push(format!(
            "(set ({term_proof_constructor} {fv_nat}) {nat_prf})"
        ));
        res.push(format!(
            "(set ({term_proof_constructor} {fv_can}) {can_prf})"
        ));
        res.push(format!(
            "(let {dedup} ({set_if_empty} {dedup_args} {fv_can} {can_prf}))"
        ));
        res.push(format!(
            "(let {vprf} ({view_proof} {dedup_args} {can_prf}))"
        ));

        // connector `fv_nat = dedup` = Trans(nat_to_dedup, Sym(dedup = f(children))).
        // `sym_vprf` reads the `vprf` let, so it must follow the statements above.
        let sym_vprf = self.mint(res, &sym, &vprf, &proof_sort);
        let connector = self.mint(
            res,
            &trans,
            &format!("{nat_to_dedup_term} {sym_vprf}"),
            &proof_sort,
        );

        nat_conn.insert(
            dedup.clone(),
            NatEntry {
                natural: fv_nat,
                connector: Some(connector),
            },
        );
        dedup
    }

    /// Head reuse of a constructor application the body already matched (proof
    /// mode). Its e-class is interned, so instead of minting `fv_can` and
    /// re-`set-if-empty`-ing it, reuse the body binding's e-class and its view
    /// proof `eclass = f(children)`. The *natural* node is still built (so a
    /// parent's `Congr` and the rule-head check keep the as-built shape), and
    /// the `natural = eclass` connector recorded in `nat_conn` — mirroring the
    /// tail of [`Self::add_constructor_with_proof`].
    #[allow(clippy::too_many_arguments)]
    fn reuse_query_term_with_proof(
        &mut self,
        res: &mut Vec<String>,
        func_type: &FuncType,
        args: &[String],
        justification: &Justification,
        nat_conn: &mut NatConn,
        view_sort: &str,
        binding: &QueryTermBinding,
    ) -> String {
        let proof_sort = self.proof_sort();
        let trans = self.proof_names().eq_trans_constructor.clone();
        let sym = self.proof_names().eq_sym_constructor.clone();
        let term_proof_constructor = self.term_proof_name(func_type.output().name());

        let (_dedup_args, fv_nat, nat_prf, nat_to_dedup_term) = self.build_natural_with_congr(
            res,
            &func_type.name,
            view_sort,
            args,
            justification,
            nat_conn,
        );
        res.push(format!(
            "(set ({term_proof_constructor} {fv_nat}) {nat_prf})"
        ));

        // Reuse the body's e-class and view proof rather than re-interning.
        let dedup = self.fresh_var();
        res.push(format!("(let {dedup} {})", binding.eclass));

        // connector `fv_nat = dedup` = Trans(nat_to_dedup, Sym(eclass = f(children))).
        let sym_vprf = self.mint(res, &sym, &binding.proof, &proof_sort);
        let connector = self.mint(
            res,
            &trans,
            &format!("{nat_to_dedup_term} {sym_vprf}"),
            &proof_sort,
        );

        nat_conn.insert(
            dedup.clone(),
            NatEntry {
                natural: fv_nat,
                connector: Some(connector),
            },
        );
        dedup
    }

    /// Query a functional-dependency view by its `children` key, binding fresh
    /// variables for the value and proof output columns:
    /// `(= (values v pf) (@FView children))`. The value is the e-class for
    /// constructors/globals and the function output for custom `:merge` views.
    /// Returns `(query, value_var, proof_var)`.
    pub(super) fn query_fd_view(
        &mut self,
        fname: &str,
        children: &[String],
    ) -> (String, String, String) {
        let view_name = self.view_name(fname);
        let value_var = self.fresh_var();
        let pf_var = self.fresh_var();
        let query = format!(
            "(= (values {value_var} {pf_var}) ({view_name} {}))",
            ListDisplay(children, " ")
        );
        (query, value_var, pf_var)
    }

    /// Rebuild a custom function's merge body inside its FD view's `:merge` (see
    /// [`Self::custom_view_merge`]), minting each constructor subterm via
    /// `add_term_and_view` (so canonical ids are used, like every other term site)
    /// with a term-free `MergeIdx` proof. `idx` is threaded pre-order (incremented
    /// once per node, leaves included) to match the checker's `subexpr_at_index`,
    /// so subexpr `idx` evaluated on the premise outputs reconstructs exactly this
    /// node's term. `old`/`new` in the body map to the `:merge` output columns
    /// `old0`/`new0`; the carried view proofs are `old1`/`new1`.
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
                    let just = Justification::MergeIdx(
                        fname.to_string(),
                        "old1".to_string(),
                        "new1".to_string(),
                        my_idx,
                    );
                    self.anchor_container_term_proof(res, &fv, &csort, &just);
                }
                fv
            }
            ResolvedExpr::Call(_, _, _) => {
                panic!("proof-mode merge body for `{fname}` contains an unsupported call form")
            }
        }
    }

    // Add to view and term tables, returning a variable for the created term.
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
                            // actions, except encoded globals: a nullary
                            // `:internal-let` function whose value is read from its
                            // FD view (see `lookup_global`). This is the only custom
                            // lookup allowed here.
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
                        // Build a container over *natural* element ids where we have
                        // them (an eq-sort arg with a connector), recording each
                        // `natural -> (deduped, connector)` edge in the element's
                        // union-find. The container's term-proof then extracts the
                        // syntactic shape the rule wrote, and the ordinary container
                        // rebuild canonicalizes the element (see "Containers" in
                        // proof_encoding.md).
                        let mut build_args = Vec::with_capacity(args.len());
                        for (a, asort) in args.iter().zip(specialized_primitive.input()) {
                            match nat_conn.get(a).cloned() {
                                Some(NatEntry {
                                    natural,
                                    connector: Some(conn),
                                }) if container_proof && asort.is_eq_sort() => {
                                    let uf = self.uf_name(asort.name());
                                    res.push(format!("(set ({uf} {natural}) (values {a} {conn}))"));
                                    build_args.push(natural);
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
                            self.anchor_container_term_proof(res, &fv, &csort, proof);
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
        // Normalize union operands to variables, then build each
        // freshly-constructed union operand directly into the other operand's
        // e-class (see proof_encoding.md, "Union in a rule").
        let normalized = self.normalize_union_operands(actions);
        let (construct_into, dropped) = Self::plan_construct_into(&normalized);
        let mut res = vec![];
        for (i, action) in normalized.iter().enumerate() {
            if dropped.contains(&i) {
                continue;
            }
            match action {
                ResolvedAction::Let(_, v, expr) if construct_into.contains_key(&v.name) => {
                    let target = construct_into[&v.name].clone();
                    self.instrument_construct_into(
                        &mut res,
                        expr,
                        &target,
                        &v.name,
                        justification,
                        nat_conn,
                    );
                }
                _ => res.extend(self.instrument_action(action, justification, nat_conn)),
            }
        }
        res
    }

    /// Instrument a rule to use term encoding. This involves using the view tables in facts,
    /// adding to term and view tables in actions.
    /// When proofs are enabled we query proof tables, then build a proof for the rule in the actions.
    /// Finally, each view update also updates the proof tables.
    fn instrument_rule(&mut self, rule: &ResolvedRule) -> Vec<Command> {
        // Fresh per generated program (see `NatConn`): a shared map would leak
        // stale entries keyed by repeated user let names (e.g. `new-e`) from
        // earlier rules/merges, referencing out-of-scope vars.
        let mut nat_conn = NatConn::default();
        // term_proofs are fetched as action-side lookups (see instrument_facts),
        // so a rule with any needs a Read/Full action context (`eval_opt` below).
        let (facts, action_lookups, proof_str, query_term_bindings) =
            self.instrument_facts(&rule.body);
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

        // Scope the body's term bindings to this rule's action instrumentation;
        // `add_term_and_view` reuses a matched application's e-class instead of
        // rebuilding it. Cleared afterward so later merge bodies / top-level
        // actions (no body query) never reuse a stale, out-of-scope binding.
        self.query_term_bindings = query_term_bindings;
        let actions = self.instrument_actions(&rule.head.0, &proof, &mut nat_conn);
        self.query_term_bindings.clear();
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
                        let (instrumented, _lookups, _proof, _bindings) =
                            self.instrument_facts(facts);
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
                let mut nat_conn = NatConn::default();
                let instrumented = self
                    .instrument_actions(
                        std::slice::from_ref(action),
                        &Justification::Fiat,
                        &mut nat_conn,
                    )
                    .join("\n");
                res.extend(self.parse_program(&instrumented));
            }
            ResolvedNCommand::Check(span, facts) => {
                let (instrumented, _lookups, _proof, _bindings) = self.instrument_facts(facts);
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

            if !command_skips_rebuild(&command) {
                res.push(Command::RunSchedule(self.rebuild()));
            }
        }

        Ok(res)
    }
}

/// Whether no maintenance rebuild is needed after `command`.
///
/// Declarations (sorts, functions, rules) run no actions. A `set` (including a
/// global-let's `(set (g) e)`) or a top-level expression over non-container
/// sorts builds and dedups terms via `set-if-empty` without merging e-classes
/// or deferring work, so no maintenance rebuild is needed after it — this is
/// what stops N global-let `set`s from each triggering a rebuild (quadratic).
/// Everything else still rebuilds: `union` merges e-classes, `delete`/`subsume`
/// defer work to the maintenance ruleset, and a container-valued action needs
/// the (`:naive`) container rebuild to recanonicalize it — all need the
/// following rebuild to run.
fn command_skips_rebuild(command: &ResolvedNCommand) -> bool {
    fn touches_container(e: &ResolvedExpr) -> bool {
        e.output_type().is_eq_container_sort()
            || matches!(e, ResolvedExpr::Call(_, _, args) if args.iter().any(touches_container))
    }
    match command {
        ResolvedNCommand::Function(..)
        | ResolvedNCommand::NormRule { .. }
        | ResolvedNCommand::Sort { .. } => true,
        ResolvedNCommand::CoreAction(ResolvedAction::Expr(_, e)) => !touches_container(e),
        ResolvedNCommand::CoreAction(ResolvedAction::Set(_, _, args, rhs)) => !args
            .iter()
            .chain(std::iter::once(rhs))
            .any(touches_container),
        _ => false,
    }
}

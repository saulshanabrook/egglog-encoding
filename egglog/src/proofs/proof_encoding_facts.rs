//! Query-side instrumentation for the term/proof encoding: rule bodies are
//! rewritten to read the view tables, and each matched fact collects a premise
//! proof for the rule's proof list.

use super::proof_checker::is_container_side_condition;
use super::proof_encoding::{ProofInstrumentor, QueryTermBinding, QueryTermBindings};
use crate::proofs::proof_encoding_helpers::Justification;
use crate::typechecking::FuncType;
use crate::*;

impl ProofInstrumentor<'_> {
    /// Instrument fact replaces terms with looking up
    /// canonical versions in the view.
    /// It also needs to look up references to globals.
    /// Adds the instrumented fact to `res` and returns a proof that the fact matched.
    fn instrument_fact(
        &mut self,
        fact: &ResolvedFact,
        res: &mut Vec<String>,
        action_lookups: &mut Vec<String>,
        bindings: &mut QueryTermBindings,
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
                    let (var, proof) =
                        self.instrument_fact_expr(arg, res, action_lookups, bindings);
                    new_args.push(var);
                    arg_proofs.push(proof);
                }

                let view_name = self.view_name(head.name());

                // The custom function's FD view is keyed by children: bind the
                // output `v` (pair-first) and the row's existence proof
                // `proof_var` (pair-second).
                let proof_var = self.fresh_var();
                let children_str = ListDisplay(&new_args, " ");
                res.push(format!(
                    "(= (values {v} {proof_var}) ({view_name} {children_str}))"
                ));

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
                let (v1, p1) = self.instrument_fact_expr(left_expr, res, action_lookups, bindings);
                let (v2, p2) = self.instrument_fact_expr(right_expr, res, action_lookups, bindings);
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
                let (_, proof) =
                    self.instrument_fact_expr(generic_expr, res, action_lookups, bindings);
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
        bindings: &mut QueryTermBindings,
    ) -> (String, String) {
        match expr {
            ResolvedExpr::Lit(_, lit) => {
                let proof_code = if self.egraph.proof_state.proofs_enabled {
                    let lit_sort = literal_sort(lit);
                    let lit_str = format!("{lit}");
                    self.reflexive_fiat_proof(action_lookups, lit_sort.name(), &lit_str)
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
                        self.reflexive_fiat_proof(action_lookups, resolved_var.sort.name(), var)
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
                        let (arg_str, proof) =
                            self.instrument_fact_expr(arg, res, action_lookups, bindings);
                        new_args.push(arg_str);
                        arg_proofs.push(Some(proof));
                    }
                }
                match resolved_call {
                    ResolvedCall::Func(func_type) => {
                        // Constructors and encoded globals both have the FD view
                        // `(children) -> (eclass, proof)`, so the same view read binds
                        // the e-class + proof.
                        assert!(
                            func_type.subtype == FunctionSubtype::Constructor
                                || self.egraph.type_info.is_global(&func_type.name),
                            "Only constructor (or global) function calls are allowed in fact expressions due to proof normal form. Got {func_type:?}",
                        );

                        let fv = self.fresh_var();
                        let view_name = self.view_name(&func_type.name);
                        // A constructor view is the FD tuple
                        // `(children) -> (eclass, {Unit|Proof})`: bind the eclass (`fv`)
                        // and proof from the tuple.
                        let view_proof_var = self.fresh_var();
                        res.push(format!(
                            "(= (values {fv} {view_proof_var}) ({view_name} {}))",
                            ListDisplay(&new_args, " ")
                        ));

                        // Record this body match so the head can reuse the e-class
                        // instead of rebuilding the same application (see
                        // `ProofInstrumentor::add_term_and_view`). Globals are
                        // excluded: a global reference lowers to a view lookup in
                        // actions, never a term build.
                        if func_type.subtype == FunctionSubtype::Constructor {
                            bindings.insert(
                                (func_type.name.to_string(), new_args.clone()),
                                QueryTermBinding {
                                    eclass: fv.clone(),
                                    proof: view_proof_var.clone(),
                                },
                            );
                        }

                        let proof = if self.proofs_enabled() {
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
                            self.reflexive_fiat_proof(
                                action_lookups,
                                specialized_primitive.output().name(),
                                &fv,
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
    /// Returns `(body_facts, action_lookups, proof, term_bindings)`. Eq-sort
    /// variables' `term_proof` fetches are emitted into `action_lookups` as
    /// `(let p (term_proof v))` lines for the caller to splice into the
    /// rule's actions (the rule is then `:unsafe-seminaive`). `term_bindings`
    /// records each constructor application the body matched, for head reuse.
    /// Callers that don't build a proof (`run :until`, `check`) discard the
    /// lookups, the proof, and the bindings.
    pub(super) fn instrument_facts(
        &mut self,
        facts: &[ResolvedFact],
    ) -> (Vec<String>, Vec<String>, String, QueryTermBindings) {
        let mut res = vec![];
        let mut action_lookups = vec![];
        let mut proof = vec![];
        let mut bindings = QueryTermBindings::default();

        for fact in facts.iter() {
            let f_proof = self.instrument_fact(fact, &mut res, &mut action_lookups, &mut bindings);
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
        (res, action_lookups, proof_list, bindings)
    }

    /// Mint a reflexive `Fiat` proof `value = value` for a term of `sort_name`
    /// (two identical ASTs under a `Fiat`), appending the mints to `stmts`.
    fn reflexive_fiat_proof(
        &mut self,
        stmts: &mut Vec<String>,
        sort_name: &str,
        value: &str,
    ) -> String {
        let to_ast = self
            .proof_names()
            .sort_to_ast_constructor
            .get(sort_name)
            .unwrap()
            .clone();
        self.term_proof_for_justification(stmts, value, &to_ast, &Justification::Fiat)
    }
}

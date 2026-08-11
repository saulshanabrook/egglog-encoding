//! Query-side instrumentation for the term/proof encoding: rule bodies are
//! rewritten to read the view tables, and each matched fact collects a premise
//! proof for the rule proofs the head writes.

use super::proof_checker::is_container_side_condition;
use super::proof_encoding::{Anchor, ProofInstrumentor, holds_eclasses};
use super::proof_encoding_helpers::{holds_sort, recomputable_premises};
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
    ) -> String {
        // A container side condition: a fact a container-producing primitive
        // determines from bound variables (see `is_container_side_condition`).
        // There is no proof to carry, so emit the fact as-is — its arguments are
        // already bound — with the `Eval` marker as its proof; the checker
        // verifies it by re-evaluation.
        if is_container_side_condition(fact) {
            res.push(fact.to_string());
            if self.egraph.proof_state.proofs_enabled {
                let eval_constructor = self.proof_names().eval_constructor.clone();
                return self.mint(action_lookups, &eval_constructor, "");
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
                    let (var, proof) = self.instrument_fact_expr(arg, res);
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
                // A custom view's row proof is reflexive over the whole
                // application `f(children…, output)`, so the output is one more
                // child position rather than the proof's left-hand side.
                for (i, arg) in new_args.iter().enumerate() {
                    self.offer_anchor(arg, &proof_var, Anchor::Child(i));
                }
                self.offer_anchor(&v.name, &proof_var, Anchor::Child(new_args.len()));

                if !self.egraph.proof_state.proofs_enabled {
                    "()".to_string()
                } else if self.names_a_global(head.name(), args) && !holds_eclasses(head.output()) {
                    let value = v.name.clone();
                    // As in `instrument_fact_expr`. A custom function with a
                    // base-sort output keeps the row's proof: its row is
                    // established, where a global's only records a value.
                    self.reflexive_fiat_proof(head.output().name(), &value)
                } else {
                    let mut proof = proof_var;
                    for (i, arg_proof) in arg_proofs.into_iter().enumerate() {
                        proof = self.mint_congr(&proof, i, &arg_proof);
                    }
                    proof
                }
            }
            ResolvedFact::Eq(_span, left_expr, right_expr) => {
                let (v1, p1) = self.instrument_fact_expr(left_expr, res);
                let (v2, p2) = self.instrument_fact_expr(right_expr, res);
                res.push(format!("(= {v1} {v2})"));
                self.alias_anchor(&v1, &v2);
                if self.egraph.proof_state.proofs_enabled {
                    let sym_pf = self.mint_sym(&p1);
                    self.mint_trans(&sym_pf, &p2)
                } else {
                    "()".to_string()
                }
            }
            ResolvedFact::Fact(generic_expr) => {
                let (_, proof) = self.instrument_fact_expr(generic_expr, res);
                if self.proofs_enabled()
                    && matches!(
                        generic_expr,
                        ResolvedExpr::Call(_, ResolvedCall::Primitive(p), _)
                            if p.output().is_eq_container_sort()
                    )
                {
                    let eval_constructor = self.proof_names().eval_constructor.clone();
                    self.mint(action_lookups, &eval_constructor, "")
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
    ) -> (String, String) {
        match expr {
            ResolvedExpr::Lit(_, lit) => {
                let proof_code = if self.egraph.proof_state.proofs_enabled {
                    let lit_sort = literal_sort(lit);
                    let lit_str = format!("{lit}");
                    self.reflexive_fiat_proof(lit_sort.name(), &lit_str)
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
                        // The variable names a term some view row the body reads
                        // mentions, so that row's proof reaches it (see
                        // [`ProofInstrumentor::request_anchor`]). Which row is
                        // only known once the whole body is walked, and the
                        // composition asking for the anchor usually drops it,
                        // so the row is both resolved and written late.
                        self.request_anchor(var)
                    } else {
                        self.reflexive_fiat_proof(resolved_var.sort.name(), var)
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
                        let (arg_str, proof) = self.instrument_fact_expr(arg, res);
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
                                || self.egraph.type_info.is_global(&func_type.name)
                                || self.egraph.type_info.is_global_table(&func_type.name),
                            "Only constructor (or global) function calls are allowed in fact expressions due to proof normal form. Got {func_type:?}",
                        );

                        let fv = self.fresh_var();
                        let view_name = self.view_name(&func_type.name);
                        let args_str = ListDisplay(&new_args, " ");

                        let proof = {
                            let view_proof_var = self.fresh_var();
                            // A constructor view is the FD tuple
                            // `(children) -> (eclass, {Unit|Proof})`: bind the eclass (`fv`)
                            // and proof from the tuple.
                            res.push(format!(
                                "(= (values {fv} {view_proof_var}) ({view_name} {args_str}))"
                            ));
                            if !self.proofs_enabled() {
                                "()".to_string()
                            } else if !holds_eclasses(func_type.output()) {
                                // The row's term names the slot as well as the value,
                                // so it lines up with nothing else and anchors
                                // nothing. The value stands for itself, as a literal
                                // would.
                                self.reflexive_fiat_proof(func_type.output().name(), &fv)
                            } else {
                                // The row proof reads `eclass = f(children)`.
                                for (i, arg) in new_args.iter().enumerate() {
                                    self.offer_anchor(arg, &view_proof_var, Anchor::Child(i));
                                }
                                self.offer_anchor(&fv, &view_proof_var, Anchor::Lhs);
                                let mut proof = view_proof_var;
                                for (i, arg_proof) in arg_proofs.into_iter().enumerate() {
                                    if let Some(arg_proof) = arg_proof {
                                        proof = self.mint_congr(&proof, i, &arg_proof);
                                    }
                                }
                                proof
                            }
                        };
                        (fv, proof)
                    }
                    ResolvedCall::Primitive(specialized_primitive) => {
                        let fv = self.fresh_var();
                        res.push(format!(
                            "(= {fv} ({} {}))",
                            specialized_primitive.name(),
                            ListDisplay(&new_args, " ")
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
                            // An eq-sort result is an element the primitive read
                            // out of a container — `vec-get`, `map-get`,
                            // `pair-first` — so it is a child of whichever
                            // argument can hold its sort.
                            let out = specialized_primitive.output();
                            let containers = specialized_primitive
                                .input()
                                .iter()
                                .zip(&new_args)
                                .filter(|(sort, _)| holds_sort(sort, out.name()))
                                .map(|(_, arg)| arg.clone())
                                .collect();
                            self.request_element_anchor(&fv, out.name(), containers)
                        } else {
                            // Base primitives produce a literal result; a
                            // reflexive `Fiat` over a literal is checker-valid.
                            self.reflexive_fiat_proof(specialized_primitive.output().name(), &fv)
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

    /// Return the instrumented query, the mints its premise proofs need, and the
    /// premise proofs the rule proof records — one per fact except the
    /// [`recomputable_premises`] the encoding leaves out.
    ///
    /// Only the mints nothing can defer come back in the second component: a
    /// side condition's `Eval` marker. Everything else a premise proof is built
    /// from is deferred, landing wherever the premise is first read — for a
    /// rule, the head's own actions. Either component makes the rule
    /// `:unsafe-seminaive`. A head that names no premise (`(panic …)`) reads
    /// none of it, so none of it is emitted; callers that build no proof at all
    /// (`run :until`, `check`) discard the lookups and the premises, and must
    /// [`ProofInstrumentor::drop_pending_lookups`].
    pub(super) fn instrument_facts(
        &mut self,
        facts: &[ResolvedFact],
    ) -> (Vec<String>, Vec<String>, Vec<String>) {
        let mut res = vec![];
        let mut action_lookups = vec![];
        let mut premises = vec![];

        let recomputable = recomputable_premises(facts, &|_| false);
        for (fact, recomputable) in facts.iter().zip(recomputable) {
            let f_proof = self.instrument_fact(fact, &mut res, &mut action_lookups);
            // Nothing reads a dropped premise, so its proof is never written.
            if !recomputable {
                premises.push(f_proof);
            }
        }
        self.bind_anchors();
        (res, action_lookups, premises)
    }

    /// [`ProofInstrumentor::fiat_reflexive_proof`] for a term of `sort_name`,
    /// deferred (see [`ProofInstrumentor::defer_lookup`]): the returned variable
    /// is bound wherever something first reads it, and nowhere if nothing does.
    fn reflexive_fiat_proof(&mut self, sort_name: &str, value: &str) -> String {
        let mut group = vec![];
        let proof = self.fiat_reflexive_proof(&mut group, value, sort_name);
        self.defer_lookup(&proof, group);
        proof
    }
}

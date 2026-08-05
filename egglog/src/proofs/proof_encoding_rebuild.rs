//! Maintenance-rule generation for the term/proof encoding: the rebuild rules
//! that keep each function's view and subsumed tables canonical, plus the rules
//! that execute requested deletes/subsumptions. (`@UF` path compression stays
//! in [`super::proof_encoding`].)

use super::proof_encoding::{ProofInstrumentor, ViewIndex};
use super::proof_encoding_helpers::Skeleton;
use crate::typechecking::FuncType;
use crate::*;

/// The composition a view rebuild's packed row states, over the columns
/// [`ProofInstrumentor::indexed_rebuild_rule`] writes: the row proof in column
/// 0, then one step proof per canonicalized child in `children`, in the order
/// the composition applies them, then the e-class's own step when `eclass`.
pub(super) fn rebuild_skeleton(children: &[usize], eclass: bool) -> Skeleton {
    let mut skeleton = Skeleton::Leaf(0);
    for (step, &child) in children.iter().enumerate() {
        skeleton = skeleton.congr(child, Skeleton::Leaf(1 + step));
    }
    if eclass {
        skeleton = Skeleton::Leaf(1 + children.len()).sym().trans(skeleton);
    }
    skeleton
}

impl ProofInstrumentor<'_> {
    /// Rules that execute deletion and subsumption based on the tables requesting the deletion/subsumption.
    pub(super) fn delete_and_subsume(&mut self, fdecl: &ResolvedFunctionDecl) -> String {
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

        // The view is keyed by children only, so match its value tuple to
        // delete/subsume by key (the bridge re-reads every value column when
        // subsuming a tuple-output view). Deletion removes the row by key;
        // subsumption marks it subsumed (kept for size/proofs but excluded from
        // matching).
        let e = self.fresh_var();
        let pf = self.fresh_var();
        let e2 = self.fresh_var();
        let pf2 = self.fresh_var();
        format!(
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
        )
    }

    /// Wrap one maintenance-rebuild rule (`facts` -> `actions`) with the rebuilding
    /// ruleset, a fresh name, and `:internal-include-subsumed` (so stale rows are
    /// rebuilt too). `naive` marks rules whose primitives read `@UF` tables the rule
    /// body doesn't join on.
    fn rebuild_rule(&mut self, facts: &str, actions: &str, naive: bool) -> String {
        let ruleset = self.proof_names().rebuilding_ruleset_name.clone();
        let fresh_name = self.egraph.parser.symbol_gen.fresh("rebuild_rule");
        let naive = if naive { ":naive " } else { "" };
        format!(
            "(rule ({facts})\n     ({actions})\n     :ruleset {ruleset} {naive}:name \"{fresh_name}\" :internal-include-subsumed)\n"
        )
    }

    /// Rebuild rules that keep a view canonical: one rule per rebuildable child
    /// column (a canonical column has no `@UF` row, so the rule simply doesn't
    /// match), plus a rule for the FD view's value column. A stale eq-sort column is
    /// replaced by its `@UF` leader, a stale container by its rebuilt value.
    ///
    /// A child update re-keys the row (`set` at the canonicalized children, then
    /// `delete`); a collision on the new key runs the view's `:merge`. The value
    /// column is canonicalized by [`Self::fd_custom_value_rebuild_rule`]. In proof mode
    /// each rule composes the updated view proof.
    pub(super) fn rebuilding_rules(&mut self, fdecl: &ResolvedFunctionDecl) -> Vec<Command> {
        let proofs = self.proofs_enabled();
        // A global's output *is* its e-class (like a constructor's), so it takes the
        // e-class rebuild below (union-tracking) — not the custom-output rebuild
        // (congruence), which would emit a nonsensical `Congr` on its nullary term.
        let output_is_eclass = self.output_is_eclass(fdecl);
        let types = fdecl.resolved_schema.view_types();
        let n = types.len();
        let child = |i: usize| format!("c{i}_");
        // Key columns of the view row: the children (the value tuple is unkeyed).
        let n_keys = n - 1;
        let key_vars: Vec<String> = (0..n_keys).map(child).collect();
        let view_name = self.view_name(&fdecl.name);
        let keys_str = format!("{}", ListDisplay(&key_vars, " "));

        let mut rules = String::new();
        // One rule per rebuildable key column (re-keys the row via set + delete).
        for (i, ty) in types[..n_keys].iter().enumerate() {
            let is_container = ty.is_eq_container_sort();
            // Eq-sort children are handled by the index-driven rule below, which
            // fixes the whole row in one firing.
            if !is_container {
                continue;
            }
            let ci = child(i);
            let canon = format!("c{i}_canon_");
            let (query_view, value_var, view_prf) = self.query_fd_view(&fdecl.name, &key_vars);
            // Canonicalize the column with the container rebuild primitive or a `@UF`
            // lookup, and build the proof pieces. Container-reading rules are `:naive`
            // (the primitive reads `@UF` tables the rule doesn't join on).
            let (canon_fact, proof_lets, pf_arg) = if is_container {
                let value_prim = self.container_rebuild_prim(ty);
                let canon_fact = format!("(= {canon} ({value_prim} {ci}))");
                if proofs {
                    let congr = self.proof_names().congr_constructor.clone();
                    let proof_sort = self.proof_sort();
                    let proof_prim = self.container_rebuild_proof_prim(ty);
                    let rebuild_pf = self.fresh_var();
                    // proof_lets: bind the container rebuild proof, then mint the congr proof.
                    let mut lets = vec![format!("(let {rebuild_pf} ({proof_prim} {ci}))")];
                    let new_pf = self.mint(
                        &mut lets,
                        &congr,
                        &format!("{view_prf} {i} {rebuild_pf}"),
                        &proof_sort,
                    );
                    (
                        canon_fact,
                        lets.join("\n                             "),
                        new_pf,
                    )
                } else {
                    (canon_fact, String::new(), "()".to_string())
                }
            } else {
                unreachable!("non-container children take the index-driven rule")
            };
            let mut updated = key_vars.clone();
            updated[i] = canon.clone();
            let updated_view = self.update_fd_view(&fdecl.name, &updated, &value_var, &pf_arg);
            let facts = format!("{query_view}\n{canon_fact}\n(!= {ci} {canon})");
            let actions =
                format!("{proof_lets}\n{updated_view}\n(delete ({view_name} {keys_str}))");
            rules.push_str(&self.rebuild_rule(&facts, &actions, is_container));
        }
        // FD view value column. A constructor/global's value *is* its e-class; a
        // custom function's eq-sort or eq-container output takes the
        // delete-then-reinsert path. A base-sort custom output never goes stale,
        // so nothing is emitted.
        for vi in self
            .egraph
            .proof_state
            .view_index
            .get(&fdecl.name)
            .cloned()
            .unwrap_or_default()
        {
            rules.push_str(&self.indexed_rebuild_rule(fdecl, &key_vars, &types, &vi));
        }
        if output_is_eclass {
            // Covered by the index rule above, which indexes the e-class column too.
        } else if fdecl.subtype == FunctionSubtype::Custom && !self.is_encoded_global(fdecl) {
            if types[n - 1].is_eq_sort() {
                rules.push_str(&self.fd_custom_value_rebuild_rule(fdecl, &key_vars, n - 1));
            } else if types[n - 1].is_eq_container_sort() {
                rules.push_str(&self.fd_container_value_rebuild_rule(fdecl, &key_vars, n - 1));
            }
        }
        self.parse_program(&rules)
    }

    /// The rebuild rule for one child eq-sort, driven by an `@UF_<S>` edge joined
    /// against that sort's declared index.
    ///
    /// The index reaches every row mentioning the moved term — at any child
    /// position or at the e-class — by lookup rather than by matching the view,
    /// and its atom binds the whole row, so nothing else need be read. The action
    /// then re-canonicalizes *every* eq-sort column with `uf_canon`, so one firing
    /// yields the fully canonical row. Two children moving in the same iteration
    /// therefore fire twice with the same result, rather than each producing a
    /// differently half-rewritten row for a later pass to merge.
    ///
    /// `uf_canon` reads `@UF_<S>` in the action, which is what makes the rule
    /// `:unsafe-seminaive` (or `:naive` under the test knob); the driving `@UF`
    /// delta in the body is what makes that read sound.
    ///
    /// In proof mode a firing writes one
    /// [`packed_proof`](super::proof_encoding_helpers::EncodingNames::packed_proof)
    /// row, or none at all when nothing was canonicalized and the view's output
    /// is not an e-class.
    fn indexed_rebuild_rule(
        &mut self,
        fdecl: &ResolvedFunctionDecl,
        key_vars: &[String],
        types: &[ArcSort],
        vi: &ViewIndex,
    ) -> String {
        use crate::proofs::proof_container_rebuild::{
            uf_canon_prim_name, uf_canon_proof_prim_name,
        };
        let proofs = self.proofs_enabled();
        let view_name = self.view_name(&fdecl.name);
        let keys_str = format!("{}", ListDisplay(key_vars, " "));
        let n_keys = key_vars.len();

        let follower = self.fresh_var();
        let leader = self.fresh_var();
        let leader_pf = self.fresh_var();
        let eclass = format!("e{}_", n_keys);
        let row_pf = self.fresh_var();
        let uf_name = self.uf_name(&vi.sort_name);
        let uf_atom = format!("(= (values {leader} {leader_pf}) ({uf_name} {follower}))");
        // The index relation is `(value, children…, eclass, proof)`.
        let index_atom = format!("({} {follower} {keys_str} {eclass} {row_pf})", vi.name);

        // Canonicalize every eq-sort column. A column that did not move
        // canonicalizes to itself and its step is reflexive, which the proof
        // simplifier drops.
        let mut lets: Vec<String> = Vec::new();
        let mut updated = key_vars.to_vec();
        // The child position and step proof of each canonicalized column, in
        // ascending position — the order the composition applies them in.
        let mut steps: Vec<(usize, String)> = Vec::new();
        for j in 0..n_keys {
            if types[j].is_eq_container_sort() || !types[j].is_eq_sort() {
                continue;
            }
            let cj = &key_vars[j];
            let uf_j = self.uf_name(types[j].name());
            let canon = format!("c{j}_canon_");
            lets.push(format!(
                "(let {canon} ({} {cj} {cj}))",
                uf_canon_prim_name(&uf_j)
            ));
            if proofs {
                let term_proof = self.term_proof_name(types[j].name());
                let refl = self.fresh_var();
                let step = self.fresh_var();
                lets.push(format!("(let {refl} ({term_proof} {cj}))"));
                lets.push(format!(
                    "(let {step} ({} {cj} {refl}))",
                    uf_canon_proof_prim_name(&uf_j)
                ));
                steps.push((j, step));
            }
            updated[j] = canon;
        }
        // Only an e-class is canonicalized here, and it moves the other way round
        // from a child: the row proof reads `eclass = f(children)`, so a new leader
        // composes as `Trans(Sym(eclass = leader), …)`. A custom function's value
        // column is an ordinary output, not an e-class — that composition would be
        // wrong for it, so it keeps [`Self::fd_custom_value_rebuild_rule`], which
        // rewrites it by `Congr` at its position.
        let out_ty = &types[n_keys];
        let mut eclass_step = None;
        let value_var = if self.output_is_eclass(fdecl)
            && out_ty.is_eq_sort()
            && !out_ty.is_eq_container_sort()
        {
            let uf_out = self.uf_name(out_ty.name());
            let canon = format!("e{n_keys}_canon_");
            lets.push(format!(
                "(let {canon} ({} {eclass} {eclass}))",
                uf_canon_prim_name(&uf_out)
            ));
            if proofs {
                let term_proof = self.term_proof_name(out_ty.name());
                let refl = self.fresh_var();
                let step = self.fresh_var();
                lets.push(format!("(let {refl} ({term_proof} {eclass}))"));
                lets.push(format!(
                    "(let {step} ({} {eclass} {refl}))",
                    uf_canon_proof_prim_name(&uf_out)
                ));
                // The packed row takes the step as it stands: its expansion is
                // what applies the `Sym`.
                eclass_step = Some(step);
            }
            canon
        } else {
            eclass.clone()
        };

        // Lay the row out and state its composition together: the row proof,
        // then each canonicalized column's step proof, then the e-class's own
        // step.
        let mut decls = String::new();
        let mut proof_acc = row_pf.clone();
        let children: Vec<usize> = steps.iter().map(|&(child, _)| child).collect();
        let skeleton = rebuild_skeleton(&children, eclass_step.is_some());
        let mut args = vec![row_pf.clone()];
        args.extend(steps.into_iter().map(|(_, step)| step));
        args.extend(eclass_step);
        if args.len() > 1 {
            let (packed, decl) = self.packed_proof_constructor(args.len());
            decls = decl;
            let proof_sort = self.proof_sort();
            let row = format!("\"{}\" {}", skeleton.spelling(), args.join(" "));
            proof_acc = self.mint(&mut lets, &packed, &row, &proof_sort);
        }

        let pf_arg = if proofs { proof_acc } else { "()".to_string() };
        let updated_view = self.update_fd_view(&fdecl.name, &updated, &value_var, &pf_arg);
        let facts = format!("{uf_atom}\n(!= {follower} {leader})\n{index_atom}");
        // Delete before re-inserting. When only the e-class moved the canonical
        // key equals the old one, so deleting afterwards would drop the row it
        // just wrote; deleting first lets the insert win, as the custom-output
        // value rebuild already does.
        let actions = format!(
            "{}\n(delete ({view_name} {keys_str}))\n{updated_view}",
            lets.join("\n                      ")
        );
        let ruleset = self.proof_names().rebuilding_ruleset_name.clone();
        let fresh_name = self.egraph.parser.symbol_gen.fresh("rebuild_rule");
        let eval_opt = self.rhs_read_eval_opt();
        format!(
            "{decls}(rule ({facts})\n     ({actions})\n     :ruleset {ruleset} {eval_opt} :name \"{fresh_name}\" :internal-include-subsumed)\n"
        )
    }

    /// One rule that canonicalizes a custom function's stale eq-sort output, at
    /// child index `out_idx`: chase the output's `@UF` edge, `delete` the stale
    /// row first so the re-`set` inserts without re-running the user merge, and in
    /// proof mode rewrite the row proof's output child by `Congr` at that position.
    ///
    /// A view whose value *is* an e-class needs no rule of its own — the whole-row
    /// rebuild canonicalizes that column too (see [`Self::indexed_rebuild_rule`]).
    fn fd_custom_value_rebuild_rule(
        &mut self,
        fdecl: &ResolvedFunctionDecl,
        key_vars: &[String],
        out_idx: usize,
    ) -> String {
        let value_uf_name = self.uf_name(fdecl.resolved_schema.output().name());
        let (query_view, value_var, view_prf) = self.query_fd_view(&fdecl.name, key_vars);
        let canon = self.fresh_var();
        let uf_prf = self.fresh_var();
        let (proof_lets, pf_arg) = if self.proofs_enabled() {
            let proof_sort = self.proof_sort();
            let congr = self.proof_names().congr_constructor.clone();
            let mut lets = vec![];
            let pf = self.mint(
                &mut lets,
                &congr,
                &format!("{view_prf} {out_idx} {uf_prf}"),
                &proof_sort,
            );
            (lets.join("\n                      "), pf)
        } else {
            (String::new(), "()".to_string())
        };
        let set_canon = self.update_fd_view(&fdecl.name, key_vars, &canon, &pf_arg);
        let view_name = self.view_name(&fdecl.name);
        let keys_str = ListDisplay(key_vars, " ").to_string();
        let actions = format!("{proof_lets}\n(delete ({view_name} {keys_str}))\n{set_canon}");
        let facts = format!(
            "{query_view}\n(= (values {canon} {uf_prf}) ({value_uf_name} {value_var}))\n(!= {value_var} {canon})"
        );
        self.rebuild_rule(&facts, &actions, false)
    }

    /// [`Self::fd_custom_value_rebuild_rule`] for an eq-container output:
    /// containers have no `@UF` to chase, so the value canonicalizes via the
    /// container rebuild primitive (`:naive` — it reads `@UF` tables the rule
    /// doesn't join on).
    fn fd_container_value_rebuild_rule(
        &mut self,
        fdecl: &ResolvedFunctionDecl,
        key_vars: &[String],
        out_idx: usize,
    ) -> String {
        let out_ty = fdecl.resolved_schema.output().clone();
        let value_prim = self.container_rebuild_prim(&out_ty);
        let (query_view, value_var, view_prf) = self.query_fd_view(&fdecl.name, key_vars);
        let canon = self.fresh_var();
        let canon_fact = format!("(= {canon} ({value_prim} {value_var}))");
        let (proof_lets, pf_arg) = if self.proofs_enabled() {
            let congr = self.proof_names().congr_constructor.clone();
            let proof_sort = self.proof_sort();
            let proof_prim = self.container_rebuild_proof_prim(&out_ty);
            let rebuild_pf = self.fresh_var();
            let mut lets = vec![format!("(let {rebuild_pf} ({proof_prim} {value_var}))")];
            let new_pf = self.mint(
                &mut lets,
                &congr,
                &format!("{view_prf} {out_idx} {rebuild_pf}"),
                &proof_sort,
            );
            (lets.join("\n                      "), new_pf)
        } else {
            (String::new(), "()".to_string())
        };
        let set_canon = self.update_fd_view(&fdecl.name, key_vars, &canon, &pf_arg);
        let view_name = self.view_name(&fdecl.name);
        let keys_str = ListDisplay(key_vars, " ").to_string();
        let facts = format!("{query_view}\n{canon_fact}\n(!= {value_var} {canon})");
        let actions = format!("{proof_lets}\n(delete ({view_name} {keys_str}))\n{set_canon}");
        self.rebuild_rule(&facts, &actions, true)
    }

    /// Rules that update the to_subsume tables when children change. One rule per
    /// eq-sort child (no proof needed for subsumed rows).
    pub(super) fn rebuilding_subsumed_rules(
        &mut self,
        fdecl: &ResolvedFunctionDecl,
    ) -> Vec<Command> {
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
                      (set ({subsumed_name} {updated_view}) ())
                      (delete ({subsumed_name} {children}))
                     )
                      :ruleset {rebuilding_ruleset} :name \"{fresh_name}\" :internal-include-subsumed)\n"
            ));
        }
        self.parse_program(&rules)
    }
}

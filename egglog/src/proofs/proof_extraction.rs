use crate::proofs::proof_encoding::ProofInstrumentor;
use crate::proofs::proof_extractor::extract_root;
use crate::proofs::proof_format::{Justification, ProofId, ProofStore, proof_store_from_term};
use crate::util::HashSet;
use crate::{ResolvedCall, TermDag, Value};
use egglog_backend_trait::BackendExt;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ProveExistsError {
    #[error("prove-exists requires a constructor")]
    RequiresConstructor,
    #[error("prove-exists does not support primitives")]
    PrimitivesUnsupported,
    #[error("Could not find a proof due to query not matching (constructor {constructor}).")]
    QueryDidNotMatch { constructor: String },
}

/// The one premise of the rule an existence proof wraps, or `None` when it
/// wraps no such rule. A view row's proof states the rule head's own conclusion
/// reflexivized — `Trans(p, Sym(p))` or `Trans(Sym(p), p)` — so the search looks
/// through those steps to the rule row itself.
fn wrapped_premise(store: &ProofStore, proof_id: ProofId) -> Option<ProofId> {
    let reflexivized = |left: ProofId, right: ProofId| match store.get(left).justification() {
        Justification::Sym(inner) if *inner == right => Some(right),
        _ => match store.get(right).justification() {
            Justification::Sym(inner) if *inner == left => Some(left),
            _ => None,
        },
    };
    let mut id = proof_id;
    loop {
        match store.get(id).justification() {
            Justification::Rule { premise_proofs, .. } => {
                return match premise_proofs.as_slice() {
                    [premise] => Some(*premise),
                    _ => None,
                };
            }
            Justification::Trans(left, right) => id = reflexivized(*left, *right)?,
            _ => return None,
        }
    }
}

impl ProofInstrumentor<'_> {
    /// Prove that a row of `call`'s view exists, or fail if no proof can be
    /// found. Any encoded function has such a view, so this reaches a custom
    /// function's rows too, not only a constructor's.
    pub(crate) fn prove_exists(
        &mut self,
        call: &ResolvedCall,
    ) -> Result<(ProofStore, ProofId), ProveExistsError> {
        let func = match call {
            ResolvedCall::Func(func) => func,
            ResolvedCall::Primitive(_) => {
                return Err(ProveExistsError::PrimitivesUnsupported);
            }
            ResolvedCall::Values(_) => {
                return Err(ProveExistsError::RequiresConstructor);
            }
        };

        // The witness is a row of the constructor's view, whose proof column
        // states `eclass = f(children)` — the constructor's existence. Every
        // encoded function has such a view, so the two guards below only catch a
        // name the encoding never rewrote: reject it rather than panic.
        let view_name = self.view_name(&func.name);
        let Some(view) = self.egraph.functions.get(&view_name) else {
            return Err(ProveExistsError::RequiresConstructor);
        };
        let view_backend_id = view.backend_id;
        let Some(proof_sort) = view.schema.outputs.last().cloned() else {
            return Err(ProveExistsError::RequiresConstructor);
        };
        // The view row is `[children…, value, proof]`; the proof is the last column.
        let proof_index = view.schema.input.len() + view.schema.outputs.len() - 1;

        let mut termdag = TermDag::default();

        // Pick the lexicographically-smallest row as the witness rather than
        // whichever row the backend happens to yield first. A backend whose row
        // order is not deterministic (e.g. the differential-dataflow backend's
        // hash-set mirror) would otherwise make the extracted existence proof —
        // and thus proof snapshots — vary run to run.
        let mut best_row: Option<Vec<Value>> = None;
        self.egraph.backend.for_each(view_backend_id, |row| {
            if best_row.as_deref().is_none_or(|best| row.vals < best) {
                best_row = Some(row.vals.to_vec());
            }
        });
        let proof_value = best_row.map(|row| row[proof_index]).ok_or_else(|| {
            ProveExistsError::QueryDidNotMatch {
                constructor: func.name.clone(),
            }
        })?;

        let proof_term_id = extract_root(self.egraph, &mut termdag, proof_value, proof_sort)
            .unwrap_or_else(|| {
                panic!("failed to extract proof term for constructor {}", func.name)
            });

        let container_normalizers = self
            .egraph
            .type_info
            .sorts
            .values()
            .filter_map(|sort| sort.rebuild_container_normalizer())
            .collect();
        // A base sort's value-constructor head is treated by the checker as an
        // unambiguous value marker, so it must resolve to exactly one primitive
        // (no overloads) — otherwise ignoring the head would be unsound.
        let mut prim_value_constructors: HashSet<String> = HashSet::default();
        for sort in self.egraph.type_info.sorts.values() {
            if let Some(head) = sort.prim_value_constructor() {
                let count = self.egraph.type_info.get_prims(&head).map_or(0, <[_]>::len);
                assert!(
                    count == 1,
                    "sort `{}` declares `{head}` as its primitive value constructor, but `{head}` \
                     resolves to {count} primitives; a value constructor must name exactly one \
                     primitive (no overloads)",
                    sort.name(),
                );
                prim_value_constructors.insert(head);
            }
        }
        let (mut proof_store, proof_id) = proof_store_from_term(
            &self.egraph.proof_state.proof_names,
            termdag,
            proof_term_id,
            &self.egraph.proof_check_program,
            container_normalizers,
            prim_value_constructors,
        );

        // Remove globals from the proof
        if let Result::Err(e) =
            proof_store.remove_globals(&self.egraph.proof_check_program, &self.egraph.global_slots)
        {
            panic!("Failed to remove globals from proof: {e}");
        }

        // If the existence proof is a single-premise rule, strip that wrapping rule
        // and use its premise; otherwise use the proof as-is (an existence proof need
        // not be rule-justified — `check_proof` below validates it either way). Which
        // shape arises depends on the witness row, chosen deterministically above, so
        // this is stable across runs and backends.
        let extra_rule_removed = wrapped_premise(&proof_store, proof_id).unwrap_or(proof_id);

        // Check the proof before simplification
        if self.egraph.proof_state.verify_proofs
            && let Result::Err(e) =
                proof_store.check_proof(extra_rule_removed, &self.egraph.proof_check_program)
        {
            log::debug!(
                "failing existence proof:\n{}",
                proof_store.proof_to_string(extra_rule_removed)
            );
            panic!("Existence proof should be valid before simplification: {e}");
        }

        // simplify the proof
        let simplified_proof = proof_store.simplify(extra_rule_removed);

        // Check the proof after simplification
        if self.egraph.proof_state.verify_proofs {
            proof_store
                .check_proof(simplified_proof, &self.egraph.proof_check_program)
                .expect("simplified existence proof should still be valid");
        }

        Ok((proof_store, simplified_proof))
    }
}

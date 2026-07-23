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

impl ProofInstrumentor<'_> {
    /// Prove the existence of a constructor or fail if a proof cannot be found.
    /// We use a constructor because inserting a value at the top level would give a trivial proof.
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

        let function = self
            .egraph
            .functions
            .get(&func.name)
            .unwrap_or_else(|| panic!("constructor {} is not declared", func.name));

        let backend_id = function.backend_id;
        // The eclass sort and its column (last input for a relation, output for a
        // plain constructor).
        let output_sort = function.extraction_output_sort().clone();
        let output_index = function.extraction_output_index();

        let mut termdag = TermDag::default();

        // Pick the lexicographically-smallest row as the witness rather than
        // whichever row the backend happens to yield first. A backend whose row
        // order is not deterministic (e.g. the differential-dataflow backend's
        // hash-set mirror) would otherwise make the extracted existence proof —
        // and thus proof snapshots — vary run to run.
        let mut best_row: Option<Vec<Value>> = None;
        self.egraph.backend.for_each(backend_id, |row| {
            if best_row.as_deref().is_none_or(|best| row.vals < best) {
                best_row = Some(row.vals.to_vec());
            }
        });
        let witness_value = best_row.map(|row| row[output_index]).ok_or_else(|| {
            ProveExistsError::QueryDidNotMatch {
                constructor: func.name.clone(),
            }
        })?;

        // `prove-exists` targets a constructor, whose eq-sort output has a proof
        // table. A function with a base-sort output (e.g. `(function f (i64) i64)`)
        // has none, so there is nothing to prove — reject it rather than panic.
        let Some(proof_function_name) = self
            .egraph
            .proof_state
            .proof_func_parent
            .get(output_sort.name())
            .cloned()
        else {
            return Err(ProveExistsError::RequiresConstructor);
        };
        let proof_function = self
            .egraph
            .functions
            .get(&proof_function_name)
            .unwrap_or_else(|| {
                panic!(
                    "proof table {proof_function_name} for constructor {} was not declared",
                    func.name
                )
            });
        let proof_sort = proof_function.schema.output().clone();
        let proof_value = self
            .egraph
            .backend
            .lookup_id(proof_function.backend_id, &[witness_value])
            .unwrap_or_else(|| panic!("no proof recorded for constructor {}", func.name));

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
        if let Result::Err(e) = proof_store.remove_globals(&self.egraph.proof_check_program) {
            panic!("Failed to remove globals from proof: {e}");
        }

        // If the existence proof is a single-premise rule, strip that wrapping rule
        // and use its premise; otherwise use the proof as-is (an existence proof need
        // not be rule-justified — `check_proof` below validates it either way). Which
        // shape arises depends on the witness row, chosen deterministically above, so
        // this is stable across runs and backends.
        let proof = proof_store.get(proof_id);
        let extra_rule_removed = match proof.justification() {
            Justification::Rule { premise_proofs, .. } => match premise_proofs.as_slice() {
                [premise_proof_id] => *premise_proof_id,
                _ => proof_id,
            },
            _ => proof_id,
        };

        // Check the proof before simplification
        if let Result::Err(e) =
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
        proof_store
            .check_proof(simplified_proof, &self.egraph.proof_check_program)
            .expect("simplified existence proof should still be valid");

        Ok((proof_store, simplified_proof))
    }
}

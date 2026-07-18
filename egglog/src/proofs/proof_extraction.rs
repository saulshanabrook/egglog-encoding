use crate::proofs::proof_encoding::ProofInstrumentor;
use crate::proofs::proof_extractor::extract_root;
use crate::proofs::proof_format::{Justification, ProofId, ProofStore, proof_store_from_term};
use crate::{ResolvedCall, TermDag};
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
        let mut witness_value = None;

        self.egraph.backend.for_each_while(backend_id, |row| {
            witness_value = Some(row.vals[output_index]);
            false
        });

        let witness_value = witness_value.ok_or_else(|| ProveExistsError::QueryDidNotMatch {
            constructor: func.name.clone(),
        })?;

        let proof_function_name = self
            .egraph
            .proof_state
            .proof_func_parent
            .get(output_sort.name())
            .unwrap_or_else(|| {
                panic!(
                    "no :internal-proof-func annotation recorded for sort {} (constructor {})",
                    output_sort.name(),
                    func.name
                )
            })
            .clone();
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
        let (mut proof_store, proof_id) = proof_store_from_term(
            &self.egraph.proof_state.proof_names,
            termdag,
            proof_term_id,
            &self.egraph.proof_check_program,
            container_normalizers,
        );

        // Remove globals from the proof
        if let Result::Err(e) = proof_store.remove_globals(&self.egraph.proof_check_program) {
            panic!("Failed to remove globals from proof: {e}");
        }

        // If the existence proof is a single-premise rule, strip that wrapping rule
        // and use its premise. Otherwise there is no wrapping rule to remove, so use
        // the proof as-is (a valid existence proof need not be rule-justified — it may
        // be `Fiat`/`Merge`/`Congr`/…; `check_proof` below validates it either way).
        // Assuming a `Rule` here made this order-dependent: the witness is a
        // constructor's first row, and a backend that iterates rows in a different
        // order (e.g. the differential-dataflow backend's `HashSet` mirror) can
        // surface a non-rule-justified row.
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

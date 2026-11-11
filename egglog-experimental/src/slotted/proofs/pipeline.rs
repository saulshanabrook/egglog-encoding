//! Lift and check ordinary proofs using retained slotted compiler results.

use super::HashMap;
use super::checker::check_claim;
use super::context::{ProofContext, SourceError};
use super::lift_slots::{self, matched_frame};
use super::program::ResolvedSlottedProgram;
use super::terms::FreshSlots;
use crate::slotted::flatten::unflatten;
use crate::slotted::query::ProofNames;
use egglog::TermDag;
use egglog::ast::{Expr, Fact};
use egglog::{CommandOutput, EGraph, Error, UserDefinedCommand};
use std::collections::BTreeMap;
use std::fmt::{self, Display, Formatter};
use std::sync::Arc;

#[derive(Clone, Debug)]
pub(in crate::slotted) struct SlottedClaim {
    pub kind: String,
    pub lhs: Expr,
    pub lhs_root: String,
    pub rhs: Expr,
    pub rhs_root: String,
    pub slot_names: BTreeMap<String, i64>,
    pub names: ProofNames,
}

impl Display for SlottedClaim {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "({} {} {})", self.kind, self.lhs, self.rhs)
    }
}

pub(crate) fn register(graph: &mut EGraph) {
    graph
        .add_command("slotted-prove".into(), Arc::new(ProveSlotted))
        .unwrap();
    graph
        .add_command("slotted-prove-extract".into(), Arc::new(ProveSlotted))
        .unwrap();
    graph
        .add_command("slotted-substitute".into(), Arc::new(ProveSlotted))
        .unwrap();
}

pub(in crate::slotted) fn error(message: impl Display) -> Error {
    Error::BackendError(format!("slotted proof: {message}"))
}

struct ProveSlotted;

impl UserDefinedCommand for ProveSlotted {
    fn supports_proofs(&self) -> bool {
        true
    }

    fn update(&self, _: &mut EGraph, _: &[Expr]) -> Result<Vec<CommandOutput>, Error> {
        Err(error(
            "missing checking program; execute a CompiledProgram or supply --slotted-source when replaying encoded proofs",
        ))
    }
}

/// The generated rule bindings used by reconstruction.
pub(in crate::slotted) type EncodingNames = HashMap<String, ProofNames>;

#[derive(Clone, Debug)]
pub(in crate::slotted) struct ProofRequest {
    pub source: ResolvedSlottedProgram,
    pub flattened: ResolvedSlottedProgram,
    pub names: EncodingNames,
    pub claims: Vec<SlottedClaim>,
}

impl ProofRequest {
    pub(in crate::slotted) fn run(
        &self,
        graph: &mut EGraph,
        facts: Vec<Fact>,
    ) -> Result<Vec<CommandOutput>, Error> {
        let evidence = graph
            .extension_state::<super::runtime_substitution::Evidence>()
            .cloned()
            .unwrap_or_default();
        let text = self.prove(graph, facts, &evidence).map_err(error)?;
        log::debug!("query extracted");
        Ok(vec![CommandOutput::UserDefined(Arc::new(text))])
    }

    #[cfg(test)]
    fn contexts(
        &self,
        slot_names: &BTreeMap<String, i64>,
    ) -> Result<(ProofContext, ProofContext, TermDag), SourceError> {
        let mut dag = TermDag::default();
        let (source, flattened) = self.contexts_in(&mut dag, slot_names)?;
        Ok((source, flattened, dag))
    }

    pub(super) fn contexts_in(
        &self,
        dag: &mut TermDag,
        slot_names: &BTreeMap<String, i64>,
    ) -> Result<(ProofContext, ProofContext), SourceError> {
        let source = self.source.context(dag, slot_names.clone())?;
        let flattened = self
            .flattened
            .flattened_context(dag, source.slot_names.clone())?;
        Ok((source, flattened))
    }

    /// Lift and check an encoded proof, returning the source proof's text.
    fn prove(
        &self,
        graph: &mut EGraph,
        facts: Vec<Fact>,
        evidence: &super::runtime_substitution::Evidence,
    ) -> Result<String, String> {
        let claim = &self.claims[0];
        let resolved = &self.source;
        let mut dag = TermDag::default();
        let (program, flattened) = self
            .contexts_in(&mut dag, &claim.slot_names)
            .map_err(|e| e.to_string())?;
        let mut evidence = evidence.lift(graph, &flattened, &self.flattened, dag, &self.names)?;
        let mut source = lift_slots::source::SourceLifter::new(
            &flattened,
            &self.flattened,
            &self.names,
            &evidence,
        );
        let (egg, root) = graph
            .prove_facts_with_visitor(facts, &mut |store, id, origin| {
                source.visit(store, id, origin)
            })
            .map_err(|error| error.to_string())?;
        evidence = source.finish()?;
        let native = lift_slots::NativeProofs {
            store: &egg,
            program: graph.proof_checking_program(),
        };
        let egg = &egg;
        let mut dag = evidence.store.term_dag.clone();
        let frame = matched_frame(egg, root, &claim.names)?;
        let mut coordinates = BTreeMap::new();
        for &slot in program.slot_names.values() {
            if let Some(coordinate) = frame.node_slot("@globals", slot) {
                coordinates.insert(coordinate, slot);
            }
        }
        let mut fresh = FreshSlots::new(program.slot_names.values().copied());
        let mut query_program = program.clone();
        for name in frame.literal_names() {
            let coordinate = frame
                .ren(&name)
                .and_then(|r| r.get(&0).copied())
                .ok_or_else(|| format!("query slot {name} has no matched coordinate"))?;
            let slot = if let Some(&slot) = coordinates.get(&coordinate) {
                slot
            } else {
                let slot = program
                    .slot_names
                    .get(&name)
                    .copied()
                    .filter(|s| !coordinates.values().any(|v| v == s))
                    .unwrap_or_else(|| fresh.fresh());
                coordinates.insert(coordinate, slot);
                slot
            };
            query_program.slot_names.insert(name, slot);
        }
        log::debug!("query witness start");
        let witnesses = lift_slots::query_witness(
            &flattened,
            &query_program,
            &mut dag,
            &self.names,
            native,
            root,
            &self.claims,
            &evidence,
        )?;
        log::debug!("query witness done");
        let mut texts = Vec::new();
        for claim in &self.claims {
            let patterns = [
                query_program.query_pattern(&mut dag, &claim.lhs),
                query_program.query_pattern(&mut dag, &claim.rhs),
            ];
            let [lhs_pattern, rhs_pattern] = patterns;
            let patterns = [
                lhs_pattern.map_err(|e| e.to_string())?,
                rhs_pattern.map_err(|e| e.to_string())?,
            ];
            // Every fact is instantiated with the same existential witnesses.
            let source = super::format::Claim {
                kind: if claim.kind == "=" {
                    super::format::ClaimKind::Eq
                } else {
                    super::format::ClaimKind::RenamingEq
                },
                lhs: query_program
                    .query_instance(&mut dag, &claim.lhs, &witnesses)
                    .map_err(|e| format!("claim {claim}: {e}"))?,
                rhs: query_program
                    .query_instance(&mut dag, &claim.rhs, &witnesses)
                    .map_err(|e| format!("claim {claim}: {e}"))?,
            };
            log::trace!(
                "egglog proof of claim {claim}:\n{}",
                egg.proof_to_string(root)
            );
            let (store, proof) = lift_slots::lift(
                &flattened,
                dag.clone(),
                &self.names,
                native,
                root,
                &source,
                &claim.names,
                [&claim.lhs_root, &claim.rhs_root],
                patterns,
                &evidence,
            )
            .map_err(|e| format!("claim {claim}: {e}"))?;
            log::debug!("query lifted {} steps", store.len());
            let (mut store, proof) = unflatten::lift(store, &program, &flattened, proof)?;
            log::debug!("query unflattened {} steps", store.len());
            check_claim(&mut store, resolved, &source, proof).map_err(|e| {
                format!(
                    "the translated proof does not check: {e}\n{}",
                    store.proof_to_string(proof)
                )
            })?;
            log::debug!("query checked {} steps", store.len());
            let proof = store.simplify(proof);
            log::debug!("query simplified {} steps", store.len());
            let renaming = check_claim(&mut store, resolved, &source, proof)
                .map_err(|e| format!("the normalized proof does not check: {e}"))?;
            log::debug!("query formatting");
            texts.push(store.claim_to_string(proof, &renaming));
        }
        Ok(texts.join("\n"))
    }
}

#[cfg(test)]
#[path = "tests/pipeline.rs"]
mod tests;

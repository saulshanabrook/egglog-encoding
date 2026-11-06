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
use egglog::ast::{Command, Expr, Fact};
use egglog::proof::{ProofId, ProofStore};
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
    pub claim: SlottedClaim,
}

impl ProofRequest {
    pub(in crate::slotted) fn run(
        &self,
        graph: &mut EGraph,
        facts: Vec<Fact>,
    ) -> Result<Vec<CommandOutput>, Error> {
        let outputs = graph.run_program(vec![Command::Prove(egglog::span!(), facts)])?;
        let (store, root) = outputs
            .into_iter()
            .find_map(|o| match o {
                CommandOutput::ProveExists {
                    proof_store,
                    proof_id,
                } => Some((proof_store, proof_id)),
                _ => None,
            })
            .ok_or_else(|| error("no existence proof returned"))?;
        let text = self.prove(&store, root).map_err(error)?;
        Ok(vec![CommandOutput::UserDefined(Arc::new(text))])
    }

    fn contexts(
        &self,
        slot_names: &BTreeMap<String, i64>,
    ) -> Result<(ProofContext, ProofContext, TermDag), SourceError> {
        let mut dag = TermDag::default();
        let source = self.source.context(&mut dag, slot_names.clone())?;
        let flattened = self
            .flattened
            .flattened_context(&mut dag, source.slot_names.clone())?;
        Ok((source, flattened, dag))
    }

    /// Lift and check an encoded proof, returning the source proof's text.
    fn prove(&self, egg: &ProofStore, root: ProofId) -> Result<String, String> {
        let claim = &self.claim;
        let resolved = &self.source;
        let (program, flattened, mut dag) = self
            .contexts(&claim.slot_names)
            .map_err(|e| e.to_string())?;
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
        // The globals were parsed before assigning query-local slot witnesses.
        let source = query_program
            .claim_expr(&mut dag, &claim.kind, &claim.lhs, &claim.rhs)
            .map_err(|e| format!("claim {claim}: {e}"))?;
        log::debug!(
            "egglog proof of claim {claim}:\n{}",
            egg.proof_to_string(root)
        );
        let (store, proof) = lift_slots::lift(
            &flattened,
            dag,
            &self.names,
            egg,
            root,
            &source,
            &claim.names,
            [&claim.lhs_root, &claim.rhs_root],
        )
        .map_err(|e| format!("claim {claim}: {e}"))?;
        let (mut store, proof) = unflatten::lift(store, &program, proof)?;
        check_claim(&mut store, resolved, &source, proof).map_err(|e| {
            format!(
                "the translated proof does not check: {e}\n{}",
                store.proof_to_string(proof)
            )
        })?;
        let proof = store.simplify(proof);
        let renaming = check_claim(&mut store, resolved, &source, proof)
            .map_err(|e| format!("the normalized proof does not check: {e}"))?;
        Ok(store.claim_to_string(proof, &renaming))
    }
}

#[cfg(test)]
#[path = "tests/pipeline.rs"]
mod tests;

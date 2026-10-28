//! Applied-class views used only while lifting encoded edges. Every view points
//! at an ordinary equality proof; changing its coordinates adds no proof step.

use super::HashMap;
use super::format::{
    MalformedStep, SlottedConclusion, SlottedJustification, SlottedProofId, SlottedProofStore,
    SlottedProposition,
};
use super::source::SlottedProgram;
use super::terms::{Renaming, all_slots, rename};
use egglog::TermId;
use std::ops::{Deref, DerefMut};

pub(super) type LiftedId = usize;

/// Coordinates for an encoded edge, whose actual proof states `lhs = rename(m, rhs)`.
#[derive(Clone, PartialEq, Eq, Hash)]
pub(super) struct AppliedEquality {
    pub lhs: TermId,
    pub renaming: Renaming,
    pub rhs: TermId,
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct Lifted {
    proposition: AppliedEquality,
    proof: SlottedProofId,
    chain: Option<(LiftedId, LiftedId)>,
}

pub(super) struct Lifting {
    store: SlottedProofStore,
    views: Vec<Lifted>,
    index: HashMap<Lifted, LiftedId>,
}

impl Deref for Lifting {
    type Target = SlottedProofStore;

    fn deref(&self) -> &Self::Target {
        &self.store
    }
}

impl DerefMut for Lifting {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.store
    }
}

impl Lifting {
    pub fn new(store: SlottedProofStore) -> Self {
        Self {
            store,
            views: vec![],
            index: HashMap::default(),
        }
    }

    fn record(
        &mut self,
        view: AppliedEquality,
        proof: SlottedProofId,
        chain: Option<(LiftedId, LiftedId)>,
    ) -> LiftedId {
        let actual = self.store.proposition(proof).clone();
        debug_assert_eq!(actual.lhs, view.lhs);
        debug_assert_eq!(
            actual.rhs,
            rename(&mut self.store.term_dag, &view.renaming, view.rhs)
        );
        let lifted = Lifted {
            proposition: view,
            proof,
            chain,
        };
        if let Some(&id) = self.index.get(&lifted) {
            return id;
        }
        let id = self.views.len();
        self.views.push(lifted.clone());
        self.index.insert(lifted, id);
        id
    }

    pub fn plain(&mut self, proof: SlottedProofId) -> LiftedId {
        let p = self.store.proposition(proof);
        self.record(
            AppliedEquality {
                lhs: p.lhs,
                renaming: Renaming::identity(),
                rhs: p.rhs,
            },
            proof,
            None,
        )
    }

    pub fn proof(&self, id: LiftedId) -> SlottedProofId {
        self.views[id].proof
    }

    pub fn view(&mut self, proof: SlottedProofId, rhs: TermId, renaming: Renaming) -> LiftedId {
        self.record(
            AppliedEquality {
                lhs: self.store.proposition(proof).lhs,
                rhs,
                renaming,
            },
            proof,
            None,
        )
    }

    pub fn proposition(&self, id: LiftedId) -> &AppliedEquality {
        &self.views[id].proposition
    }

    pub fn chain(&self, id: LiftedId) -> Option<(LiftedId, LiftedId)> {
        self.views[id].chain
    }

    pub fn normalize(&self, p: AppliedEquality) -> AppliedEquality {
        AppliedEquality {
            renaming: p.renaming.restricted(&all_slots(&self.term_dag, p.rhs)),
            ..p
        }
    }

    pub fn fiat(&mut self, lhs: TermId, rhs: TermId) -> LiftedId {
        let proof = self.store.fiat(lhs, rhs);
        self.plain(proof)
    }

    pub fn sym(&mut self, id: LiftedId) -> LiftedId {
        let p = self.proposition(id).clone();
        let back = self.store.sym(self.views[id].proof);
        let inverse = p.renaming.inverse();
        let proof = self.store.equivariance(back, inverse.clone());
        self.record(
            AppliedEquality {
                lhs: p.rhs,
                renaming: inverse,
                rhs: p.lhs,
            },
            proof,
            None,
        )
    }

    pub fn trans(&mut self, left: LiftedId, right: LiftedId) -> Result<LiftedId, MalformedStep> {
        let (l, r) = (
            self.proposition(left).clone(),
            self.proposition(right).clone(),
        );
        if l.rhs != r.lhs {
            return Err(MalformedStep(
                "trans: applied-class middle terms differ".into(),
            ));
        }
        let right_proof = self
            .store
            .equivariance(self.views[right].proof, l.renaming.clone());
        let proof = self.store.trans(self.views[left].proof, right_proof)?;
        Ok(self.record(
            AppliedEquality {
                lhs: l.lhs,
                renaming: l.renaming.compose(&r.renaming),
                rhs: r.rhs,
            },
            proof,
            Some((left, right)),
        ))
    }

    pub fn congr(
        &mut self,
        id: LiftedId,
        child_index: usize,
        child: LiftedId,
    ) -> Result<LiftedId, MalformedStep> {
        let p = self.proposition(id).clone();
        let child_proof = self
            .store
            .equivariance(self.views[child].proof, p.renaming.clone());
        let proof = self
            .store
            .congr(self.views[id].proof, child_index, child_proof)?;
        let actual_rhs = self.store.proposition(proof).rhs;
        let rhs = rename(&mut self.term_dag, &p.renaming.inverse(), actual_rhs);
        Ok(self.record(AppliedEquality { rhs, ..p }, proof, None))
    }

    pub fn project(&mut self, id: LiftedId, child_index: usize) -> Result<LiftedId, MalformedStep> {
        let inverse = self.proposition(id).renaming.inverse();
        let proof = self.store.project(self.views[id].proof, child_index)?;
        let proof = self.store.equivariance(proof, inverse);
        Ok(self.plain(proof))
    }

    /// Change edge coordinates, leaving its ordinary proof untouched.
    pub fn reframe(&mut self, id: LiftedId, sigma: Renaming) -> LiftedId {
        let p = self.proposition(id).clone();
        let rhs = rename(&mut self.term_dag, &sigma, p.rhs);
        let view = AppliedEquality {
            rhs,
            renaming: p.renaming.compose(&sigma.inverse()),
            ..p
        };
        self.record(view, self.views[id].proof, None)
    }

    pub fn equivariance(&mut self, id: LiftedId, sigma: &Renaming) -> LiftedId {
        let p = self.proposition(id).clone();
        let lhs = rename(&mut self.term_dag, sigma, p.lhs);
        let proof = self.store.equivariance(self.views[id].proof, sigma.clone());
        self.record(
            AppliedEquality {
                lhs,
                renaming: sigma.compose(&p.renaming),
                rhs: p.rhs,
            },
            proof,
            None,
        )
    }

    pub fn rule(
        &mut self,
        proposition: SlottedProposition,
        name: String,
        substitution: Vec<(String, TermId)>,
        premises: Vec<LiftedId>,
        program: &SlottedProgram,
    ) -> LiftedId {
        let premises = premises
            .into_iter()
            .enumerate()
            .map(|(i, id)| {
                let p = self.proposition(id);
                // The root must end at the actual rule instance. A side equality
                // can use either orientation whose endpoint names are alpha-equivalent
                // to the source condition; free names must match exactly.
                if i == 0
                    || p.renaming
                        .moves_any(&program.free_slots(&self.term_dag, p.rhs))
                {
                    let inverse = p.renaming.inverse();
                    self.store.equivariance(self.views[id].proof, inverse)
                } else {
                    self.views[id].proof
                }
            })
            .collect();
        let proof = self.store.add(
            proposition,
            SlottedJustification::Rule {
                name,
                substitution,
                premises,
            },
        );
        self.plain(proof)
    }

    pub fn proposition_to_string(&self, p: &AppliedEquality) -> String {
        format!(
            "{} = {}·{}",
            self.term_dag.to_string(p.lhs),
            p.renaming,
            self.term_dag.to_string(p.rhs)
        )
    }

    pub fn proof_to_string(&self, id: LiftedId) -> String {
        self.store.proof_to_string(self.views[id].proof)
    }

    pub fn finish(self, id: LiftedId) -> (SlottedProofStore, SlottedConclusion) {
        let p = &self.views[id];
        let conclusion = SlottedConclusion {
            proof: p.proof,
            renaming: p.proposition.renaming.clone(),
        };
        (self.store, conclusion)
    }
}

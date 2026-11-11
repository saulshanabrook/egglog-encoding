//! Applied-class views used only while lifting encoded edges. Every view points
//! at an ordinary equality proof; changing its coordinates adds no proof step.

use super::HashMap;
use super::context::ProofContext;
use super::format::{MalformedStep, ProofId, SlottedProofStore};
use super::terms::{Renaming, all_slots, rename};
use egglog::TermId;
use egglog::proof::{Justification, Proposition};
use std::ops::{Deref, DerefMut};

pub(in crate::slotted) type ViewId = usize;

/// Coordinates for an encoded edge, whose actual proof states `lhs = rename(m, rhs)`.
#[derive(Clone, PartialEq, Eq, Hash)]
pub(in crate::slotted) struct AppliedEquality {
    pub lhs: TermId,
    pub renaming: Renaming,
    pub rhs: TermId,
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct View {
    proposition: AppliedEquality,
    proof: ProofId,
}

pub(in crate::slotted) struct Coordinates {
    store: SlottedProofStore,
    views: Vec<View>,
    index: HashMap<View, ViewId>,
}

impl Deref for Coordinates {
    type Target = SlottedProofStore;

    fn deref(&self) -> &Self::Target {
        &self.store
    }
}

impl DerefMut for Coordinates {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.store
    }
}

impl Coordinates {
    pub fn new(store: SlottedProofStore) -> Self {
        Self {
            store,
            views: vec![],
            index: HashMap::default(),
        }
    }

    fn record(&mut self, view: AppliedEquality, proof: ProofId) -> ViewId {
        let actual = self.store.proposition(proof).clone();
        debug_assert_eq!(actual.lhs, view.lhs);
        debug_assert_eq!(
            actual.rhs,
            rename(&mut self.store.term_dag, &view.renaming, view.rhs)
        );
        let lifted = View {
            proposition: view,
            proof,
        };
        if let Some(&id) = self.index.get(&lifted) {
            return id;
        }
        let id = self.views.len();
        self.views.push(lifted.clone());
        self.index.insert(lifted, id);
        id
    }

    pub fn plain(&mut self, proof: ProofId) -> ViewId {
        let p = self.store.proposition(proof);
        self.record(
            AppliedEquality {
                lhs: p.lhs,
                renaming: Renaming::identity(),
                rhs: p.rhs,
            },
            proof,
        )
    }

    pub fn proof(&self, id: ViewId) -> ProofId {
        self.views[id].proof
    }

    pub fn view(&mut self, proof: ProofId, rhs: TermId, renaming: Renaming) -> ViewId {
        self.record(
            AppliedEquality {
                lhs: self.store.proposition(proof).lhs,
                rhs,
                renaming,
            },
            proof,
        )
    }

    pub fn edge(&self, id: ViewId) -> &AppliedEquality {
        &self.views[id].proposition
    }

    pub fn normalize(&self, p: AppliedEquality) -> AppliedEquality {
        AppliedEquality {
            renaming: p.renaming.restricted(&all_slots(&self.term_dag, p.rhs)),
            ..p
        }
    }

    pub fn fiat(&mut self, lhs: TermId, rhs: TermId) -> ViewId {
        let proof = self.store.fiat(lhs, rhs);
        self.plain(proof)
    }

    pub fn sym(&mut self, id: ViewId) -> ViewId {
        let p = self.edge(id).clone();
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
        )
    }

    pub fn trans(&mut self, left: ViewId, right: ViewId) -> Result<ViewId, MalformedStep> {
        let (l, r) = (self.edge(left).clone(), self.edge(right).clone());
        if l.rhs != r.lhs {
            return Err(MalformedStep::MiddleTermMismatch {
                left: self.term_dag.to_string(l.rhs),
                right: self.term_dag.to_string(r.lhs),
            });
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
        ))
    }

    pub fn congr(
        &mut self,
        id: ViewId,
        child_index: usize,
        child: ViewId,
    ) -> Result<ViewId, MalformedStep> {
        let p = self.edge(id).clone();
        let child_proof = self
            .store
            .equivariance(self.views[child].proof, p.renaming.clone());
        let proof = self
            .store
            .congr(self.views[id].proof, child_index, child_proof)?;
        let actual_rhs = self.store.proposition(proof).rhs;
        let rhs = rename(&mut self.term_dag, &p.renaming.inverse(), actual_rhs);
        Ok(self.record(AppliedEquality { rhs, ..p }, proof))
    }

    pub fn project(&mut self, id: ViewId, child_index: usize) -> Result<ViewId, MalformedStep> {
        let inverse = self.edge(id).renaming.inverse();
        let proof = self.store.project(self.views[id].proof, child_index)?;
        let proof = self.store.equivariance(proof, inverse);
        Ok(self.plain(proof))
    }

    /// Change edge coordinates, leaving its ordinary proof untouched.
    pub fn reframe(&mut self, id: ViewId, sigma: Renaming) -> ViewId {
        let p = self.edge(id).clone();
        let rhs = rename(&mut self.term_dag, &sigma, p.rhs);
        let view = AppliedEquality {
            rhs,
            renaming: p.renaming.compose(&sigma.inverse()),
            ..p
        };
        self.record(view, self.views[id].proof)
    }

    pub fn equivariance(&mut self, id: ViewId, sigma: &Renaming) -> ViewId {
        let p = self.edge(id).clone();
        let lhs = rename(&mut self.term_dag, sigma, p.lhs);
        let proof = self.store.equivariance(self.views[id].proof, sigma.clone());
        self.record(
            AppliedEquality {
                lhs,
                renaming: sigma.compose(&p.renaming),
                rhs: p.rhs,
            },
            proof,
        )
    }

    pub fn rule(
        &mut self,
        proposition: Proposition,
        name: String,
        substitution: Vec<(String, TermId)>,
        premises: Vec<ViewId>,
        program: &ProofContext,
    ) -> ViewId {
        let premises: Vec<_> = premises
            .into_iter()
            .enumerate()
            .map(|(i, id)| {
                let p = self.edge(id);
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
        let proof = self.store.ordinary(
            proposition,
            Justification::Rule {
                name,
                substitution: substitution.into_iter().collect(),
                premise_proofs: premises,
            },
        );
        self.plain(proof)
    }

    pub fn edge_to_string(&self, p: &AppliedEquality) -> String {
        format!(
            "{} = {}·{}",
            self.term_dag.to_string(p.lhs),
            p.renaming,
            self.term_dag.to_string(p.rhs)
        )
    }

    pub fn finish(self, id: ViewId) -> (SlottedProofStore, ProofId) {
        (self.store, self.views[id].proof)
    }
}

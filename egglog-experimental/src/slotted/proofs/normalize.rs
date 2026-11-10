//! Push equivariance through ordinary equality steps, sharing each transported
//! subproof, and remove reflexive scaffolding. Source steps retain their checked
//! instantiations; any remaining equivariance is immediately above a source step.

use super::HashMap;
use super::format::{ProofId, RulePremise, SlottedProof, SlottedProofStore};
use super::terms::{Renaming, all_slots, rename, slot_of};
use egglog::Term;
use egglog::proof::Justification as Step;

type Key = (ProofId, Renaming);

impl SlottedProofStore {
    /// Normalize an already checked proof. Check the resulting proof again before
    /// using it, just as for any other proof transformation.
    pub fn simplify(&mut self, root: ProofId) -> ProofId {
        // Only the action on a step's endpoints matters. Keeping unrelated
        // coordinates in the memo key can expand a shared proof exponentially
        // when it is reached through different binder-renaming paths.
        let support: HashMap<_, _> = self
            .dependencies(root)
            .into_iter()
            .map(|id| {
                let p = self.proposition(id);
                let mut slots = all_slots(&self.term_dag, p.lhs);
                slots.extend(all_slots(&self.term_dag, p.rhs));
                (id, slots)
            })
            .collect();
        let root = (root, Renaming::identity());
        let mut memo = HashMap::<Key, ProofId>::default();
        let mut work = vec![(root.clone(), false)];
        while let Some(((id, rho), ready)) = work.pop() {
            let key = (id, rho.clone());
            if memo.contains_key(&key) {
                continue;
            }
            let proof = self.get(id).clone();
            let children: Vec<Key> = match &proof {
                SlottedProof::Equivariance {
                    proof, renaming, ..
                } => vec![(*proof, rho.compose(renaming))],
                SlottedProof::Rule(_) => proof
                    .premises()
                    .into_iter()
                    .map(|p| (p, Renaming::identity()))
                    .collect(),
                _ => proof
                    .premises()
                    .into_iter()
                    .map(|p| (p, rho.clone()))
                    .collect(),
            }
            .into_iter()
            .map(|(id, rho)| (id, rho.restricted(&support[&id])))
            .collect();
            if !ready {
                work.push((key, true));
                work.extend(children.into_iter().rev().map(|k| (k, false)));
                continue;
            }
            let children: Vec<_> = children.iter().map(|k| memo[k]).collect();
            let result = match proof {
                SlottedProof::Rule(mut proof) => {
                    let normalized = |p| memo[&(p, Renaming::identity())];
                    proof.premises = proof
                        .premises
                        .into_iter()
                        .map(|p| match p {
                            RulePremise::Equality(p) => RulePremise::Equality(normalized(p)),
                            RulePremise::RenamingEq { left, right } => RulePremise::RenamingEq {
                                left: normalized(left),
                                right: normalized(right),
                            },
                        })
                        .collect();
                    self.simplify_source(SlottedProof::Rule(proof), &rho)
                }
                SlottedProof::Equivariance { .. } => children[0],
                SlottedProof::Alpha { proposition, .. } => {
                    let rhs = rename(&mut self.term_dag, &rho, proposition.rhs);
                    if rhs == self.proposition(children[0]).rhs {
                        children[0]
                    } else {
                        self.alpha(children[0], rhs)
                    }
                }
                SlottedProof::Ordinary(proof) => match proof.justification() {
                    Step::Sym(_) => self.simple_sym(children[0]),
                    Step::Proj { child_index, .. } => self
                        .project(children[0], *child_index)
                        .expect("normalizing preserves projected children"),
                    Step::Trans(..) => {
                        let (a, b) = (children[0], children[1]);
                        if self.reflexive(a) {
                            b
                        } else if self.reflexive(b) {
                            a
                        } else {
                            self.trans(a, b)
                                .expect("normalizing preserves middle terms")
                        }
                    }
                    Step::Congr { child_index, .. } => {
                        if self.reflexive(children[1]) {
                            children[0]
                        } else {
                            self.congr(children[0], *child_index, children[1])
                                .expect("normalizing preserves child terms")
                        }
                    }
                    Step::Fiat => self.simplify_source(SlottedProof::Ordinary(proof), &rho),
                    _ => unreachable!("normalization requires a checked slotted proof"),
                },
            };
            memo.insert(key, result);
        }
        memo[&root]
    }

    fn simplify_source(&mut self, proof: SlottedProof, rho: &Renaming) -> ProofId {
        let p = proof.proposition();
        let lhs = rename(&mut self.term_dag, rho, p.lhs);
        let rhs = rename(&mut self.term_dag, rho, p.rhs);
        if lhs == rhs
            && (slot_of(&self.term_dag, lhs).is_some()
                || matches!(self.term_dag.get(lhs), Term::Lit(_)))
        {
            return self.fiat(lhs, rhs);
        }
        let unchanged = (lhs, rhs) == (p.lhs, p.rhs);
        let slots = all_slots(&self.term_dag, p.lhs)
            .union(&all_slots(&self.term_dag, p.rhs))
            .copied()
            .collect();
        let source = self.add(proof);
        if unchanged {
            source
        } else {
            self.equivariance(source, rho.restricted(&slots))
        }
    }

    fn reflexive(&self, p: ProofId) -> bool {
        let p = self.proposition(p);
        p.lhs == p.rhs
    }

    fn simple_sym(&mut self, p: ProofId) -> ProofId {
        if self.reflexive(p) {
            p
        } else if let SlottedProof::Ordinary(proof) = self.get(p)
            && let Step::Sym(inner) = proof.justification()
        {
            *inner
        } else {
            self.sym(p)
        }
    }
}

#[cfg(test)]
#[path = "tests/normalize.rs"]
mod tests;

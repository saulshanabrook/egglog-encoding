//! Simplify a checked proof while preserving shared subproofs and source steps.

use super::HashMap;
use super::format::{ProofId, RulePremise, SlottedProof, SlottedProofStore};
use egglog::proof::Justification as Step;

impl SlottedProofStore {
    /// Simplify an already checked proof without changing its proposition.
    /// Check the resulting proof again before using it.
    pub fn simplify(&mut self, root: ProofId) -> ProofId {
        let mut memo = HashMap::<ProofId, ProofId>::default();
        let mut work = vec![(root, false)];
        while let Some((id, ready)) = work.pop() {
            if memo.contains_key(&id) {
                continue;
            }
            let proof = self.get(id);
            let bypass = match proof {
                SlottedProof::Ordinary(proof) => match proof.justification() {
                    Step::Trans(a, b) if self.reflexive(*a) => Some(*b),
                    Step::Trans(a, b) if self.reflexive(*b) => Some(*a),
                    Step::Congr {
                        proof, child_proof, ..
                    } if self.reflexive(*child_proof) => Some(*proof),
                    Step::Sym(p) if self.reflexive(*p) => Some(*p),
                    _ => None,
                },
                _ => None,
            };
            let children = bypass.map_or_else(|| proof.premises(), |p| vec![p]);
            if !ready {
                work.push((id, true));
                work.extend(children.into_iter().rev().map(|p| (p, false)));
                continue;
            }
            let children: Vec<_> = children.iter().map(|p| memo[p]).collect();
            if bypass.is_some() {
                memo.insert(id, children[0]);
                continue;
            }
            let result = match self.get(id).clone() {
                SlottedProof::Rule(mut proof) => {
                    proof.premises = proof
                        .premises
                        .into_iter()
                        .map(|p| match p {
                            RulePremise::Equality(p) => RulePremise::Equality(memo[&p]),
                            RulePremise::RenamingEq { left, right } => RulePremise::RenamingEq {
                                left: memo[&left],
                                right: memo[&right],
                            },
                        })
                        .collect();
                    self.add(SlottedProof::Rule(proof))
                }
                SlottedProof::Equivariance {
                    proposition,
                    mut renaming,
                    ..
                } => {
                    let mut proof = children[0];
                    if let SlottedProof::Equivariance {
                        proof: inner,
                        renaming: rho,
                        ..
                    } = self.get(proof)
                    {
                        renaming = renaming.compose(rho);
                        proof = *inner;
                    }
                    if &proposition == self.proposition(proof) {
                        proof
                    } else {
                        // Distributing this renaming over a shared derivation
                        // can create a distinct copy for every path to a source step.
                        self.add(SlottedProof::Equivariance {
                            proposition,
                            proof,
                            renaming,
                        })
                    }
                }
                SlottedProof::Alpha { proposition, .. } => {
                    let mut proof = children[0];
                    if let SlottedProof::Alpha { proof: inner, .. } = self.get(proof) {
                        proof = *inner;
                    }
                    self.alpha(proof, proposition.rhs)
                }
                SlottedProof::Ordinary(proof) => match proof.justification() {
                    Step::Sym(_) => self.simple_sym(children[0]),
                    Step::Proj { child_index, .. } => self
                        .project(children[0], *child_index)
                        .expect("simplifying preserves projected children"),
                    Step::Trans(..) => self
                        .trans(children[0], children[1])
                        .expect("simplifying preserves middle terms"),
                    Step::Congr { child_index, .. } => self
                        .congr(children[0], *child_index, children[1])
                        .expect("simplifying preserves child terms"),
                    Step::Fiat => id,
                    _ => unreachable!("simplification requires a checked slotted proof"),
                },
            };
            memo.insert(id, result);
        }
        memo[&root]
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

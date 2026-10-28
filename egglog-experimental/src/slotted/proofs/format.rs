//! Ordinary equalities over slotted surface terms and their justifications.

use super::HashMap;
use super::terms::{Renaming, all_slots, rename, slot_of};
use egglog::{Term, TermDag, TermId, ast::Literal, proof::proof_term_to_string};
use std::collections::{BTreeMap, BTreeSet};

/// An index into a [`SlottedProofStore`].
pub type SlottedProofId = usize;

/// An ordinary equality between two surface terms.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct SlottedProposition {
    /// The term on the left.
    pub lhs: TermId,
    /// The term on the right.
    pub rhs: TermId,
}

impl SlottedProposition {
    /// State an equality. Any renaming has already been applied to the terms.
    pub fn equal(lhs: TermId, rhs: TermId) -> Self {
        Self { lhs, rhs }
    }
}

/// An ordinary proof of `lhs = rename(renaming, rhs)` for a surface claim.
/// The witness belongs to the claim, not to the proof's equality propositions.
#[derive(Clone, Debug)]
pub struct SlottedConclusion {
    /// The ordinary equality proof.
    pub proof: SlottedProofId,
    /// How the requested right-hand term is named in the proof.
    pub renaming: Renaming,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
/// A source axiom, rewrite application, or operation on earlier proof steps.
pub enum SlottedJustification {
    /// A term the program built, or a source `union`.
    Fiat,
    /// A rewrite instantiated by the substitution, given proofs of its premises:
    /// the root pattern first, then each `:when` equality pattern in order.
    Rule {
        /// The source rewrite's name.
        name: String,
        /// Source variables and the terms substituted for them.
        substitution: Vec<(String, TermId)>,
        /// Proofs of the rewrite's pattern premises, in source order.
        premises: Vec<SlottedProofId>,
    },
    /// Reverse an equality.
    Sym(SlottedProofId),
    /// Compose equalities with matching middle terms.
    Trans(SlottedProofId, SlottedProofId),
    /// Replace one right-hand child using an equality proof.
    Congr {
        /// The equality whose right-hand term is updated.
        proof: SlottedProofId,
        /// The child's zero-based surface column.
        child_index: usize,
        /// The equality used to replace the child.
        child_proof: SlottedProofId,
    },
    /// Establish a right-hand child's reflexivity from its parent's proof.
    Proj {
        /// The proof whose right-hand term contains the child.
        proof: SlottedProofId,
        /// The child's zero-based surface column.
        child_index: usize,
    },
    /// Apply one finite slot permutation to both sides of a proved equality.
    Equivariance {
        /// The equality being transported.
        proof: SlottedProofId,
        /// The permutation applied to both terms.
        renaming: Renaming,
    },
}

#[derive(Clone, Debug)]
/// A proposition together with the step that justifies it.
pub struct SlottedProof {
    /// The equality stated by this step.
    pub proposition: SlottedProposition,
    /// How it follows from the source program or earlier steps.
    pub justification: SlottedJustification,
}

/// Distinct slotted proof steps over one [`TermDag`].
#[derive(Clone, Debug, Default)]
pub struct SlottedProofStore {
    /// Shared storage for source terms and instantiated terms.
    pub term_dag: TermDag,
    slot_names: BTreeMap<i64, String>,
    proofs: Vec<SlottedProof>,
    index: HashMap<(SlottedProposition, SlottedJustification), SlottedProofId>,
}

/// Why a derived step could not be formed from its inputs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MalformedStep(pub String);

impl SlottedProofStore {
    /// Start a proof store over an existing term dag.
    pub fn new(term_dag: TermDag) -> Self {
        Self {
            slot_names: (0..term_dag.size())
                .filter_map(|t| slot_of(&term_dag, t))
                .map(|s| (s, format!("${s}")))
                .collect(),
            term_dag,
            ..Default::default()
        }
    }

    /// Use the compiler's source spellings when displaying encoded slot IDs.
    pub fn with_slot_names(mut self, names: &BTreeMap<String, i64>) -> Self {
        self.slot_names = names.iter().map(|(name, &id)| (id, name.clone())).collect();
        self
    }

    /// The number of distinct proof steps stored.
    pub fn len(&self) -> usize {
        self.proofs.len()
    }

    /// Whether the store contains no proof steps.
    pub fn is_empty(&self) -> bool {
        self.proofs.is_empty()
    }

    /// Look up a proof step by its store-local index.
    pub fn get(&self, id: SlottedProofId) -> &SlottedProof {
        &self.proofs[id]
    }

    /// The proposition stated by a stored proof step.
    pub fn proposition(&self, id: SlottedProofId) -> &SlottedProposition {
        &self.proofs[id].proposition
    }

    /// Record a proof as stated. The checker decides whether it is valid.
    pub fn add(
        &mut self,
        proposition: SlottedProposition,
        justification: SlottedJustification,
    ) -> SlottedProofId {
        let key = (proposition, justification);
        if let Some(&id) = self.index.get(&key) {
            return id;
        }
        let id = self.proofs.len();
        self.proofs.push(SlottedProof {
            proposition: key.0.clone(),
            justification: key.1.clone(),
        });
        self.index.insert(key, id);
        id
    }

    /// State a source union or a built term's reflexivity; the checker validates it.
    pub fn fiat(&mut self, lhs: TermId, rhs: TermId) -> SlottedProofId {
        self.add(
            SlottedProposition::equal(lhs, rhs),
            SlottedJustification::Fiat,
        )
    }

    /// Reverse the endpoints of an equality.
    pub fn sym(&mut self, proof: SlottedProofId) -> SlottedProofId {
        let p = self.proposition(proof).clone();
        self.add(
            SlottedProposition::equal(p.rhs, p.lhs),
            SlottedJustification::Sym(proof),
        )
    }

    /// Compose equalities whose middle terms match exactly.
    pub fn trans(
        &mut self,
        left: SlottedProofId,
        right: SlottedProofId,
    ) -> Result<SlottedProofId, MalformedStep> {
        let (l, r) = (
            self.proposition(left).clone(),
            self.proposition(right).clone(),
        );
        if l.rhs != r.lhs {
            return Err(MalformedStep(format!(
                "trans: middle terms differ: {} vs {}",
                self.term_dag.to_string(l.rhs),
                self.term_dag.to_string(r.lhs)
            )));
        }
        Ok(self.add(
            SlottedProposition::equal(l.lhs, r.rhs),
            SlottedJustification::Trans(left, right),
        ))
    }

    /// Replace a child using an ordinary equality `c = c'`.
    pub fn congr(
        &mut self,
        proof: SlottedProofId,
        child_index: usize,
        child_proof: SlottedProofId,
    ) -> Result<SlottedProofId, MalformedStep> {
        let p = self.proposition(proof).clone();
        let c = self.proposition(child_proof).clone();
        let Term::App(head, children) = self.term_dag.get(p.rhs).clone() else {
            return Err(MalformedStep(
                "congr: right-hand side is not an application".into(),
            ));
        };
        let Some(&child) = children.get(child_index) else {
            return Err(MalformedStep(format!("congr: no child {child_index}")));
        };
        if child != c.lhs {
            return Err(MalformedStep(format!(
                "congr: child {} is not the child proof's left side {}",
                self.term_dag.to_string(child),
                self.term_dag.to_string(c.lhs)
            )));
        }
        let mut children = children;
        children[child_index] = c.rhs;
        let rhs = self.term_dag.app(head, children);
        Ok(self.add(
            SlottedProposition::equal(p.lhs, rhs),
            SlottedJustification::Congr {
                proof,
                child_index,
                child_proof,
            },
        ))
    }

    /// Derive `sigma(lhs) = sigma(rhs)` by equivariance of the slotted theory.
    pub fn equivariance(&mut self, proof: SlottedProofId, sigma: Renaming) -> SlottedProofId {
        if sigma.is_identity() {
            return proof;
        }
        let p = self.proposition(proof).clone();
        let lhs = rename(&mut self.term_dag, &sigma, p.lhs);
        let rhs = rename(&mut self.term_dag, &sigma, p.rhs);
        self.add(
            SlottedProposition::equal(lhs, rhs),
            SlottedJustification::Equivariance {
                proof,
                renaming: sigma,
            },
        )
    }

    /// Establish that a child of the proved right-hand term exists.
    pub fn project(
        &mut self,
        proof: SlottedProofId,
        child_index: usize,
    ) -> Result<SlottedProofId, MalformedStep> {
        let Term::App(_, children) = self.term_dag.get(self.proposition(proof).rhs) else {
            return Err(MalformedStep("projection needs an application".into()));
        };
        let child = *children
            .get(child_index)
            .ok_or_else(|| MalformedStep("projection index out of bounds".into()))?;
        Ok(self.add(
            SlottedProposition::equal(child, child),
            SlottedJustification::Proj { proof, child_index },
        ))
    }

    /// The proofs `root` depends on, dependencies first, `root` last.
    pub fn dependencies(&self, root: SlottedProofId) -> Vec<SlottedProofId> {
        let mut order = vec![];
        let mut state: HashMap<SlottedProofId, bool> = HashMap::default();
        let mut stack = vec![(root, false)];
        while let Some((id, children_done)) = stack.pop() {
            if children_done {
                order.push(id);
                state.insert(id, true);
                continue;
            }
            if state.contains_key(&id) {
                continue;
            }
            state.insert(id, false);
            stack.push((id, true));
            for dep in self.children(id) {
                if !state.contains_key(&dep) {
                    stack.push((dep, false));
                }
            }
        }
        order
    }

    /// The immediate proof dependencies of a step.
    pub fn children(&self, id: SlottedProofId) -> Vec<SlottedProofId> {
        match &self.proofs[id].justification {
            SlottedJustification::Fiat => vec![],
            SlottedJustification::Rule { premises, .. } => premises.clone(),
            SlottedJustification::Sym(p) | SlottedJustification::Equivariance { proof: p, .. } => {
                vec![*p]
            }
            SlottedJustification::Proj { proof, .. } => vec![*proof],
            SlottedJustification::Trans(a, b) => vec![*a, *b],
            SlottedJustification::Congr {
                proof, child_proof, ..
            } => vec![*proof, *child_proof],
        }
    }

    /// Display an ordinary equality in source slot names.
    pub fn proposition_to_string(&self, p: &SlottedProposition) -> String {
        self.named_proposition(p, &self.display_names(None, []))
    }

    /// Name terms and permutation coordinates without colliding with source slots
    /// or rule variables.
    fn display_names(
        &self,
        root: Option<SlottedProofId>,
        extra: impl IntoIterator<Item = i64>,
    ) -> BTreeMap<i64, String> {
        let mut names = self.slot_names.clone();
        let mut used: BTreeSet<String> = names.values().cloned().collect();
        for t in 0..self.term_dag.size() {
            if let Term::Var(v) = self.term_dag.get(t) {
                used.insert(format!("${}", v.trim_start_matches('$')));
            }
        }
        let mut slots = vec![];
        let ids = root
            .map(|p| self.dependencies(p))
            .unwrap_or_else(|| (0..self.len()).collect());
        for id in ids {
            let proof = self.get(id);
            let mut terms = vec![proof.proposition.rhs, proof.proposition.lhs];
            match &proof.justification {
                SlottedJustification::Equivariance { renaming, .. } => {
                    slots.extend(renaming.entries().flat_map(|(a, b)| [a, b]));
                }
                SlottedJustification::Rule { substitution, .. } => {
                    used.extend(
                        substitution
                            .iter()
                            .map(|(v, _)| format!("${}", v.trim_start_matches('$'))),
                    );
                    terms.extend(substitution.iter().rev().map(|(_, t)| *t));
                }
                _ => {}
            }
            while let Some(term) = terms.pop() {
                if let Some(slot) = slot_of(&self.term_dag, term) {
                    slots.push(slot);
                } else if let Term::App(_, children) = self.term_dag.get(term) {
                    terms.extend(children.iter().rev().copied());
                }
            }
        }
        if root.is_none() {
            slots.extend((0..self.term_dag.size()).filter_map(|t| slot_of(&self.term_dag, t)));
        }
        let mut next = 0;
        for slot in slots.into_iter().chain(extra) {
            names.entry(slot).or_insert_with(|| {
                loop {
                    let name = format!("$v{next}");
                    next += 1;
                    if used.insert(name.clone()) {
                        break name;
                    }
                }
            });
        }
        names
    }

    fn named_term(&self, term: TermId, names: &BTreeMap<i64, String>) -> String {
        if let Some(slot) = slot_of(&self.term_dag, term) {
            return names[&slot].clone();
        }
        match self.term_dag.get(term) {
            Term::App(head, children) if !children.is_empty() => format!(
                "({head} {})",
                children
                    .iter()
                    .map(|&c| self.named_term(c, names))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            _ => self.term_dag.to_string(term),
        }
    }

    fn named_dag(&self, names: &BTreeMap<i64, String>) -> (TermDag, Vec<TermId>) {
        let mut dag = TermDag::default();
        let mut terms = Vec::with_capacity(self.term_dag.size());
        for id in 0..self.term_dag.size() {
            let term = match self.term_dag.get(id) {
                Term::Var(v) => dag.var(
                    slot_of(&self.term_dag, id)
                        .and_then(|slot| names.get(&slot))
                        .unwrap_or(v)
                        .clone(),
                ),
                Term::Lit(lit) => dag.lit(lit.clone()),
                Term::App(head, children) => dag.app(
                    head.clone(),
                    children.iter().map(|&child| terms[child]).collect(),
                ),
            };
            terms.push(term);
        }
        (dag, terms)
    }

    fn renaming_term(
        dag: &mut TermDag,
        renaming: &Renaming,
        names: &BTreeMap<i64, String>,
    ) -> TermId {
        let entries = renaming
            .entries()
            .map(|(a, b)| {
                let target = dag.var(names[&b].clone());
                dag.app(names[&a].clone(), vec![target])
            })
            .collect();
        dag.app("renaming".into(), entries)
    }

    fn named_proposition(&self, p: &SlottedProposition, names: &BTreeMap<i64, String>) -> String {
        format!(
            "{} = {}",
            self.named_term(p.lhs, names),
            self.named_term(p.rhs, names)
        )
    }

    /// Print a proof in egglog's S-expression format, with source slot names.
    pub fn proof_to_string(&self, root: SlottedProofId) -> String {
        let names = self.display_names(Some(root), []);
        let (mut dag, terms) = self.named_dag(&names);
        let proof = self.proof_term(root, &mut dag, &terms, &names);
        proof_term_to_string(&dag, proof)
    }

    fn proof_term(
        &self,
        root: SlottedProofId,
        dag: &mut TermDag,
        terms: &[TermId],
        names: &BTreeMap<i64, String>,
    ) -> TermId {
        let mut proofs = HashMap::default();
        for id in self.dependencies(root) {
            let proof = &self.proofs[id];
            let equality = dag.app(
                "=".into(),
                vec![terms[proof.proposition.lhs], terms[proof.proposition.rhs]],
            );
            let term = match &proof.justification {
                SlottedJustification::Fiat => dag.app("Fiat".into(), vec![equality]),
                SlottedJustification::Rule {
                    name,
                    substitution,
                    premises,
                } => {
                    let name = dag.lit(Literal::String(name.clone()));
                    let name = dag.app("name".into(), vec![name]);
                    let premises = dag.app(
                        "premises".into(),
                        premises.iter().map(|p| proofs[p]).collect(),
                    );
                    let substitution = substitution
                        .iter()
                        .map(|(var, term)| dag.app(var.clone(), vec![terms[*term]]))
                        .collect();
                    let substitution = dag.app("substitution".into(), substitution);
                    dag.app("Rule".into(), vec![equality, name, premises, substitution])
                }
                SlottedJustification::Sym(p) => dag.app("Sym".into(), vec![equality, proofs[p]]),
                SlottedJustification::Trans(a, b) => {
                    dag.app("Trans".into(), vec![equality, proofs[a], proofs[b]])
                }
                SlottedJustification::Congr {
                    proof,
                    child_index,
                    child_proof,
                } => {
                    let index = dag.lit(Literal::Int(*child_index as i64));
                    dag.app(
                        "Congr".into(),
                        vec![equality, proofs[proof], proofs[child_proof], index],
                    )
                }
                SlottedJustification::Equivariance { proof, renaming } => {
                    let renaming = Self::renaming_term(dag, renaming, names);
                    dag.app(
                        "Equivariance".into(),
                        vec![equality, proofs[proof], renaming],
                    )
                }
                SlottedJustification::Proj { proof, child_index } => {
                    let index = dag.lit(Literal::Int(*child_index as i64));
                    dag.app("Proj".into(), vec![equality, proofs[proof], index])
                }
            };
            proofs.insert(id, term);
        }
        proofs[&root]
    }

    /// Print the proof, wrapped in a `Claim` when a renaming witness is needed.
    pub fn conclusion_to_string(&mut self, conclusion: &SlottedConclusion) -> String {
        let p = self.proposition(conclusion.proof).clone();
        let rhs = rename(&mut self.term_dag, &conclusion.renaming.inverse(), p.rhs);
        let witness = conclusion
            .renaming
            .restricted(&all_slots(&self.term_dag, rhs));
        let names = self.display_names(
            Some(conclusion.proof),
            witness.entries().flat_map(|(a, b)| [a, b]),
        );
        let (mut dag, terms) = self.named_dag(&names);
        let mut proof = self.proof_term(conclusion.proof, &mut dag, &terms, &names);
        if rhs != p.rhs {
            let renaming = Self::renaming_term(&mut dag, &witness, &names);
            let rhs = dag.app("rename".into(), vec![renaming, terms[rhs]]);
            let equality = dag.app("=".into(), vec![terms[p.lhs], rhs]);
            proof = dag.app("Claim".into(), vec![equality, proof]);
        }
        proof_term_to_string(&dag, proof)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::slotted::proofs::terms::slot_term;

    #[test]
    fn fresh_display_names_cover_permutation_only_coordinates() {
        let mut dag = TermDag::default();
        let a = slot_term(&mut dag, 10);
        dag.var("v1".into());
        let mut store = SlottedProofStore::new(dag)
            .with_slot_names(&BTreeMap::from([("$a".into(), 10), ("$v0".into(), 20)]));
        let refl = store.fiat(a, a);
        let proof = store.equivariance(refl, Renaming::new([(30, 31), (31, 30)]).unwrap());
        assert_eq!(
            store.proof_to_string(proof),
            "(Equivariance (= $a $a) (Fiat (= $a $a)) (renaming ($v2 $v3) ($v3 $v2)))"
        );
    }
}

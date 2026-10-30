//! Import existing evidence and compose ordinary raw proofs for ground terms.

use super::ground::{Node, Row, fail};
use super::proof_extractor::RootExtractor;
use super::proof_format::{ProofId, ProofStore, RawProof, RawProofId, RawProofStore};
use crate::*;
use std::iter::once;

/// A raw proof together with the endpoints needed to compose it.
/// All IDs belong to the enclosing [`Proofs`] store and its term DAG.
#[derive(Clone, Copy)]
pub(super) struct RawEquality {
    pub(super) proof: RawProofId,
    pub(super) lhs: TermId,
    pub(super) rhs: TermId,
}

/// Raw operations and their decoded or composition-derived conclusions.
pub(super) struct Proofs {
    pub(super) raw: RawProofStore,
    conclusions: HashMap<RawProofId, RawEquality>,
    normalizers: HashMap<String, PrimitiveValidator>,
    value_heads: HashSet<String>,
}

impl Proofs {
    /// Import the looked-up rows and decode their dependencies once. Returned
    /// nodes retain their input order and carry proofs with known endpoints.
    pub(super) fn import(
        egraph: &EGraph,
        nodes: Vec<Node>,
    ) -> Result<(Self, Vec<Node<RawEquality>>), Error> {
        let normalizers: HashMap<_, _> = egraph
            .type_info
            .sorts
            .values()
            .filter_map(|sort| sort.rebuild_container_normalizer())
            .collect();
        let mut value_heads = HashSet::default();
        for sort in egraph.type_info.sorts.values() {
            if let Some(head) = sort.prim_value_constructor() {
                if egraph.type_info.get_prims(&head).map_or(0, <[_]>::len) != 1 {
                    return Err(fail(format!(
                        "ambiguous primitive value constructor {head}"
                    )));
                }
                value_heads.insert(head);
            }
        }
        let sort = egraph
            .get_sort_by_name(&egraph.proof_state.proof_names.proof_datatype)
            .ok_or_else(|| fail("missing proof sort"))?
            .clone();
        let mut raw = RawProofStore::new(&egraph.proof_state.proof_names);
        let mut extractor = RootExtractor::new();
        let mut imported = HashMap::default();
        for node in &nodes {
            if let Some(row) = node.row {
                for value in once(row.proof).chain(row.to_leader) {
                    if imported.contains_key(&value) {
                        continue;
                    }
                    let term = extractor
                        .extract(egraph, &mut raw.term_dag, value, &sort)
                        .ok_or_else(|| fail("could not materialize existing proof evidence"))?;
                    imported.insert(value, raw.parse(term));
                }
            }
        }
        // Eval is a rule side condition, not a standalone equality.
        let roots = raw
            .proofs()
            .filter_map(|(id, proof)| (!matches!(proof, RawProof::Eval)).then_some(id))
            .collect::<Vec<_>>();
        let (decoded, ids) = raw.lift(
            &egraph.proof_check_program,
            &roots,
            normalizers.clone(),
            value_heads.clone(),
        );
        let conclusions: HashMap<_, _> = roots
            .into_iter()
            .zip(ids)
            .map(|(proof, id)| {
                let equality = decoded.get(id);
                (
                    proof,
                    RawEquality {
                        proof,
                        lhs: equality.lhs(),
                        rhs: equality.rhs(),
                    },
                )
            })
            .collect();
        raw.term_dag = decoded.term_dag;
        let nodes = nodes
            .into_iter()
            .map(|node| Node {
                value: node.value,
                row: node.row.map(|row| Row {
                    kind: row.kind,
                    proof: conclusions[&imported[&row.proof]],
                    to_leader: row.to_leader.map(|value| conclusions[&imported[&value]]),
                }),
            })
            .collect();
        Ok((
            Self {
                raw,
                conclusions,
                normalizers,
                value_heads,
            },
            nodes,
        ))
    }

    /// Record an operation and its conclusion. The endpoints must describe that operation.
    pub(super) fn add(&mut self, operation: RawProof, lhs: TermId, rhs: TermId) -> RawEquality {
        let proof = self.raw.add_proof(operation);
        let equality = RawEquality { proof, lhs, rhs };
        self.conclusions.insert(proof, equality);
        equality
    }

    /// Reverse an equality.
    pub(super) fn sym(&mut self, proof: RawEquality) -> RawEquality {
        self.add(RawProof::Sym(proof.proof), proof.rhs, proof.lhs)
    }

    /// Compose equalities whose middle terms agree.
    pub(super) fn trans(&mut self, left: RawEquality, right: RawEquality) -> RawEquality {
        self.add(
            RawProof::Trans(left.proof, right.proof),
            left.lhs,
            right.rhs,
        )
    }

    /// Establish reflexivity at a proof's right endpoint.
    fn reflexive(&mut self, proof: RawEquality) -> RawEquality {
        if proof.lhs == proof.rhs {
            return proof;
        }
        let back = self.sym(proof);
        self.trans(back, proof)
    }

    /// Establish reflexivity at a child of the right endpoint. The child must exist.
    pub(super) fn project(&mut self, proof: RawEquality, child: usize) -> RawEquality {
        let Term::App(_, children) = self.raw.term_dag.get(proof.rhs) else {
            unreachable!("projection requires an application")
        };
        let term = children[child];
        self.add(RawProof::Proj(proof.proof, child), term, term)
    }

    /// Rewrite a child of the right endpoint. That child must equal `step.lhs`.
    pub(super) fn congr(
        &mut self,
        proof: RawEquality,
        child: usize,
        step: RawEquality,
    ) -> RawEquality {
        let Term::App(head, children) = self.raw.term_dag.get(proof.rhs).clone() else {
            unreachable!("congruence requires an application")
        };
        let mut children = children;
        children[child] = step.rhs;
        let rhs = self.raw.term_dag.app(head, children);
        self.add(
            RawProof::Congr(proof.proof, child, step.proof),
            proof.lhs,
            rhs,
        )
    }

    /// Normalize a container term, or retain a non-container term.
    fn normalize(&mut self, term: TermId) -> TermId {
        let Term::App(head, children) = self.raw.term_dag.get(term).clone() else {
            return term;
        };
        match self.normalizers.get(&head) {
            Some(validate) => {
                validate(&mut self.raw.term_dag, &children).expect("valid container term")
            }
            None => term,
        }
    }

    /// Append normalization of the right endpoint when it changes the term.
    fn normalize_proof(&mut self, proof: RawEquality) -> RawEquality {
        let rhs = self.normalize(proof.rhs);
        if rhs == proof.rhs {
            return proof;
        }
        self.add(RawProof::ContainerNormalize(proof.proof), proof.lhs, rhs)
    }

    /// Equality evidence reachable from these raw roots. Eval markers have no conclusion.
    pub(super) fn dependencies(&self, roots: &[RawEquality]) -> Vec<RawEquality> {
        let mut pending = roots
            .iter()
            .rev()
            .map(|proof| proof.proof)
            .collect::<Vec<_>>();
        let mut seen = HashSet::default();
        let mut result = Vec::new();
        while let Some(id) = pending.pop() {
            if !seen.insert(id) {
                continue;
            }
            if let Some(proof) = self.conclusions.get(&id) {
                result.push(*proof);
            }
            match self.raw.get(id) {
                RawProof::Fiat(..)
                | RawProof::FiatTerm(..)
                | RawProof::FiatUnion(..)
                | RawProof::Eval => {}
                RawProof::Rule(_, premises, bridges, _) => {
                    pending.extend(premises.iter().chain(bridges).rev().copied())
                }
                RawProof::ProjPrim(_, _, arguments) => {
                    pending.extend(arguments.iter().rev().copied())
                }
                RawProof::Trans(left, right)
                | RawProof::CongrAll(left, right)
                | RawProof::Congr(left, _, right)
                | RawProof::MergeFnIdx(_, left, right, _)
                | RawProof::MergeFnRow(_, left, right) => pending.extend([*right, *left]),
                RawProof::Sym(proof)
                | RawProof::Proj(proof, _)
                | RawProof::ContainerNormalize(proof) => pending.push(*proof),
            }
        }
        result
    }

    /// Find the requested equality in either orientation in `evidence`.
    pub(super) fn equality(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        evidence: &[RawEquality],
    ) -> Option<RawEquality> {
        for &proof in evidence {
            if proof.lhs == lhs && proof.rhs == rhs {
                return Some(proof);
            }
            if proof.rhs == lhs && proof.lhs == rhs {
                return Some(self.sym(proof));
            }
        }
        None
    }

    /// Project `term` from either endpoint of the supplied evidence.
    fn witness(&mut self, term: TermId, evidence: &[RawEquality]) -> Option<RawEquality> {
        for &proof in evidence {
            for (endpoint, reverse) in [(proof.rhs, false), (proof.lhs, true)] {
                if let Some(path) = self.path(endpoint, term) {
                    let mut proof = if reverse { self.sym(proof) } else { proof };
                    for child in path {
                        proof = self.project(proof, child);
                    }
                    return Some(proof);
                }
            }
        }
        None
    }

    /// A projection path to `target`, including the empty path for `root` itself.
    fn path(&self, root: TermId, target: TermId) -> Option<Vec<usize>> {
        if root == target {
            return Some(vec![]);
        }
        let mut pending = vec![(root, vec![])];
        let mut seen = HashSet::default();
        while let Some((term, path)) = pending.pop() {
            if !seen.insert(term) {
                continue;
            }
            if let Term::App(_, children) = self.raw.term_dag.get(term) {
                for (index, &child) in children.iter().enumerate().rev() {
                    let mut path = path.clone();
                    path.push(index);
                    if child == target {
                        return Some(path);
                    }
                    pending.push((child, path));
                }
            }
        }
        None
    }

    /// Whether reflexivity is justified by a literal or a base value constructor.
    fn value_term(&self, term: TermId) -> bool {
        match self.raw.term_dag.get(term) {
            Term::Lit(_) => true,
            Term::App(head, children) => {
                self.value_heads.contains(head)
                    && children.iter().all(|&child| self.value_term(child))
            }
            Term::Var(_) => false,
        }
    }

    /// Replace proved argument terms by their leaders and normalize containers.
    fn leader(&mut self, term: TermId, arguments: &[RawEquality]) -> TermId {
        if let Some(proof) = arguments.iter().find(|proof| proof.lhs == term) {
            return proof.rhs;
        }
        if let Term::App(head, children) = self.raw.term_dag.get(term).clone()
            && self.normalizers.contains_key(&head)
        {
            let children = children
                .into_iter()
                .map(|child| self.leader(child, arguments))
                .collect();
            let term = self.raw.term_dag.app(head, children);
            return self.normalize(term);
        }
        term
    }

    /// Prove `lhs = rhs` using argument-to-leader equalities and reachable evidence.
    /// Errors when the requested endpoints cannot be connected. A container whose
    /// shape changed during normalization needs a witness of its original shape.
    pub(super) fn certificate(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        arguments: &[RawEquality],
        evidence: &[RawEquality],
    ) -> Result<RawEquality, Error> {
        if let Some(proof) = self.equality(lhs, rhs, evidence) {
            return Ok(proof);
        }
        if lhs == rhs && self.value_term(lhs) {
            return Ok(self.add(RawProof::Fiat(lhs, lhs), lhs, lhs));
        }
        if let Some(anchor) = self.witness(lhs, evidence) {
            if lhs == rhs {
                return Ok(self.reflexive(anchor));
            }
            if self.leader(lhs, arguments) != rhs {
                return Err(fail(
                    "primitive evaluation does not preserve the requested equality",
                ));
            }
            // As in runtime container rebuilding, rewrite equality-sort leaves
            // at every occurrence, then normalize the resulting container.
            let mut proof = self.reflexive(anchor).proof;
            for argument in arguments {
                proof = self
                    .raw
                    .add_proof(RawProof::CongrAll(proof, argument.proof));
            }
            return Ok(self.add(RawProof::ContainerNormalize(proof), lhs, rhs));
        }
        let anchor = self.witness(rhs, evidence).ok_or_else(|| {
            fail(format!(
                "Could not find term {} in the e-graph",
                self.raw.term_dag.to_string(lhs)
            ))
        })?;
        let Term::App(_, selected) = self.raw.term_dag.get(lhs).clone() else {
            return Err(fail(
                "a non-container primitive result needs an existing equality",
            ));
        };
        let mut targets = selected
            .into_iter()
            .map(|term| Some((term, self.leader(term, arguments))))
            .collect::<Vec<_>>();
        let Term::App(_, actual) = self.raw.term_dag.get(anchor.rhs).clone() else {
            return Err(fail("a container witness must end at an application"));
        };
        let mut proof = self.reflexive(anchor);
        for (index, actual) in actual.into_iter().enumerate() {
            let target = targets
                .iter_mut()
                .find(|target| target.is_some_and(|(_, leader)| leader == actual))
                .ok_or_else(|| fail("container witness has incompatible elements"))?;
            let (term, leader) = target.take().unwrap();
            let projected = self.project(anchor, index);
            let mut child_evidence = vec![projected];
            child_evidence.extend_from_slice(evidence);
            let step = self.certificate(term, leader, arguments, &child_evidence)?;
            let step = self.sym(step);
            proof = self.congr(proof, index, step);
        }
        if targets.iter().any(Option::is_some) {
            return Err(fail(format!(
                "Could not find term {} in the e-graph",
                self.raw.term_dag.to_string(lhs)
            )));
        }
        let proof = self.normalize_proof(proof);
        let proof = self.sym(proof);
        if proof.lhs != lhs || proof.rhs != rhs {
            return Err(fail(format!(
                "Could not find term {} in the e-graph",
                self.raw.term_dag.to_string(lhs)
            )));
        }
        Ok(proof)
    }

    /// Lift completed roots with the ordinary lifter, preserving their order.
    pub(super) fn lift(
        self,
        program: &Vec<ResolvedNCommand>,
        roots: &[RawProofId],
    ) -> (ProofStore, Vec<ProofId>) {
        self.raw
            .lift(program, roots, self.normalizers, self.value_heads)
    }
}

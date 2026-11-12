//! Import existing evidence and compose ordinary raw proofs for ground terms.

use super::ground::{Node, Row, fail};
use super::proof_extractor::RootExtractor;
use super::proof_format::{
    ProofId, ProofStore, RawProof, RawProofId, RawProofStore, RecordedProofs,
};
use super::proof_lifting::{ProofBuilder, ProofLifter, ProofVisitor, Synthesis, global_bindings};
use crate::*;
use egglog_numeric_id::DenseIdMap;
use std::iter::once;

/// A raw proof together with the endpoints needed to compose it.
/// All IDs belong to the enclosing [`Proofs`] store and its term DAG.
#[derive(Clone, Copy)]
pub(super) struct RawEquality {
    pub(super) proof: RawProofId,
    pub(super) lhs: TermId,
    pub(super) rhs: TermId,
}

/// One ground request's raw namespace and decoded proof arena.
///
/// Raw nodes and term IDs are append-only during composition. The term DAG is
/// moved into `decoded` only while lifting; otherwise `term_dag` owns it. The
/// private memos never escape with a recorded capture or a returned proof store.
pub(super) struct Proofs<'program> {
    raw: RawProofStore,
    pub(super) term_dag: TermDag,
    pub(super) globals: HashMap<String, TermId>,
    program: &'program [ResolvedNCommand],
    decoded: ProofStore,
    synthesis: Synthesis,
    lifted: DenseIdMap<RawProofId, ProofId>,
    conclusions: HashMap<RawProofId, RawEquality>,
}

impl<'program> Proofs<'program> {
    /// Import the looked-up rows and decode their dependencies once. Returned
    /// nodes retain their input order and carry proofs with known endpoints.
    pub(super) fn import(
        egraph: &'program EGraph,
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
        let (mut proofs, ids) = Self::from_raw(
            raw,
            &egraph.proof_check_program,
            normalizers,
            value_heads,
            &roots,
        );
        let conclusions: HashMap<_, _> = roots
            .into_iter()
            .zip(ids)
            .map(|(proof, id)| {
                let equality = proofs.decoded.get(id);
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
        proofs.conclusions = conclusions;
        Ok((proofs, nodes))
    }

    /// Start the only memo that may refer to this owned raw namespace.
    fn from_raw(
        mut raw: RawProofStore,
        program: &'program [ResolvedNCommand],
        normalizers: HashMap<String, PrimitiveValidator>,
        value_heads: HashSet<String>,
        roots: &[RawProofId],
    ) -> (Self, Vec<ProofId>) {
        let mut term_dag = std::mem::take(&mut raw.term_dag);
        let globals = global_bindings(program, &mut term_dag)
            .unwrap_or_else(|_| panic!("failed to gather globals from program"));
        let mut proofs = Self {
            raw,
            term_dag,
            globals,
            program,
            decoded: ProofStore::new(TermDag::default(), normalizers, value_heads),
            synthesis: Synthesis::default(),
            lifted: DenseIdMap::new(),
            conclusions: HashMap::default(),
        };
        let roots = proofs.decode_roots(roots);
        (proofs, roots)
    }

    /// Resume only this owner's memo; new borrowed plans never outlive the call.
    fn decode_roots(&mut self, roots: &[RawProofId]) -> Vec<ProofId> {
        self.decoded.term_dag = std::mem::take(&mut self.term_dag);
        let roots = {
            let mut lifting =
                ProofLifter::new(self.program, &self.globals, &self.raw, &mut self.lifted);
            let mut builder = ProofBuilder {
                store: &mut self.decoded,
                synthesis: &mut self.synthesis,
            };
            roots
                .iter()
                .map(|&root| lifting.proof(&mut builder, root))
                .collect()
        };
        self.term_dag = std::mem::take(&mut self.decoded.term_dag);
        roots
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
        let Term::App(_, children) = self.term_dag.get(proof.rhs) else {
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
        let Term::App(head, children) = self.term_dag.get(proof.rhs).clone() else {
            unreachable!("congruence requires an application")
        };
        let mut children = children;
        children[child] = step.rhs;
        let rhs = self.term_dag.app(head, children);
        self.add(
            RawProof::Congr(proof.proof, child, step.proof),
            proof.lhs,
            rhs,
        )
    }

    /// Normalize a container term, or retain a non-container term.
    fn normalize(&mut self, term: TermId) -> TermId {
        let Term::App(head, children) = self.term_dag.get(term).clone() else {
            return term;
        };
        match self.decoded.container_normalizers.get(&head) {
            Some(validate) => {
                validate(&mut self.term_dag, &children).expect("valid container term")
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
            if let Term::App(_, children) = self.term_dag.get(term) {
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
        match self.term_dag.get(term) {
            Term::Lit(_) => true,
            Term::App(head, children) => {
                self.decoded.prim_value_constructors.contains(head)
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
        if let Term::App(head, children) = self.term_dag.get(term).clone()
            && self.decoded.container_normalizers.contains_key(&head)
        {
            let children = children
                .into_iter()
                .map(|child| self.leader(child, arguments))
                .collect();
            let term = self.term_dag.app(head, children);
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
                self.term_dag.to_string(lhs)
            ))
        })?;
        let Term::App(_, selected) = self.term_dag.get(lhs).clone() else {
            return Err(fail(
                "a non-container primitive result needs an existing equality",
            ));
        };
        let mut targets = selected
            .into_iter()
            .map(|term| Some((term, self.leader(term, arguments))))
            .collect::<Vec<_>>();
        let Term::App(_, actual) = self.term_dag.get(anchor.rhs).clone() else {
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
                self.term_dag.to_string(lhs)
            )));
        }
        let proof = self.normalize_proof(proof);
        let proof = self.sym(proof);
        if proof.lhs != lhs || proof.rhs != rhs {
            return Err(fail(format!(
                "Could not find term {} in the e-graph",
                self.term_dag.to_string(lhs)
            )));
        }
        Ok(proof)
    }

    /// Return completed roots in order, retaining the import arena and its memo.
    pub(super) fn lift(
        mut self,
        roots: &[RawProofId],
        visit: Option<&mut ProofVisitor<'_>>,
    ) -> (ProofStore, Vec<ProofId>) {
        if visit.is_some() {
            // Import decodes a superset of the requested roots. Fresh lifting
            // preserves exactly which origins are visited and in which order.
            self.raw.term_dag = self.term_dag;
            let normalizers = std::mem::take(&mut self.decoded.container_normalizers);
            let value_heads = std::mem::take(&mut self.decoded.prim_value_constructors);
            // Do not retain the import arena alongside the visitor's fresh lift.
            drop(self.decoded);
            drop(self.lifted);
            drop(self.synthesis);
            drop(self.globals);
            drop(self.conclusions);
            return self
                .raw
                .lift_with(self.program, roots, normalizers, value_heads, visit);
        }
        let roots = self.decode_roots(roots);
        self.decoded.term_dag = self.term_dag;
        (self.decoded, roots)
    }

    /// A delayed capture keeps no decoded IDs, plans, or request-local globals.
    pub(super) fn record(mut self, roots: Vec<RawProofId>) -> RecordedProofs {
        self.raw.term_dag = self.term_dag;
        RecordedProofs {
            program_len: self.program.len(),
            raw: self.raw,
            roots,
            normalizers: self.decoded.container_normalizers,
            value_heads: self.decoded.prim_value_constructors,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::proofs::{proof_format::Justification, proof_lifting::ProofOrigin};

    fn graph() -> EGraph {
        let mut graph = EGraph::new_with_proofs();
        graph
            .parse_and_run_program(
                None,
                r#"
            (datatype E (A) (B) (F E) (G E))
            (let input (A))
            (let spare (B))
            (rule ((= x (A))) ((F x)) :name "make-f")
            (rule ((= x (F (A)))) ((G x)) :name "make-g")
            (run 2)
        "#,
            )
            .unwrap();
        graph
    }

    fn capture(graph: &EGraph) -> (RecordedProofs, RawProofId) {
        let mut terms = TermDag::default();
        let a = terms.app("A".into(), vec![]);
        let f = terms.app("F".into(), vec![a]);
        let g = terms.app("G".into(), vec![f]);
        let spare = terms.app("spare".into(), vec![]);
        let sort = graph.get_sort_by_name("E").unwrap().clone();
        let recorded = graph
            .record_existing_terms(
                &terms,
                &[(g, sort.clone()), (f, sort.clone()), (spare, sort)],
            )
            .unwrap();
        let first = recorded
            .raw
            .proofs()
            .find_map(|(id, proof)| {
                matches!(proof, RawProof::Rule(name, ..) if name == "make-f").then_some(id)
            })
            .expect("the imported F proof records its rule");
        (recorded, first)
    }

    /// Copy raw content with the same dense IDs, but no decoded memo or arena.
    fn fresh_raw(proofs: &Proofs<'_>, graph: &EGraph) -> RawProofStore {
        let mut raw = RawProofStore::new(&graph.proof_state.proof_names);
        raw.term_dag = proofs.term_dag.clone();
        for (expected, proof) in proofs.raw.proofs() {
            assert_eq!(raw.add_proof(proof.clone()), expected);
        }
        raw
    }

    fn endpoints(store: &ProofStore, roots: &[ProofId]) -> Vec<(String, String)> {
        roots
            .iter()
            .map(|&root| {
                let proof = store.get(root);
                (
                    store.term_dag().to_string(proof.lhs()),
                    store.term_dag().to_string(proof.rhs()),
                )
            })
            .collect()
    }

    #[test]
    fn resumed_lifting_matches_fresh_with_appended_nodes_and_mixed_roots() {
        let graph = graph();
        let (recorded, first) = capture(&graph);
        let wanted = recorded.roots[0];
        let program = &graph.proof_check_program[..recorded.program_len];
        let (mut proofs, first_ids) = Proofs::from_raw(
            recorded.raw,
            program,
            recorded.normalizers,
            recorded.value_heads,
            &[first],
        );
        let cached = first_ids[0];
        let before = proofs.decoded.proofs().count();
        assert_eq!(proofs.decode_roots(&[first, first]), vec![cached, cached]);
        assert_eq!(proofs.decoded.proofs().count(), before);

        let prefix = (0..proofs.term_dag.size())
            .map(|id| proofs.term_dag.get(id).clone())
            .collect::<Vec<_>>();
        let equality = proofs.decoded.get(cached);
        let old = RawEquality {
            proof: first,
            lhs: equality.lhs(),
            rhs: equality.rhs(),
        };
        let back = proofs.sym(old);
        let composed = proofs.trans(old, back);
        let literal = proofs.term_dag.lit(Literal::Int(1001));
        let appended = proofs.add(RawProof::Fiat(literal, literal), literal, literal);
        let roots = [wanted, composed.proof, first, appended.proof, wanted];
        for (id, term) in prefix.iter().enumerate() {
            assert_eq!(proofs.term_dag.get(id), term);
        }
        // wanted needs another rule's fresh plan; first must stay a memo hit.
        assert!(proofs.lifted.get(wanted).is_none());
        let raw = fresh_raw(&proofs, &graph);
        let (mut fresh, fresh_ids) = raw.lift_with(
            program,
            &roots,
            proofs.decoded.container_normalizers.clone(),
            proofs.decoded.prim_value_constructors.clone(),
            None,
        );
        let (mut resumed, resumed_ids) = proofs.lift(&roots, None);
        assert_eq!(
            endpoints(&fresh, &fresh_ids),
            endpoints(&resumed, &resumed_ids)
        );
        assert_eq!(resumed_ids[2], cached);
        assert_eq!(resumed_ids[0], resumed_ids[4]);
        for (id, term) in prefix.iter().enumerate() {
            assert_eq!(resumed.term_dag().get(id), term);
        }
        // Printing follows every reachable premise and preserves justification,
        // substitution and child order without exposing arena-local IDs.
        for (&fresh_id, &resumed_id) in fresh_ids.iter().zip(&resumed_ids) {
            assert_eq!(
                fresh.proof_to_string(fresh_id),
                resumed.proof_to_string(resumed_id)
            );
        }
        fresh.check_proofs(&fresh_ids, program).unwrap();
        resumed.check_proofs(&resumed_ids, program).unwrap();
    }

    #[test]
    fn resumed_lifting_keeps_interned_firings_across_fresh_head_plans() {
        let mut graph = EGraph::new_with_proofs();
        graph
            .parse_and_run_program(
                None,
                "(datatype E (Num i64) (F E) (G E))
                 (Num 1) (Num 2)
                 (rule ((= x (Num n))) ((let child (F x)) (G child)) :name \"build\")
                 (run 1)",
            )
            .unwrap();
        let mut terms = TermDag::default();
        let inputs = [1, 2].map(|n| {
            let n = terms.lit(Literal::Int(n));
            let num = terms.app("Num".into(), vec![n]);
            let f = terms.app("F".into(), vec![num]);
            let g = terms.app("G".into(), vec![f]);
            (f, g)
        });
        let sort = graph.get_sort_by_name("E").unwrap().clone();
        let requested =
            [inputs[0].1, inputs[0].0, inputs[1].1, inputs[1].0].map(|root| (root, sort.clone()));
        let recorded = graph.record_existing_terms(&terms, &requested).unwrap();
        let first = recorded.roots[1];
        let roots = [
            recorded.roots[2],
            recorded.roots[0],
            first,
            recorded.roots[2],
        ];
        let program = &graph.proof_check_program[..recorded.program_len];
        let (mut proofs, initial_ids) = Proofs::from_raw(
            recorded.raw,
            program,
            recorded.normalizers,
            recorded.value_heads,
            &[first],
        );
        let cached = initial_ids[0];
        let (name, premises) = proofs
            .decoded
            .proofs()
            .find_map(|(_, proof)| match proof.justification() {
                Justification::Rule {
                    name,
                    premise_proofs,
                    ..
                } if name == "build" => Some((name.clone(), premise_proofs.clone())),
                _ => None,
            })
            .expect("the first column decoded its rule firing");
        let firing = ProofBuilder {
            store: &mut proofs.decoded,
            synthesis: &mut proofs.synthesis,
        }
        .rule_firing(&name, &premises);
        assert!(proofs.lifted.get(roots[0]).is_none());
        assert!(proofs.lifted.get(roots[1]).is_none());
        let raw = fresh_raw(&proofs, &graph);
        let (mut fresh, fresh_ids) = raw.lift_with(
            program,
            &roots,
            proofs.decoded.container_normalizers.clone(),
            proofs.decoded.prim_value_constructors.clone(),
            None,
        );
        // Resume the unseen firing first: losing the old namespace would reuse
        // its compact firing ID for a different premise vector. Both fresh walks
        // must retain the request's keys while decoding uncached raw columns.
        proofs.decode_roots(&roots);
        assert!(
            ProofBuilder {
                store: &mut proofs.decoded,
                synthesis: &mut proofs.synthesis,
            }
            .rule_firing(&name, &premises)
                == firing
        );
        let (mut resumed, resumed_ids) = proofs.lift(&roots, None);
        assert_eq!(resumed_ids[2], cached);
        assert_eq!(resumed_ids[0], resumed_ids[3]);
        for (&fresh_id, &resumed_id) in fresh_ids.iter().zip(&resumed_ids) {
            assert_eq!(
                fresh.proof_to_string(fresh_id),
                resumed.proof_to_string(resumed_id)
            );
        }
        fresh.check_proofs(&fresh_ids, program).unwrap();
        resumed.check_proofs(&resumed_ids, program).unwrap();
    }

    type OriginEvent = (String, usize, Vec<usize>, String, String, usize);

    fn origin_event(store: &ProofStore, id: ProofId, origin: ProofOrigin<'_>) -> OriginEvent {
        let (kind, action, path, program_len) = match origin {
            ProofOrigin::GlobalTerm {
                action,
                path,
                program,
            } => ("global-term".into(), action, path.to_vec(), program.len()),
            ProofOrigin::GlobalUnion {
                action,
                swapped,
                program,
            } => (
                format!("global-union-{swapped}"),
                action,
                vec![],
                program.len(),
            ),
            ProofOrigin::Rule {
                rule,
                action,
                path,
                program,
            } => (
                format!("rule:{}", rule.name),
                action,
                path.to_vec(),
                program.len(),
            ),
        };
        let proof = store.get(id);
        (
            kind,
            action,
            path,
            store.term_dag().to_string(proof.lhs()),
            store.term_dag().to_string(proof.rhs()),
            program_len,
        )
    }

    #[test]
    fn visitor_lifting_matches_fresh_and_omits_unused_import_origins() {
        let graph = graph();
        let (recorded, first) = capture(&graph);
        let wanted = recorded.roots[0];
        let spare = recorded.roots[2];
        let program = &graph.proof_check_program[..recorded.program_len];
        let (proofs, _) = Proofs::from_raw(
            recorded.raw,
            program,
            recorded.normalizers,
            recorded.value_heads,
            &[first, spare],
        );
        let raw = fresh_raw(&proofs, &graph);
        let mut fresh_events = Vec::new();
        let (mut fresh, fresh_roots) = raw.lift_with(
            program,
            &[wanted],
            proofs.decoded.container_normalizers.clone(),
            proofs.decoded.prim_value_constructors.clone(),
            Some(&mut |store, id, origin| fresh_events.push(origin_event(store, id, origin))),
        );
        let mut resumed_events = Vec::new();
        let (mut resumed, resumed_roots) = proofs.lift(
            &[wanted],
            Some(&mut |store, id, origin| {
                resumed_events.push(origin_event(store, id, origin));
            }),
        );
        assert!(!fresh_events.is_empty());
        assert_eq!(fresh_events, resumed_events);
        assert!(resumed_events.iter().all(|event| event.3 != "(B)"));
        assert_eq!(
            endpoints(&fresh, &fresh_roots),
            endpoints(&resumed, &resumed_roots)
        );
        for (&fresh_id, &resumed_id) in fresh_roots.iter().zip(&resumed_roots) {
            assert_eq!(
                fresh.proof_to_string(fresh_id),
                resumed.proof_to_string(resumed_id)
            );
        }
        fresh.check_proofs(&fresh_roots, program).unwrap();
        resumed.check_proofs(&resumed_roots, program).unwrap();
    }
}

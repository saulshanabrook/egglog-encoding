//! Lift proofs of flattened rewrites back to the original source rules.
use super::coordinates::Coordinates;
use super::format::{ProofId, RulePremise, SlottedConclusion, SlottedProof, SlottedProofStore};
use super::guards::proof_body;
use super::source::{SlottedProgram, pattern_term};
use super::terms::{Renaming, term_renaming};
use super::{HashMap, HashSet};
use egglog::ast::{Literal, ResolvedExpr, ResolvedFact};
use egglog::proof::{Justification as Step, Proposition};
use egglog::{Term, TermId};
use std::collections::VecDeque;

type Result<T> = std::result::Result<T, String>;

pub(super) fn lift(
    old: SlottedProofStore,
    program: &SlottedProgram,
    conclusion: SlottedConclusion,
) -> Result<(SlottedProofStore, SlottedConclusion)> {
    let steps: Vec<_> = old
        .dependencies(conclusion.proof)
        .into_iter()
        .map(|id| (id, old.get(id).clone()))
        .collect();
    let mut out = Coordinates::new(old);
    let mut lifted = HashMap::default();
    for (id, proof) in steps {
        let proposition = proof.proposition().clone();
        let result = match &proof {
            SlottedProof::Alpha { proof, .. } => {
                let premise = out.proof(lifted[proof]);
                let proof = out.alpha(premise, proposition.rhs);
                out.plain(proof)
            }
            SlottedProof::Equivariance {
                proof, renaming, ..
            } => {
                let p = out.equivariance(lifted[proof], renaming);
                out.reframe(p, renaming.clone())
            }
            SlottedProof::Rule(proof) => {
                let premises = proof
                    .premises
                    .iter()
                    .map(|p| match p {
                        RulePremise::Equality(p) => Ok(out.proof(lifted[p])),
                        RulePremise::RenamingEq { .. } => {
                            Err("renaming equality occurs before source rule reconstruction".into())
                        }
                    })
                    .collect::<Result<Vec<_>>>()?;
                let result = lift_rule(
                    &mut out,
                    program,
                    &proof.name,
                    proof
                        .substitution
                        .iter()
                        .map(|(v, t)| (v.clone(), *t))
                        .collect(),
                    premises,
                    proposition.clone(),
                )
                .map_err(|e| format!("lifting source rule {}: {e}", proof.name))?;
                let rhs = out.proposition(result).rhs;
                let refreshed = program.refresh_binders(&mut out.term_dag, rhs);
                let result = if refreshed == rhs {
                    result
                } else {
                    out.alpha(result, refreshed)
                };
                let actual = out.proposition(result).clone();
                let renaming = term_renaming(&out.term_dag, &[(proposition.rhs, actual.rhs)])
                    .ok_or("lifted rule changes the right-hand term's shape")?;
                out.view(result, proposition.rhs, renaming)
            }
            SlottedProof::Ordinary(proof) => match proof.justification() {
                Step::Fiat => {
                    let proof = source_fiat(&mut out, program, proposition.clone())?;
                    out.plain(proof)
                }
                Step::Sym(p) => out.sym(lifted[p]),
                Step::Trans(a, b) => out.trans(lifted[a], lifted[b]).map_err(|e| e.to_string())?,
                Step::Congr {
                    proof: parent,
                    child_index,
                    child_proof,
                } => {
                    // Restore RHS names without changing the child matched by the parent.
                    let mut child = lifted[child_proof];
                    let actual = out.proposition(out.proof(child));
                    let wanted = out.edge(child);
                    if let Some(renaming) = term_renaming(
                        &out.term_dag,
                        &[(actual.lhs, wanted.lhs), (actual.rhs, wanted.rhs)],
                    ) {
                        child = out.equivariance(child, &renaming);
                    }
                    let p = out
                        .congr(lifted[parent], *child_index, child)
                        .map_err(|e| e.to_string())?;
                    let rhs = out.edge(p).rhs;
                    let renaming = term_renaming(&out.term_dag, &[(rhs, proposition.rhs)])
                        .ok_or("lifting congruence changes the right-hand term's shape")?;
                    out.reframe(p, renaming)
                }
                Step::Proj {
                    proof: parent,
                    child_index,
                } => out
                    .project(lifted[parent], *child_index)
                    .map_err(|e| e.to_string())?,
                _ => {
                    return Err(
                        "unsupported ordinary step while unflattening a slotted proof".into(),
                    );
                }
            },
        };
        lifted.insert(id, result);
    }
    let (store, mut result) = out.finish(lifted[&conclusion.proof]);
    result.renaming = result.renaming.compose(&conclusion.renaming);
    Ok((store, result))
}

fn source_fiat(
    store: &mut SlottedProofStore,
    program: &SlottedProgram,
    claimed: Proposition,
) -> Result<ProofId> {
    if claimed.lhs == claimed.rhs && program.is_built(&store.term_dag, claimed.lhs)
        || program.is_union(claimed.lhs, claimed.rhs)
    {
        return Ok(store.fiat(claimed.lhs, claimed.rhs));
    }
    for union in &program.unions {
        for (lhs, rhs) in [(union.lhs, union.rhs), (union.rhs, union.lhs)] {
            if program.alpha_eq(&mut store.term_dag, lhs, claimed.lhs)
                && program.alpha_eq(&mut store.term_dag, rhs, claimed.rhs)
            {
                let proof = store.fiat(lhs, rhs);
                return Ok(Witnesses::new(store, program, vec![]).alpha_endpoints(
                    proof,
                    claimed.lhs,
                    claimed.rhs,
                ));
            }
        }
    }
    let mut known = vec![];
    for root in program
        .lets
        .values()
        .copied()
        .chain(program.unions.iter().flat_map(|u| [u.lhs, u.rhs]))
    {
        let refreshed = program.refresh_binders(&mut store.term_dag, root);
        let proof = store.fiat(root, root);
        known.push(if refreshed == root {
            proof
        } else {
            store.alpha(proof, refreshed)
        });
    }
    let mut witnesses = Witnesses::new(store, program, known);
    if claimed.lhs == claimed.rhs {
        witnesses.reflexive(claimed.lhs)
    } else {
        Err("fiat is not an original source union".into())
    }
}

fn lift_rule(
    store: &mut SlottedProofStore,
    program: &SlottedProgram,
    name: &str,
    substitution: Vec<(String, TermId)>,
    premises: Vec<ProofId>,
    claimed: Proposition,
) -> Result<ProofId> {
    let rule = program
        .rewrites
        .get(name)
        .ok_or_else(|| format!("missing original rewrite {name}"))?;
    let mut sigma: HashMap<_, _> = substitution
        .iter()
        .cloned()
        .chain(rule.globals.iter().map(|(v, &t)| (v.clone(), t)))
        .collect();
    let (body, auxiliary) = proof_body(rule, &mut store.term_dag, &sigma)?;
    sigma.extend(auxiliary);
    let instance = |store: &mut SlottedProofStore, expr| -> Result<TermId> {
        let term = pattern_term(&mut store.term_dag, expr);
        rule.instantiate(&mut store.term_dag, term, &sigma)
    };
    let (lhs, rhs) = rule.endpoints();
    let lhs = instance(store, lhs)?;
    let rhs = instance(store, rhs)?;
    let variables: HashSet<_> = rule
        .patterns()
        .flat_map(|expr| expr.vars())
        .map(|var| var.name)
        .filter(|name| !rule.globals.contains_key(name))
        .collect();
    let substitution = substitution
        .into_iter()
        .filter(|(var, _)| variables.contains(var))
        .collect();
    let mut witnesses = Witnesses::new(store, program, premises);
    let root = witnesses.exists(lhs)?;
    let mut source_premises = vec![RulePremise::Equality(root)];
    for fact in &body[1..] {
        let proof = match fact {
            ResolvedFact::Eq(_, a, b) => {
                let a = instance(witnesses.store, a)?;
                let b = instance(witnesses.store, b)?;
                RulePremise::Equality(witnesses.condition_equality(program, a, b)?)
            }
            ResolvedFact::Fact(ResolvedExpr::Call(
                _,
                egglog::ResolvedCall::Primitive(head),
                args,
            )) => {
                if head.name() == "renaming-=" {
                    let a = instance(witnesses.store, &args[0])?;
                    let b = instance(witnesses.store, &args[1])?;
                    let left = witnesses.renaming_equality(a, b)?;
                    let right = witnesses.reflexive(b)?;
                    RulePremise::RenamingEq { left, right }
                } else {
                    let unit = witnesses.store.term_dag.lit(Literal::Unit);
                    RulePremise::Equality(witnesses.store.fiat(unit, unit))
                }
            }
            ResolvedFact::Fact(expr) => {
                let term = instance(witnesses.store, expr)?;
                RulePremise::Equality(witnesses.exists(term)?)
            }
        };
        source_premises.push(proof);
    }
    let source = witnesses.store.rule(
        Proposition::new(lhs, rhs),
        name.into(),
        substitution,
        source_premises,
    );
    witnesses.add(source);
    if claimed.lhs != claimed.rhs
        && let Some(renaming) = witnesses.renaming(&[(lhs, claimed.lhs)])
    {
        return Ok(witnesses.store.equivariance(source, renaming));
    }
    if claimed.lhs == claimed.rhs {
        return witnesses.reflexive(claimed.lhs);
    }
    witnesses.exists(claimed.lhs)?;
    let before = witnesses.reconstruct(claimed.lhs, lhs, true)?;
    let start = witnesses.store.proposition(before).lhs;
    let renaming = witnesses
        .renaming(&[(start, claimed.lhs)])
        .ok_or("reconstruction changes the left-hand term's shape")?;
    let middle = witnesses
        .store
        .trans(before, source)
        .map_err(|e| e.to_string())?;
    let result = if witnesses.renaming(&[(rhs, claimed.rhs)]).is_some() {
        middle
    } else {
        let after = witnesses.equality(rhs, claimed.rhs)?;
        witnesses
            .store
            .trans(middle, after)
            .map_err(|e| e.to_string())?
    };
    Ok(witnesses.store.equivariance(result, renaming))
}

/// Ordinary equalities for the atoms of one match. Reconstruction depends only
/// on these proofs, not on encoded classes, frames, or compiler variable names.
struct Witnesses<'a> {
    store: &'a mut SlottedProofStore,
    program: &'a SlottedProgram,
    edges: Vec<ProofId>,
    known: HashMap<TermId, ProofId>,
    memo: HashMap<(TermId, TermId, bool), ProofId>,
    active: HashSet<(TermId, TermId, bool)>,
}

impl<'a> Witnesses<'a> {
    fn new(
        store: &'a mut SlottedProofStore,
        program: &'a SlottedProgram,
        proofs: Vec<ProofId>,
    ) -> Self {
        let mut out = Self {
            store,
            program,
            edges: vec![],
            known: HashMap::default(),
            memo: HashMap::default(),
            active: HashSet::default(),
        };
        for proof in proofs {
            out.add(proof);
        }
        out
    }

    fn add(&mut self, proof: ProofId) {
        self.edges.push(proof);
        let inverse = self.store.sym(proof);
        let mut work = vec![inverse, proof];
        while let Some(p) = work.pop() {
            let term = self.store.proposition(p).rhs;
            if self.known.contains_key(&term) {
                continue;
            }
            self.known.insert(term, p);
            if let Term::App(_, children) = self.store.term_dag.get(term) {
                let count = children.len();
                for i in (0..count).rev() {
                    work.push(self.store.project(p, i).expect("valid child index"));
                }
            }
        }
    }

    fn reflexive(&mut self, term: TermId) -> Result<ProofId> {
        if self.program.is_built(&self.store.term_dag, term) {
            return Ok(self.store.fiat(term, term));
        }
        let proof = self.exists(term)?;
        if self.store.proposition(proof).lhs == term {
            return Ok(proof);
        }
        let inverse = self.store.sym(proof);
        self.store.trans(inverse, proof).map_err(|e| e.to_string())
    }

    fn exists(&mut self, term: TermId) -> Result<ProofId> {
        if let Some(&p) = self.known.get(&term) {
            return Ok(p);
        }
        let mut candidates: Vec<_> = self.known.keys().copied().collect();
        candidates.sort_unstable();
        let refreshed = self.program.refresh_binders(&mut self.store.term_dag, term);
        for target in [term, refreshed] {
            for &candidate in &candidates {
                if let Ok(proof) = self.reconstruct(candidate, target, true) {
                    let proof = if target == term {
                        proof
                    } else {
                        self.store.alpha(proof, term)
                    };
                    self.add(proof);
                    return Ok(proof);
                }
            }
        }
        Err(format!(
            "no matched evidence for {}",
            self.store.term_dag.to_string(term)
        ))
    }

    fn renaming(&self, pairs: &[(TermId, TermId)]) -> Option<Renaming> {
        term_renaming(&self.store.term_dag, pairs)
    }

    fn condition_equality(
        &mut self,
        program: &SlottedProgram,
        a: TermId,
        b: TermId,
    ) -> Result<ProofId> {
        for proof in self.edges.clone() {
            let p = self.store.proposition(proof).clone();
            if program.alpha_eq(&mut self.store.term_dag, p.lhs, a)
                && program.alpha_eq(&mut self.store.term_dag, p.rhs, b)
            {
                return Ok(self.alpha_endpoints(proof, a, b));
            }
            if program.alpha_eq(&mut self.store.term_dag, p.rhs, a)
                && program.alpha_eq(&mut self.store.term_dag, p.lhs, b)
            {
                let proof = self.store.sym(proof);
                return Ok(self.alpha_endpoints(proof, a, b));
            }
        }
        if program.alpha_eq(&mut self.store.term_dag, a, b) {
            let proof = self.reflexive(a)?;
            return Ok(self.alpha_endpoints(proof, a, b));
        }
        self.equality(a, b)
    }

    fn alpha_endpoints(&mut self, mut proof: ProofId, lhs: TermId, rhs: TermId) -> ProofId {
        if self.store.proposition(proof).rhs != rhs {
            proof = self.store.alpha(proof, rhs);
        }
        if self.store.proposition(proof).lhs != lhs {
            proof = self.store.sym(proof);
            proof = self.store.alpha(proof, lhs);
            proof = self.store.sym(proof);
        }
        proof
    }

    fn renaming_equality(&mut self, a: TermId, b: TermId) -> Result<ProofId> {
        for term in [a, b] {
            let proof = self.exists(term)?;
            self.add(proof);
        }
        if let Ok(proof) = self.equality(a, b) {
            return Ok(proof);
        }
        let initial = self.reflexive(a)?;
        let mut work = VecDeque::from([initial]);
        let mut seen = Vec::new();
        while let Some(proof) = work.pop_front() {
            let current = self.store.proposition(proof).rhs;
            if self
                .program
                .eq_modulo_renaming(&mut self.store.term_dag, current, b)
            {
                return Ok(proof);
            }
            if seen.iter().any(|&term| {
                self.program
                    .eq_modulo_renaming(&mut self.store.term_dag, current, term)
            }) {
                continue;
            }
            seen.push(current);
            for edge in self.edges.clone() {
                let p = self.store.proposition(edge).clone();
                for (left, reversed) in [(p.lhs, false), (p.rhs, true)] {
                    if let Some(renaming) = self.renaming(&[(left, current)]) {
                        let edge = if reversed { self.store.sym(edge) } else { edge };
                        let edge = self.store.equivariance(edge, renaming);
                        work.push_back(self.store.trans(proof, edge).map_err(|e| e.to_string())?);
                    }
                }
            }
        }
        Err("no equality up to renaming between the guard's terms".into())
    }

    fn equality(&mut self, from: TermId, to: TermId) -> Result<ProofId> {
        self.reconstruct(from, to, false)
    }

    // Existence allows a permutation of the whole derivation. An equality must
    // preserve its starting term as well as end at the requested target.
    fn reconstruct(&mut self, from: TermId, to: TermId, rename_source: bool) -> Result<ProofId> {
        let key = (from, to, rename_source);
        if let Some(&p) = self.memo.get(&key) {
            return Ok(p);
        }
        if !self.active.insert(key) {
            return Err("cyclic atom expansion".into());
        }
        let result = self.search(from, to, rename_source);
        self.active.remove(&key);
        if let Ok(p) = result {
            self.memo.insert(key, p);
        }
        result
    }

    fn search(&mut self, from: TermId, to: TermId, rename_source: bool) -> Result<ProofId> {
        for edge in self.edges.clone() {
            let p = self.store.proposition(edge).clone();
            if let Some(renaming) = self.renaming(&[(p.lhs, from), (p.rhs, to)]) {
                return Ok(self.store.equivariance(edge, renaming));
            }
            if let Some(renaming) = self.renaming(&[(p.rhs, from), (p.lhs, to)]) {
                let inverse = self.store.sym(edge);
                return Ok(self.store.equivariance(inverse, renaming));
            }
        }
        let initial = self
            .known
            .get(&from)
            .copied()
            .ok_or("unknown starting term")?;
        let back = self.store.sym(initial);
        let initial = self.store.trans(back, initial).map_err(|e| e.to_string())?;
        let mut work = VecDeque::from([initial]);
        let mut seen = Vec::new();
        while let Some(proof) = work.pop_front() {
            let current = self.store.proposition(proof).rhs;
            if current == to {
                return Ok(proof);
            }
            if self.program.alpha_eq(&mut self.store.term_dag, current, to) {
                return Ok(self.store.alpha(proof, to));
            }
            if rename_source && let Some(renaming) = self.renaming(&[(current, to)]) {
                return Ok(self.store.equivariance(proof, renaming));
            }
            if seen.iter().any(|&term| {
                current == term || rename_source && self.renaming(&[(current, term)]).is_some()
            }) {
                continue;
            }
            seen.push(current);
            if let (Term::App(head, children), Term::App(want, targets)) = (
                self.store.term_dag.get(current).clone(),
                self.store.term_dag.get(to).clone(),
            ) && head == want
                && children.len() == targets.len()
            {
                let mut expanded = Ok(proof);
                for (index, &target) in targets.iter().enumerate() {
                    expanded = expanded.and_then(|mut parent| {
                        let Term::App(_, children) = self
                            .store
                            .term_dag
                            .get(self.store.proposition(parent).rhs)
                            .clone()
                        else {
                            unreachable!()
                        };
                        let child = children[index];
                        if child == target {
                            return Ok(parent);
                        }
                        let projection = self
                            .store
                            .project(parent, index)
                            .map_err(|e| e.to_string())?;
                        self.known.entry(child).or_insert(projection);
                        let proof = self.equality(child, target).or_else(|error| {
                            if rename_source {
                                self.reconstruct(child, target, true)
                            } else {
                                Err(error)
                            }
                        })?;
                        if rename_source {
                            let left = self.store.proposition(proof).lhs;
                            let mut pairs = vec![(child, left)];
                            pairs.extend(targets[..index].iter().map(|&t| (t, t)));
                            let renaming =
                                self.renaming(&pairs).ok_or("inconsistent sibling names")?;
                            parent = self.store.equivariance(parent, renaming);
                        }
                        self.store
                            .congr(parent, index, proof)
                            .map_err(|e| e.to_string())
                    });
                    if expanded.is_err() {
                        break;
                    }
                }
                if let Ok(proof) = expanded {
                    return Ok(proof);
                }
            }
            for edge in self.edges.clone() {
                let p = self.store.proposition(edge).clone();
                for (left, reversed) in [(p.lhs, false), (p.rhs, true)] {
                    let renaming = if left == current {
                        Renaming::identity()
                    } else if rename_source
                        && let Some(renaming) = self.renaming(&[(left, current)])
                    {
                        renaming
                    } else {
                        continue;
                    };
                    let edge = if reversed { self.store.sym(edge) } else { edge };
                    let edge = self.store.equivariance(edge, renaming);
                    work.push_back(self.store.trans(proof, edge).map_err(|e| e.to_string())?);
                }
            }
        }
        Err(format!(
            "cannot reconstruct {} = {} from matched atoms",
            self.store.term_dag.to_string(from),
            self.store.term_dag.to_string(to)
        ))
    }
}

#[cfg(test)]
#[path = "unflatten_tests.rs"]
mod tests;

//! Undo pattern flattening by replaying the original rule's constructor traversal.
use crate::slotted::proofs::context::{ProofContext, SourceFact, SourceRule, pattern_term};
use crate::slotted::proofs::format::{ProofId, RulePremise, SlottedProof, SlottedProofStore};
use crate::slotted::proofs::terms::slot_of;
use crate::slotted::proofs::{HashMap, HashSet};
use egglog::ast::{Literal, ResolvedExpr, ResolvedExprExt, ResolvedFact};
use egglog::proof::{Justification as Step, Proposition};
use egglog::{ResolvedCall, Term, TermId};
use std::collections::VecDeque;

type Result<T> = std::result::Result<T, String>;

pub(in crate::slotted) fn lift(
    mut store: SlottedProofStore,
    program: &ProofContext,
    flattened: &ProofContext,
    root: ProofId,
) -> Result<(SlottedProofStore, ProofId)> {
    let steps = store.dependencies(root);
    let axioms = source_axioms(&mut store, program, flattened);
    let mut lifted = HashMap::default();
    for id in steps {
        let proof = store.get(id).clone();
        let claimed = proof.proposition().clone();
        let result = match proof {
            SlottedProof::Alpha { proof, .. } => alpha_rhs(&mut store, lifted[&proof], claimed.rhs),
            SlottedProof::Equivariance {
                proof, renaming, ..
            } => store.equivariance(lifted[&proof], renaming),
            SlottedProof::Rule(proof) => {
                let premises = proof
                    .premises
                    .iter()
                    .map(|p| match p {
                        RulePremise::Equality(p) => Ok(lifted[p]),
                        RulePremise::RenamingEq { .. } => {
                            Err("renaming premise before unflattening".into())
                        }
                    })
                    .collect::<Result<Vec<_>>>()?;
                replay_rule(
                    &mut store,
                    program,
                    flattened,
                    &proof.name,
                    proof.substitution.into_iter().collect(),
                    premises,
                    claimed.clone(),
                )
                .map_err(|e| format!("lifting source rule {}: {e}", proof.name))?
            }
            SlottedProof::Ordinary(proof) => match proof.justification() {
                Step::Fiat => {
                    if let Some(&p) = axioms.get(&(claimed.lhs, claimed.rhs)) {
                        p
                    } else if claimed.lhs == claimed.rhs
                        && (matches!(store.term_dag.get(claimed.lhs), Term::Lit(_))
                            || slot_of(&store.term_dag, claimed.lhs).is_some())
                    {
                        store.fiat(claimed.lhs, claimed.rhs)
                    } else {
                        return Err("fiat is not a flattened source axiom".into());
                    }
                }
                Step::Sym(p) => store.sym(lifted[p]),
                Step::Trans(a, b) => store
                    .trans(lifted[a], lifted[b])
                    .map_err(|e| e.to_string())?,
                Step::Congr {
                    proof,
                    child_index,
                    child_proof,
                } => store
                    .congr(lifted[proof], *child_index, lifted[child_proof])
                    .map_err(|e| e.to_string())?,
                Step::Proj { proof, child_index } => store
                    .project(lifted[proof], *child_index)
                    .map_err(|e| e.to_string())?,
                _ => return Err("unsupported ordinary step while unflattening".into()),
            },
        };
        debug_assert_eq!(store.proposition(result), &claimed);
        lifted.insert(id, result);
    }
    Ok((store, lifted[&root]))
}

fn alpha_rhs(store: &mut SlottedProofStore, proof: ProofId, rhs: TermId) -> ProofId {
    if store.proposition(proof).rhs == rhs {
        proof
    } else {
        store.alpha(proof, rhs)
    }
}

fn reflexive(store: &mut SlottedProofStore, proof: ProofId) -> ProofId {
    let p = store.proposition(proof);
    if p.lhs == p.rhs {
        return proof;
    }
    let back = store.sym(proof);
    store.trans(back, proof).expect("inverse endpoints agree")
}

fn alpha_endpoints(
    store: &mut SlottedProofStore,
    mut proof: ProofId,
    lhs: TermId,
    rhs: TermId,
) -> ProofId {
    if store.proposition(proof).rhs != rhs {
        proof = alpha_rhs(store, proof, rhs);
    }
    if store.proposition(proof).lhs != lhs {
        proof = store.sym(proof);
        proof = alpha_rhs(store, proof, lhs);
        proof = store.sym(proof);
    }
    proof
}

/// Source axioms in flattened coordinates. The contexts must share declaration order.
fn source_axioms(
    store: &mut SlottedProofStore,
    program: &ProofContext,
    flat: &ProofContext,
) -> HashMap<(TermId, TermId), ProofId> {
    let mut axioms = HashMap::default();
    let mut roots = Vec::new();
    for (name, &source) in &program.lets {
        let target = flat.lets[name];
        let proof = store.fiat(source, source);
        let proof = alpha_rhs(store, proof, target);
        roots.push(reflexive(store, proof));
    }
    for (source, target) in program.unions.iter().zip(&flat.unions) {
        let proof = store.fiat(source.lhs, source.rhs);
        let proof = alpha_endpoints(store, proof, target.lhs, target.rhs);
        axioms.insert((target.lhs, target.rhs), proof);
        let back = store.sym(proof);
        axioms.insert((target.rhs, target.lhs), back);
        roots.extend([proof, back]);
    }
    while let Some(proof) = roots.pop() {
        let term = store.proposition(proof).rhs;
        if axioms.contains_key(&(term, term)) {
            continue;
        }
        let proof = reflexive(store, proof);
        axioms.insert((term, term), proof);
        if let Term::App(_, children) = store.term_dag.get(term) {
            for i in (0..children.len()).rev() {
                roots.push(store.project(proof, i).expect("source child"));
            }
        }
    }
    axioms
}

/// Premises and bindings for replaying one source rule application.
struct Replay<'a> {
    store: &'a mut SlottedProofStore,
    rule: &'a SourceRule,
    flat: &'a SourceRule,
    sigma: HashMap<String, TermId>,
    atoms: VecDeque<(ResolvedExpr, ProofId)>,
    values: VecDeque<(ResolvedExpr, ProofId)>,
    comparisons: VecDeque<ProofId>,
    known: HashMap<TermId, ProofId>,
}

impl Replay<'_> {
    fn instance(&mut self, expr: &ResolvedExpr) -> Result<TermId> {
        let term = pattern_term(&mut self.store.term_dag, expr);
        self.rule
            .instantiate(&mut self.store.term_dag, term, &self.sigma)
    }

    fn flat_instance(&mut self, expr: &ResolvedExpr) -> Result<TermId> {
        let term = pattern_term(&mut self.store.term_dag, expr);
        self.flat
            .instantiate(&mut self.store.term_dag, term, &self.sigma)
    }

    fn remember(&mut self, expr: &ResolvedExpr, proof: ProofId) -> Result<()> {
        self.known.insert(self.store.proposition(proof).rhs, proof);
        // Only follow the pattern, never expand substituted terms into trees.
        if let ResolvedExpr::Call(_, ResolvedCall::Func(_), args) = expr {
            for (i, arg) in args.iter().enumerate() {
                let child = self.store.project(proof, i).map_err(|e| e.to_string())?;
                self.remember(arg, child)?;
            }
        }
        Ok(())
    }

    fn exists(&mut self, term: TermId) -> Result<ProofId> {
        if let Some(&p) = self.known.get(&term) {
            return Ok(reflexive(self.store, p));
        }
        if matches!(self.store.term_dag.get(term), Term::Lit(_))
            || slot_of(&self.store.term_dag, term).is_some()
        {
            return Ok(self.store.fiat(term, term));
        }
        Err(format!(
            "no occurrence for {} in the matched patterns",
            self.store.term_dag.to_string(term)
        ))
    }

    fn is_local(&self, expr: &ResolvedExpr) -> bool {
        matches!(expr, ResolvedExpr::Var(_, var) if !self.rule.globals.contains_key(&var.name))
    }

    fn is_global_proxy(&self, source: &ResolvedExpr, flat: &ResolvedExpr) -> bool {
        matches!(source, ResolvedExpr::Var(_,v) if self.rule.globals.contains_key(&v.name))
            && matches!(flat, ResolvedExpr::Var(_,v) if !self.flat.globals.contains_key(&v.name))
    }

    /// A matched root is either a source variable, a constructor atom, or a
    /// captured global. Their premise order was fixed by the forward traversal.
    fn pattern(&mut self, expr: &ResolvedExpr) -> Result<ProofId> {
        if self.is_local(expr) {
            let term = self.instance(expr)?;
            return self.exists(term);
        }
        let (flat, proof) = if matches!(expr, ResolvedExpr::Call(..)) {
            self.atoms.pop_front().ok_or("missing constructor atom")?
        } else {
            self.values.pop_front().ok_or("missing global binding")?
        };
        self.expand(expr, &flat, proof)
    }

    /// Expand a constructor's flattened children in the same preorder used by
    /// `flatten`. Restoring the flat atom's bound names first keeps its child
    /// occurrences in the substitution's coordinates.
    fn expand(
        &mut self,
        source: &ResolvedExpr,
        flat: &ResolvedExpr,
        mut proof: ProofId,
    ) -> Result<ProofId> {
        let target = self.flat_instance(flat)?;
        proof = alpha_rhs(self.store, proof, target);
        if let (ResolvedExpr::Call(_, _, args), ResolvedExpr::Call(_, _, flat_args)) =
            (source, flat)
        {
            for (i, (arg, flat_arg)) in args.iter().zip(flat_args).enumerate() {
                let child = if matches!(arg, ResolvedExpr::Call(..))
                    && matches!(flat_arg, ResolvedExpr::Var(..))
                    || self.is_global_proxy(arg, flat_arg)
                {
                    Some(self.pattern(arg)?)
                } else if matches!(arg, ResolvedExpr::Call(..)) {
                    let child = self.store.project(proof, i).map_err(|e| e.to_string())?;
                    Some(self.expand(arg, flat_arg, child)?)
                } else {
                    None
                };
                if let Some(child) = child {
                    proof = self
                        .store
                        .congr(proof, i, child)
                        .map_err(|e| e.to_string())?;
                }
            }
        }
        let target = self.instance(source)?;
        proof = alpha_rhs(self.store, proof, target);
        self.remember(source, proof)?;
        Ok(proof)
    }

    fn equality(&mut self, a: &ResolvedExpr, b: &ResolvedExpr) -> Result<ProofId> {
        if self.is_local(a) && !self.is_local(b) {
            return self.pattern(b);
        }
        if self.is_local(b) && !self.is_local(a) {
            let p = self.pattern(a)?;
            return Ok(self.store.sym(p));
        }
        let a = self.pattern(a)?;
        let b = self.pattern(b)?;
        let comparison = self
            .comparisons
            .pop_front()
            .ok_or("missing equality comparison")?;
        let back = self.store.sym(a);
        let proof = self
            .store
            .trans(back, comparison)
            .map_err(|e| e.to_string())?;
        self.store.trans(proof, b).map_err(|e| e.to_string())
    }

    /// Right-hand constructors were not flattened. Only captured global proxies
    /// need their matching equalities, in reverse, at the original occurrences.
    fn rhs(
        &mut self,
        source: &ResolvedExpr,
        flat: &ResolvedExpr,
        mut proof: ProofId,
    ) -> Result<ProofId> {
        if self.is_global_proxy(source, flat) {
            let global = self.pattern(source)?;
            let back = self.store.sym(global);
            proof = self.store.trans(proof, back).map_err(|e| e.to_string())?;
        } else if let (
            ResolvedExpr::Call(_, ResolvedCall::Func(_), args),
            ResolvedExpr::Call(_, _, flat_args),
        ) = (source, flat)
        {
            for (i, (arg, flat_arg)) in args.iter().zip(flat_args).enumerate() {
                let child = self.store.project(proof, i).map_err(|e| e.to_string())?;
                let child = self.rhs(arg, flat_arg, child)?;
                proof = self
                    .store
                    .congr(proof, i, child)
                    .map_err(|e| e.to_string())?;
            }
        }
        Ok(proof)
    }
}

fn replay_rule(
    store: &mut SlottedProofStore,
    program: &ProofContext,
    flattened: &ProofContext,
    name: &str,
    substitution: Vec<(String, TermId)>,
    premises: Vec<ProofId>,
    claimed: Proposition,
) -> Result<ProofId> {
    let rule = program
        .rewrites
        .get(name)
        .ok_or("missing original rewrite")?;
    let flat = flattened
        .rewrites
        .get(name)
        .ok_or("missing flattened rewrite")?;
    let mut replay = Replay {
        store,
        rule,
        flat,
        sigma: substitution.iter().cloned().collect(),
        atoms: VecDeque::new(),
        values: VecDeque::new(),
        comparisons: VecDeque::new(),
        known: HashMap::default(),
    };
    let (flat_lhs, flat_rhs) = flat.endpoints();
    let root_target = replay.flat_instance(flat_lhs)?;
    let root = alpha_rhs(replay.store, premises[0], root_target);
    let root = reflexive(replay.store, root);
    replay.remember(flat_lhs, root)?;
    let bindings: Vec<_> = flat
        .conditions()
        .iter()
        .filter_map(SourceFact::binding)
        .collect();
    if bindings.len() + 1 != premises.len() {
        return Err("flattened premise count differs from its bindings".into());
    }
    for ((var, expr), proof) in bindings.into_iter().zip(premises[1..].iter().copied()) {
        let rhs = replay.flat_instance(expr)?;
        let lhs = *replay.sigma.get(var).ok_or("unbound flattened atom")?;
        let proof = alpha_endpoints(replay.store, proof, lhs, rhs);
        replay.remember(expr, proof)?;
        let back = replay.store.sym(proof);
        replay.known.insert(lhs, back);
        match expr {
            ResolvedExpr::Call(..) => replay.atoms.push_back((expr.clone(), proof)),
            ResolvedExpr::Var(_, v) if flat.globals.contains_key(&v.name) => {
                replay.values.push_back((expr.clone(), proof))
            }
            _ => replay.comparisons.push_back(proof),
        }
    }
    let (lhs_expr, rhs_expr) = rule.endpoints();
    let before = if matches!(lhs_expr, ResolvedExpr::Call(..)) {
        replay.expand(lhs_expr, flat_lhs, root)?
    } else if replay.is_local(lhs_expr) {
        root
    } else {
        replay.pattern(lhs_expr)?
    };
    let mut equalities = HashMap::default();
    let mut renamings = HashMap::default();
    for fact in rule.conditions() {
        match fact {
            ResolvedFact::Eq(_, a, b) => {
                let proof = replay.equality(a, b)?;
                equalities.insert((replay.instance(a)?, replay.instance(b)?), proof);
            }
            ResolvedFact::Fact(ResolvedExpr::Call(_, ResolvedCall::Primitive(head), args)) => {
                if head.name() == "renaming-=" {
                    let left = replay.pattern(&args[0])?;
                    let right = replay.pattern(&args[1])?;
                    let left = replay.store.sym(left);
                    let right = replay.store.sym(right);
                    renamings.insert(
                        (replay.instance(&args[0])?, replay.instance(&args[1])?),
                        (left, right),
                    );
                } else {
                    for arg in args {
                        if program.sorts.contains(arg.output_type().name()) {
                            replay.pattern(arg)?;
                        }
                    }
                }
            }
            ResolvedFact::Fact(expr) => {
                replay.pattern(expr)?;
            }
        }
    }
    let mut sigma = replay.sigma.clone();
    sigma.extend(rule.globals.iter().map(|(v, &t)| (v.clone(), t)));
    let auxiliary = rule.normal.bindings(&mut replay.store.term_dag, &sigma)?;
    replay.sigma.extend(auxiliary);
    let mut source_premises = vec![RulePremise::Equality(before)];
    for fact in &rule.normal.body[1..] {
        let proof = match fact {
            ResolvedFact::Eq(_, a, b) => {
                let a = replay.instance(a)?;
                let b = replay.instance(b)?;
                RulePremise::Equality(if a == b {
                    replay.exists(a)?
                } else {
                    *equalities
                        .get(&(a, b))
                        .ok_or("missing source equality premise")?
                })
            }
            ResolvedFact::Fact(ResolvedExpr::Call(_, ResolvedCall::Primitive(head), args))
                if head.name() == "renaming-=" =>
            {
                let key = (replay.instance(&args[0])?, replay.instance(&args[1])?);
                let &(left, right) = renamings.get(&key).ok_or("missing renaming premise")?;
                RulePremise::RenamingEq { left, right }
            }
            ResolvedFact::Fact(ResolvedExpr::Call(_, ResolvedCall::Primitive(_), _)) => {
                let unit = replay.store.term_dag.lit(Literal::Unit);
                RulePremise::Equality(replay.store.fiat(unit, unit))
            }
            ResolvedFact::Fact(expr) => {
                let term = replay.instance(expr)?;
                RulePremise::Equality(replay.exists(term)?)
            }
        };
        source_premises.push(proof);
    }
    let lhs = replay.instance(lhs_expr)?;
    let rhs = replay.instance(rhs_expr)?;
    let variables: HashSet<_> = rule
        .patterns()
        .flat_map(|expr| expr.vars())
        .map(|v| v.name)
        .filter(|v| !rule.globals.contains_key(v))
        .collect();
    let substitution = substitution
        .into_iter()
        .filter(|(v, _)| variables.contains(v))
        .collect();
    let source = replay.store.rule(
        Proposition::new(lhs, rhs),
        name.into(),
        substitution,
        source_premises,
    );
    let proof = replay
        .store
        .trans(before, source)
        .map_err(|e| e.to_string())?;
    let proof = replay.rhs(rhs_expr, flat_rhs, proof)?;
    if !replay.atoms.is_empty() || !replay.values.is_empty() || !replay.comparisons.is_empty() {
        return Err("source traversal did not consume the flattened premises".into());
    }
    let flat_rhs_term = replay.flat_instance(flat_rhs)?;
    let proof = alpha_rhs(replay.store, proof, flat_rhs_term);
    Ok(alpha_endpoints(
        replay.store,
        proof,
        claimed.lhs,
        claimed.rhs,
    ))
}

#[cfg(test)]
#[path = "tests/unflatten.rs"]
mod tests;

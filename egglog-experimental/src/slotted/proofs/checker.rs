//! Checks surface proofs against the slotted source program.

use super::context::{ProofContext, SourceFact, check_term_sort, pattern_term};
use super::format::{Claim, ClaimKind, RulePremise, RuleProof, SlottedProof, SlottedProofStore};
use super::program::ResolvedSlottedProgram;
use super::terms::{Renaming, all_slots, rename, slot_of, slot_term, term_renaming};
use super::{HashMap, HashSet};
use egglog::ast::{Literal, ResolvedExpr, ResolvedExprExt, ResolvedFact};
use egglog::proof::{Justification, Proof, ProofCheckContext, ProofId, ProofStore, Proposition};
use egglog::{Term, TermDag};
use egglog_numeric_id::NumericId;
use std::collections::BTreeSet;
use thiserror::Error;

#[derive(Debug, Clone, Error)]
/// A proof step or final claim that the source program does not justify.
pub enum SlottedCheckError {
    /// The original program cannot be resolved for proof checking.
    #[error("invalid slotted source program: {0}")]
    Source(#[from] super::context::SourceError),
    /// A fiat step is absent from the source program.
    #[error(
        "proof #{proof}: fiat {claim} is neither a built term's reflexivity nor a source union"
    )]
    InvalidFiat {
        /// The rejected step.
        proof: ProofId,
        /// Its printed proposition.
        claim: String,
    },
    /// A rule application names an undeclared rewrite.
    #[error("proof #{proof}: no rewrite named {name:?}")]
    RuleNotFound {
        /// The rejected step.
        proof: ProofId,
        /// The requested rewrite.
        name: String,
    },
    /// A rule application supplies the wrong number of premises.
    #[error(
        "proof #{proof}: rule {name:?} takes {expected} premises after guard normalization, {actual} given"
    )]
    PremiseCount {
        /// The rejected step.
        proof: ProofId,
        /// The applied rewrite.
        name: String,
        /// The number required after guard normalization.
        expected: usize,
        /// The number supplied by the proof.
        actual: usize,
    },
    /// A substitution omits a variable used by the rewrite.
    #[error("proof #{proof}: rule {name:?} leaves {variable} unbound")]
    Unbound {
        /// The rejected step.
        proof: ProofId,
        /// The applied rewrite.
        name: String,
        /// The missing substitution key.
        variable: String,
    },
    /// A rule application does not match its source rewrite.
    #[error("proof #{proof}: rule {name:?}: {detail}")]
    Rule {
        /// The rejected step.
        proof: ProofId,
        /// The applied rewrite.
        name: String,
        /// The violated rule requirement.
        detail: String,
    },
    /// A proof-algebra step does not follow from its premises.
    #[error("proof #{proof}: {step}: {detail}")]
    Step {
        /// The rejected step.
        proof: ProofId,
        /// The proof operation being checked.
        step: &'static str,
        /// The violated operation requirement.
        detail: String,
    },
    /// The checked root proves a different claim.
    #[error(
        "the claim ({kind}) is not what the proof shows: it proves {proven}, the claim is {claim}"
    )]
    Claim {
        /// The requested equality kind.
        kind: String,
        /// The proposition established by the proof.
        proven: String,
        /// The proposition requested by the source.
        claim: String,
    },
}

/// Check a proof against the resolved original slotted program.
/// The program must be typechecked and retain the source's binder annotations.
/// Its axioms and scoped globals are interpreted in `store`'s term arena.
pub fn check_proof(
    store: &mut SlottedProofStore,
    source: &ResolvedSlottedProgram,
    root: ProofId,
) -> Result<Proposition, SlottedCheckError> {
    let program = source.for_proof(store)?;
    check_proof_in_program(store, &program, root)
}

/// Check a claim and its proof against the resolved original slotted program.
/// Return the permutation from the claim's right endpoint to the proved one,
/// after refreshing binders. For ordinary equality it must fix the free slots
/// of at least one endpoint. The claim's terms and `root` belong to `store`.
pub fn check_claim(
    store: &mut SlottedProofStore,
    source: &ResolvedSlottedProgram,
    claim: &Claim,
    root: ProofId,
) -> Result<Renaming, SlottedCheckError> {
    let program = source.for_proof(store)?;
    check_claim_in_program(store, &program, claim, root)
}

type CheckedProofs = HashMap<ProofId, Proposition>;

/// Check an equality proof and every proof it depends on, returning what it proves.
pub(in crate::slotted) fn check_proof_in_program(
    store: &mut SlottedProofStore,
    program: &ProofContext,
    root: ProofId,
) -> Result<Proposition, SlottedCheckError> {
    let mut ordinary = ProofStore::new(
        std::mem::take(&mut store.term_dag),
        HashMap::default(),
        HashSet::default(),
    );
    let context = ProofCheckContext::new(&[], ordinary.term_dag_mut())
        .expect("an empty program has no invalid axioms");
    let result = (|| {
        let mut checked = HashMap::default();
        for id in store.dependencies(root) {
            let result = check_one(store, &mut ordinary, &context, program, id, &checked)?;
            checked.insert(id, result);
        }
        Ok(checked.remove(&root).expect("root was checked"))
    })();
    store.term_dag = std::mem::take(ordinary.term_dag_mut());
    result
}

/// Check that a proof establishes a claim.
pub(super) fn check_claim_in_program(
    store: &mut SlottedProofStore,
    program: &ProofContext,
    claim: &Claim,
    root: ProofId,
) -> Result<Renaming, SlottedCheckError> {
    let proven = check_proof_in_program(store, program, root)?;
    let lhs = program.refresh_binders(&mut store.term_dag, claim.lhs);
    let rhs = program.refresh_binders(&mut store.term_dag, claim.rhs);
    if proven.lhs == lhs {
        let witness = match claim.kind {
            ClaimKind::RenamingEq => term_renaming(&store.term_dag, &[(rhs, proven.rhs)]),
            ClaimKind::Eq => [rhs, lhs].into_iter().find_map(|endpoint| {
                let mut pairs = vec![(rhs, proven.rhs)];
                for slot in program.free_slots(&store.term_dag, endpoint) {
                    let term = slot_term(&mut store.term_dag, slot);
                    pairs.push((term, term));
                }
                term_renaming(&store.term_dag, &pairs)
            }),
        };
        if let Some(witness) = witness {
            return Ok(witness);
        }
    }
    Err(SlottedCheckError::Claim {
        kind: match claim.kind {
            ClaimKind::Eq => "=".into(),
            ClaimKind::RenamingEq => "renaming-=".into(),
        },
        proven: store.proposition_to_string(&proven),
        claim: store.proposition_to_string(&Proposition::new(claim.lhs, claim.rhs)),
    })
}

fn proposition_string(dag: &TermDag, p: &Proposition) -> String {
    format!("{} = {}", dag.to_string(p.lhs), dag.to_string(p.rhs))
}

fn check_one(
    store: &SlottedProofStore,
    ordinary: &mut ProofStore,
    context: &ProofCheckContext,
    program: &ProofContext,
    id: ProofId,
    checked: &CheckedProofs,
) -> Result<Proposition, SlottedCheckError> {
    let proof = store.get(id);
    let step = |step: &'static str, detail: String| SlottedCheckError::Step {
        proof: id,
        step,
        detail,
    };
    for p in proof.premises() {
        if !checked.contains_key(&p) {
            return Err(step(
                "premise",
                format!("proof #{p} is used before it is established: the proof is cyclic"),
            ));
        }
    }
    let premise = |p: &ProofId| checked[p].clone();
    let claimed = proof.proposition();
    if let SlottedProof::Ordinary(proof) = proof
        && matches!(proof.justification(), Justification::Fiat)
        && claimed.lhs == claimed.rhs
        && matches!(
            ordinary.term_dag().get(claimed.lhs),
            Term::Lit(Literal::Unit)
        )
    {
        // Ordinary primitive guards use Unit reflexivity as their result premise.
        let proposition = ordinary
            .check_step(id, proof, &[], context, |_, _| {
                unreachable!("Fiat has no premises")
            })
            .map_err(|e| step("literal", e.to_string()))?;
        return Ok(proposition);
    }
    let dag = ordinary.term_dag_mut();
    let lhs_sort = check_term_sort(program, dag, claimed.lhs, None).map_err(|e| step("sort", e))?;
    check_term_sort(program, dag, claimed.rhs, Some(&lhs_sort)).map_err(|e| step("sort", e))?;
    if lhs_sort == "Var" && claimed.lhs != claimed.rhs {
        return Err(step(
            "rigid variable",
            "distinct Var names cannot be equal".into(),
        ));
    }
    if let SlottedProof::Ordinary(proof) = proof
        && matches!(
            proof.justification(),
            Justification::Sym(_)
                | Justification::Trans(..)
                | Justification::Congr { .. }
                | Justification::Proj { .. }
        )
    {
        ordinary
            .check_step(id, proof, &[], context, |_, p| Ok(checked[&p].clone()))
            .map_err(|e| step("equality", e.to_string()))?;
    }
    let dag = ordinary.term_dag_mut();
    let derived = match proof {
        SlottedProof::Rule(proof) => {
            return check_rule(ordinary, context, program, id, proof, checked);
        }
        SlottedProof::Alpha { proof, .. } => {
            let p = premise(proof);
            if !program.alpha_eq(dag, p.rhs, claimed.rhs) {
                return Err(step(
                    "alpha",
                    "right endpoints are not alpha-equivalent".into(),
                ));
            }
            Proposition::new(p.lhs, claimed.rhs)
        }
        SlottedProof::Equivariance {
            proof, renaming, ..
        } => {
            let p = premise(proof);
            let lhs = rename(dag, renaming, p.lhs);
            let rhs = rename(dag, renaming, p.rhs);
            Proposition::new(lhs, rhs)
        }
        SlottedProof::Ordinary(proof) => {
            match proof.justification() {
                Justification::Fiat => {
                    let reflexive =
                        claimed.lhs == claimed.rhs && program.is_built(dag, claimed.lhs);
                    if !(reflexive || program.is_union(claimed.lhs, claimed.rhs)) {
                        return Err(SlottedCheckError::InvalidFiat {
                            proof: id,
                            claim: proposition_string(dag, claimed),
                        });
                    }
                }
                Justification::Sym(_)
                | Justification::Trans(..)
                | Justification::Congr { .. }
                | Justification::Proj { .. } => {}
                Justification::Rule { .. } => {
                    unreachable!("rules have typed premises in the slotted store")
                }
                Justification::MergeFn { .. }
                | Justification::ContainerNormalize { .. }
                | Justification::Eval => {
                    return Err(step(
                        "source",
                        "this step is not supported by the slotted source language".into(),
                    ));
                }
            };
            claimed.clone()
        }
    };
    if &derived != claimed {
        return Err(step(
            "conclusion",
            format!(
                "states {} but derives {}",
                proposition_string(ordinary.term_dag(), claimed),
                proposition_string(ordinary.term_dag(), &derived)
            ),
        ));
    }
    Ok(derived)
}

fn check_rule(
    ordinary: &mut ProofStore,
    context: &ProofCheckContext,
    program: &ProofContext,
    id: ProofId,
    proof: &RuleProof,
    checked: &CheckedProofs,
) -> Result<Proposition, SlottedCheckError> {
    let RuleProof {
        name,
        substitution,
        premises: premise_proofs,
        proposition: claimed,
    } = proof;
    let dag = ordinary.term_dag_mut();
    let rule = program
        .rewrites
        .get(name)
        .ok_or_else(|| SlottedCheckError::RuleNotFound {
            proof: id,
            name: name.to_string(),
        })?;
    let fail = |detail: String| SlottedCheckError::Rule {
        proof: id,
        name: name.to_string(),
        detail,
    };
    if let Some(name) = substitution
        .keys()
        .find(|name| rule.globals.contains_key(*name))
    {
        return Err(fail(format!(
            "substitution overrides captured global {name}"
        )));
    }
    let bindings: HashMap<_, _> = substitution
        .iter()
        .chain(rule.globals.iter())
        .map(|(name, &term)| (name.clone(), term))
        .collect();
    let unbound = |variable: String| SlottedCheckError::Unbound {
        proof: id,
        name: name.to_string(),
        variable,
    };

    let (_, rhs_expr) = rule.endpoints();
    let rhs_pattern = pattern_term(dag, rhs_expr);
    for var in rule.patterns().flat_map(|expr| expr.vars()) {
        let term = *bindings
            .get(&var.name)
            .ok_or_else(|| unbound(var.name.clone()))?;
        check_term_sort(program, dag, term, Some(var.sort.name()))
            .map_err(|e| fail(format!("binding {}: {e}", var.name)))?;
    }

    // Distinct $ literals require distinct names; plain Var locals accepted by
    // the source-program API can alias.
    let literals: Vec<_> = rule
        .patterns()
        .flat_map(|expr| expr.vars())
        .filter(|var| var.sort.name() == "Var")
        .map(|var| var.name)
        .filter(|name| !rule.globals.contains_key(name))
        .collect();
    let mut by_slot: HashMap<i64, String> = HashMap::default();
    for literal in literals.iter().filter(|v| v.starts_with('$')) {
        let term = *substitution
            .get(literal)
            .ok_or_else(|| unbound(literal.clone()))?;
        let slot = slot_of(dag, term).ok_or_else(|| {
            fail(format!(
                "{literal} is bound to {}, not a slot",
                dag.to_string(term)
            ))
        })?;
        if let Some(other) = by_slot.insert(slot, literal.clone())
            && other != *literal
        {
            return Err(fail(format!(
                "{other} and {literal} are both ${slot}: different slot literals are different slots"
            )));
        }
    }

    // Right-hand-side slot literals absent from the body must be fresh.
    let body_vars: HashSet<String> = rule
        .rule
        .body
        .iter()
        .flat_map(SourceFact::terms)
        .flat_map(|expr| expr.vars())
        .map(|var| var.name)
        .collect();
    for var in rule.pattern_vars(dag, rhs_pattern) {
        if body_vars.contains(&var) {
            continue;
        }
        if !var.starts_with('$') {
            return Err(fail(format!("{var} occurs only on the right-hand side")));
        }
        let minted = *substitution.get(&var).ok_or_else(|| unbound(var.clone()))?;
        let slot = slot_of(dag, minted)
            .ok_or_else(|| fail(format!("minted {var} is bound to a non-slot")))?;
        let used: BTreeSet<i64> = substitution
            .iter()
            .filter(|(name, _)| name.as_str() != var)
            .map(|(_, t)| t)
            .chain(rule.globals.values())
            .flat_map(|t| all_slots(dag, *t))
            .collect();
        if used.contains(&slot) {
            return Err(fail(format!(
                "minted {var} is ${slot}, which another binding mentions"
            )));
        }
    }

    let facts = &rule.normal.body;
    let auxiliary = rule.normal.bindings(dag, &bindings).map_err(&fail)?;
    if premise_proofs.len() != facts.len() {
        return Err(SlottedCheckError::PremiseCount {
            proof: id,
            name: name.clone(),
            expected: facts.len(),
            actual: premise_proofs.len(),
        });
    }
    let mut substitution = substitution.clone();
    substitution.extend(rule.globals.clone());
    substitution.extend(auxiliary);
    let mut premises = Vec::new();
    let equality = |premise: &RulePremise| {
        let RulePremise::Equality(id) = premise else {
            return Err(fail(
                "expected an equality premise, found RenamingEq".into(),
            ));
        };
        Ok(&checked[id])
    };
    for (i, (fact, premise)) in facts.iter().zip(premise_proofs).enumerate() {
        if let ResolvedFact::Fact(ResolvedExpr::Call(
            _,
            egglog::ResolvedCall::Primitive(head),
            args,
        )) = fact
        {
            let result = if head.name() == "renaming-=" {
                let RulePremise::RenamingEq { left, right } = premise else {
                    return Err(fail("renaming-= requires a RenamingEq premise".into()));
                };
                for ((arg, &p), variable) in args
                    .iter()
                    .zip([left, right])
                    .zip(&rule.normal.renaming_args[&i])
                {
                    let p = &checked[&p];
                    check_term_sort(program, dag, p.rhs, Some(arg.output_type().name()))
                        .map_err(&fail)?;
                    substitution.insert(variable.name.clone(), p.rhs);
                    premises.push(p.clone());
                }
                let unit = dag.lit(Literal::Unit);
                Proposition::new(unit, unit)
            } else {
                equality(premise)?.clone()
            };
            premises.push(result);
        } else {
            let checked = equality(premise)?;
            let condition_sort = match fact {
                ResolvedFact::Eq(_, expr, _) | ResolvedFact::Fact(expr) => expr.output_type(),
            };
            check_term_sort(program, dag, checked.lhs, Some(condition_sort.name()))
                .map_err(&fail)?;
            premises.push(checked.clone());
        }
    }
    let native_proof = Proof::new(
        claimed.clone(),
        Justification::Rule {
            name: name.clone(),
            substitution,
            premise_proofs: (0..premises.len()).map(ProofId::from_usize).collect(),
        },
    );
    let proven = ordinary
        .check_step(id, &native_proof, &rule.normal.commands, context, |_, p| {
            Ok(premises[p.index()].clone())
        })
        .map_err(|e| fail(e.to_string()))?;
    Ok(proven)
}

#[cfg(test)]
#[path = "tests/checker.rs"]
mod tests;

#[cfg(test)]
#[path = "tests/checker_guard.rs"]
mod guard_tests;

//! Materialize native explanations; optional validation walks their complete DAG.

use super::*;
use std::collections::HashSet;
use std::sync::Arc;

pub(super) fn materialize(eg: &mut G, start: &str, goal: &str, verify: bool) -> Result<(), String> {
    let left = RecExpr::<L>::parse(start).map_err(|e| format!("{e:?}"))?;
    let right = RecExpr::<L>::parse(goal).map_err(|e| format!("{e:?}"))?;
    let proof = eg.explain_equivalence(left, right);
    if verify {
        eg.check();
        let mut checked = HashSet::new();
        let mut pending = vec![proof.clone()];
        while let Some(proof) = pending.pop() {
            if !checked.insert(Arc::as_ptr(&proof)) {
                continue;
            }
            match proof.proof() {
                // Explicit leaves are the native library's recorded rewrite/union axioms.
                Proof::Explicit(_) => {
                    eg.get_syn_node(&proof.l);
                    eg.get_syn_node(&proof.r);
                }
                Proof::Reflexivity(_) => {
                    if proof.l != proof.r {
                        return Err("native reflexivity proof has different endpoints".into());
                    }
                }
                Proof::Symmetry(SymmetryProof(child)) => {
                    let reversed = Equation {
                        l: child.r.clone(),
                        r: child.l.clone(),
                    };
                    if !same_equation(&proof, &reversed) {
                        return Err("native symmetry proof has inconsistent endpoints".into());
                    }
                    pending.push(child.clone());
                }
                Proof::Transitivity(TransitivityProof(left, right)) => {
                    check_transitivity(&proof, left, right)?;
                    pending.extend([left.clone(), right.clone()]);
                }
                Proof::Congruence(rule) => {
                    // The native checker validates the heads, binders and child equations.
                    rule.check(&proof, eg);
                    pending.extend(rule.0.iter().cloned());
                }
            }
        }
    }
    // The native registry already hash-conses explanation steps. Retain its complete
    // in-memory result without flattening or serializing the certificate.
    std::hint::black_box(proof);
    Ok(())
}

fn same_equation(left: &Equation, right: &Equation) -> bool {
    let mut renaming = SlotMap::new();
    for (left, right) in [(&left.l, &right.l), (&left.r, &right.r)] {
        if left.id != right.id || left.m.keys() != right.m.keys() {
            return false;
        }
        let next = left.m.inverse().compose(&right.m);
        let Some(combined) = renaming.try_union(&next) else {
            return false;
        };
        renaming = combined;
    }
    renaming.is_bijection() && left.apply_slotmap(&renaming) == *right
}

/// Check transitivity modulo the native proof format's independent slot renamings.
fn check_transitivity(goal: &Equation, left: &Equation, right: &Equation) -> Result<(), String> {
    if left.l.id != goal.l.id || right.r.id != goal.r.id || left.r.id != right.l.id {
        return Err("native transitivity proof has incompatible classes".into());
    }
    let mut first = left.l.m.inverse().compose_partial(&goal.l.m);
    let mut second = right.r.m.inverse().compose_partial(&goal.r.m);
    let extend_first = |first: &SlotMap, second: &SlotMap| {
        first
            .try_union(
                &left
                    .r
                    .m
                    .inverse()
                    .compose_partial(&right.l.m)
                    .compose_partial(second),
            )
            .ok_or("native transitivity has conflicting left renamings")
    };
    let extend_second = |first: &SlotMap, second: &SlotMap| {
        second
            .try_union(
                &right
                    .l
                    .m
                    .inverse()
                    .compose_partial(&left.r.m)
                    .compose_partial(first),
            )
            .ok_or("native transitivity has conflicting right renamings")
    };
    first = extend_first(&first, &second)?;
    second = extend_second(&first, &second)?;
    for slot in left.slots() {
        if !first.contains_key(slot) {
            first.insert(slot, Slot::fresh());
        }
    }
    second = extend_second(&first, &second)?;
    for slot in right.slots() {
        if !second.contains_key(slot) {
            second.insert(slot, Slot::fresh());
        }
    }
    let left = left.apply_slotmap(&first);
    let right = right.apply_slotmap(&second);
    if !first.is_bijection()
        || !second.is_bijection()
        || left.l != goal.l
        || right.r != goal.r
        || left.r != right.l
    {
        return Err("native transitivity proof does not establish its conclusion".into());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn both_matchers_materialize_and_validate_the_same_substitution_goal() {
        for (policy, lhs) in [
            (Substitution::Syntactic, "nested (app (lam $x ?body) ?t)"),
            (
                Substitution::Snapshot,
                "atom root app lam t\natom lam lam $x body",
            ),
        ] {
            let source = format!(
                "rounds 1\nterm (app (lam $0 (var $0)) (null))\nrule\n{lhs}\nrhs root ?body[(var $x) := ?t]\ngoal (null)\n"
            );
            for mode in [ProofMode::Extract, ProofMode::Check] {
                let outcome = run_spec(&source, policy, mode).unwrap();
                assert_eq!(outcome.goals, [true]);
                assert_eq!(outcome.proof_summary.check_requests, 1);
                assert_eq!(outcome.proof_summary.produced_certificates, 1);
                assert_eq!(
                    outcome.proof_summary.verified_certificates,
                    usize::from(mode == ProofMode::Check)
                );
            }
        }
    }
}

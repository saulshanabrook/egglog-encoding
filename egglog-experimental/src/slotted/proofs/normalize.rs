//! Push equivariance through ordinary equality steps, sharing each transported
//! subproof, and remove reflexive scaffolding. Source steps retain their checked
//! instantiations; any remaining equivariance is immediately above a source step.

use super::HashMap;
use super::format::{SlottedJustification as Step, SlottedProofId, SlottedProofStore};
use super::terms::{Renaming, all_slots, rename, slot_of};
use egglog::Term;

type Key = (SlottedProofId, Renaming);

impl SlottedProofStore {
    /// Normalize an already checked proof. Check the resulting proof again before
    /// using it, just as for any other proof transformation.
    pub fn simplify(&mut self, root: SlottedProofId) -> SlottedProofId {
        let root = (root, Renaming::identity());
        let mut memo = HashMap::<Key, SlottedProofId>::default();
        let mut work = vec![(root.clone(), false)];
        while let Some(((id, rho), ready)) = work.pop() {
            let key = (id, rho.clone());
            if memo.contains_key(&key) {
                continue;
            }
            let proof = self.get(id).clone();
            let children: Vec<Key> = match &proof.justification {
                Step::Equivariance { proof, renaming } => vec![(*proof, rho.compose(renaming))],
                Step::Rule { premises, .. } => premises
                    .iter()
                    .map(|&p| (p, Renaming::identity()))
                    .collect(),
                _ => self
                    .children(id)
                    .into_iter()
                    .map(|p| (p, rho.clone()))
                    .collect(),
            };
            if !ready {
                work.push((key, true));
                work.extend(children.into_iter().rev().map(|k| (k, false)));
                continue;
            }
            let children: Vec<_> = children.iter().map(|k| memo[k]).collect();
            let result = match proof.justification {
                Step::Equivariance { .. } => children[0],
                Step::Sym(_) => self.simple_sym(children[0]),
                Step::Proj { child_index, .. } => self
                    .project(children[0], child_index)
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
                        self.congr(children[0], child_index, children[1])
                            .expect("normalizing preserves child terms")
                    }
                }
                Step::Fiat | Step::Rule { .. } => {
                    let step = match proof.justification {
                        Step::Rule {
                            name, substitution, ..
                        } => Step::Rule {
                            name,
                            substitution,
                            premises: children,
                        },
                        _ => Step::Fiat,
                    };
                    let p = proof.proposition;
                    let lhs = rename(&mut self.term_dag, &rho, p.lhs);
                    let rhs = rename(&mut self.term_dag, &rho, p.rhs);
                    // All slots and literals have reflexivity independently of
                    // source construction. Compound terms still need provenance.
                    if lhs == rhs
                        && (slot_of(&self.term_dag, lhs).is_some()
                            || matches!(self.term_dag.get(lhs), Term::Lit(_)))
                    {
                        self.fiat(lhs, rhs)
                    } else {
                        let unchanged = (lhs, rhs) == (p.lhs, p.rhs);
                        let slots = all_slots(&self.term_dag, p.lhs)
                            .union(&all_slots(&self.term_dag, p.rhs))
                            .copied()
                            .collect();
                        let source = self.add(p, step);
                        if unchanged {
                            source
                        } else {
                            self.equivariance(source, rho.restricted(&slots))
                        }
                    }
                }
            };
            memo.insert(key, result);
        }
        memo[&root]
    }

    fn reflexive(&self, p: SlottedProofId) -> bool {
        let p = self.proposition(p);
        p.lhs == p.rhs
    }

    fn simple_sym(&mut self, p: SlottedProofId) -> SlottedProofId {
        if self.reflexive(p) {
            p
        } else if let Step::Sym(inner) = self.get(p).justification {
            inner
        } else {
            self.sym(p)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::slotted::proofs::checker::check_proof;
    use crate::slotted::proofs::source::{ColumnKind, SlottedProgram};
    use egglog::TermDag;

    #[test]
    fn transports_binder_children_and_preserves_source_axioms() {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram::default();
        program.add_constructor("F", vec![ColumnKind::Child]);
        program.add_constructor("G", vec![ColumnKind::Child]);
        program.add_constructor("Wrap", vec![ColumnKind::Child]);
        program.add_constructor("Lam", vec![ColumnKind::Binder, ColumnKind::Child]);
        for (name, term) in [
            ("f", "(F $0)"),
            ("g", "(G $0)"),
            ("lam", "(Lam $0 (F $0))"),
            ("wrap", "(Wrap (Lam $0 (F $0)))"),
        ] {
            program.add_let(&mut dag, name, term).unwrap();
        }
        program.add_union(&mut dag, "f", "g", "U").unwrap();
        let mut store = SlottedProofStore::new(dag);
        let union = store.fiat(program.lets["f"], program.lets["g"]);
        let lam = store.fiat(program.lets["lam"], program.lets["lam"]);
        let lam = store.congr(lam, 1, union).unwrap();
        let wrap = store.fiat(program.lets["wrap"], program.lets["wrap"]);
        let wrap = store.congr(wrap, 0, lam).unwrap();
        let root = store.equivariance(wrap, Renaming::new([(0, 1), (1, 2), (2, 0)]).unwrap());
        let expected = check_proof(&mut store, &program, root).unwrap();
        let normalized = store.simplify(root);
        assert_eq!(
            check_proof(&mut store, &program, normalized).unwrap(),
            expected
        );
        assert_eq!(
            store.term_dag.to_string(expected.proposition.rhs),
            "(Wrap (Lam $1 (G $1)))"
        );
        for id in store.dependencies(normalized) {
            if let Step::Equivariance { proof, .. } = store.get(id).justification {
                assert!(matches!(
                    store.get(proof).justification,
                    Step::Fiat | Step::Rule { .. }
                ));
            }
        }
        let again = store.simplify(normalized);
        assert_eq!(store.proposition(again), &expected.proposition);
    }

    #[test]
    fn inverse_transports_cancel_without_trusting_new_fiats() {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram::default();
        program.add_constructor("F", vec![ColumnKind::Child]);
        program.add_let(&mut dag, "f", "(F $0)").unwrap();
        let mut store = SlottedProofStore::new(dag);
        let source = store.fiat(program.lets["f"], program.lets["f"]);
        let rho = Renaming::new([(0, 1), (1, 2), (2, 0)]).unwrap();
        let first = store.equivariance(source, rho.clone());
        let second = store.equivariance(first, rho.inverse());
        let normalized = store.simplify(second);
        assert_eq!(normalized, source);
        check_proof(&mut store, &program, normalized).unwrap();
        let transported = store.simplify(first);
        let p = store.proposition(transported).clone();
        let forged = store.fiat(p.lhs, p.rhs);
        assert!(check_proof(&mut store, &program, forged).is_err());
        check_proof(&mut store, &program, transported).unwrap();
    }
}

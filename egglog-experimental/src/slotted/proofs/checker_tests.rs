use super::{SlottedCheckError, check_claim, check_proof};
use crate::slotted::proofs::format::{
    Claim, ClaimKind, ProofId, SlottedConclusion, SlottedProof, SlottedProofStore,
};
use crate::slotted::proofs::source::{ColumnKind, SlottedProgram};
use crate::slotted::proofs::terms::{Renaming, slot_term};
use egglog::proof::{Justification, Proposition};
use egglog::{TermDag, TermId};
use egglog_numeric_id::NumericId;

fn variable(dag: &mut TermDag, name: i64) -> TermId {
    let slot = slot_term(dag, name);
    dag.app("V".into(), vec![slot])
}

fn figure_3() -> (SlottedProofStore, SlottedProgram, Claim) {
    let mut dag = TermDag::default();
    let mut program = SlottedProgram::default();
    program.add_constructor("V", vec![ColumnKind::Var]);
    program.add_constructor("Mul", vec![ColumnKind::Child, ColumnKind::Child]);
    program.add_constructor("Null", vec![]);
    program
        .add_let(&mut dag, "m7", "(Mul (V $7) (Null))")
        .unwrap();
    program.add_let(&mut dag, "zero", "(Null)").unwrap();
    program.add_union(&mut dag, "m7", "zero").unwrap();
    let claim = program
        .claim(&mut dag, "=", "(Mul (V $9) (Null))", "zero")
        .unwrap();
    (SlottedProofStore::new(dag), program, claim)
}

#[test]
fn redundancy_by_equivariance() {
    let (mut store, program, claim) = figure_3();
    let (m7, zero) = (program.lets["m7"], program.lets["zero"]);
    let union = store.fiat(m7, zero);
    let back = store.sym(union);
    let renamed = store.equivariance(back, Renaming::new([(7, 9), (9, 7)]).unwrap());
    let proof = store.sym(renamed);
    let proven = check_proof(&mut store, &program, proof).unwrap();
    // Equivariance acts on both endpoints; `(Null)` has no slots.
    assert_eq!(
        store.proposition_to_string(&proven),
        "(Mul (V $9) (Null)) = (Null)"
    );
    check_claim(
        &mut store,
        &program,
        &claim,
        &SlottedConclusion {
            proof,
            renaming: Renaming::identity(),
        },
    )
    .unwrap();
    let text = store.proof_to_string(proof);
    assert!(
        text.contains("(Equivariance") && text.contains("(renaming ($7 $9) ($9 $7))"),
        "{text}"
    );
}

#[test]
fn a_non_injective_equivariance_cannot_be_stated() {
    assert!(Renaming::new([(0, 1)]).is_none());
}

#[test]
fn equivariance_checks_both_endpoints() {
    let (mut store, program, _) = figure_3();
    let (term, zero) = (program.lets["m7"], program.lets["zero"]);
    let union = store.fiat(term, zero);
    let sigma = Renaming::new([(7, 9), (9, 7)]).unwrap();
    let transported = store.equivariance(union, sigma.clone());
    check_proof(&mut store, &program, transported).unwrap();
    let forged = store.add(SlottedProof::Equivariance {
        proposition: Proposition::new(term, zero),
        proof: union,
        renaming: sigma,
    });
    assert!(matches!(
        check_proof(&mut store, &program, forged),
        Err(SlottedCheckError::Step {
            step: "conclusion",
            ..
        })
    ));
}

#[test]
fn claim_witnesses_distinguish_free_and_bound_names() {
    let mut dag = TermDag::default();
    let mut program = SlottedProgram::default();
    program.add_constructor("V", vec![ColumnKind::Var]);
    program.add_constructor("F", vec![ColumnKind::Child]);
    program.add_constructor("Lam", vec![ColumnKind::Binder, ColumnKind::Child]);
    program.add_let(&mut dag, "free", "(F (V $0))").unwrap();
    program
        .add_let(&mut dag, "bound", "(Lam $0 (V $0))")
        .unwrap();
    let free = program.claim(&mut dag, "=", "free", "(F (V $1))").unwrap();
    let bound = program
        .claim(&mut dag, "=", "bound", "(Lam $1 (V $1))")
        .unwrap();
    let mut store = SlottedProofStore::new(dag);
    let proof = store.fiat(free.lhs, free.lhs);
    let witness = SlottedConclusion {
        proof,
        renaming: Renaming::new([(0, 1), (1, 0)]).unwrap(),
    };
    assert!(check_claim(&mut store, &program, &free, &witness).is_err());
    let renaming_claim = Claim {
        kind: ClaimKind::RenamingEq,
        ..free
    };
    check_claim(&mut store, &program, &renaming_claim, &witness).unwrap();
    let wrong = SlottedConclusion {
        renaming: Renaming::identity(),
        ..witness.clone()
    };
    assert!(check_claim(&mut store, &program, &renaming_claim, &wrong).is_err());
    let proof = store.fiat(bound.lhs, bound.lhs);
    check_claim(
        &mut store,
        &program,
        &bound,
        &SlottedConclusion { proof, ..witness },
    )
    .unwrap();
}

#[test]
fn alpha_checks_scopes_payloads_and_its_premise() {
    let mut dag = TermDag::default();
    let mut program = SlottedProgram::default();
    program.add_constructor("V", vec![ColumnKind::Var]);
    program.add_constructor("Lam", vec![ColumnKind::Binder, ColumnKind::Child]);
    program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
    program.add_sorted_constructor("Num", "U", vec![ColumnKind::Payload("i64".into())]);
    let source = "(Lam $0 (Lam $0 (Pair (V $0) (Pair (V $2) (Num 1)))))";
    program.add_let(&mut dag, "input", source).unwrap();
    let input = program.lets["input"];
    assert_eq!(dag.to_string(input), source);
    let mut store = SlottedProofStore::new(dag);
    let premise = store.fiat(input, input);
    for (target, valid) in [
        (
            "(Lam $3 (Lam $4 (Pair (V $4) (Pair (V $2) (Num 1)))))",
            true,
        ),
        (
            "(Lam $3 (Lam $4 (Pair (V $3) (Pair (V $2) (Num 1)))))",
            false,
        ),
        (
            "(Lam $2 (Lam $4 (Pair (V $4) (Pair (V $2) (Num 1)))))",
            false,
        ),
        (
            "(Lam $3 (Lam $4 (Pair (V $4) (Pair (V $5) (Num 1)))))",
            false,
        ),
        (
            "(Lam $3 (Lam $4 (Pair (V $4) (Pair (V $2) (Num 2)))))",
            false,
        ),
    ] {
        let rhs = program
            .claim(&mut store.term_dag, "=", "input", target)
            .unwrap()
            .rhs;
        let proof = store.alpha(premise, rhs);
        assert_eq!(
            check_proof(&mut store, &program, proof).is_ok(),
            valid,
            "{target}"
        );
        if valid {
            let renamed = store.equivariance(proof, Renaming::new([(2, 6), (6, 2)]).unwrap());
            let simplified = store.simplify(renamed);
            assert_eq!(
                check_proof(&mut store, &program, renamed).unwrap(),
                check_proof(&mut store, &program, simplified).unwrap()
            );
            let changed_left = store.add(SlottedProof::Alpha {
                proposition: Proposition::new(rhs, rhs),
                proof: premise,
            });
            assert!(check_proof(&mut store, &program, changed_left).is_err());
            let invented = store.fiat(rhs, rhs);
            let proof = store.alpha(invented, input);
            assert!(check_proof(&mut store, &program, proof).is_err());
        }
    }
}

#[test]
fn congruence_cannot_put_a_constructor_in_a_binder_column() {
    let mut dag = TermDag::default();
    let mut program = SlottedProgram::default();
    program.add_constructor("V", vec![ColumnKind::Var]);
    program.add_constructor("Lam", vec![ColumnKind::Binder, ColumnKind::Child]);
    program.add_constructor("K", vec![]);
    program
        .add_let(&mut dag, "input", "(Lam $0 (V $0))")
        .unwrap();
    program.add_union(&mut dag, "$0", "(K)").unwrap();
    let input = program.lets["input"];
    let union = &program.unions[0];
    let mut store = SlottedProofStore::new(dag);
    let root = store.fiat(input, input);
    let child = store.fiat(union.lhs, union.rhs);
    let proof = store.congr(root, 0, child).unwrap();
    assert!(
        check_proof(&mut store, &program, proof)
            .unwrap_err()
            .to_string()
            .contains("expected Var")
    );
}

#[test]
fn source_globals_cannot_be_overridden_by_a_rule_substitution() {
    let mut dag = TermDag::default();
    let mut program = SlottedProgram::default();
    program.add_constructor("V", vec![ColumnKind::Var]);
    program.add_constructor("F", vec![ColumnKind::Child]);
    program.add_let(&mut dag, "fixed", "(V $0)").unwrap();
    program.add_let(&mut dag, "input", "(F (V $1))").unwrap();
    program
        .add_rewrite(&mut dag, r#"(rewrite (F x) fixed :name "r")"#)
        .unwrap();
    // A later scope cannot change what the rule captured.
    program.add_let(&mut dag, "fixed", "(V $2)").unwrap();
    let input = program.lets["input"];
    let old = variable(&mut dag, 0);
    let x = variable(&mut dag, 1);
    let new = variable(&mut dag, 2);
    let mut store = SlottedProofStore::new(dag);
    let root = store.fiat(input, input);
    for (rhs, substitution, valid) in [
        (old, vec![("x".into(), x)], true),
        (new, vec![("x".into(), x)], false),
        (new, vec![("x".into(), x), ("fixed".into(), new)], false),
        (old, vec![("x".into(), x), ("fixed".into(), old)], false),
    ] {
        let proof = store.ordinary(
            Proposition::new(input, rhs),
            Justification::Rule {
                name: "r".into(),
                substitution: substitution.into_iter().collect(),
                premise_proofs: vec![root],
            },
        );
        assert_eq!(check_proof(&mut store, &program, proof).is_ok(), valid);
    }
}

#[test]
fn rule_side_patterns_require_explicit_alpha_and_preserve_free_names() {
    let mut dag = TermDag::default();
    let mut program = SlottedProgram::default();
    program.add_constructor("V", vec![ColumnKind::Var]);
    program.add_constructor("F", vec![ColumnKind::Child]);
    program.add_constructor("Pair", vec![ColumnKind::Child, ColumnKind::Child]);
    program.add_constructor("Lam", vec![ColumnKind::Binder, ColumnKind::Child]);
    program.add_constructor("K", vec![]);
    program
        .add_let(&mut dag, "child", "(Lam $0 (Pair (V $0) (V $3)))")
        .unwrap();
    program.add_let(&mut dag, "root", "(F child)").unwrap();
    program
        .add_rewrite(
            &mut dag,
            r#"(rewrite (F x) (K) :when ((= x (Lam $a (Pair (V $a) (V $b))))) :name "r")"#,
        )
        .unwrap();
    let (root, child) = (program.lets["root"], program.lets["child"]);
    let mut store = SlottedProofStore::new(dag);
    let premise = store.fiat(root, root);
    let side = store.fiat(child, child);
    let k = store.term_dag.app("K".into(), vec![]);
    let a = slot_term(&mut store.term_dag, 1);
    for (free_slot, convert, valid) in [(3, false, false), (3, true, true), (4, true, false)] {
        let b = slot_term(&mut store.term_dag, free_slot);
        let va = store.term_dag.app("V".into(), vec![a]);
        let vb = store.term_dag.app("V".into(), vec![b]);
        let pair = store.term_dag.app("Pair".into(), vec![va, vb]);
        let lam = store.term_dag.app("Lam".into(), vec![a, pair]);
        let side = if convert {
            store.alpha(side, lam)
        } else {
            side
        };
        let rule = store.ordinary(
            Proposition::new(root, k),
            Justification::Rule {
                name: "r".into(),
                substitution: vec![("x".into(), child), ("$a".into(), a), ("$b".into(), b)]
                    .into_iter()
                    .collect(),
                premise_proofs: vec![premise, side],
            },
        );
        assert_eq!(check_proof(&mut store, &program, rule).is_ok(), valid);
    }
}

#[test]
fn original_conditions_require_evidence_in_source_order() {
    let mut dag = TermDag::default();
    let mut program = SlottedProgram::default();
    program.add_constructor("V", vec![ColumnKind::Var]);
    for name in ["F", "G", "H"] {
        program.add_constructor(name, vec![ColumnKind::Child]);
    }
    program.add_constructor("A", vec![]);
    program.add_let(&mut dag, "input", "(F (G (A)))").unwrap();
    program.add_let(&mut dag, "side", "(H (A))").unwrap();
    program
        .add_rewrite(
            &mut dag,
            r#"(rewrite (F (G x)) (H x) :when ((= (G x) y) (H x)) :name "nested")"#,
        )
        .unwrap();
    let input = program.lets["input"];
    let side = program.lets["side"];
    let a = dag.app("A".into(), vec![]);
    let g = dag.app("G".into(), vec![a]);
    let mut store = SlottedProofStore::new(dag);
    let root = store.fiat(input, input);
    let equality = store.fiat(g, g);
    let existence = store.fiat(side, side);
    for (premises, valid) in [
        (vec![root, equality, existence], true),
        (vec![root, existence, equality], false),
        (vec![root, equality], false),
        (vec![root, equality, equality], false),
    ] {
        let proof = store.ordinary(
            Proposition::new(input, side),
            Justification::Rule {
                name: "nested".into(),
                substitution: vec![("x".into(), a), ("y".into(), g)].into_iter().collect(),
                premise_proofs: premises,
            },
        );
        assert_eq!(check_proof(&mut store, &program, proof).is_ok(), valid);
    }
}

#[test]
fn fiat_needs_a_built_term_or_a_union() {
    let (mut store, program, _claim) = figure_3();
    let s9 = variable(&mut store.term_dag, 9);
    let null = store.term_dag.app("Null".into(), vec![]);
    let bogus = store.term_dag.app("Mul".into(), vec![s9, null]);
    let proof = store.fiat(bogus, bogus);
    let err = check_proof(&mut store, &program, proof).unwrap_err();
    assert!(
        matches!(err, SlottedCheckError::InvalidFiat { .. }),
        "{err}"
    );
    let wrong = store.fiat(null, bogus);
    assert!(check_proof(&mut store, &program, wrong).is_err());
}

#[test]
fn rule_instances_and_minted_slots() {
    let mut dag = TermDag::default();
    let mut program = SlottedProgram::default();
    program.add_constructor("V", vec![ColumnKind::Var]);
    program.add_constructor("F", vec![ColumnKind::Child, ColumnKind::Child]);
    program.add_constructor("Lam", vec![ColumnKind::Binder, ColumnKind::Child]);
    program.add_constructor("App", vec![ColumnKind::Child, ColumnKind::Child]);
    program.add_constructor("Num", vec![ColumnKind::Payload("i64".into())]);
    program
        .add_let(&mut dag, "t", "(F (Num 1) (Num 2))")
        .unwrap();
    program
        .add_let(&mut dag, "u", "(F (V $1) (Num 2))")
        .unwrap();
    program
        .add_rewrite(
            &mut dag,
            r#"(rewrite (F x y) (Lam $s (App (F x y) (V $s))) :name "wrap")"#,
        )
        .unwrap();
    program
        .add_rewrite(
            &mut dag,
            r#"(rewrite (Lam $x (App f (V $x))) f :name "eta" :when ((not-free $x f)))"#,
        )
        .unwrap();
    let mut store = SlottedProofStore::new(dag);
    let t = program.lets["t"];
    let one = store.term_dag.lit(egglog::ast::Literal::Int(1));
    let two = store.term_dag.lit(egglog::ast::Literal::Int(2));
    let num1 = store.term_dag.app("Num".into(), vec![one]);
    let num2 = store.term_dag.app("Num".into(), vec![two]);
    let s4 = slot_term(&mut store.term_dag, 4);
    let v4 = store.term_dag.app("V".into(), vec![s4]);
    let app = store.term_dag.app("App".into(), vec![t, v4]);
    let wrapped = store.term_dag.app("Lam".into(), vec![s4, app]);
    let root = store.fiat(t, t);
    let wrap = store.ordinary(
        Proposition::new(t, wrapped),
        Justification::Rule {
            name: "wrap".into(),
            substitution: vec![("x".into(), num1), ("y".into(), num2), ("$s".into(), s4)]
                .into_iter()
                .collect(),
            premise_proofs: vec![root],
        },
    );
    check_proof(&mut store, &program, wrap).unwrap();

    // eta on the wrapped term: (Lam $4 (App t $4)) = t, with $4 not free in t
    let unit = store.term_dag.lit(egglog::ast::Literal::Unit);
    let guard = store.fiat(unit, unit);
    let eta = store.ordinary(
        Proposition::new(wrapped, t),
        Justification::Rule {
            name: "eta".into(),
            substitution: vec![("$x".into(), s4), ("f".into(), t)]
                .into_iter()
                .collect(),
            premise_proofs: vec![wrap, guard],
        },
    );
    check_proof(&mut store, &program, eta).unwrap();

    // minting a slot the other bindings mention is refused
    let s1 = slot_term(&mut store.term_dag, 1);
    let v1 = store.term_dag.app("V".into(), vec![s1]);
    let f1 = store.term_dag.app("F".into(), vec![v1, num2]);
    let app1 = store.term_dag.app("App".into(), vec![f1, v1]);
    let bad_wrapped = store.term_dag.app("Lam".into(), vec![s1, app1]);
    let f1_root = store.ordinary(Proposition::new(f1, f1), Justification::Fiat);
    let bad = store.ordinary(
        Proposition::new(f1, bad_wrapped),
        Justification::Rule {
            name: "wrap".into(),
            substitution: vec![("x".into(), v1), ("y".into(), num2), ("$s".into(), s1)]
                .into_iter()
                .collect(),
            premise_proofs: vec![f1_root],
        },
    );
    let err = check_proof(&mut store, &program, bad).unwrap_err();
    assert!(err.to_string().contains("minted"), "{err}");
}
#[test]
fn minted_slots_avoid_source_globals() {
    let mut dag = TermDag::default();
    let mut program = SlottedProgram::default();
    program.add_constructor("V", vec![ColumnKind::Var]);
    program.add_constructor("F", vec![ColumnKind::Child]);
    program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
    program.add_let(&mut dag, "fixed", "(V $0)").unwrap();
    program.add_let(&mut dag, "input", "(F (V $1))").unwrap();
    program
        .add_rewrite(
            &mut dag,
            r#"(rewrite (F x) (Pair fixed (V $fresh)) :name "r")"#,
        )
        .unwrap();
    let input = program.lets["input"];
    let zero = variable(&mut dag, 0);
    let one = variable(&mut dag, 1);
    let mut store = SlottedProofStore::new(dag);
    let root = store.fiat(input, input);
    for (slot, valid) in [(0, false), (1, false), (2, true), (37, true)] {
        let fresh = slot_term(&mut store.term_dag, slot);
        let term = store.term_dag.app("V".into(), vec![fresh]);
        let rhs = store.term_dag.app("Pair".into(), vec![zero, term]);
        let proof = store.ordinary(
            Proposition::new(input, rhs),
            Justification::Rule {
                name: "r".into(),
                substitution: vec![("x".into(), one), ("$fresh".into(), fresh)]
                    .into_iter()
                    .collect(),
                premise_proofs: vec![root],
            },
        );
        assert_eq!(check_proof(&mut store, &program, proof).is_ok(), valid);
    }
}

#[test]
fn slot_literals_are_distinct_slots() {
    let mut dag = TermDag::default();
    let mut program = SlottedProgram::default();
    program.add_constructor("V", vec![ColumnKind::Var]);
    program.add_constructor("F", vec![ColumnKind::Child, ColumnKind::Child]);
    program.add_constructor("A", vec![]);
    program
        .add_let(&mut dag, "ff", "(F (V $0) (V $0))")
        .unwrap();
    program.add_let(&mut dag, "fa", "(F (A) (V $0))").unwrap();
    program
        .add_rewrite(
            &mut dag,
            r#"(rewrite (F (V $x) (V $y)) (A) :name "distinct")"#,
        )
        .unwrap();
    let mut store = SlottedProofStore::new(dag);
    let (ff, fa) = (program.lets["ff"], program.lets["fa"]);
    let a = store.term_dag.app("A".into(), vec![]);
    let s0 = slot_term(&mut store.term_dag, 0);
    let root = store.fiat(ff, ff);
    // `(F $x $y)` does not match `(F $0 $0)`: two literals, one slot
    let aliased = store.ordinary(
        Proposition::new(ff, a),
        Justification::Rule {
            name: "distinct".into(),
            substitution: vec![("$x".into(), s0), ("$y".into(), s0)]
                .into_iter()
                .collect(),
            premise_proofs: vec![root],
        },
    );
    let err = check_proof(&mut store, &program, aliased).unwrap_err();
    assert!(err.to_string().contains("different slot literals"), "{err}");
    // a slot literal is bound to a slot, never to a term
    let root = store.fiat(fa, fa);
    let non_slot = store.ordinary(
        Proposition::new(fa, a),
        Justification::Rule {
            name: "distinct".into(),
            substitution: vec![("$x".into(), a), ("$y".into(), s0)]
                .into_iter()
                .collect(),
            premise_proofs: vec![root],
        },
    );
    let err = check_proof(&mut store, &program, non_slot).unwrap_err();
    assert!(err.to_string().contains("expected Var"), "{err}");
}

#[test]
fn corrupt_and_cyclic_proofs_are_rejected() {
    let (mut store, program, _claim) = figure_3();
    let (m7, zero) = (program.lets["m7"], program.lets["zero"]);
    let union = store.fiat(m7, zero);
    let refl = store.fiat(m7, m7);
    // a transitivity whose middle terms differ
    let trans = store.ordinary(Proposition::new(m7, m7), Justification::Trans(union, refl));
    let err = check_proof(&mut store, &program, trans).unwrap_err();
    assert!(err.to_string().contains("matching middle terms"), "{err}");
    // a congruence whose child proof is about another term
    let congr = store.ordinary(
        Proposition::new(m7, m7),
        Justification::Congr {
            proof: refl,
            child_index: 1,
            child_proof: union,
        },
    );
    let err = check_proof(&mut store, &program, congr).unwrap_err();
    assert!(err.to_string().contains("child proof lhs"), "{err}");
    // a step stating something other than what it derives
    let sym = store.ordinary(Proposition::new(m7, zero), Justification::Sym(union));
    let err = check_proof(&mut store, &program, sym).unwrap_err();
    assert!(
        matches!(
            err,
            SlottedCheckError::Step {
                step: "equality",
                ..
            }
        ),
        "{err}"
    );
    // a proof that depends on itself
    let next = store.len();
    let first = store.ordinary(
        Proposition::new(zero, m7),
        Justification::Sym(ProofId::from_usize(next + 1)),
    );
    assert_eq!(first, ProofId::from_usize(next));
    let second = store.ordinary(Proposition::new(m7, zero), Justification::Sym(first));
    let err = check_proof(&mut store, &program, second).unwrap_err();
    assert!(err.to_string().contains("cyclic"), "{err}");
}

#[test]
fn variable_term_equality_cannot_equate_names_or_other_carriers() {
    let mut dag = TermDag::default();
    let mut program = SlottedProgram::default();
    program.add_sorted_constructor("VA", "A", vec![ColumnKind::Var]);
    program.add_sorted_constructor("VB", "B", vec![ColumnKind::Var]);
    program.add_sorted_constructor("LamA", "A", vec![ColumnKind::Binder, ColumnKind::Child]);
    program.add_union(&mut dag, "(VA $0)", "(VA $1)").unwrap();
    program.add_let(&mut dag, "b0", "(VB $0)").unwrap();
    program.add_let(&mut dag, "b1", "(VB $1)").unwrap();
    program
        .add_let(&mut dag, "lam", "(LamA $0 (VA $0))")
        .unwrap();
    let a0 = program.unions[0].lhs;
    let a1 = program.unions[0].rhs;
    let b0 = program.lets["b0"];
    let b1 = program.lets["b1"];
    let zero = slot_term(&mut dag, 0);
    let one = slot_term(&mut dag, 1);
    let mut store = SlottedProofStore::new(dag);
    let terms = store.fiat(a0, a1);
    check_proof(&mut store, &program, terms).unwrap();
    let name = store.project(terms, 0).unwrap();
    assert_eq!(
        check_proof(&mut store, &program, name).unwrap(),
        Proposition::new(one, one)
    );
    for proof in [
        store.fiat(zero, one),
        store.ordinary(
            Proposition::new(zero, one),
            Justification::Proj {
                proof: terms,
                child_index: 0,
            },
        ),
        store.fiat(b0, b1),
    ] {
        assert!(check_proof(&mut store, &program, proof).is_err());
    }
    let lam = program.lets["lam"];
    let parent = store.fiat(lam, lam);
    assert!(store.congr(parent, 0, terms).is_err());
    // Even a malformed recorded source union cannot equate rigid names.
    program.add_union(&mut store.term_dag, "$0", "$1").unwrap();
    let names = store.fiat(zero, one);
    assert!(
        check_proof(&mut store, &program, names)
            .unwrap_err()
            .to_string()
            .contains("distinct Var names")
    );
}

#[test]
fn transitivity_cannot_bridge_constructor_sorts() {
    let mut dag = TermDag::default();
    let mut program = SlottedProgram::default();
    program.add_sorted_constructor("VA", "A", vec![ColumnKind::Var]);
    program.add_sorted_constructor("VB", "B", vec![ColumnKind::Var]);
    program.add_union(&mut dag, "(VA $0)", "(VA $1)").unwrap();
    program.add_union(&mut dag, "(VB $1)", "(VB $2)").unwrap();
    let [a, b] = program.unions.as_slice() else {
        unreachable!()
    };
    let mut store = SlottedProofStore::new(dag);
    let left = store.fiat(a.lhs, a.rhs);
    let right = store.fiat(b.lhs, b.rhs);
    assert!(store.trans(left, right).is_err());
    let forged = store.ordinary(
        Proposition::new(a.lhs, b.rhs),
        Justification::Trans(left, right),
    );
    assert!(
        check_proof(&mut store, &program, forged)
            .unwrap_err()
            .to_string()
            .contains("expected A")
    );
}

#[test]
fn native_rule_bindings_and_conditions_preserve_constructor_sorts() {
    let mut dag = TermDag::default();
    let mut program = SlottedProgram::default();
    program.add_sorted_constructor("VA", "A", vec![ColumnKind::Var]);
    program.add_sorted_constructor("VB", "B", vec![ColumnKind::Var]);
    program.add_sorted_constructor("WA", "A", vec![ColumnKind::Child]);
    program.add_sorted_constructor("PairA", "A", vec![ColumnKind::Child; 2]);
    for (name, term) in [
        ("a0", "(VA $0)"),
        ("a1", "(VA $1)"),
        ("b1", "(VB $1)"),
        ("wa", "(WA (VA $1))"),
        ("pair", "(PairA (VA $0) (VA $1))"),
    ] {
        program.add_let(&mut dag, name, term).unwrap();
    }
    program.add_union(&mut dag, "a0", "wa").unwrap();
    program
        .add_rewrite(&mut dag, r#"(rewrite x y :when ((= x (WA y))) :name "r")"#)
        .unwrap();
    let a0 = program.lets["a0"];
    let a1 = program.lets["a1"];
    let b1 = program.lets["b1"];
    let wa = program.lets["wa"];
    let mut store = SlottedProofStore::new(dag);
    let root = store.fiat(a0, a0);
    let side = store.fiat(a0, wa);
    for (binding, valid) in [(a1, true), (b1, false)] {
        let rule = store.ordinary(
            Proposition::new(a0, a1),
            Justification::Rule {
                name: "r".into(),
                substitution: [("x".into(), a0), ("y".into(), binding)]
                    .into_iter()
                    .collect(),
                premise_proofs: vec![root, side],
            },
        );
        assert_eq!(check_proof(&mut store, &program, rule).is_ok(), valid);
    }
    for invalid in [
        r#"(rewrite (VA $x) (VB $x) :name "cross")"#,
        r#"(rewrite $x $y :when ((= p (PairA (VA $x) (VA $y)))) :name "names")"#,
    ] {
        assert!(program.add_rewrite(&mut store.term_dag, invalid).is_err());
    }
}

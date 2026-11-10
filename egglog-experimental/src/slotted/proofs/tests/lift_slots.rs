use super::*;

#[test]
fn slot_matching_preserves_shared_constraints_and_bijections() {
    let program = ProofContext::default();
    let names = EncodingNames::default();
    let egg = ProofStore::new(TermDag::default(), HashMap::default(), HashSet::default());
    let mut dag = TermDag::default();
    let slots: Vec<_> = (0..3).map(|slot| slot_term(&mut dag, slot)).collect();
    let repeated = dag.app("Pair".into(), vec![slots[0], slots[0]]);
    let distinct = dag.app("Pair".into(), vec![slots[1], slots[2]]);
    let mut left = repeated;
    let mut right = dag.app("Pair".into(), vec![slots[1], slots[1]]);
    // These terms have billions of tree occurrences but only dozens of DAG
    // nodes. Matching must retain the slot constraint while sharing the walk.
    for _ in 0..32 {
        left = dag.app("Pair".into(), vec![left, left]);
        right = dag.app("Pair".into(), vec![right, right]);
    }
    let tr = SlotLifter::new(&program, dag, &names, &egg);
    let mut pairs = BTreeMap::new();
    assert!(tr.match_slots(left, right, &mut pairs).is_ok());
    assert_eq!(pairs, BTreeMap::from([(0, 1)]));
    assert!(Renaming::completing(pairs).is_some());

    let mut pairs = BTreeMap::new();
    assert!(tr.match_slots(repeated, distinct, &mut pairs).is_err());
    assert_eq!(
        tr.unify_slots(repeated, distinct, &mut BTreeMap::new())
            .unwrap_err(),
        "slot $0 would have to be both $1 and $2"
    );
    let mut pairs = BTreeMap::new();
    assert!(tr.match_slots(distinct, repeated, &mut pairs).is_ok());
    assert!(Renaming::completing(pairs).is_none());
    // An identical pair still constrains its slot to itself; skipping it would
    // incorrectly accept an incompatible mapping supplied by an earlier match.
    assert!(
        tr.match_slots(slots[0], slots[0], &mut BTreeMap::from([(0, 1)]))
            .is_err()
    );
    // A rejected structural candidate must not try to print the enormous DAG.
    assert!(
        tr.match_slots(left, slots[0], &mut BTreeMap::new())
            .is_err()
    );
}

#[test]
fn source_names_take_precedence_over_generated_rule_kinds() {
    let mut program = ProofContext::default();
    program.add_constructor("N", vec![]);
    program
        .add_rewrite(
            &mut TermDag::default(),
            "(rewrite (N) (N) :name slotted/group-shrink)",
        )
        .unwrap();
    assert_eq!(
        rule_kind(&program, "slotted/group-shrink"),
        RuleKind::Source("slotted/group-shrink")
    );
    assert_eq!(
        rule_kind(&program, "slotted/group-shrink/apply"),
        RuleKind::Apply("slotted/group-shrink")
    );
    assert_eq!(
        rule_kind(&program, "slotted/group-shrink/0"),
        RuleKind::GroupShrink
    );
    assert_eq!(
        rule_kind(&program, "slotted/unknown/0"),
        RuleKind::Unknown("slotted/unknown/0")
    );
}

pub(in crate::slotted::proofs) fn check_restricted_symmetries(
    program: &ProofContext,
    dag: TermDag,
    names: &EncodingNames,
    egg: &ProofStore,
) -> LiftResult<usize> {
    let mut tr = SlotLifter::new(program, dag, names, egg);
    let mut checked = 0;
    for (id, proof) in egg.proofs() {
        let Justification::Rule {
            name,
            substitution,
            premise_proofs,
        } = proof.justification()
        else {
            continue;
        };
        if rule_kind(program, name) != RuleKind::GroupShrink {
            continue;
        }
        let old = tr.group(substitution["_s"])?;
        let slots = tr.slot_map(substitution["_cs"])?;
        if old
            .iter()
            .all(|g| g.keys().all(|slot| slots.contains_key(slot)))
        {
            continue;
        }
        let restored = egg
            .proofs()
            .find_map(|(restored, proof)| match proof.justification() {
                Justification::Rule {
                    name,
                    premise_proofs,
                    ..
                } if rule_kind(program, name) == RuleKind::GroupRestore
                    && premise_proofs.first() == Some(&id) =>
                {
                    Some(restored)
                }
                _ => None,
            })
            .ok_or("restricted group has no restore proof")?;
        let (_, args) = tr.app(proof.lhs()).ok_or("expected staged group row")?;
        let class = args[0];
        for generator in old {
            let restricted = compose(&slots, &compose(&generator, &slots));
            if is_identity(&restricted) || restricted.len() == generator.len() {
                continue;
            }
            let symmetry = tr.product_symmetry(
                class,
                &restricted,
                &[(generator, premise_proofs[0])],
                Some(&slots),
            )?;
            let proof = tr.out.proof(symmetry);
            crate::slotted::proofs::checker::check_proof_in_program(&mut tr.out, program, proof)
                .map_err(|e| e.to_string())?;
            checked += 1;
        }
        for g in tr.group(args[1])? {
            if is_identity(&g) {
                continue;
            }
            let symmetry = tr.symmetry(class, &g, restored)?;
            let proof = tr.out.proof(symmetry);
            crate::slotted::proofs::checker::check_proof_in_program(&mut tr.out, program, proof)
                .map_err(|e| e.to_string())?;
        }
    }
    Ok(checked)
}

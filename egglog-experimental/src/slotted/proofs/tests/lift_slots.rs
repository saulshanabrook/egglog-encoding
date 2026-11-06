use super::*;

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

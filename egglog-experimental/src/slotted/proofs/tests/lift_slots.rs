use super::*;

#[test]
fn variable_expansion_replays_its_construction_witness() {
    use crate::slotted::{Compiler, Options, ProofMode, new_egraph_with_proofs};
    use egglog::CommandOutput;

    let mut compiler = Compiler::new(Options {
        proof_mode: ProofMode::Prove,
        ..Default::default()
    });
    let encoded = compiler
        .compile_program(
            None,
            "(datatype E (Start) (Wrap E) (One))
             (let input (Start))
             (rewrite (Start) (Wrap (One)) :name build)
             (run 1)
             (check (= input (Wrap (One))))",
        )
        .unwrap();
    // Retain the ordinary proof before the source lifter visits the build rule.
    let commands = encoded.to_string().replace("(slotted-prove 0 ", "(prove ");
    let mut graph = new_egraph_with_proofs();
    let egg = graph
        .parse_and_run_program(None, &commands)
        .unwrap()
        .into_iter()
        .find_map(|output| match output {
            CommandOutput::ProveExists { proof_store, .. } => Some(proof_store),
            _ => None,
        })
        .unwrap();
    let request = encoded.proofs.values().next().unwrap();
    let mut dag = TermDag::default();
    let context = request
        .flattened
        .context(&mut dag, BTreeMap::new())
        .unwrap();
    let mut lifter = SlotLifter::new(&context, dag, &request.names, &egg);
    let (witness, class, target) = egg
        .proofs()
        .find_map(|(id, proof)| {
            if !matches!(proof.justification(), Justification::Rule { name, .. } if name == "build/apply")
                || proof.lhs() != proof.rhs()
                || !lifter.is_carrier_term(proof.lhs())
            {
                return None;
            }
            let target = lifter.dec(proof.lhs()).unwrap();
            lifter.reflexive(target).is_err().then_some((id, proof.lhs(), target))
        })
        .expect("a newly constructed term must have its own rule witness");
    let pattern = lifter.out.term_dag.var("total".into());
    let subst = IndexMap::default();
    let bridges = HashMap::default();
    let ctx = ExpandCtx {
        prems: &[witness],
        subst: &subst,
        names: HashMap::default(),
        classes: BTreeMap::new(),
        readings: BTreeMap::new(),
        bridges: &bridges,
    };
    let expanded = lifter
        .expand(class, pattern, &[], &ctx, HashMap::default())
        .unwrap();
    let (mut store, proof) = lifter.out.finish(expanded.proof);
    super::super::check_proof(&mut store, &request.flattened, proof).unwrap();
    assert_eq!(store.proposition(proof), &Proposition::new(target, target));
}

#[test]
fn existence_proofs_respect_binder_scopes() {
    use crate::slotted::proofs::{check_proof, resolve_program};
    use egglog::ast::{Parser, parse_sexps};

    for (input, target, exists) in [
        (
            "(Pair (Lam $0 (V $0)) (V $0))",
            "(Pair (Lam $1 (V $1)) (V $0))",
            true,
        ),
        (
            "(Pair (Lam $0 (V $0)) (Lam $0 (V $0)))",
            "(Pair (Lam $1 (V $1)) (Lam $2 (V $2)))",
            true,
        ),
        ("(Lam $0 (V $1))", "(Lam $1 (V $1))", false),
    ] {
        let source =
            format!("(datatype E (V Var) (Lam Var E :binder 0) (Pair E E)) (let input {input})");
        let source = resolve_program(&parse_sexps(None, &source).unwrap()).unwrap();
        let mut dag = TermDag::default();
        let context = source.context(&mut dag, BTreeMap::new()).unwrap();
        let target = Parser::default()
            .get_expr_from_string(None, target)
            .unwrap();
        let target = context.ground_term(&mut dag, &target).unwrap();
        let names = EncodingNames::default();
        let egg = ProofStore::new(TermDag::default(), HashMap::default(), HashSet::default());
        let mut lifter = SlotLifter::new(&context, dag, &names, &egg);
        let proof = lifter.reflexive(target);
        if !exists {
            assert!(
                proof.is_err(),
                "alpha conversion cannot capture a free slot"
            );
            continue;
        }
        let proof = proof.unwrap();
        let (mut store, proof) = lifter.out.finish(proof);
        check_proof(&mut store, &source, proof).unwrap();
        assert_eq!(store.proposition(proof), &Proposition::new(target, target));
    }
}

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

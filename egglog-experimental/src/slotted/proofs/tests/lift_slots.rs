use super::*;

pub(in crate::slotted::proofs) fn native_query(
    graph: &mut egglog::EGraph,
    commands: &str,
    program: &ProofContext,
    source: &super::super::ResolvedSlottedProgram,
    names: &EncodingNames,
    dag: TermDag,
) -> (ProofStore, source::Certificates) {
    let mut evidence = source::Certificates {
        store: SlottedProofStore::new(dag),
        ..Default::default()
    };
    let mut source = source::SourceLifter::new(program, source, names, &evidence);
    let mut egg = None;
    for command in graph.parse_program(None, commands).unwrap() {
        if let egglog::ast::Command::Prove(_, facts) = command {
            egg = Some(
                graph
                    .prove_facts_with_visitor(facts, &mut |store, id, origin| {
                        source.visit(store, id, origin)
                    })
                    .unwrap()
                    .0,
            );
        } else {
            graph.run_program(vec![command]).unwrap();
        }
    }
    evidence = source.finish().unwrap();
    (egg.unwrap(), evidence)
}

#[test]
fn composition_preserves_scoped_alpha_and_edge_coordinates() {
    let mut program = ProofContext::default();
    program.add_constructor("Start", vec![]);
    program.add_constructor("Done", vec![]);
    program.add_constructor("V", vec![ColumnKind::Var]);
    program.add_constructor(
        "Let",
        vec![ColumnKind::Child, ColumnKind::Binder, ColumnKind::Child],
    );
    let mut dag = TermDag::default();
    program
        .add_union(&mut dag, "(Start)", "(Let (V $10) $10 (V $10))")
        .unwrap();
    program
        .add_union(&mut dag, "(Let (V $0) $1 (V $1))", "(Done)")
        .unwrap();
    program
        .add_union(&mut dag, "(Let (V $2) $1 (V $1))", "(Done)")
        .unwrap();
    let names = EncodingNames::default();
    let egg = ProofStore::new(TermDag::default(), HashMap::default(), HashSet::default());
    let mut lifter = SlotLifter::new(
        &program,
        dag,
        &names,
        NativeProofs {
            store: &egg,
            program: &[],
        },
    );
    let [first, second, wrong] = program.unions.as_slice() else {
        unreachable!()
    };
    let left = lifter.out.fiat(first.lhs, first.rhs);
    let left = lifter
        .out
        .reframe(left, Renaming::new([(0, 10), (10, 0)]).unwrap());
    let right = lifter.out.fiat(second.lhs, second.rhs);
    let wrong = lifter.out.fiat(wrong.lhs, wrong.rhs);
    assert!(lifter.trans(left, wrong).is_err());
    let proof = lifter.trans(left, right).unwrap();
    let (mut store, proof) = lifter.out.finish(proof);
    super::super::checker::check_proof_in_program(&mut store, &program, proof).unwrap();
    assert_eq!(
        store.proposition(proof),
        &Proposition::new(first.lhs, second.rhs)
    );
}

#[test]
fn recorded_existence_rejects_incompatible_shapes_before_alpha_conversion() {
    let mut program = ProofContext::default();
    program.add_constructor("Z", vec![]);
    program.add_constructor("V", vec![ColumnKind::Var]);
    program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
    program.add_constructor("Triple", vec![ColumnKind::Child; 3]);
    let mut dag = TermDag::default();
    let vars: Vec<_> = (0..5)
        .map(|slot| {
            let slot = slot_term(&mut dag, slot);
            dag.app("V".into(), vec![slot])
        })
        .collect();
    let zero = dag.app("Z".into(), vec![]);
    let good = dag.app("Triple".into(), vec![vars[3], vars[4], zero]);
    let mut shared = zero;
    for _ in 0..32 {
        shared = dag.app("Pair".into(), vec![shared, shared]);
    }
    let bad = dag.app("Triple".into(), vec![vars[0], vars[0], shared]);
    let target = dag.app("Triple".into(), vec![vars[1], vars[2], zero]);
    program.lets.insert("good".into(), good);
    program.lets.insert("bad".into(), bad);
    let names = EncodingNames::default();
    let egg = ProofStore::new(TermDag::default(), HashMap::default(), HashSet::default());
    let mut lifter = SlotLifter::new(
        &program,
        dag,
        &names,
        NativeProofs {
            store: &egg,
            program: &[],
        },
    );
    assert!(lifter.reflexive(target).is_err());
    let bad = lifter.out.fiat(bad, bad);
    assert!(lifter.existence_from(bad, target).is_err());
    let good = lifter.out.fiat(good, good);
    let proof = lifter.existence_from(good, target).unwrap();
    let (mut store, proof) = lifter.out.finish(proof);
    super::super::checker::check_proof_in_program(&mut store, &program, proof).unwrap();
    assert_eq!(store.proposition(proof), &Proposition::new(target, target));
}

#[test]
fn constructed_support_survives_rekeying_under_a_binder() {
    use crate::slotted::{Compiler, Options, ProofMode, new_egraph_with_proofs};

    let mut compiler = Compiler::new(Options {
        proof_mode: ProofMode::Prove,
        ..Default::default()
    });
    let encoded = compiler
        .compile_program(
            None,
            "(datatype E (V Var) (Null) (Pair E E) (Wrap E) (Input E) (Lam Var E :binder 0))
         (let replacement (Pair (V $0) (Lam $1 (V $1))))
         (let old (Wrap (Null)))
         (let input (Input old))
         (union replacement old)
         (rewrite (Input body) (Lam $x (Pair body (V $x))) :name build)
         (run 1)
         (check (= input (Lam $bound (Pair old (V $bound)))))",
        )
        .unwrap();
    let commands = encoded.to_string().replace("(slotted-prove 0 ", "(prove ");
    let union = commands
        .lines()
        .find(|line| line.starts_with("(union "))
        .unwrap();
    let schedule = commands
        .lines()
        .find(|line| line.starts_with("(run-schedule ") && line.contains("slotted-apply"))
        .unwrap();
    // Retain the match, then apply the declared union before its head runs.
    // This forces the stored input column to change class while its frame
    // retains the original support, including beneath the new binder.
    let machinery = crate::slotted::maintenance::MACHINERY;
    let delayed = format!(
        "(run-schedule {machinery} (run) (saturate (run slotted-refine)))\n{union}\n(run-schedule {machinery} (run slotted-apply) {machinery})"
    );
    let commands = commands
        .lines()
        .filter(|line| *line != union)
        .collect::<Vec<_>>()
        .join("\n")
        .replace(schedule, &delayed);
    let request = encoded.proofs.values().next().unwrap();
    let mut dag = TermDag::default();
    let context = request
        .flattened
        .context(&mut dag, BTreeMap::new())
        .unwrap();
    let mut graph = new_egraph_with_proofs();
    let (egg, evidence) = native_query(
        &mut graph,
        &commands,
        &context,
        &request.flattened,
        &request.names,
        dag,
    );
    let mut lifter = SlotLifter::with_evidence(
        &context,
        evidence.store.term_dag.clone(),
        &request.names,
        NativeProofs {
            store: &egg,
            program: graph.proof_checking_program(),
        },
        &evidence,
    )
    .unwrap();
    assert!(egg.proofs().any(|(_, proof)| {
        matches!(proof.justification(), Justification::Rule { name, premise_proofs, .. }
            if name == "build/apply" && !lifter.unwrap_match(premise_proofs[0]).unwrap().1.is_empty())
    }), "the stored match must actually be rekeyed");
    assert!(
        !evidence.head_supports.is_empty(),
        "the built children must need support certificates"
    );
    let mut results = Vec::new();
    for (&(proof, column), &certificate) in &evidence.head_supports {
        let mut store = evidence.store.clone();
        super::super::checker::check_proof_in_program(&mut store, &context, certificate).unwrap();
        let row = egg.get(proof).rhs();
        let (head, args) = lifter.app(row).unwrap();
        let (_, _, physical) = context.constructors[head]
            .encoded_columns()
            .nth(column)
            .unwrap();
        let class = args[physical.end - 1];
        let term = lifter.dec(class).unwrap();
        let support = Support {
            origin: SupportOrigin::Constructor {
                proof,
                column,
                rhs: true,
            },
            transport: None,
        };
        let slots = lifter.support_slots(support).unwrap();
        let slot = *context
            .free_slots(&lifter.out.term_dag, term)
            .difference(&slots)
            .next()
            .unwrap();
        let fresh = lifter.fresh();
        let permutation = Renaming::new([(slot, fresh), (fresh, slot)]).unwrap();
        let result = lifter
            .support_permutation(support, class, &permutation)
            .unwrap();
        results.push(lifter.out.proof(result));
    }
    let mut store = (*lifter.out).clone();
    for proof in results {
        super::super::checker::check_proof_in_program(&mut store, &context, proof).unwrap();
    }
}

#[test]
fn constructed_terms_replay_their_recorded_rule_head() {
    use crate::slotted::{Compiler, Options, ProofMode, new_egraph_with_proofs};

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
    let request = encoded.proofs.values().next().unwrap();
    let mut dag = TermDag::default();
    let context = request
        .flattened
        .context(&mut dag, BTreeMap::new())
        .unwrap();
    let (egg, evidence) = native_query(
        &mut graph,
        &commands,
        &context,
        &request.flattened,
        &request.names,
        dag,
    );
    let mut lifter = SlotLifter::with_evidence(
        &context,
        evidence.store.term_dag.clone(),
        &request.names,
        NativeProofs {
            store: &egg,
            program: graph.proof_checking_program(),
        },
        &evidence,
    )
    .unwrap();
    lifter.known.clear();
    let (witness, _, target) = egg
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
    let proof = lifter.eq(witness).unwrap();
    let (mut store, proof) = lifter.out.finish(proof);
    super::super::check_proof(&mut store, &request.flattened, proof).unwrap();
    assert_eq!(store.proposition(proof), &Proposition::new(target, target));
}

#[test]
fn carrier_projections_replay_the_recorded_parent_and_column() {
    use crate::slotted::{Compiler, Options, ProofMode, new_egraph_with_proofs};

    let mut compiler = Compiler::new(Options {
        proof_mode: ProofMode::Prove,
        ..Default::default()
    });
    let encoded = compiler
        .compile_program(
            None,
            "(datatype E (Start) (V Var) (Wrap E) (Lam Var E :binder 0))
             (let input (Start))
             (rewrite (Start) (Lam $x (Wrap (V $x))) :name build)
             (run 1)
             (check (= input (Lam $y (Wrap (V $y)))))",
        )
        .unwrap();
    let commands = encoded.to_string().replace("(slotted-prove 0 ", "(prove ");
    let request = encoded.proofs.values().next().unwrap();
    let mut dag = TermDag::default();
    let context = request
        .flattened
        .context(&mut dag, BTreeMap::new())
        .unwrap();
    let mut graph = new_egraph_with_proofs();
    let (egg, evidence) = native_query(
        &mut graph,
        &commands,
        &context,
        &request.flattened,
        &request.names,
        dag,
    );
    let mut checked = 0;
    for (id, proof) in egg.proofs() {
        if !matches!(proof.justification(), Justification::Rule { name, .. } if name == "build/apply")
        {
            continue;
        }
        let mut lifter = SlotLifter::with_evidence(
            &context,
            evidence.store.term_dag.clone(),
            &request.names,
            NativeProofs {
                store: &egg,
                program: graph.proof_checking_program(),
            },
            &evidence,
        )
        .unwrap();
        let Some((head, args)) = lifter.app(proof.rhs()) else {
            continue;
        };
        let physical = match head {
            "Lam" => 2,
            "Wrap" => 1,
            _ => continue,
        };
        let child = args[physical];
        let expected = lifter.dec(child).unwrap();
        let lifted = lifter.project(id, physical).unwrap();
        let (mut store, lifted) = lifter.out.finish(lifted);
        super::super::check_proof(&mut store, &request.flattened, lifted).unwrap();
        assert_eq!(
            store.proposition(lifted),
            &Proposition::new(expected, expected)
        );
        checked += 1;
    }
    assert!(
        checked > 0,
        "the extracted proof must contain a constructed parent"
    );
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
        let mut lifter = SlotLifter::new(
            &context,
            dag,
            &names,
            NativeProofs {
                store: &egg,
                program: &[],
            },
        );
        let input = context.lets.values().copied().next().unwrap();
        let proof = lifter.out.fiat(input, input);
        let proof = lifter.existence_from(proof, target);
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
    let tr = SlotLifter::new(
        &program,
        dag,
        &names,
        NativeProofs {
            store: &egg,
            program: &[],
        },
    );
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
    names: &EncodingNames,
    egg: NativeProofs<'_>,
    evidence: &source::Certificates,
) -> LiftResult<usize> {
    let mut tr = SlotLifter::with_evidence(
        program,
        evidence.store.term_dag.clone(),
        names,
        egg,
        evidence,
    )?;
    let mut checked = 0;
    let mut certificates = 0;
    let mut invocations = 0;
    for (id, proof) in egg.proofs() {
        let Justification::Rule {
            name,
            substitution,
            premise_proofs,
        } = proof.justification()
        else {
            continue;
        };
        if rule_kind(program, name) == RuleKind::InvocationMerge {
            let expected = Proposition::new(tr.dec(proof.lhs())?, tr.dec(proof.rhs())?);
            let merged = tr.eq(id)?;
            let merged = tr.out.proof(merged);
            crate::slotted::proofs::checker::check_proof_in_program(&mut tr.out, program, merged)
                .map_err(|e| e.to_string())?;
            assert_eq!(tr.out.proposition(merged), &expected);
            invocations += 1;
        }
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
            let term = tr.dec(class)?;
            for slot in program.free_slots(&tr.out.term_dag, term) {
                if g.contains_key(&slot) {
                    continue;
                }
                let fresh = tr.fresh();
                let certificate = tr.group_certificate(class, &g, restored, slot, fresh)?;
                let certificate = tr.out.proof(certificate);
                crate::slotted::proofs::checker::check_proof_in_program(
                    &mut tr.out,
                    program,
                    certificate,
                )
                .map_err(|e| e.to_string())?;
                let swap = Renaming::new([(slot, fresh), (fresh, slot)]).unwrap();
                let target = rename(&mut tr.out.term_dag, &swap, term);
                assert_eq!(
                    tr.out.proposition(certificate),
                    &Proposition::new(term, target)
                );
                certificates += 1;
            }
            if is_identity(&g) {
                continue;
            }
            let symmetry = tr.symmetry(class, &g, restored)?;
            let proof = tr.out.proof(symmetry);
            crate::slotted::proofs::checker::check_proof_in_program(&mut tr.out, program, proof)
                .map_err(|e| e.to_string())?;
        }
    }
    assert!(
        certificates > 0,
        "the restricted group must omit a free slot"
    );
    assert!(
        invocations > 0,
        "the proof must merge equal invocation names"
    );
    Ok(checked)
}

#[test]
fn equal_decoded_endpoints_preserve_a_nontrivial_class_equality() {
    let mut program = ProofContext::default();
    program.add_constructor("V", vec![ColumnKind::Var]);
    program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
    let mut dag = TermDag::default();
    program
        .add_union(&mut dag, "(Pair (V $0) (V $1))", "(Pair (V $1) (V $0))")
        .unwrap();
    let term = program.unions[0].lhs;
    let mut encoded = TermDag::default();
    let mut map = |entries: &[i64]| {
        let entries = entries
            .iter()
            .map(|&n| encoded.lit(Literal::Int(n)))
            .collect();
        encoded.app("map-of".into(), entries)
    };
    let identity = map(&[0, 0]);
    let redundant = map(&[0, 0, 7, 9]);
    let shifted = map(&[0, 1]);
    let variable = encoded.app("V".into(), vec![identity]);
    let left = encoded.app("Pair".into(), vec![identity, variable, shifted, variable]);
    let right = encoded.app("Pair".into(), vec![redundant, variable, shifted, variable]);
    let egg = ProofStore::new(encoded, HashMap::default(), HashSet::default());
    let names = EncodingNames::default();
    let mut lifter = SlotLifter::new(
        &program,
        dag,
        &names,
        NativeProofs {
            store: &egg,
            program: &[],
        },
    );
    assert_ne!(left, right);
    assert_eq!(lifter.dec(left).unwrap(), term);
    assert_eq!(lifter.dec(right).unwrap(), term);
    let proof = lifter.out.fiat(term, program.unions[0].rhs);
    let swap = Renaming::new([(0, 1), (1, 0)]).unwrap();
    let proof = lifter.out.reframe(proof, swap.clone());
    let oriented = lifter.orient(proof, left, right).unwrap();
    assert_eq!(lifter.out.edge(oriented).renaming, swap);
    let reflexive = lifter.orient(proof, left, left).unwrap();
    assert!(lifter.out.edge(reflexive).renaming.is_identity());
    let (mut store, proof) = lifter.out.finish(oriented);
    super::super::checker::check_proof_in_program(&mut store, &program, proof).unwrap();
}

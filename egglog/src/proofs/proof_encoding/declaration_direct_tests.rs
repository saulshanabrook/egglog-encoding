use std::panic::{AssertUnwindSafe, catch_unwind};

use super::*;
use crate::EGraph;
use crate::ast::{GenericActions, GenericFact, GenericRule, ResolvedNCommand};
use crate::proofs::generated_binder::{
    GeneratedBatch, GeneratedEntry, GeneratedVar, GeneratedVarRole, LocalId, PrimitiveKey,
    resolve_generated_batch,
};
use crate::typechecking::TypeError;

fn before_proofs(egraph: &mut EGraph, source: &str) -> Vec<ResolvedNCommand> {
    let mut resolved = Vec::new();
    for command in egraph
        .parse_program(Some("declaration-direct.egg".to_owned()), source)
        .unwrap()
    {
        resolved.extend(egraph.resolve_command_before_proofs(command).unwrap());
    }
    crate::remove_globals::remove_globals(resolved, &mut egraph.parser.symbol_gen)
}

fn planned_function(declaration: &PlannedDeclaration) -> &GeneratedFunctionDecl {
    let PlannedDeclarationKind::Function(function) = &declaration.kind else {
        panic!("expected planned function, got {:?}", declaration.kind)
    };
    function
}

fn function_key(function: &GeneratedFunctionDecl) -> &FunctionKey {
    let CallKey::Function(key) = &function.resolved_schema else {
        panic!("planned declaration did not carry a function key")
    };
    key
}

fn planned_names(group: &TypedHoistGroup) -> Vec<&str> {
    group
        .declarations
        .iter()
        .map(|declaration| match &declaration.kind {
            PlannedDeclarationKind::Sort(decl) => decl.key.name.as_str(),
            PlannedDeclarationKind::Function(decl) => decl.name.as_str(),
            PlannedDeclarationKind::Index(decl) => decl.name.as_str(),
            PlannedDeclarationKind::Ruleset(_, name) => name.as_str(),
            PlannedDeclarationKind::Rule(rule) => rule.name.as_str(),
        })
        .collect()
}

#[test]
fn headers_are_fully_typed_and_keep_source_order_and_metadata() {
    let mut egraph = EGraph::new_with_proofs();
    let instrumentor = ProofInstrumentor::new(&mut egraph);
    let span = crate::span!();
    let names = instrumentor.proof_names().clone();
    let mut catalog = GeneratedSignatureCatalog::default();

    let term = instrumentor.plan_term_header_direct(&mut catalog, &span);
    assert_eq!(
        planned_names(&term),
        [
            names.path_compress_ruleset_name.as_str(),
            names.rebuilding_ruleset_name.as_str(),
            names.rebuilding_cleanup_ruleset_name.as_str(),
            names.subsume_ruleset_name.as_str(),
        ]
    );
    let proof = instrumentor.plan_proof_header_direct(&mut catalog, &span);
    assert_eq!(
        planned_names(&proof),
        [
            names.proof_datatype.as_str(),
            names.rule_link_constructor.as_str(),
            names.merge_fn_idx_constructor.as_str(),
            names.merge_fn_row_constructor.as_str(),
            names.eq_trans_constructor.as_str(),
            names.eq_sym_constructor.as_str(),
            names.congr_constructor.as_str(),
            names.congr_all_constructor.as_str(),
            names.proj_constructor.as_str(),
            names.container_normalize_constructor.as_str(),
            names.eval_constructor.as_str(),
        ]
    );
    let PlannedDeclarationKind::Sort(proof_sort) = &proof.declarations[0].kind else {
        panic!("proof header must begin with its sort")
    };
    assert_eq!(proof_sort.key.class, SortSemanticClass::Eq);
    assert_eq!(
        proof_sort.proof_constructors,
        Some(ProofConstructorNames {
            congr: names.congr_constructor,
            congr_all: names.congr_all_constructor,
            trans: names.eq_trans_constructor,
            sym: names.eq_sym_constructor,
            normalize: names.container_normalize_constructor,
            fiat: names.fiat_prefix,
            proj: names.proj_constructor,
            proj_all: names.proj_all_prefix,
        })
    );
    for declaration in &proof.declarations[1..] {
        let function = planned_function(declaration);
        assert!(function.internal_hidden);
        assert!(function.internal_term_node);
        assert!(function.unextractable);
        assert!(!function.internal_let);
        assert!(function.term_constructor.is_none());
        assert!(function.merge.is_none());
        assert_eq!(function.schema.outputs, ["Unit"]);
        assert_eq!(function.span, span);
    }
}

#[test]
fn rule_arity_header_is_sorted_recursive_one_shot_state() {
    let mut egraph = EGraph::new_with_proofs();
    let program = before_proofs(
        &mut egraph,
        r#"
            (datatype A (A0) (A1 A))
            (rule () ((A0)) :name "zero")
            (fail (rule ((= x (A1 y))) ((union x y)) :name "nested"))
            (rule ((= x (A1 y))) ((union x y)) :name "duplicate-arity")
        "#,
    );
    let mut expected = Vec::new();
    fn collect(commands: &[ResolvedNCommand], expected: &mut Vec<usize>) {
        for command in commands {
            match command {
                ResolvedNCommand::NormRule { rule } => expected.push(
                    recomputable_premises(&rule.body, &|_| false)
                        .iter()
                        .filter(|value| !**value)
                        .count(),
                ),
                ResolvedNCommand::Fail(_, nested) => collect(nested, expected),
                _ => {}
            }
        }
    }
    collect(&program, &mut expected);
    expected.sort_unstable();
    expected.dedup();

    let mut instrumentor = ProofInstrumentor::new(&mut egraph);
    let mut catalog = GeneratedSignatureCatalog::default();
    let first = instrumentor.plan_rule_arity_header_direct(&mut catalog, &program);
    let actual = planned_names(&first)
        .into_iter()
        .map(|name| {
            instrumentor
                .proof_names()
                .fused_rule_arity(name)
                .expect("rule-arity declaration name")
        })
        .collect::<Vec<_>>();
    assert_eq!(actual, expected);
    assert!(first.declarations.iter().all(|declaration| {
        let function = planned_function(declaration);
        function.internal_hidden
            && function.internal_term_node
            && function.unextractable
            && function.merge.is_none()
    }));
    assert!(
        instrumentor
            .plan_rule_arity_header_direct(&mut catalog, &program)
            .declarations
            .is_empty()
    );
}

#[test]
fn pending_relations_are_typed_one_shot_and_subsumption_stays_adjacent() {
    let mut egraph = EGraph::new_with_proofs();
    let source = before_proofs(&mut egraph, "(sort E) (function f (E) E :merge old)");
    let function = source
        .iter()
        .find_map(|command| match command {
            ResolvedNCommand::Function(function) if function.name == "f" => {
                let ResolvedCall::Func(function) = &function.resolved_schema else {
                    unreachable!()
                };
                Some(function.clone())
            }
            _ => None,
        })
        .expect("source function f");
    let span = crate::span!();
    let mut instrumentor = ProofInstrumentor::new(&mut egraph);
    let mut catalog = GeneratedSignatureCatalog::default();
    let e = SortKey {
        name: "E".to_owned(),
        class: SortSemanticClass::Eq,
    };

    let (fiat_name, fiat) = instrumentor.plan_fiat_pending_direct(&span, e.clone());
    assert!(matches!(
        catalog.function_call(&fiat_name, &span),
        Err(crate::proofs::generated_binder::GeneratedBindError::MissingCatalogSignature {
            kind: "function",
            name,
            ..
        }) if name == fiat_name
    ));
    fiat.register_signatures(&mut catalog);
    assert!(catalog.function_call(&fiat_name, &span).is_ok());
    let fiat_decl = planned_function(&fiat.declarations[0]);
    assert!(fiat_decl.unextractable);
    assert_eq!(
        function_key(fiat_decl)
            .inputs
            .iter()
            .map(|sort| sort.name.as_str())
            .collect::<Vec<_>>(),
        ["E", "E", instrumentor.proof_names().proof_datatype.as_str()]
    );
    assert!(
        instrumentor
            .plan_fiat_pending_direct(&span, e.clone())
            .1
            .declarations
            .is_empty()
    );

    let (_, projection) = instrumentor.plan_projection_pending_direct(&span, e);
    projection.register_signatures(&mut catalog);
    assert_eq!(projection.declarations.len(), 1);
    assert!(planned_function(&projection.declarations[0]).unextractable);
    assert!(
        instrumentor
            .plan_projection_pending_direct(
                &span,
                SortKey {
                    name: "E".to_owned(),
                    class: SortSemanticClass::Eq,
                },
            )
            .1
            .declarations
            .is_empty()
    );

    let (_, packed) = instrumentor.plan_packed_pending_direct(&span, 3);
    packed.register_signatures(&mut catalog);
    let packed_decl = planned_function(&packed.declarations[0]);
    assert!(packed_decl.unextractable);
    assert_eq!(function_key(packed_decl).inputs.len(), 5);
    assert!(
        instrumentor
            .plan_packed_pending_direct(&span, 3)
            .1
            .declarations
            .is_empty()
    );

    let empty_rule = GenericRule {
        span: span.clone(),
        body: vec![],
        head: GenericActions(vec![]),
        name: "subsumption-apply".to_owned(),
        ruleset: instrumentor.proof_names().subsume_ruleset_name.clone(),
        eval_mode: RuleEvalMode::Seminaive,
        no_decomp: false,
        include_subsumed: false,
    };
    let group = instrumentor.plan_subsumption_pending_direct(
        &span,
        &function,
        "marker".to_owned(),
        vec![empty_rule],
    );
    group.register_signatures(&mut catalog);
    assert_eq!(planned_names(&group), ["marker", "subsumption-apply"]);
    let marker = planned_function(&group.declarations[0]);
    assert!(marker.internal_hidden);
    assert!(marker.unextractable);
    assert!(!marker.internal_term_node);
    assert!(matches!(
        group.declarations[1].kind,
        PlannedDeclarationKind::Rule(_)
    ));
    assert!(
        instrumentor
            .plan_subsumption_pending_direct(&span, &function, "marker".to_owned(), vec![],)
            .declarations
            .is_empty()
    );
}

#[test]
fn path_compression_checked_builder_pins_full_proof_and_term_structures() {
    let mut egraph = EGraph::new_with_proofs();
    let instrumentor = ProofInstrumentor::new(&mut egraph);
    let span = crate::span!();
    let e = SortKey {
        name: "E".to_owned(),
        class: SortSemanticClass::Eq,
    };
    let proof = SortKey {
        name: instrumentor.proof_names().proof_datatype.clone(),
        class: SortSemanticClass::Eq,
    };
    let proof_values = CallKey::Values(vec![e.clone(), proof.clone()]);
    let proof_uf = FunctionKey {
        name: "UF-E-proof".to_owned(),
        subtype: FunctionSubtype::Custom,
        inputs: vec![e.clone()],
        output: ValueShape::Tuple(vec![e.clone(), proof.clone()]),
    };
    let mut catalog = GeneratedSignatureCatalog::default();
    let rule = instrumentor.path_compression_rule_direct(
        &mut catalog,
        &span,
        e.clone(),
        proof.clone(),
        proof_uf.clone(),
        "compress-proof".to_owned(),
        "compress-rules".to_owned(),
        "a".to_owned(),
        "b".to_owned(),
        "c".to_owned(),
        "pb".to_owned(),
        "pc".to_owned(),
        Some("compressed".to_owned()),
    );
    let local = |id, name: &str, sort: &SortKey| GeneratedVar {
        id: LocalId(id),
        name: name.to_owned(),
        sort: sort.clone(),
        role: GeneratedVarRole::Local,
    };
    let b = local(0, "b", &e);
    let pb = local(1, "pb", &proof);
    let a = local(2, "a", &e);
    let c = local(3, "c", &e);
    let pc = local(4, "pc", &proof);
    let compressed = local(5, "compressed", &proof);
    let var = |variable: &GeneratedVar| GenericExpr::Var(span.clone(), variable.clone());
    let unequal = CallKey::Primitive(PrimitiveKey {
        name: "!=".to_owned(),
        inputs: vec![e.clone(), e.clone()],
        output: SortKey {
            name: "Unit".to_owned(),
            class: SortSemanticClass::Value,
        },
    });
    let trans = CallKey::Primitive(PrimitiveKey {
        name: crate::proofs::proof_fresh::mint_prim_name(
            &instrumentor.proof_names().eq_trans_constructor,
        ),
        inputs: vec![proof.clone(), proof.clone()],
        output: proof.clone(),
    });
    assert_eq!(
        rule,
        GenericRule {
            span: span.clone(),
            body: vec![
                GenericFact::Eq(
                    span.clone(),
                    GenericExpr::Call(span.clone(), proof_values.clone(), vec![var(&b), var(&pb)],),
                    GenericExpr::Call(
                        span.clone(),
                        CallKey::Function(proof_uf.clone()),
                        vec![var(&a)],
                    ),
                ),
                GenericFact::Eq(
                    span.clone(),
                    GenericExpr::Call(span.clone(), proof_values.clone(), vec![var(&c), var(&pc)],),
                    GenericExpr::Call(
                        span.clone(),
                        CallKey::Function(proof_uf.clone()),
                        vec![var(&b)],
                    ),
                ),
                GenericFact::Fact(GenericExpr::Call(
                    span.clone(),
                    unequal.clone(),
                    vec![var(&b), var(&c)],
                )),
            ],
            head: GenericActions(vec![
                GenericAction::Let(
                    span.clone(),
                    compressed.clone(),
                    GenericExpr::Call(span.clone(), trans, vec![var(&pb), var(&pc)],),
                ),
                GenericAction::Set(
                    span.clone(),
                    CallKey::Function(proof_uf.clone()),
                    vec![var(&a)],
                    GenericExpr::Call(span.clone(), proof_values, vec![var(&c), var(&compressed)],),
                ),
            ]),
            name: "compress-proof".to_owned(),
            ruleset: "compress-rules".to_owned(),
            eval_mode: RuleEvalMode::Seminaive,
            no_decomp: false,
            include_subsumed: false,
        }
    );

    let unit = SortKey {
        name: "Unit".to_owned(),
        class: SortSemanticClass::Value,
    };
    let term_values = CallKey::Values(vec![e.clone(), unit.clone()]);
    let term_uf = FunctionKey {
        name: "UF-E-term".to_owned(),
        subtype: FunctionSubtype::Custom,
        inputs: vec![e.clone()],
        output: ValueShape::Tuple(vec![e.clone(), unit.clone()]),
    };
    drop(instrumentor);
    let mut term_egraph = EGraph::new_with_term_encoding();
    let term_instrumentor = ProofInstrumentor::new(&mut term_egraph);
    let mut catalog = GeneratedSignatureCatalog::default();
    let rule = term_instrumentor.path_compression_rule_direct(
        &mut catalog,
        &span,
        e.clone(),
        unit.clone(),
        term_uf.clone(),
        "compress-term".to_owned(),
        "compress-rules".to_owned(),
        "a".to_owned(),
        "b".to_owned(),
        "c".to_owned(),
        "pb".to_owned(),
        "pc".to_owned(),
        None,
    );
    let b = local(0, "b", &e);
    let pb = local(1, "pb", &unit);
    let a = local(2, "a", &e);
    let c = local(3, "c", &e);
    let pc = local(4, "pc", &unit);
    assert_eq!(
        rule,
        GenericRule {
            span: span.clone(),
            body: vec![
                GenericFact::Eq(
                    span.clone(),
                    GenericExpr::Call(span.clone(), term_values.clone(), vec![var(&b), var(&pb)],),
                    GenericExpr::Call(
                        span.clone(),
                        CallKey::Function(term_uf.clone()),
                        vec![var(&a)],
                    ),
                ),
                GenericFact::Eq(
                    span.clone(),
                    GenericExpr::Call(span.clone(), term_values.clone(), vec![var(&c), var(&pc)],),
                    GenericExpr::Call(
                        span.clone(),
                        CallKey::Function(term_uf.clone()),
                        vec![var(&b)],
                    ),
                ),
                GenericFact::Fact(GenericExpr::Call(
                    span.clone(),
                    unequal,
                    vec![var(&b), var(&c)],
                )),
            ],
            head: GenericActions(vec![GenericAction::Set(
                span.clone(),
                CallKey::Function(term_uf),
                vec![var(&a)],
                GenericExpr::Call(
                    span.clone(),
                    term_values,
                    vec![var(&c), GenericExpr::Lit(span.clone(), Literal::Unit)],
                ),
            )]),
            name: "compress-term".to_owned(),
            ruleset: "compress-rules".to_owned(),
            eval_mode: RuleEvalMode::Seminaive,
            no_decomp: false,
            include_subsumed: false,
        }
    );
}

#[test]
fn path_compression_rejects_proof_mode_and_carried_sort_drift() {
    let span = crate::span!();
    let e = SortKey {
        name: "E".to_owned(),
        class: SortSemanticClass::Eq,
    };
    let unit = SortKey {
        name: "Unit".to_owned(),
        class: SortSemanticClass::Value,
    };
    let uf = |carried: &SortKey| FunctionKey {
        name: "UF-E".to_owned(),
        subtype: FunctionSubtype::Custom,
        inputs: vec![e.clone()],
        output: ValueShape::Tuple(vec![e.clone(), carried.clone()]),
    };
    let rejected =
        |instrumentor: &ProofInstrumentor<'_>, carried: SortKey, compressed: Option<String>| {
            let mut catalog = GeneratedSignatureCatalog::default();
            let panic = catch_unwind(AssertUnwindSafe(|| {
                instrumentor.path_compression_rule_direct(
                    &mut catalog,
                    &span,
                    e.clone(),
                    carried.clone(),
                    uf(&carried),
                    "compress".to_owned(),
                    "rules".to_owned(),
                    "a".to_owned(),
                    "b".to_owned(),
                    "c".to_owned(),
                    "pb".to_owned(),
                    "pc".to_owned(),
                    compressed,
                )
            }))
            .expect_err("incoherent path compression plan must panic");
            panic
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| {
                    panic
                        .downcast_ref::<&str>()
                        .map(|message| (*message).to_owned())
                })
                .expect("path compression panic must contain text")
        };

    let mut proof_egraph = EGraph::new_with_proofs();
    let proof_instrumentor = ProofInstrumentor::new(&mut proof_egraph);
    let proof = SortKey {
        name: proof_instrumentor.proof_names().proof_datatype.clone(),
        class: SortSemanticClass::Eq,
    };
    let message = rejected(&proof_instrumentor, unit.clone(), Some("proof".to_owned()));
    assert!(message.contains("proof-mode coherence"));
    let message = rejected(&proof_instrumentor, proof, None);
    assert!(message.contains("proof-mode coherence"));
    drop(proof_instrumentor);

    let mut term_egraph = EGraph::new_with_term_encoding();
    let term_instrumentor = ProofInstrumentor::new(&mut term_egraph);
    let message = rejected(&term_instrumentor, unit, Some("proof".to_owned()));
    assert!(message.contains("proof-mode coherence"));
    assert!(message.contains(&span.to_string()));
}

#[test]
fn source_sorts_preserve_portable_presorts_state_and_name_order() {
    let mut egraph = EGraph::new_with_proofs();
    let source = before_proofs(
        &mut egraph,
        "(sort E) (sort EV (Vec E)) (sort EF (UnstableFn (E) E))",
    );
    let sorts = source
        .iter()
        .filter_map(|command| match command {
            ResolvedNCommand::Sort {
                span,
                name,
                presort_and_args,
                unionable,
                ..
            } => Some((
                span.clone(),
                name.clone(),
                presort_and_args.clone(),
                *unionable,
            )),
            _ => None,
        })
        .collect::<Vec<_>>();
    let mut instrumentor = ProofInstrumentor::new(&mut egraph);
    let mut catalog = GeneratedSignatureCatalog::default();

    let expected_before = instrumentor.egraph.parser.symbol_gen.clone();
    let regular = instrumentor.plan_source_sort_direct(
        &mut catalog,
        &sorts[0].0,
        &sorts[0].1,
        &sorts[0].2,
        sorts[0].3,
    );
    assert!(matches!(
        regular.declarations[0].kind,
        PlannedDeclarationKind::Sort(_)
    ));
    assert!(matches!(
        regular.declarations.last().unwrap().kind,
        PlannedDeclarationKind::Rule(_)
    ));
    assert!(regular.declarations.iter().any(|declaration| {
        matches!(&declaration.kind, PlannedDeclarationKind::Function(function)
            if function.name == instrumentor.egraph.proof_state.uf_parent["E"])
    }));

    let mut expected = expected_before;
    let _: String = expected.fresh("UF_E");
    let _: String = expected.fresh("uf_path_compress");
    let _: String = expected.fresh("uf_a");
    let _: String = expected.fresh("uf_b");
    let _: String = expected.fresh("uf_c");
    let _: String = expected.fresh("uf_pb");
    let _: String = expected.fresh("uf_pc");
    let _: String = expected.fresh("pv");
    let _: String = expected.fresh("pv");
    assert_eq!(instrumentor.egraph.parser.symbol_gen, expected);

    let vec_plan = instrumentor.plan_source_sort_direct(
        &mut catalog,
        &sorts[1].0,
        &sorts[1].1,
        &sorts[1].2,
        sorts[1].3,
    );
    let PlannedDeclarationKind::Sort(vec_sort) = &vec_plan.declarations[0].kind else {
        panic!("container plan must begin with its source sort")
    };
    assert_eq!(vec_sort.key.class, SortSemanticClass::EqContainer);
    let presort = vec_sort.presort.as_ref().expect("portable Vec presort");
    assert_eq!(presort.name, "Vec");
    assert_eq!(
        presort.args.as_slice(),
        [GeneratedPresortArg::Sort(SortKey {
            name: "E".to_owned(),
            class: SortSemanticClass::Eq,
        })]
    );
    assert!(vec_sort.container_rebuild.is_some());
    assert!(vec_sort.uf.is_none());
    assert_eq!(vec_plan.declarations.len(), 2);
    assert!(matches!(
        vec_plan.declarations[1].kind,
        PlannedDeclarationKind::Function(_)
    ));
    assert!(
        instrumentor
            .egraph
            .proof_state
            .container_rebuild_name
            .contains_key("EV")
    );
    assert!(
        instrumentor
            .egraph
            .proof_state
            .container_rebuild_proof_name
            .contains_key("EV")
    );

    let fn_plan = instrumentor.plan_source_sort_direct(
        &mut catalog,
        &sorts[2].0,
        &sorts[2].1,
        &sorts[2].2,
        sorts[2].3,
    );
    let PlannedDeclarationKind::Sort(fn_sort) = &fn_plan.declarations[0].kind else {
        unreachable!()
    };
    let presort = fn_sort
        .presort
        .as_ref()
        .expect("portable UnstableFn presort");
    assert_eq!(presort.name, "UnstableFn");
    assert!(matches!(
        presort.args.as_slice(),
        [GeneratedPresortArg::SortList(inputs), GeneratedPresortArg::Sort(output)]
            if inputs.iter().map(|sort| sort.name.as_str()).collect::<Vec<_>>() == ["E"]
                && output.name == "E"
    ));
}

#[test]
fn term_view_and_indexes_preserve_unused_fresh_grouping_exclusion_and_metadata() {
    let mut egraph = EGraph::new_with_proofs();
    let source = before_proofs(
        &mut egraph,
        r#"
            (sort E)
            (sort EV (Vec E))
            (function F (E E EV i64) i64 :no-merge :unextractable :internal-cost 7)
            (constructor C (E EV E) E :cost 9)
        "#,
    );
    let functions = source
        .iter()
        .filter_map(|command| match command {
            ResolvedNCommand::Function(function) => Some(function.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    let f = functions
        .iter()
        .find(|function| function.name == "F")
        .unwrap();
    let c = functions
        .iter()
        .find(|function| function.name == "C")
        .unwrap();
    let mut instrumentor = ProofInstrumentor::new(&mut egraph);
    let mut catalog = GeneratedSignatureCatalog::default();
    let mut overlay = EncodedFunctionPlanningOverlay::default();

    let before_f = instrumentor.egraph.parser.symbol_gen.clone();
    let (f_plan, f_layout) =
        instrumentor.plan_term_and_view_direct(&mut catalog, &mut overlay, &f.span, f);
    let mut expected_f = before_f;
    let expected_view: String = expected_f.fresh("FView");
    let expected_term_sort: String = expected_f.fresh("view");
    let expected_index: String = expected_f.fresh("FOcc_E");
    assert_eq!(instrumentor.egraph.parser.symbol_gen, expected_f);
    assert_eq!(f_layout.view.name, expected_view);
    assert_eq!(f_layout.term_eclass_sort.name, expected_term_sort);
    assert!(!f_layout.output_is_eclass);
    assert_eq!(f_layout.indexes.len(), 1);
    assert_eq!(f_layout.indexes[0].name, expected_index);
    assert_eq!(f_layout.indexes[0].any_of, [0, 1]);
    assert_eq!(overlay.staged.by_source["F"], f_layout);
    assert_eq!(
        planned_names(&f_plan),
        [
            f_layout.term_eclass_sort.name.as_str(),
            "F",
            f_layout.view.name.as_str(),
            f_layout.indexes[0].name.as_str(),
        ]
    );
    assert_eq!(
        f_plan
            .declarations
            .iter()
            .enumerate()
            .filter_map(|(index, declaration)| declaration.layout_commit.as_ref().map(|_| index))
            .collect::<Vec<_>>(),
        [2],
        "only the successfully registered view publishes the encoded layout"
    );
    let view_decl = planned_function(&f_plan.declarations[2]);
    assert_eq!(view_decl.cost, Some(7));
    assert!(view_decl.unextractable);
    assert_eq!(view_decl.term_constructor.as_deref(), Some("F"));
    assert_eq!(view_decl.identity_vals, Some(1));
    assert!(!view_decl.internal_term_node);
    let term_decl = planned_function(&f_plan.declarations[1]);
    assert!(term_decl.internal_hidden);
    assert!(term_decl.internal_term_node);
    assert!(term_decl.unextractable);
    assert_eq!(function_key(term_decl).inputs.len(), 6);

    let before_c = instrumentor.egraph.parser.symbol_gen.clone();
    let (c_plan, c_layout) =
        instrumentor.plan_term_and_view_direct(&mut catalog, &mut overlay, &c.span, c);
    let mut expected_c = before_c;
    let expected_c_view: String = expected_c.fresh("CView");
    let _: String = expected_c.fresh("view");
    let expected_c_index: String = expected_c.fresh("COcc_E");
    let _: String = expected_c.fresh("UF_E");
    let _: String = expected_c.fresh("pv");
    assert_eq!(instrumentor.egraph.parser.symbol_gen, expected_c);
    assert_eq!(c_layout.view.name, expected_c_view);
    assert!(c_layout.output_is_eclass);
    assert_eq!(c_layout.term_eclass_sort.name, "E");
    assert_eq!(c_layout.indexes[0].name, expected_c_index);
    assert_eq!(c_layout.indexes[0].any_of, [0, 2, 3]);
    assert_eq!(overlay.staged.by_source["C"], c_layout);
    let congruence_packed = c_plan
        .declarations
        .iter()
        .enumerate()
        .find_map(|(index, declaration)| match &declaration.kind {
            PlannedDeclarationKind::Function(function) => instrumentor
                .proof_names()
                .packed_proof_columns(&function.name)
                .map(|columns| (index, function.name.as_str(), columns)),
            _ => None,
        })
        .expect("constructor congruence merge must claim Packed_2");
    assert_eq!(congruence_packed.0, 1);
    assert_eq!(congruence_packed.2, 2);
    assert_eq!(
        planned_names(&c_plan),
        [
            "C",
            congruence_packed.1,
            c_layout.view.name.as_str(),
            c_layout.indexes[0].name.as_str(),
        ],
        "congruence Packed stays inline after the term relation"
    );
    assert_eq!(
        instrumentor.egraph.proof_state.proof_names.fn_to_term_sort["C"],
        "E"
    );
    assert_eq!(
        instrumentor.egraph.proof_state.view_index["C"][0].sort_name,
        "E"
    );
    assert!(c_plan.declarations.iter().any(|declaration| {
        matches!(&declaration.kind, PlannedDeclarationKind::Function(function)
            if function.name == c_layout.view.name && function.cost == Some(9))
    }));
}

#[test]
fn encoded_global_is_a_nullary_constructor_view_with_internal_let_metadata() {
    let mut egraph = EGraph::new_with_proofs();
    let source = before_proofs(&mut egraph, "(sort E) (constructor Z () E) (let G (Z))");
    let functions = source
        .iter()
        .filter_map(|command| match command {
            ResolvedNCommand::Function(function) => Some(function.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    let z = functions
        .iter()
        .find(|function| function.name == "Z")
        .unwrap();
    let global = functions
        .iter()
        .find(|function| function.name == "G")
        .unwrap();
    assert!(global.internal_let);
    assert_eq!(global.subtype, FunctionSubtype::Custom);

    let mut instrumentor = ProofInstrumentor::new(&mut egraph);
    let mut catalog = GeneratedSignatureCatalog::default();
    let mut overlay = EncodedFunctionPlanningOverlay::default();
    instrumentor.plan_term_and_view_direct(&mut catalog, &mut overlay, &z.span, z);
    let before = instrumentor.egraph.parser.symbol_gen.clone();
    let (plan, layout) =
        instrumentor.plan_term_and_view_direct(&mut catalog, &mut overlay, &global.span, global);

    assert!(layout.output_is_eclass);
    assert_eq!(layout.term_eclass_sort.name, "E");
    assert_eq!(
        layout.term.inputs.as_slice(),
        std::slice::from_ref(&layout.term_eclass_sort)
    );
    assert!(layout.view.inputs.is_empty());
    assert_eq!(layout.indexes.len(), 1);
    assert_eq!(layout.indexes[0].any_of, [0]);
    assert_eq!(
        planned_names(&plan),
        [
            "G",
            layout.view.name.as_str(),
            layout.indexes[0].name.as_str(),
        ]
    );
    let term = planned_function(&plan.declarations[0]);
    assert!(term.internal_hidden);
    assert!(term.internal_term_node);
    assert!(!term.internal_let);
    let view = planned_function(&plan.declarations[1]);
    assert!(view.internal_let);
    assert!(view.unextractable);
    assert!(!view.internal_hidden);
    assert_eq!(view.term_constructor.as_deref(), Some("G"));
    assert_eq!(view.identity_vals, Some(1));
    assert!(view.merge.is_some());
    assert!(plan.declarations[1].layout_commit.is_some());

    let mut expected = before;
    let expected_view: String = expected.fresh("GView");
    let _: String = expected.fresh("view");
    let expected_index: String = expected.fresh("GOcc_E");
    let _: String = expected.fresh("pv");
    assert_eq!(layout.view.name, expected_view);
    assert_eq!(layout.indexes[0].name, expected_index);
    assert_eq!(instrumentor.egraph.parser.symbol_gen, expected);
}

#[test]
fn custom_merge_is_typed_postorder_with_packed_hoist_and_exact_freshness() {
    let mut egraph = EGraph::new_with_proofs();
    let source = before_proofs(
        &mut egraph,
        r#"
            (sort E)
            (sort EV (Vec E))
            (constructor K (E) E)
            (function F (E EV i64) E :merge (K (K (K old))))
        "#,
    );
    let functions = source
        .iter()
        .filter_map(|command| match command {
            ResolvedNCommand::Function(function) => Some(function.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    let k = functions
        .iter()
        .find(|function| function.name == "K")
        .unwrap();
    let f = functions
        .iter()
        .find(|function| function.name == "F")
        .unwrap();
    let mut instrumentor = ProofInstrumentor::new(&mut egraph);
    let mut catalog = GeneratedSignatureCatalog::default();
    let mut overlay = EncodedFunctionPlanningOverlay::default();

    // K establishes the exact term/view roles consumed recursively by F's
    // custom merge and claims the ubiquitous two-column packed constructor.
    let (_, k_layout) =
        instrumentor.plan_term_and_view_direct(&mut catalog, &mut overlay, &k.span, k);
    let before_f = instrumentor.egraph.parser.symbol_gen.clone();
    let (f_plan, f_layout) =
        instrumentor.plan_term_and_view_direct(&mut catalog, &mut overlay, &f.span, f);

    let packed = f_plan
        .declarations
        .iter()
        .enumerate()
        .filter_map(|(index, declaration)| match &declaration.kind {
            PlannedDeclarationKind::Function(function) => instrumentor
                .proof_names()
                .packed_proof_columns(&function.name)
                .map(|columns| (index, function.name.clone(), columns)),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(packed.len(), 1);
    assert_eq!(
        packed[0].0, 0,
        "a custom-merge Packed declaration must use the source-command hoist"
    );
    assert_eq!(packed[0].2, 3);
    assert_eq!(f_layout.indexes.len(), 1);
    assert_eq!(f_layout.indexes[0].any_of, [0]);
    assert_eq!(
        planned_names(&f_plan),
        [
            packed[0].1.as_str(),
            f_layout.term_eclass_sort.name.as_str(),
            "F",
            f_layout.view.name.as_str(),
            f_layout.indexes[0].name.as_str(),
        ],
        "custom pending declarations precede the term prefix; non-E columns stay out of the index"
    );
    assert!(f_plan.declarations[3].layout_commit.is_some());
    assert!(
        f_plan
            .declarations
            .iter()
            .enumerate()
            .all(|(index, declaration)| { index == 3 || declaration.layout_commit.is_none() })
    );

    let view = planned_function(&f_plan.declarations[3]);
    let merge = view.merge.as_ref().expect("typed custom FD merge");
    let mint_idx = crate::proofs::proof_fresh::mint_prim_name(
        &instrumentor.proof_names().merge_fn_idx_constructor,
    );
    let mint_row = crate::proofs::proof_fresh::mint_prim_name(
        &instrumentor.proof_names().merge_fn_row_constructor,
    );
    let indexes = merge
        .actions
        .0
        .iter()
        .filter_map(|action| match action {
            GenericAction::Let(_, _, GenericExpr::Call(_, CallKey::Primitive(primitive), args))
                if primitive.name == mint_idx =>
            {
                match &args[3] {
                    GenericExpr::Lit(_, Literal::Int(index)) => Some(*index),
                    other => panic!("MergeIdx index was not an integer: {other:?}"),
                }
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        indexes,
        [2, 1, 0],
        "merge nodes are numbered preorder but emitted after their children"
    );
    let set_if_empty = crate::proofs::proof_fresh::set_if_empty_prim_name(&k_layout.view.name);
    let view_proof = crate::proofs::proof_fresh::view_proof_prim_name(&k_layout.view.name);
    let k_view_primitives = merge
        .actions
        .0
        .iter()
        .filter_map(|action| {
            let GenericAction::Let(_, _, GenericExpr::Call(_, CallKey::Primitive(primitive), _)) =
                action
            else {
                return None;
            };
            (primitive.name == set_if_empty || primitive.name == view_proof)
                .then_some(primitive.name.as_str())
        })
        .collect::<Vec<_>>();
    assert_eq!(
        k_view_primitives
            .iter()
            .filter(|name| **name == set_if_empty)
            .count(),
        3,
        "each constructor level seeds or reuses its canonical KView row"
    );
    assert_eq!(
        k_view_primitives
            .iter()
            .filter(|name| **name == view_proof)
            .count(),
        3,
        "each constructor level reads the proof stored with its KView row"
    );
    assert!(matches!(
        merge.actions.0.last(),
        Some(GenericAction::Let(
            _,
            _,
            GenericExpr::Call(_, CallKey::Primitive(primitive), _)
        )) if primitive.name == mint_row
    ));
    let GenericExpr::Call(_, CallKey::Values(_), result) = &merge.result else {
        panic!("custom merge must return a value/proof tuple")
    };
    let GenericExpr::Call(_, CallKey::Primitive(outer), outer_args) = &result[1] else {
        panic!("custom merge proof must select the stable old row")
    };
    assert_eq!(outer.name, "select-eq");
    assert!(matches!(
        &outer_args[3],
        GenericExpr::Call(_, CallKey::Primitive(inner), _) if inner.name == "select-eq"
    ));

    let mut expected = before_f;
    let expected_view: String = expected.fresh("FView");
    let expected_term_sort: String = expected.fresh("view");
    let expected_index: String = expected.fresh("FOcc_E");
    for _ in 0..27 {
        let _: String = expected.fresh("pv");
    }
    assert_eq!(f_layout.view.name, expected_view);
    assert_eq!(f_layout.term_eclass_sort.name, expected_term_sort);
    assert_eq!(f_layout.indexes[0].name, expected_index);
    assert_eq!(instrumentor.egraph.parser.symbol_gen, expected);
}

#[test]
fn custom_merge_preserves_global_old_and_renames_only_local_new() {
    let mut egraph = EGraph::new_with_term_encoding();
    let mut source = Vec::new();
    for command in egraph
        .parse_program(
            Some("custom-merge-variable-roles.egg".to_owned()),
            r#"
                (datatype RoleE (RoleA) (RoleB) (RolePick RoleE RoleE))
                (let old (RoleA))
                (function role-score (i64) RoleE :merge (RolePick old new))
            "#,
        )
        .unwrap()
    {
        source.extend(egraph.resolve_command_before_proofs(command).unwrap());
    }
    let function = source
        .iter()
        .find_map(|command| match command {
            ResolvedNCommand::Function(function) if function.name == "role-score" => {
                Some(function.clone())
            }
            _ => None,
        })
        .expect("source function must be resolved before global removal");
    let source_merge = function.merge.as_ref().expect("source custom merge");
    let GenericExpr::Call(_, ResolvedCall::Func(source_head), source_args) = &source_merge.result
    else {
        panic!("expected the source RolePick constructor")
    };
    assert_eq!(source_head.name, "RolePick");
    assert!(matches!(
        &source_args[..],
        [
            GenericExpr::Var(_, crate::ResolvedVar { name: old, is_global_ref: true, .. }),
            GenericExpr::Var(_, crate::ResolvedVar { name: new, is_global_ref: false, .. })
        ] if old == "old" && new == "new"
    ));
    let mut removal_symbols = egraph.parser.symbol_gen.clone();
    let removed = crate::remove_globals::remove_globals(source.clone(), &mut removal_symbols);
    let global = removed
        .iter()
        .find_map(|command| match command {
            ResolvedNCommand::Function(function) if function.name == "old" => {
                Some(function.clone())
            }
            _ => None,
        })
        .expect("global removal must materialize the encoded old declaration");

    let mut instrumentor = ProofInstrumentor::new(&mut egraph);
    let mut catalog = GeneratedSignatureCatalog::default();
    let mut overlay = EncodedFunctionPlanningOverlay::default();
    for prerequisite in source.iter().filter_map(|command| match command {
        ResolvedNCommand::Function(function) if function.name != "role-score" => Some(function),
        _ => None,
    }) {
        instrumentor.plan_term_and_view_direct(
            &mut catalog,
            &mut overlay,
            &prerequisite.span,
            prerequisite,
        );
    }
    instrumentor.plan_term_and_view_direct(&mut catalog, &mut overlay, &global.span, &global);
    let before_role_score = instrumentor.egraph.parser.symbol_gen.clone();
    let (plan, layout) = instrumentor.plan_term_and_view_direct(
        &mut catalog,
        &mut overlay,
        &function.span,
        &function,
    );
    let view = plan
        .declarations
        .iter()
        .find_map(|declaration| {
            let PlannedDeclarationKind::Function(function) = &declaration.kind else {
                return None;
            };
            (function.name == layout.view.name).then_some(function)
        })
        .expect("custom FD view declaration");
    let merge = view.merge.as_ref().expect("typed custom FD merge");
    let mut observed_variables = Vec::new();
    let mut observed_functions = Vec::new();
    let mut observed_primitives = Vec::new();
    let mut observe = |expr: GeneratedExpr| {
        match &expr {
            GenericExpr::Var(_, variable) => {
                observed_variables.push((variable.name.clone(), variable.role));
            }
            GenericExpr::Call(_, CallKey::Function(function), _) => {
                observed_functions.push(function.name.clone());
            }
            GenericExpr::Call(_, CallKey::Primitive(primitive), _) => {
                observed_primitives.push(primitive.name.clone());
            }
            GenericExpr::Call(_, CallKey::Values(_), _) | GenericExpr::Lit(..) => {}
        }
        expr
    };
    for action in &merge.actions.0 {
        action.clone().visit_exprs(&mut observe);
    }
    merge.result.clone().visit_exprs(&mut observe);
    let old_view = instrumentor.proof_names().view_name["old"].clone();
    let old_read = crate::proofs::proof_fresh::set_if_empty_prim_name(&old_view);
    assert_eq!(
        observed_primitives
            .iter()
            .filter(|name| name.as_str() == crate::proofs::proof_fresh::GET_FRESH_PRIM_NAME)
            .count(),
        1,
        "the term-mode global view read has one unconstrained term fallback"
    );
    assert_eq!(
        observed_primitives
            .iter()
            .filter(|name| **name == old_read)
            .count(),
        1,
        "the source global must be read through its encoded zero-input view"
    );
    assert!(!observed_functions.iter().any(|name| name == "old"));
    assert!(
        !observed_variables
            .iter()
            .any(|(name, role)| name == "old" && *role == GeneratedVarRole::Global)
    );
    assert!(observed_variables.contains(&("new0".to_owned(), GeneratedVarRole::Local)));
    assert!(!observed_variables.contains(&("old0".to_owned(), GeneratedVarRole::Local)));

    let mut expected = before_role_score;
    let expected_view: String = expected.fresh("role-scoreView");
    let expected_term_sort: String = expected.fresh("view");
    for _ in 0..4 {
        let _: String = expected.fresh("pv");
    }
    assert_eq!(layout.view.name, expected_view);
    assert_eq!(layout.term_eclass_sort.name, expected_term_sort);
    assert_eq!(instrumentor.egraph.parser.symbol_gen, expected);
}

#[test]
fn custom_merge_global_view_read_has_exact_proof_fallback_order_and_freshness() {
    let mut egraph = EGraph::new_with_proofs();
    let mut source = Vec::new();
    for command in egraph
        .parse_program(
            Some("custom-merge-global-proof-read.egg".to_owned()),
            r#"
                (datatype RoleE (RoleA) (RoleB) (RolePick RoleE RoleE))
                (let old (RoleA))
                (function role-score (i64) RoleE :merge (RolePick old new))
            "#,
        )
        .unwrap()
    {
        source.extend(egraph.resolve_command_before_proofs(command).unwrap());
    }
    let mut removal_symbols = egraph.parser.symbol_gen.clone();
    let removed = crate::remove_globals::remove_globals(source, &mut removal_symbols);
    let function = removed
        .iter()
        .find_map(|command| match command {
            ResolvedNCommand::Function(function) if function.name == "role-score" => {
                Some(function.clone())
            }
            _ => None,
        })
        .expect("removed source custom function");

    let mut instrumentor = ProofInstrumentor::new(&mut egraph);
    let mut catalog = GeneratedSignatureCatalog::default();
    let mut overlay = EncodedFunctionPlanningOverlay::default();
    for prerequisite in removed.iter().filter_map(|command| match command {
        ResolvedNCommand::Function(function) if function.name != "role-score" => Some(function),
        _ => None,
    }) {
        instrumentor.plan_term_and_view_direct(
            &mut catalog,
            &mut overlay,
            &prerequisite.span,
            prerequisite,
        );
    }
    let before_role_score = instrumentor.egraph.parser.symbol_gen.clone();
    let (plan, layout) = instrumentor.plan_term_and_view_direct(
        &mut catalog,
        &mut overlay,
        &function.span,
        &function,
    );
    let view = plan
        .declarations
        .iter()
        .find_map(|declaration| {
            let PlannedDeclarationKind::Function(function) = &declaration.kind else {
                return None;
            };
            (function.name == layout.view.name).then_some(function)
        })
        .expect("custom FD view declaration");
    let merge = view.merge.as_ref().expect("typed custom FD merge");
    let [
        GenericAction::Let(
            _,
            term_fallback,
            GenericExpr::Call(_, CallKey::Primitive(term_get), term_args),
        ),
        GenericAction::Let(
            _,
            proof_fallback,
            GenericExpr::Call(_, CallKey::Primitive(proof_get), proof_args),
        ),
        GenericAction::Let(_, value, GenericExpr::Call(_, CallKey::Primitive(read), read_args)),
        ..,
    ] = &merge.actions.0[..]
    else {
        panic!("proof-mode global read must lead with its two fallbacks and view lookup")
    };
    assert_eq!(
        term_get.name,
        crate::proofs::proof_fresh::GET_FRESH_PRIM_NAME
    );
    assert_eq!(
        proof_get.name,
        crate::proofs::proof_fresh::GET_FRESH_PRIM_NAME
    );
    assert_eq!(
        term_args,
        &[GenericExpr::Lit(
            function.span.clone(),
            Literal::String("RoleE".to_owned())
        )]
    );
    assert_eq!(
        proof_args,
        &[GenericExpr::Lit(
            function.span.clone(),
            Literal::String(instrumentor.proof_names().proof_datatype.clone())
        )]
    );
    let old_view = instrumentor.proof_names().view_name["old"].clone();
    assert_eq!(
        read.name,
        crate::proofs::proof_fresh::set_if_empty_prim_name(&old_view)
    );
    assert_eq!(
        read_args,
        &[
            GenericExpr::Var(function.span.clone(), term_fallback.clone()),
            GenericExpr::Var(function.span.clone(), proof_fallback.clone()),
        ]
    );
    for variable in [term_fallback, proof_fallback, value] {
        assert_eq!(variable.role, GeneratedVarRole::Local);
    }

    let forbidden = [
        crate::proofs::proof_fresh::mint_prim_name("old"),
        crate::proofs::proof_fresh::view_proof_prim_name(&old_view),
    ];
    let mut forbidden_calls = Vec::new();
    let mut observe = |expr: GeneratedExpr| {
        if let GenericExpr::Call(_, CallKey::Primitive(primitive), _) = &expr
            && forbidden.contains(&primitive.name)
        {
            forbidden_calls.push(primitive.name.clone());
        }
        expr
    };
    for action in &merge.actions.0 {
        action.clone().visit_exprs(&mut observe);
    }
    merge.result.clone().visit_exprs(&mut observe);
    assert!(forbidden_calls.is_empty());

    let mut expected = before_role_score;
    let expected_view: String = expected.fresh("role-scoreView");
    let expected_term_sort: String = expected.fresh("view");
    for _ in 0..10 {
        let _: String = expected.fresh("pv");
    }
    assert_eq!(layout.view.name, expected_view);
    assert_eq!(layout.term_eclass_sort.name, expected_term_sort);
    assert_eq!(instrumentor.egraph.parser.symbol_gen, expected);
}

#[test]
fn failed_custom_merge_rolls_back_its_view_and_receipt_but_keeps_term_prefix() {
    let mut planning_egraph = EGraph::new_with_proofs();
    let source = before_proofs(
        &mut planning_egraph,
        r#"
            (sort E)
            (sort EV (Vec E))
            (constructor K (E) E)
            (function F (E EV i64) E :merge (K (K (K old))))
        "#,
    );
    let sorts = source
        .iter()
        .filter_map(|command| match command {
            ResolvedNCommand::Sort {
                span,
                name,
                presort_and_args,
                unionable,
                ..
            } => Some((
                span.clone(),
                name.clone(),
                presort_and_args.clone(),
                *unionable,
            )),
            _ => None,
        })
        .collect::<Vec<_>>();
    let functions = source
        .iter()
        .filter_map(|command| match command {
            ResolvedNCommand::Function(function) => Some(function.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    let k = functions
        .iter()
        .find(|function| function.name == "K")
        .unwrap();
    let f = functions
        .iter()
        .find(|function| function.name == "F")
        .unwrap();
    let mut catalog = GeneratedSignatureCatalog::default();
    let persistent_roles = EncodedFunctionCatalog::default();
    let mut overlay = EncodedFunctionPlanningOverlay::default();
    let mut instrumentor = ProofInstrumentor::new(&mut planning_egraph);
    let span = crate::span!();
    let mut prefix_groups = vec![
        instrumentor.plan_term_header_direct(&mut catalog, &span),
        instrumentor.plan_proof_header_direct(&mut catalog, &span),
    ];
    for (span, name, presort, unionable) in &sorts {
        prefix_groups.push(instrumentor.plan_source_sort_direct(
            &mut catalog,
            span,
            name,
            presort,
            *unionable,
        ));
    }
    let (k_group, _) =
        instrumentor.plan_term_and_view_direct(&mut catalog, &mut overlay, &k.span, k);
    prefix_groups.push(k_group);
    let (f_group, f_layout) =
        instrumentor.plan_term_and_view_direct(&mut catalog, &mut overlay, &f.span, f);
    assert!(!persistent_roles.by_source.contains_key("F"));
    assert!(overlay.staged.by_source.contains_key("F"));

    let view_index = f_group
        .declarations
        .iter()
        .position(|declaration| {
            matches!(&declaration.kind, PlannedDeclarationKind::Function(function)
                if function.name == f_layout.view.name)
        })
        .expect("F view declaration");
    let good_view = f_group.declarations[view_index].clone();
    let receipt = good_view
        .layout_commit
        .clone()
        .expect("view owns the role receipt");
    let mut bad_view = good_view.clone();
    let PlannedDeclarationKind::Function(function) = &mut bad_view.kind else {
        unreachable!()
    };
    function
        .merge
        .as_mut()
        .expect("F view has a custom merge")
        .result = GenericExpr::Lit(f.span.clone(), Literal::String("wrong-shape".to_owned()));
    let mut view_then_bad_index = f_group.declarations[view_index..].to_vec();
    let bad_index_name = view_then_bad_index
        .iter_mut()
        .find_map(|declaration| match &mut declaration.kind {
            PlannedDeclarationKind::Index(index) => {
                index.any_of.clear();
                Some(index.name.clone())
            }
            _ => None,
        })
        .expect("F must have a later occurrence index to invalidate");

    let mut prefix = vec![];
    for group in prefix_groups {
        for declaration in group.declarations {
            prefix.push(GeneratedEntry::Declaration(Box::new(
                declaration.into_entry(),
            )));
        }
    }
    for declaration in f_group.declarations.into_iter().take(view_index) {
        let entry = declaration.into_entry();
        assert!(entry.layout_commit.is_none());
        prefix.push(GeneratedEntry::Declaration(Box::new(entry)));
    }
    drop(instrumentor);

    let mut binding_egraph = EGraph::new_with_proofs();
    resolve_generated_batch(&mut binding_egraph, GeneratedBatch { entries: prefix })
        .expect("declarations preceding FView must bind");
    assert!(binding_egraph.type_info().get_func_type("F").is_some());
    assert!(
        binding_egraph
            .type_info()
            .get_func_type(&f_layout.view.name)
            .is_none()
    );
    assert!(
        !binding_egraph
            .proof_state
            .encoded_functions
            .by_source
            .contains_key("F")
    );
    let mut later_index_egraph = binding_egraph.clone();
    let mut view_then_bad_index = view_then_bad_index.into_iter();
    let view = view_then_bad_index
        .next()
        .expect("view must precede its occurrence index")
        .into_entry();
    let nested_index = view_then_bad_index
        .map(|declaration| GeneratedEntry::Declaration(Box::new(declaration.into_entry())))
        .collect::<Vec<_>>();
    let later_index = GeneratedBatch {
        entries: vec![GeneratedEntry::Fail(
            f.span.clone(),
            vec![
                GeneratedEntry::Declaration(Box::new(view)),
                GeneratedEntry::Fail(f.span.clone(), nested_index),
            ],
        )],
    };
    assert!(
        resolve_generated_batch(&mut later_index_egraph, later_index).is_err(),
        "the invalid later index must reject the nested declaration batch"
    );
    assert!(
        later_index_egraph
            .type_info()
            .get_func_type(&f_layout.view.name)
            .is_some()
    );
    assert_eq!(
        later_index_egraph.proof_state.encoded_functions.by_source["F"],
        f_layout
    );
    assert!(
        later_index_egraph
            .type_info()
            .get_func_type(&bad_index_name)
            .is_none()
    );
    let before_failure = binding_egraph.parser.symbol_gen.clone();
    let view_generation = binding_egraph
        .type_info()
        .call_cache_stamp(&f_layout.view.name, false)
        .0;
    let mut later_error_egraph = binding_egraph.clone();

    let failed = GeneratedBatch {
        entries: vec![GeneratedEntry::Declaration(Box::new(bad_view.into_entry()))],
    };
    assert!(resolve_generated_batch(&mut binding_egraph, failed).is_err());
    assert_eq!(binding_egraph.parser.symbol_gen, before_failure);
    assert_eq!(
        binding_egraph
            .type_info()
            .call_cache_stamp(&f_layout.view.name, false)
            .0,
        view_generation
    );
    assert!(
        binding_egraph
            .type_info()
            .get_func_type(&f_layout.view.name)
            .is_none()
    );
    assert!(
        !binding_egraph
            .proof_state
            .encoded_functions
            .by_source
            .contains_key("F")
    );

    // A receipt commits at its own successful declaration even when the next
    // child of the same Fail wrapper is rejected. This mirrors TypeInfo's
    // prefix-committing declaration contract rather than treating a generated
    // batch or Fail subtree as an atomic catalog transaction.
    let successful_view = good_view.clone().into_entry();
    let duplicate_view = successful_view.command.clone();
    let later_error = GeneratedBatch {
        entries: vec![GeneratedEntry::Fail(
            f.span.clone(),
            vec![
                GeneratedEntry::Declaration(Box::new(successful_view)),
                GeneratedEntry::Command(Box::new(duplicate_view)),
            ],
        )],
    };
    assert!(resolve_generated_batch(&mut later_error_egraph, later_error).is_err());
    assert!(
        later_error_egraph
            .type_info()
            .get_func_type(&f_layout.view.name)
            .is_some()
    );
    assert_eq!(
        later_error_egraph.proof_state.encoded_functions.by_source["F"],
        f_layout
    );

    let retry = GeneratedBatch {
        entries: vec![GeneratedEntry::Declaration(Box::new(
            good_view.into_entry(),
        ))],
    };
    resolve_generated_batch(&mut binding_egraph, retry)
        .expect("rolled-back custom view must be reusable");
    assert!(
        binding_egraph
            .type_info()
            .get_func_type(&f_layout.view.name)
            .is_some()
    );
    assert_eq!(
        binding_egraph.proof_state.encoded_functions.by_source["F"],
        f_layout
    );
    assert_eq!(receipt.layout.source_name, "F");
}

fn ordered_union_expr_shape(expr: &GeneratedExpr, span: &Span) -> String {
    match expr {
        GenericExpr::Var(actual, variable) => {
            assert_eq!(actual, span);
            format!("v{}", variable.id.0)
        }
        GenericExpr::Lit(actual, literal) => {
            assert_eq!(actual, span);
            format!("{literal:?}")
        }
        GenericExpr::Call(actual, head, args) => {
            assert_eq!(actual, span);
            let head = match head {
                CallKey::Function(function) => format!("fn:{}", function.name),
                CallKey::Primitive(primitive) => primitive.name.clone(),
                CallKey::Values(sorts) => format!(
                    "values<{}>",
                    sorts
                        .iter()
                        .map(|sort| format!("{}:{:?}", sort.name, sort.class))
                        .collect::<Vec<_>>()
                        .join(",")
                ),
            };
            let args = args
                .iter()
                .map(|arg| ordered_union_expr_shape(arg, span))
                .collect::<Vec<_>>()
                .join(",");
            format!("{head}({args})")
        }
    }
}

fn ordered_union_merge_shape(merge: &GeneratedMerge, span: &Span) -> (Vec<String>, String) {
    let actions = merge
        .actions
        .0
        .iter()
        .map(|action| match action {
            GenericAction::Let(actual, variable, value) => {
                assert_eq!(actual, span);
                format!(
                    "let v{}={}",
                    variable.id.0,
                    ordered_union_expr_shape(value, span)
                )
            }
            GenericAction::Set(actual, CallKey::Function(function), args, value) => {
                assert_eq!(actual, span);
                let args = args
                    .iter()
                    .map(|arg| ordered_union_expr_shape(arg, span))
                    .collect::<Vec<_>>()
                    .join(",");
                format!(
                    "set fn:{}({args})={}",
                    function.name,
                    ordered_union_expr_shape(value, span)
                )
            }
            action => panic!("unexpected ordered-union merge action: {action:?}"),
        })
        .collect();
    (actions, ordered_union_expr_shape(&merge.result, span))
}

#[test]
fn ordered_union_merge_has_exact_structure_ids_and_first_use_packed_group() {
    let mut egraph = EGraph::new_with_proofs();
    let mut instrumentor = ProofInstrumentor::new(&mut egraph);
    let mut catalog = GeneratedSignatureCatalog::default();
    let span = crate::span!();
    let value = SortKey {
        name: "E".to_owned(),
        class: SortSemanticClass::Eq,
    };
    let proof = SortKey {
        name: instrumentor.proof_names().proof_datatype.clone(),
        class: SortSemanticClass::Eq,
    };
    let uf = FunctionKey {
        name: "UF".to_owned(),
        subtype: FunctionSubtype::Custom,
        inputs: vec![value.clone()],
        output: ValueShape::Tuple(vec![value.clone(), proof.clone()]),
    };
    let composition = Skeleton::Leaf(0).trans(Skeleton::Leaf(1).sym());
    let spelling = composition.spelling();
    let packed = instrumentor.proof_names().packed_proof(composition.width());
    let mint = crate::proofs::proof_fresh::mint_prim_name(&packed);
    let mut expected_symbols = instrumentor.egraph.parser.symbol_gen.clone();
    let expected_displaced = expected_symbols.fresh("pv");
    let (pending, merge) = instrumentor.plan_ordered_union_merge_direct(
        &mut catalog,
        &span,
        value.clone(),
        uf.clone(),
        composition.clone(),
    );
    assert_eq!(instrumentor.egraph.parser.symbol_gen, expected_symbols);
    assert_eq!(planned_names(&pending), [packed.as_str()]);
    pending.register_signatures(&mut catalog);
    assert_eq!(pending.declarations.len(), 1);
    let [
        GenericAction::Let(_, hi, _),
        GenericAction::Let(_, lo, _),
        GenericAction::Let(_, displaced, _),
        GenericAction::Set(..),
    ] = merge.actions.0.as_slice()
    else {
        panic!("proof merge action kinds changed: {:?}", merge.actions)
    };
    assert_eq!((hi.id, hi.name.as_str()), (LocalId(4), "hi_pf_"));
    assert_eq!((lo.id, lo.name.as_str()), (LocalId(5), "lo_pf_"));
    assert_eq!(
        (displaced.id, &displaced.name),
        (LocalId(6), &expected_displaced)
    );
    let (actions, result) = ordered_union_merge_shape(&merge, &span);
    assert_eq!(
        actions,
        [
            "let v4=proof-of-max(v0,v1,v2,v3)".to_owned(),
            "let v5=proof-of-min(v0,v1,v2,v3)".to_owned(),
            format!("let v6={mint}(String({:?}),v4,v5)", spelling),
            format!(
                "set fn:UF(ordering-max(v0,v2))=values<E:Eq,{}:Eq>(ordering-min(v0,v2),v6)",
                proof.name
            ),
        ]
    );
    assert_eq!(
        result,
        format!("values<E:Eq,{}:Eq>(ordering-min(v0,v2),v5)", proof.name)
    );

    let (repeat, _) = instrumentor.plan_ordered_union_merge_direct(
        &mut catalog,
        &span,
        value.clone(),
        uf,
        composition,
    );
    assert!(repeat.declarations.is_empty());

    drop(instrumentor);
    let mut term_egraph = EGraph::new_with_term_encoding();
    let mut term_instrumentor = ProofInstrumentor::new(&mut term_egraph);
    let unit = SortKey {
        name: "Unit".to_owned(),
        class: SortSemanticClass::Value,
    };
    let term_uf = FunctionKey {
        name: "UF".to_owned(),
        subtype: FunctionSubtype::Custom,
        inputs: vec![value.clone()],
        output: ValueShape::Tuple(vec![value.clone(), unit]),
    };
    let before_symbols = term_instrumentor.egraph.parser.symbol_gen.clone();
    let (pending, merge) = term_instrumentor.plan_ordered_union_merge_direct(
        &mut GeneratedSignatureCatalog::default(),
        &span,
        value,
        term_uf,
        Skeleton::Leaf(0),
    );
    assert_eq!(term_instrumentor.egraph.parser.symbol_gen, before_symbols);
    assert!(pending.declarations.is_empty());
    let (actions, result) = ordered_union_merge_shape(&merge, &span);
    assert_eq!(
        actions,
        ["set fn:UF(ordering-max(v0,v1))=values<E:Eq,Unit:Value>(ordering-min(v0,v1),Unit)"]
    );
    assert_eq!(result, "values<E:Eq,Unit:Value>(ordering-min(v0,v1),Unit)");
}

#[test]
fn layout_overlay_and_receipts_pin_prefix_commit_push_pop_and_stale_failure() {
    let value = SortKey {
        name: "i64".to_owned(),
        class: SortSemanticClass::Value,
    };
    let unit = SortKey {
        name: "Unit".to_owned(),
        class: SortSemanticClass::Value,
    };
    let layout = EncodedFunctionLayout {
        source_name: "f".to_owned(),
        source_subtype: FunctionSubtype::Custom,
        term: FunctionKey {
            name: "f".to_owned(),
            subtype: FunctionSubtype::Custom,
            inputs: vec![value.clone()],
            output: ValueShape::Scalar(unit.clone()),
        },
        view: FunctionKey {
            name: "f-view".to_owned(),
            subtype: FunctionSubtype::Custom,
            inputs: vec![],
            output: ValueShape::Tuple(vec![value.clone(), unit]),
        },
        term_eclass_sort: value,
        output_is_eclass: false,
        indexes: vec![],
    };
    let persistent = EncodedFunctionCatalog::default();
    let mut overlay = EncodedFunctionPlanningOverlay::default();
    let receipt = overlay.stage(&persistent, layout.clone());
    assert!(!persistent.by_source.contains_key("f"));
    assert_eq!(overlay.staged.by_source["f"], layout);

    // The declaration's own failed registration never applies its receipt.
    let after_failed_declaration = persistent.clone();
    assert!(!after_failed_declaration.by_source.contains_key("f"));

    // A successful prefix applies its receipt immediately, so a later error —
    // including one caught by Fail — cannot erase the already-committed role.
    let mut after_caught_fail = persistent.clone();
    after_caught_fail.commit(receipt.clone());
    assert_eq!(after_caught_fail.by_source["f"], layout);
    after_caught_fail.commit(receipt);

    // Push snapshots the persistent state; Pop restores it and discards only
    // layouts committed inside the scope.
    let pushed = after_caught_fail.clone();
    let mut scoped = pushed.clone();
    let mut scoped_layout = layout.clone();
    scoped_layout.source_name = "scoped".to_owned();
    scoped.commit(EncodedFunctionLayoutCommit {
        layout: scoped_layout,
    });
    assert!(scoped.by_source.contains_key("scoped"));
    scoped = pushed.clone();
    assert!(!scoped.by_source.contains_key("scoped"));

    let mut conflicting = layout;
    conflicting.view.name = "different-view".to_owned();
    assert!(
        catch_unwind(AssertUnwindSafe(|| {
            after_caught_fail.commit(EncodedFunctionLayoutCommit {
                layout: conflicting,
            })
        }))
        .is_err()
    );
}

#[test]
fn persistent_layout_receipts_survive_caught_fail_and_follow_push_pop() {
    let mut egraph = EGraph::new_with_proofs();
    egraph
        .parse_and_run_program(
            None,
            r#"
                (fail
                    (function committed-layout (i64) i64 :merge old)
                    (panic "caught after declaration"))
            "#,
        )
        .expect("Fail must catch the later action error");
    assert!(
        egraph
            .proof_state
            .encoded_functions
            .by_source
            .contains_key("committed-layout")
    );

    egraph.parse_and_run_program(None, "(push)").unwrap();
    egraph
        .parse_and_run_program(None, "(function scoped-layout (i64) i64 :merge old)")
        .unwrap();
    assert!(
        egraph
            .proof_state
            .encoded_functions
            .by_source
            .contains_key("scoped-layout")
    );
    egraph.parse_and_run_program(None, "(pop)").unwrap();
    assert!(
        egraph
            .proof_state
            .encoded_functions
            .by_source
            .contains_key("committed-layout")
    );
    assert!(
        !egraph
            .proof_state
            .encoded_functions
            .by_source
            .contains_key("scoped-layout")
    );
}

#[test]
fn push_only_first_batch_keeps_headers_but_pop_restores_later_declarations() {
    let mut egraph = EGraph::new_with_term_encoding();
    assert!(!egraph.proof_state.term_header_added);
    egraph
        .parse_and_run_program(Some("push-header-snapshot.egg".to_owned()), "(push)")
        .expect("a push-only first batch must install headers before Push");
    assert!(egraph.proof_state.term_header_added);
    egraph
        .parse_and_run_program(
            Some("push-header-snapshot.egg".to_owned()),
            "(function ScopedAfterPush (i64) i64 :no-merge)",
        )
        .unwrap();
    assert!(
        egraph
            .proof_state
            .encoded_functions
            .by_source
            .contains_key("ScopedAfterPush")
    );
    egraph.parse_and_run_program(None, "(pop)").unwrap();
    assert!(
        egraph.proof_state.term_header_added,
        "Pop restored a snapshot from before the one-time typed headers"
    );
    assert!(
        !egraph
            .proof_state
            .encoded_functions
            .by_source
            .contains_key("ScopedAfterPush"),
        "Pop retained a typed declaration introduced after Push"
    );
    egraph
        .parse_and_run_program(None, "(sort HeaderSurvivor)")
        .expect("the retained path-compression ruleset must accept a later sort rule");
}

#[test]
fn typed_declaration_restores_reserved_name_checks_before_binding() {
    let mut egraph = EGraph::new_with_term_encoding();
    egraph.parser.ensure_no_reserved_symbols = false;
    egraph
        .parse_and_run_program(None, "(relation @UF_Broken ())")
        .expect("the reserved-name prefix must bind while checking is disabled");
    assert!(
        egraph.parser.ensure_no_reserved_symbols,
        "a successful generated declaration run must restore reserved-name checks"
    );

    // The generated UF declaration for Broken collides with the prefix. The
    // declaration planner restores reserved-name checking before binding and
    // preserves the source sort span on the resulting collision.
    egraph.parser.ensure_no_reserved_symbols = false;
    let error = egraph
        .parse_and_run_program(None, "(sort Broken)")
        .unwrap_err();
    assert!(matches!(
        error,
        crate::Error::TypeError(TypeError::FunctionAlreadyBound(ref name, ref span))
            if name == "@UF_Broken" && span.string() == "(sort Broken)"
    ));
    assert!(egraph.parser.ensure_no_reserved_symbols);
}

use super::*;
use egglog_backend_trait::{
    CriterionCaptureSpec, FiringCaptureSpec, ReplayConstructorSpec, ReplayOpId, ReplaySortId,
    SourceCaptureSpec, SourceRef,
};

#[test]
fn add_rule_rejects_trace_capture_metadata_before_mutation() {
    let replay = Arc::new(ReplayConstructorSpec::new(
        ReplaySortId::new(0),
        ReplayOpId::new(0),
        [],
    ));
    let mut cases = Vec::new();

    let mut firing = TestRule::new("firing capture");
    firing.spec.firing_capture = Some(FiringCaptureSpec {
        rule: 0,
        bindings: Box::new([]),
        union_sorts: Box::new([]),
    });
    cases.push(firing.spec);

    let mut criterion = TestRule::new("criterion capture");
    criterion.spec.criterion_capture = Some(CriterionCaptureSpec {
        check: 0,
        equalities: Box::new([]),
    });
    cases.push(criterion.spec);

    let mut source = TestRule::new("source capture");
    source.spec.source_capture = Some(SourceCaptureSpec {
        source: SourceRef::Synthetic(0),
        union_sorts: Box::new([]),
    });
    cases.push(source.spec);

    let mut body_replay = TestRule::new("body primitive replay");
    body_replay.spec.core.body.atoms.push(GenericAtom {
        span: Span::Panic,
        head: RuleBodyCall::Primitive {
            id: ExternalFunctionId::new(0),
            name: "external".into(),
            output: ColumnTy::Id,
            replay: Some(Arc::clone(&replay)),
        },
        // Deliberately structurally invalid: the capture boundary must run
        // before ordinary DD shape validation.
        args: Vec::new(),
    });
    cases.push(body_replay.spec);

    let mut action_replay = TestRule::new("action primitive replay");
    action_replay.spec.core.head.0.push(GenericCoreAction::Set(
        Span::Panic,
        RuleActionCall::Primitive {
            id: ExternalFunctionId::new(0),
            name: "external".into(),
            output: ColumnTy::Id,
            replay: Some(replay),
        },
        Vec::new(),
        Vec::new(),
    ));
    cases.push(action_replay.spec);

    let mut eg = EGraph::new();
    for spec in cases {
        let name = spec.name.clone();
        let error = Backend::add_rule(&mut eg, spec).unwrap_err();
        assert_eq!(
            error.to_string(),
            format!("DD backend cannot add rule {name:?}: trace capture metadata is unsupported")
        );
        assert!(eg.rules.is_empty());
    }
}

#[test]
fn freed_rule_slots_are_reused_without_stale_execution_state() {
    let mut eg = EGraph::new();
    let input = id_table(&mut eg, "input", 2);
    let output = id_table(&mut eg, "output", 2);
    eg.insert_live_row(input, row(&[1, 10]));

    let mut fused = TestRule::new("fused");
    let key = fused.new_var(ColumnTy::Id);
    let value = fused.new_var(ColumnTy::Id);
    fused.query_table(input, &[key.clone(), value.clone()], Some(false));
    fused.set(output, &[key, value]);
    let first_id = fused.build(&mut eg);
    run_rules(&mut eg, &[first_id]).unwrap();
    assert!(!eg.dd_fused.is_empty());
    assert!(!eg.dd_fused_fed_versions.is_empty());

    Backend::free_rule(&mut eg, first_id);
    assert_eq!(eg.rules.len(), 1);
    assert!(eg.rules[first_id.rep() as usize].is_none());
    assert!(eg.dd_fused.is_empty());
    assert!(eg.dd_fused_fed_versions.is_empty());
    assert!(!eg.seen.contains_key(&(first_id.rep() as usize)));

    let mut atomless = TestRule::new("atomless replacement");
    atomless.set(
        output,
        &[constant(2, ColumnTy::Id), constant(20, ColumnTy::Id)],
    );
    let owned_lifetime = Arc::new(());
    let retained = owned_lifetime.clone();
    let owned = Backend::register_external_func(
        &mut eg,
        Box::new(egglog_core_relations::make_external_func(move |_, _| {
            let _ = &retained;
            Some(Value::new(0))
        })),
    );
    atomless.spec.owned_external_funcs.push(owned);
    assert_eq!(Arc::strong_count(&owned_lifetime), 2);
    let replacement_id = atomless.build(&mut eg);
    assert_eq!(replacement_id, first_id);
    assert_eq!(eg.rules.len(), 1);
    assert!(eg.dd_fused.is_empty());
    assert!(eg.dd_fused_fed_versions.is_empty());
    assert!(!eg.seen.contains_key(&(replacement_id.rep() as usize)));

    run_rules(&mut eg, &[replacement_id]).unwrap();
    assert!(eg.seen.contains_key(&(replacement_id.rep() as usize)));
    assert!(eg.mirror[&output].contains(&row(&[2, 20])));
    Backend::free_rule(&mut eg, replacement_id);
    assert_eq!(Arc::strong_count(&owned_lifetime), 1);
    Backend::free_rule(&mut eg, replacement_id);
    assert_eq!(Arc::strong_count(&owned_lifetime), 1);

    // Repeated temporary-rule lifecycles must keep the slot vector bounded
    // and must not leak atom-less firing state into the replacement rule.
    for iteration in 0..16 {
        let rule = TestRule::new(&format!("temporary {iteration}")).build(&mut eg);
        assert_eq!(rule, first_id);
        assert_eq!(eg.rules.len(), 1);
        assert!(!eg.seen.contains_key(&(rule.rep() as usize)));
        assert!(eg.dd_fused.is_empty());
        assert!(eg.dd_fused_fed_versions.is_empty());

        run_rules(&mut eg, &[rule]).unwrap();
        assert!(eg.seen.contains_key(&(rule.rep() as usize)));
        Backend::free_rule(&mut eg, rule);
        assert!(!eg.seen.contains_key(&(rule.rep() as usize)));
    }
    assert_eq!(eg.rules.len(), 1);
}

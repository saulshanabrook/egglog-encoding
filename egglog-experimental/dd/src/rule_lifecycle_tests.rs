use super::*;
use egglog_backend_trait::{
    CriterionCaptureSpec, FiringCaptureSpec, ReplayCallSpec, ReplayOpId, ReplaySortId,
    RuleCaptureSpec, SourceCaptureSpec, SourceRef,
};

#[test]
fn add_rule_rejects_trace_capture_metadata_before_mutation() {
    let replay = Arc::new(ReplayCallSpec::new(
        ReplaySortId::new(0),
        ReplayOpId::new(0),
        [],
    ));
    let mut cases = Vec::new();

    let mut firing = TestRule::new("firing capture");
    firing.spec.capture = Some(RuleCaptureSpec::Firing(FiringCaptureSpec {
        rule: 0,
        bindings: Box::new([]),
        union_sorts: Box::new([]),
    }));
    cases.push(firing.spec);

    let mut criterion = TestRule::new("criterion capture");
    criterion.spec.capture = Some(RuleCaptureSpec::Criterion(CriterionCaptureSpec {
        check: 0,
        equalities: Box::new([]),
    }));
    cases.push(criterion.spec);

    let mut source = TestRule::new("source capture");
    source.spec.capture = Some(RuleCaptureSpec::Source(SourceCaptureSpec {
        source: SourceRef::Synthetic(0),
        union_sorts: Box::new([]),
    }));
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
fn free_rule_releases_owned_external_funcs_exactly_once() {
    let mut eg = EGraph::new();
    let owned_lifetime = Arc::new(());
    let retained = owned_lifetime.clone();
    let owned = Backend::register_external_func(
        &mut eg,
        Box::new(egglog_core_relations::make_external_func(move |_, _| {
            let _ = &retained;
            Some(Value::new(0))
        })),
    );

    let mut rule = TestRule::new("owned external");
    rule.spec.owned_external_funcs.push(owned);
    let rule = rule.build(&mut eg);
    assert_eq!(Arc::strong_count(&owned_lifetime), 2);

    Backend::free_rule(&mut eg, rule);
    assert_eq!(Arc::strong_count(&owned_lifetime), 1);
    Backend::free_rule(&mut eg, rule);
    assert_eq!(Arc::strong_count(&owned_lifetime), 1);
}

use egglog_ast::{core::GenericCoreRule, span::Span};

use super::*;
use crate::{CriterionCaptureSpec, FiringCaptureSpec, SourceCaptureSpec, SourceRef};

fn empty_rule(
    firing_capture: Option<FiringCaptureSpec>,
    criterion_capture: Option<CriterionCaptureSpec>,
    source_capture: Option<SourceCaptureSpec>,
) -> RuleSpec {
    RuleSpec {
        name: "invalid-capture-metadata".into(),
        seminaive: false,
        no_decomp: false,
        core: GenericCoreRule {
            span: Span::Panic,
            body: Default::default(),
            head: Default::default(),
        },
        firing_capture,
        criterion_capture,
        source_capture,
        owned_external_funcs: Vec::new(),
    }
}

#[test]
fn backend_rejects_multiple_capture_metadata_kinds_without_panicking() {
    let rule = FiringCaptureSpec {
        rule: 0,
        bindings: Box::new([]),
        union_sorts: Box::new([]),
    };
    let check = CriterionCaptureSpec {
        check: 0,
        equalities: Box::new([]),
    };
    let source = SourceCaptureSpec {
        source: SourceRef::Synthetic(0),
        union_sorts: Box::new([]),
    };
    for spec in [
        empty_rule(Some(rule.clone()), Some(check.clone()), None),
        empty_rule(Some(rule.clone()), None, Some(source.clone())),
        empty_rule(None, Some(check.clone()), Some(source.clone())),
        empty_rule(
            Some(rule.clone()),
            Some(check.clone()),
            Some(source.clone()),
        ),
    ] {
        let error = Backend::add_rule(&mut EGraph::default(), spec).unwrap_err();
        assert_eq!(
            error.to_string(),
            "one backend rule cannot have more than one kind of capture metadata"
        );
    }
}

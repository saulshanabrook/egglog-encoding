use super::ProofContext;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum RuleKind<'a> {
    Source(&'a str),
    Apply(&'a str),
    BinderRefresh,
    BinderStrip,
    ChildUpdate,
    ClassSlots,
    CosetReadings,
    CosetRepair,
    GroupEmpty,
    GroupRestore,
    GroupShrink,
    Invocation,
    InvocationMerge,
    Migration,
    NodeSymmetry,
    OneLeader,
    OrientMax,
    OrientMin,
    ReadingBig,
    ReadingSmall,
    RestateEdge,
    SeedIdentity,
    SelfEdgeSymmetry,
    SelfSymmetry,
    ShapeCollision,
    ShapeDedup,
    ShapeEqual,
    ShapeIndex,
    SlotClosure,
    Transitivity,
    TransportDown,
    TransportUp,
    Unknown(&'a str),
}

/// Recognize source rules before interpreting generated maintenance names.
pub(super) fn rule_kind<'a>(program: &ProofContext, name: &'a str) -> RuleKind<'a> {
    if let Some(user) = name.strip_suffix("/apply")
        && program.rewrites.contains_key(user)
    {
        return RuleKind::Apply(user);
    }
    if program.rewrites.contains_key(name) {
        return RuleKind::Source(name);
    }
    match name
        .strip_prefix("slotted/")
        .and_then(|rest| rest.split('/').next())
    {
        Some("binder-refresh") => RuleKind::BinderRefresh,
        Some("binder-strip") => RuleKind::BinderStrip,
        Some("child-update") => RuleKind::ChildUpdate,
        Some("class-slots") => RuleKind::ClassSlots,
        Some("coset-readings") => RuleKind::CosetReadings,
        Some("coset-repair") => RuleKind::CosetRepair,
        Some("group-empty") => RuleKind::GroupEmpty,
        Some("group-restore") => RuleKind::GroupRestore,
        Some("group-shrink") => RuleKind::GroupShrink,
        Some("invocation") => RuleKind::Invocation,
        Some("invocation-merge") => RuleKind::InvocationMerge,
        Some("migration") => RuleKind::Migration,
        Some("node-symmetry") => RuleKind::NodeSymmetry,
        Some("one-leader") => RuleKind::OneLeader,
        Some("orient-max") => RuleKind::OrientMax,
        Some("orient-min") => RuleKind::OrientMin,
        Some("reading-big") => RuleKind::ReadingBig,
        Some("reading-small") => RuleKind::ReadingSmall,
        Some("restate-edge") => RuleKind::RestateEdge,
        Some("seed-identity") => RuleKind::SeedIdentity,
        Some("self-edge-symmetry") => RuleKind::SelfEdgeSymmetry,
        Some("self-symmetry") => RuleKind::SelfSymmetry,
        Some("shape-collision") => RuleKind::ShapeCollision,
        Some("shape-dedup") => RuleKind::ShapeDedup,
        Some("shape-equal") => RuleKind::ShapeEqual,
        Some("shape-index") => RuleKind::ShapeIndex,
        Some("slot-closure") => RuleKind::SlotClosure,
        Some("transitivity") => RuleKind::Transitivity,
        Some("transport-down") => RuleKind::TransportDown,
        Some("transport-up") => RuleKind::TransportUp,
        _ => RuleKind::Unknown(name),
    }
}

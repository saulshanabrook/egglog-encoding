//! Stable identities and passive records in a captured execution trace.

use super::*;

macro_rules! handle {
    ($name:ident, $inner:ty) => {
        #[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $name($inner);

        impl $name {
            pub const fn new(value: $inner) -> Self {
                Self(value)
            }

            pub const fn get(self) -> $inner {
                self.0
            }
        }
    };
}

handle!(FactId, u64);
handle!(RuleMatchId, u64);
handle!(ReplayTermId, u32);
handle!(ReplaySortId, u32);
handle!(ReplayOpId, u32);
// Dense identity of one effective native union in raw receipt history,
// including same-syntax alias joins.
handle!(AppliedEqualityId, u64);
handle!(EqualityEdgeCount, u64);
handle!(CausalWave, u64);
handle!(HistoryPosition, u64);
handle!(RowOriginSiteId, u32);
handle!(TermOriginSiteId, u32);
handle!(CauseDraftId, u64);
handle!(ReceiptCauseId, u32);

/// Replay-observable keyed-table semantics.
///
/// Constructor and value-function removals can change a later grounded write
/// or lookup-or-insert. Presence relations have no merge-bearing cell, so
/// their removals are retained only as diagnostics.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ReplayTableKind {
    PresenceRelation,
    Constructor,
    ValueFunction,
}

/// Stable index into the shared causal DAG.
/// A dependency can point directly at an observed rule match or at a shared
/// non-rule cause node. Keeping the tagged distinction public avoids
/// manufacturing one cause-arena node for every native match.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ReceiptCauseRef {
    Rule(RuleMatchId),
    Cause(ReceiptCauseId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct PremiseSlot(u16);

impl PremiseSlot {
    pub(crate) fn from_usize(value: usize) -> Self {
        Self(
            value
                .try_into()
                .expect("a receipt has more than u16 premises"),
        )
    }

    pub(crate) fn index(self) -> usize {
        self.0 as usize
    }
}

impl FactId {
    pub(crate) const MISSING: Self = Self(0);

    pub(crate) fn is_missing(self) -> bool {
        self == Self::MISSING
    }
}

impl ReplayTermId {
    pub const MISSING: Self = Self(0);

    pub fn is_missing(self) -> bool {
        self == Self::MISSING
    }
}

impl CauseDraftId {
    pub(crate) const UNATTRIBUTED: Self = Self(0);

    pub(crate) fn is_unattributed(self) -> bool {
        self == Self::UNATTRIBUTED
    }

    pub(super) fn public(self) -> ReceiptCauseId {
        ReceiptCauseId::new(
            self.get()
                .try_into()
                .expect("public receipt cause arena exceeds u32"),
        )
    }
}

/// One word carried by native effects. The high bit distinguishes a direct
/// rule observation from a generic cause-node id; zero remains unattributed.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub(crate) struct CauseRef(u64);

impl CauseRef {
    const MATCH_TAG: u64 = 1 << 63;
    pub(crate) const UNATTRIBUTED: Self = Self(0);

    pub(super) fn rule(matched: RuleMatchId) -> Self {
        assert!(matched.get() != 0 && matched.get() < Self::MATCH_TAG);
        Self(Self::MATCH_TAG | matched.get())
    }

    pub(super) fn node(node: CauseDraftId) -> Self {
        assert!(!node.is_unattributed() && node.get() < Self::MATCH_TAG);
        Self(node.get())
    }

    pub(super) fn rule_match(self) -> Option<RuleMatchId> {
        (self.0 & Self::MATCH_TAG != 0).then(|| RuleMatchId::new(self.0 & !Self::MATCH_TAG))
    }

    pub(super) fn cause_node(self) -> Option<CauseDraftId> {
        (self != Self::UNATTRIBUTED && self.0 & Self::MATCH_TAG == 0)
            .then(|| CauseDraftId::new(self.0))
    }

    pub(super) fn is_unattributed(self) -> bool {
        self == Self::UNATTRIBUTED
    }

    #[cfg(test)]
    pub(super) fn into_public(self) -> ReceiptCauseRef {
        match self.rule_match() {
            Some(rule) => ReceiptCauseRef::Rule(rule),
            None => ReceiptCauseRef::Cause(
                self.cause_node()
                    .expect("unattributed cause cannot be published")
                    .public(),
            ),
        }
    }
}

#[cfg(test)]
impl From<CauseRef> for ReceiptCauseRef {
    fn from(value: CauseRef) -> Self {
        value.into_public()
    }
}

impl From<CauseDraftId> for CauseRef {
    fn from(value: CauseDraftId) -> Self {
        Self::node(value)
    }
}

impl From<RuleMatchId> for CauseRef {
    fn from(value: RuleMatchId) -> Self {
        Self::rule(value)
    }
}

impl From<ReceiptCauseRef> for CauseRef {
    fn from(value: ReceiptCauseRef) -> Self {
        match value {
            ReceiptCauseRef::Rule(rule) => Self::rule(rule),
            ReceiptCauseRef::Cause(cause) => Self::node(CauseDraftId::new(cause.get() as u64)),
        }
    }
}

impl From<CauseDraftId> for ReceiptCauseRef {
    fn from(value: CauseDraftId) -> Self {
        Self::Cause(value.public())
    }
}

impl From<ReceiptCauseId> for ReceiptCauseRef {
    fn from(value: ReceiptCauseId) -> Self {
        Self::Cause(value)
    }
}

impl From<RuleMatchId> for ReceiptCauseRef {
    fn from(value: RuleMatchId) -> Self {
        Self::Rule(value)
    }
}

/// Stable reference back to one original input fact.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum SourceRef {
    /// Test and embedding callers may provide their own stable input ordinal.
    Synthetic(u64),
    /// One physical row of an original `(input ...)` command.
    InputRow {
        /// Frontend-global source-command ordinal.
        command: u64,
        /// One-based physical line number in the source file.
        line: u64,
    },
}

/// Static source identity attached to every effective lane of one source
/// action. Source actions do not manufacture rule matches.
#[derive(Clone, Debug)]
pub struct SourceReceiptSpec {
    pub(crate) source: SourceRef,
}

impl SourceReceiptSpec {
    pub fn new(source: SourceRef) -> Self {
        Self { source }
    }
}

/// Static witness and typed-equality layout for one positive check.
#[derive(Clone, Copy, Debug)]
pub enum CheckEndpointSource {
    Premise {
        premise: usize,
        column: usize,
        value: QueryEntry,
        constructor: Option<(ReplaySortId, ReplayOpId)>,
    },
    Current {
        value: QueryEntry,
        sort: ReplaySortId,
    },
}

impl CheckEndpointSource {
    pub fn premise(premise: usize, column: usize, value: QueryEntry) -> Self {
        Self::Premise {
            premise,
            column,
            value,
            constructor: None,
        }
    }

    pub fn premise_constructor(
        premise: usize,
        column: usize,
        value: QueryEntry,
        sort: ReplaySortId,
        op: ReplayOpId,
    ) -> Self {
        Self::Premise {
            premise,
            column,
            value,
            constructor: Some((sort, op)),
        }
    }

    pub fn current(value: QueryEntry, sort: ReplaySortId) -> Self {
        Self::Current { value, sort }
    }

    pub(crate) fn value(&self) -> &QueryEntry {
        match self {
            Self::Premise { value, .. } | Self::Current { value, .. } => value,
        }
    }
}

/// Static witness and typed-equality layout for one positive check.
#[derive(Clone, Debug)]
pub struct CheckReceiptSpec {
    pub(crate) check: u32,
    pub(crate) premises: Box<[AtomId]>,
    pub(crate) equalities: Box<[(CheckEndpointSource, CheckEndpointSource)]>,
}

impl CheckReceiptSpec {
    pub fn new(check: u32, premises: impl IntoIterator<Item = AtomId>) -> Self {
        Self {
            check,
            premises: premises.into_iter().collect(),
            equalities: Box::new([]),
        }
    }

    pub fn with_equalities(
        mut self,
        equalities: impl IntoIterator<Item = (CheckEndpointSource, CheckEndpointSource)>,
    ) -> Self {
        self.equalities = equalities.into_iter().collect();
        self
    }
}

/// Static receipt metadata retained with a compiled rule.
#[derive(Clone, Debug)]
pub struct RuleReceiptSpec {
    pub(crate) rule: u32,
    pub(crate) premises: Box<[AtomId]>,
    pub(crate) bindings: Box<[RuleBindingSpec]>,
}

/// One source-ordered binding retained by an effective rule match.
#[derive(Clone, Copy, Debug)]
pub enum RuleBindingSpec {
    Variable {
        variable: Variable,
        current_sort: Option<ReplaySortId>,
    },
    Constant {
        term: ReplayTermId,
        sort: ReplaySortId,
    },
}

impl RuleBindingSpec {
    pub fn variable(variable: Variable, current_sort: Option<ReplaySortId>) -> Self {
        Self::Variable {
            variable,
            current_sort,
        }
    }

    pub fn constant(term: ReplayTermId, sort: ReplaySortId) -> Self {
        Self::Constant { term, sort }
    }
}

impl RuleReceiptSpec {
    pub fn new(
        rule: u32,
        premises: impl IntoIterator<Item = AtomId>,
        ordinary_vars: impl IntoIterator<Item = Variable>,
    ) -> Self {
        Self {
            rule,
            premises: premises.into_iter().collect(),
            bindings: ordinary_vars
                .into_iter()
                .map(|variable| RuleBindingSpec::variable(variable, None))
                .collect(),
        }
    }

    pub fn with_bindings(
        rule: u32,
        premises: impl IntoIterator<Item = AtomId>,
        bindings: impl IntoIterator<Item = RuleBindingSpec>,
    ) -> Self {
        Self {
            rule,
            premises: premises.into_iter().collect(),
            bindings: bindings.into_iter().collect(),
        }
    }

    pub fn with_current_vars(
        mut self,
        vars: impl IntoIterator<Item = (Variable, ReplaySortId)>,
    ) -> Self {
        let current_vars = vars.into_iter().collect::<HashMap<_, _>>();
        for binding in &mut self.bindings {
            if let RuleBindingSpec::Variable {
                variable,
                current_sort,
            } = binding
                && let Some(sort) = current_vars.get(variable)
            {
                *current_sort = Some(*sort);
            }
        }
        self
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct PremiseOccurrence {
    pub(crate) premise: usize,
    pub(crate) column: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ReplayEqualitySource {
    Premise(PremiseOccurrence),
    Constant(EqualityEndpoint),
}

/// One node in the static source-to-action term recipe. Nodes share producer
/// subgraphs while a rule is compiled and instantiate only for promoted
/// observations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RekeyOutcome {
    Moved,
    Absorbed(FactId),
    Replaced(FactId),
}

/// One effective logical-row relocation. Pure rekeys preserve `fact`; a
/// collision records which live fact absorbed or replaced it. The equality
/// landmark is immutable and historically bounded at the rebuild decision.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RekeyRecord {
    pub(crate) fact: FactId,
    pub(crate) table: TableId,
    pub(crate) wave: CausalWave,
    pub(crate) position: HistoryPosition,
    pub(crate) equalities: EqualityLandmark,
    pub(crate) outcome: RekeyOutcome,
}

/// Exact positional child changes produced by one serial container rebuild.
///
/// The container's structural replay term remains immutable. Re-executing the
/// child equalities makes that same term denote the rebuilt native container.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ContainerDependency {
    pub(crate) wave: CausalWave,
    pub(crate) equalities: EqualityLandmark,
}

/// Receipt-only logical identity for one container version. Borrowed views
/// expose the dependency itself; native refresh bookkeeping additionally
/// needs the exact structural producer that owned the raw container id.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ContainerVersionDependency {
    pub(crate) outer: EqualityEndpoint,
    pub(crate) dependency: Arc<ContainerDependency>,
}

#[derive(Clone)]
pub(crate) struct ContainerParentCandidate {
    pub(crate) endpoint: EqualityEndpoint,
    pub(crate) child_sorts: Arc<[ReplaySortId]>,
}

/// Forward-only overlay of existing immutable container terms during one
/// cloned-registry rebuild transaction. Source mappings remain historical;
/// only additional `(sort, raw) -> term` anchors are staged. Abort drops this
/// value without touching shared receipt state.
#[derive(Clone, Debug, Default)]
pub(crate) struct ContainerAnchorJournal {
    pub(super) additions: HashMap<(ReplaySortId, Value), SmallVec<[ReplayTermId; 2]>>,
}

impl ContainerAnchorJournal {
    pub(super) fn additions(&self, sort: ReplaySortId, value: Value) -> Option<&[ReplayTermId]> {
        self.additions.get(&(sort, value)).map(SmallVec::as_slice)
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.additions.is_empty()
    }

    pub(crate) fn extend(&mut self, other: Self) {
        for (key, terms) in other.additions {
            let current = self.additions.entry(key).or_default();
            for term in terms {
                if !current.contains(&term) {
                    current.push(term);
                }
            }
            current.sort_unstable_by_key(|term| term.get());
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EqualityReason {
    RuleUnion(RuleMatchId),
    SourceUnion {
        cause: ReceiptCauseId,
    },
    MergeFn {
        /// Shared exact cause root. Dependencies are unfolded lazily through
        /// [`CausalReceiptView::cause`].
        cause: ReceiptCauseId,
    },
    Congruence {
        /// Shared exact cause root; no growing prefix is copied per edge.
        cause: ReceiptCauseId,
        wave: CausalWave,
        as_of_edges: EqualityEdgeCount,
        position: HistoryPosition,
    },
}

impl EqualityReason {
    pub fn rule_match(&self) -> Option<RuleMatchId> {
        match self {
            EqualityReason::RuleUnion(id) => Some(*id),
            EqualityReason::SourceUnion { .. } => None,
            EqualityReason::MergeFn { .. } => None,
            EqualityReason::Congruence { .. } => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReceiptCausePrior {
    Fact(FactId),
    Cause(ReceiptCauseRef),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct EqualityEndpoint {
    pub sort: ReplaySortId,
    pub term: ReplayTermId,
    pub raw: crate::Value,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CheckEndpointOccurrence {
    FactCell(FactCellRef),
    Current,
}

/// Exact native support retained for the first successful match of one check.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckRoot {
    pub check: u32,
    pub wave: CausalWave,
    pub position: HistoryPosition,
    pub premises: Box<[FactId]>,
    pub equalities: Box<[(EqualityEndpoint, EqualityEndpoint)]>,
    pub equality_occurrences: Box<[(CheckEndpointOccurrence, CheckEndpointOccurrence)]>,
    pub as_of_edges: EqualityEdgeCount,
}

/// One effective replay-observable keyed-row removal.
///
/// The immutable victim fact retains the historical table/key row, so the
/// event needs no copied key payload. `cause` is the exact rule lane whose
/// head staged the removal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RemovalRecord {
    pub wave: CausalWave,
    pub position: HistoryPosition,
    pub as_of_edges: EqualityEdgeCount,
    pub removed_fact: FactId,
    pub cause: RuleMatchId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TypedCellEquality {
    pub column: crate::ColumnId,
    pub left: EqualityEndpoint,
    pub right: EqualityEndpoint,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct EqualityLandmark {
    /// Dense applied-edge prefix visible at this exact global history point.
    pub(crate) as_of_edges: EqualityEdgeCount,
    /// Cross-stream cutoff for zero-edge fact/rekey/alias attachments.
    pub(crate) position: HistoryPosition,
    pub(crate) pairs: Box<[TypedCellEquality]>,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ReceiptCounters {
    /// Every normal-return native rule lane, including inert observations.
    pub observed_matches: u64,
    pub premise_handles: u64,
    /// Logical match-term handles exposed by [`CausalReceiptView::match_terms`].
    pub logical_match_term_handles: u64,
    /// Match-term handles physically retained by the receipt arena.
    pub stored_match_term_handles: u64,
    /// Logical bytes exposed by [`CausalReceiptView::match_terms`].
    pub logical_match_term_bytes: u64,
    /// Match-term bytes physically retained by the receipt arena.
    pub stored_match_term_bytes: u64,
    pub unattributed_commits: u64,
    pub redundant_unions: u64,
    /// Effective constructor/value-function removals retained for slicing.
    pub effective_removals: u64,
    /// Effective presence-relation removals observed but not retained.
    pub relation_removals: u64,
    /// Semantic rows for which an exact rebuild cause was captured.
    pub rebuild_causes: u64,
    /// Changed typed cells stored across those rebuild causes.
    pub rebuild_equalities: u64,
    /// Logical bytes of rebuild cause and changed-cell payload captured.
    pub rebuild_bytes: u64,
    /// `Current` binding slots with a complete replay-safe structural recipe.
    pub supported_current_recipe_roots: u64,
    /// `Current` binding slots whose structural producer remains unsupported.
    /// Reached slots fail closed during slicing; this counter makes cohort
    /// coverage visible before replay is wired.
    pub missing_current_recipe_roots: u64,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CausalReceiptTotals {
    pub facts: u64,
    pub matches: u64,
    pub causes: u64,
    pub applied_equalities: u64,
    pub rekeys: u64,
    pub removals: u64,
    pub check_roots: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReplayTableSchema {
    pub table: TableId,
    pub kind: ReplayTableKind,
    pub key_columns: usize,
    pub columns: Arc<[Option<ReplaySortId>]>,
    pub constructor: Option<ReplayConstructorSpec>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FactCellRef {
    pub fact: FactId,
    pub column: crate::ColumnId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HistoricalFactCell {
    pub occurrence: FactCellRef,
    pub created: EqualityEndpoint,
    pub endpoint: EqualityEndpoint,
    pub rekeys: Box<[HistoryPosition]>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawEqualitySupport {
    pub applied: Box<[AppliedEqualityId]>,
    pub facts: Box<[FactId]>,
    pub causes: Box<[ReceiptCauseRef]>,
    pub rekeys: Box<[HistoryPosition]>,
}

/// The exact support and capture lower bounds for one structural checked
/// alias. Once established, the persistent alias lets a later grounded firing
/// reuse an e-class value after its constructor row has been deleted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawTermAvailability {
    pub support: RawEqualitySupport,
    pub aliases: Box<[RawAliasWindow]>,
}

/// Earliest native point after which one structural Call occurrence can be
/// captured by a persistent checked alias. Entries are emitted child-first in
/// structural occurrence order; equal `term` ids may therefore appear more
/// than once with different lower bounds. Bounds belong only to the exact
/// constructor row that names this occurrence; causal support facts are not
/// alias liveness.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RawAliasWindow {
    pub term: ReplayTermId,
    pub available_after: HistoryPosition,
    /// A refreshed ordered-container spelling and its structural descendants
    /// cannot canonicalize back to aliases from an earlier container version.
    pub fresh_after: Option<HistoryPosition>,
}

pub(super) fn combine_raw_equality_support(
    parts: impl IntoIterator<Item = RawEqualitySupport>,
) -> RawEqualitySupport {
    let mut applied = Vec::new();
    let mut facts = Vec::new();
    let mut causes = Vec::new();
    let mut rekeys = Vec::new();
    for part in parts {
        applied.extend(part.applied);
        facts.extend(part.facts);
        causes.extend(part.causes);
        rekeys.extend(part.rekeys);
    }
    applied.sort_unstable();
    applied.dedup();
    facts.sort_unstable();
    facts.dedup();
    causes.sort_unstable();
    causes.dedup();
    rekeys.sort_unstable();
    rekeys.dedup();
    RawEqualitySupport {
        applied: applied.into_boxed_slice(),
        facts: facts.into_boxed_slice(),
        causes: causes.into_boxed_slice(),
        rekeys: rekeys.into_boxed_slice(),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ReceiptPremiseOccurrence {
    pub premise: usize,
    pub column: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReceiptBindingSource {
    Premise {
        representative: ReceiptPremiseOccurrence,
        occurrences: Box<[ReceiptPremiseOccurrence]>,
    },
    Current {
        sort: ReplaySortId,
        residual: u32,
        replay_safe: bool,
    },
    Constant {
        term: ReplayTermId,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReceiptEqualitySource {
    Premise(ReceiptPremiseOccurrence),
    Constant(EqualityEndpoint),
}

#[derive(Clone, Copy, Debug)]
pub struct RawFactRecord<'a> {
    pub id: FactId,
    pub table: TableId,
    pub position: HistoryPosition,
    pub cause: ReceiptCauseRef,
    pub values: &'a [Value],
}

#[derive(Clone, Copy, Debug)]
pub struct RawMatchRecord<'a> {
    pub id: RuleMatchId,
    pub rule: u32,
    pub wave: CausalWave,
    pub position: HistoryPosition,
    pub as_of_edges: EqualityEdgeCount,
    pub premises: &'a [FactId],
    pub merge_reads: &'a [FactId],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawReceiptCause<'a> {
    Source(&'a SourceRef),
    Rebuild {
        wave: CausalWave,
        prior_fact: FactId,
        as_of_edges: EqualityEdgeCount,
        position: HistoryPosition,
        equalities: &'a [TypedCellEquality],
    },
    ContainerCanonicalize {
        wave: CausalWave,
        as_of_edges: EqualityEdgeCount,
        position: HistoryPosition,
        equalities: &'a [TypedCellEquality],
    },
    ContainerRefresh {
        wave: CausalWave,
        prior_fact: FactId,
        as_of_edges: EqualityEdgeCount,
        position: HistoryPosition,
        equalities: &'a [TypedCellEquality],
    },
    Merge {
        incoming: ReceiptCauseRef,
        prior: ReceiptCausePrior,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RawEqualityEndpoint {
    pub sort: ReplaySortId,
    pub raw: Value,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawAppliedEquality {
    pub id: AppliedEqualityId,
    pub wave: CausalWave,
    pub position: HistoryPosition,
    pub left: RawEqualityEndpoint,
    pub right: RawEqualityEndpoint,
    pub native_parent: Value,
    pub native_child: Value,
    pub reason: EqualityReason,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectedAppliedEquality {
    pub id: AppliedEqualityId,
    pub wave: CausalWave,
    pub position: HistoryPosition,
    pub left: EqualityEndpoint,
    pub right: EqualityEndpoint,
    pub native_parent: Value,
    pub native_child: Value,
    pub reason: EqualityReason,
}

#[derive(Clone, Copy, Debug)]
pub struct RawRekeyRecord<'a> {
    pub fact: FactId,
    pub table: TableId,
    pub wave: CausalWave,
    pub position: HistoryPosition,
    pub as_of_edges: EqualityEdgeCount,
    pub equality_position: HistoryPosition,
    pub equalities: &'a [TypedCellEquality],
    pub outcome: RekeyOutcome,
}

#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum ReceiptViewError {
    #[error("causal receipt history is not finalized: {0}")]
    NotFinalized(&'static str),
    #[error("causal receipt lock is poisoned: {0}")]
    Poisoned(&'static str),
    #[error("unknown causal fact {0:?}")]
    UnknownFact(FactId),
    #[error("unknown causal match {0:?}")]
    UnknownMatch(RuleMatchId),
    #[error("unknown causal cause {0:?}")]
    UnknownCause(ReceiptCauseId),
    #[error("unknown applied equality {0:?}")]
    UnknownEquality(AppliedEqualityId),
    #[error("unknown causal rekey at {0:?}")]
    UnknownRekey(HistoryPosition),
    #[error("unknown causal removal {0}")]
    UnknownRemoval(usize),
    #[error("unknown successful check {0}")]
    UnknownCheck(u32),
    #[error("unknown replay table {0:?}")]
    UnknownTable(TableId),
    #[error("invalid causal receipt history: {0}")]
    Invalid(String),
    #[error(
        "causal fact {fact:?} ended at {ended_at:?} with successor {successor:?}; it is not live at {position:?}"
    )]
    FactNoLongerLive {
        fact: FactId,
        position: HistoryPosition,
        ended_at: HistoryPosition,
        successor: Option<FactId>,
    },
}

/// Opaque proof that both raw union endpoints were resolved through the
/// canonical typed replay-term map before native staging.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum EqualityTermRef {
    Exact(ReplayTermId),
    Site(TermOriginSiteId),
    Cell {
        origin: RowOriginRef,
        table: TableId,
        column: u16,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct PendingEqualityEndpoint {
    pub(crate) sort: ReplaySortId,
    pub(crate) raw: crate::Value,
    pub(crate) term: EqualityTermRef,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[doc(hidden)]
pub struct TypedEqualityProposal {
    pub(super) wave: CausalWave,
    pub(super) left: PendingEqualityEndpoint,
    pub(super) right: PendingEqualityEndpoint,
}

impl TypedEqualityProposal {
    pub(crate) fn wave(self) -> CausalWave {
        self.wave
    }

    pub(crate) fn left(self) -> PendingEqualityEndpoint {
        self.left
    }

    pub(crate) fn right(self) -> PendingEqualityEndpoint {
        self.right
    }
}

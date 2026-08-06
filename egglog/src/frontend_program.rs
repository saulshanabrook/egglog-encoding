//! Owned, backend-free command and schedule envelope for a resolved frontend.
//!
//! [`crate::frontend_snapshot`] owns the nominal catalog, merge programs, and
//! core rules.  This module adds the command-sensitive information that cannot
//! be recovered from that final catalog: exact index identity, primitive
//! capabilities, source rule options, extraction metadata, structured
//! schedules, catalog-prefix ruleset membership, input ownership, display
//! sites, and command/output provenance.
//!
//! Execution and proof-check streams deliberately have separate nominal
//! namespaces.  Proof instrumentation inserts declarations and maintenance
//! commands, so the streams must never be zipped by command position or by the
//! numeric value of an ID.  Their only shared identities are exact source-group
//! and parsed-subcommand identities plus owned input-payload IDs.
//!
//! This is a DTO and structural validator, not the capture mapper.  In
//! particular, assigning IDs, attaching generated-command origins, resolving
//! prefix-sensitive print sites, freezing ruleset membership, and classifying
//! primitive effects are deferred to that mapper.  No backend token, backend
//! type, source-name inference, or schema-selected semantic role appears here.

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt::{self, Display, Formatter};
use std::io::ErrorKind as IoErrorKind;
use std::ops::{BitOr, BitOrAssign, Range};
use std::path::PathBuf;

use crate::frontend_snapshot::{
    ChangeKind, CoreAction, FunctionId, FunctionKind, LiteralValue, MergeValueOperation,
    PrimitiveId, PrimitiveSemantics, ReadMode, ResolvedCoreSnapshot, RuleActionCall, RuleBodyCall,
    RuleId, RuleTerm, RuleVar, RuleVarId, RulesetId, SortId, SortSemantics, TypedLiteral,
};
use crate::typed_input::{
    DeclaredInputSort, InputColumnRole, InputFunctionSubtype, InputLiteral, InputPathMetadata,
    InputScalarKind, InputSortAuthority, TypedInputFile, TypedInputParseError, TypedInputRow,
    TypedInputSchema, parse_tsv_with_resolved_schema, resolve_input_path,
};

macro_rules! stable_id {
    ($(#[$meta:meta])* $name:ident) => {
        $(#[$meta])*
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $name(u32);

        impl $name {
            /// Construct an identity from its deterministic arena ordinal.
            pub const fn new(ordinal: u32) -> Self {
                Self(ordinal)
            }

            /// Return the deterministic arena ordinal.
            pub const fn ordinal(self) -> u32 {
                self.0
            }
        }
    };
}

stable_id!(
    /// Stable identity of one declared occurrence index in a program view.
    IndexId
);
stable_id!(
    /// Stable identity of one top-level structured schedule in a program view.
    ScheduleId
);
stable_id!(
    /// Stable identity of one input payload shared by the program views.
    InputPayloadId
);
stable_id!(
    /// Dense identity of one physical source transaction/rollback group.
    SourceGroupId
);
stable_id!(
    /// Dense group-local identity of one parsed source subcommand.
    SourceSubcommandId
);
stable_id!(
    /// Dense ordinal of a finalized command inside one program view.
    CommandOrdinal
);
stable_id!(
    /// Dense source-position identity of an admitted user-visible `print-size`
    /// or no-file `print-stats` event. Schedule Runs are structurally retained
    /// but never consume this stdout event namespace.
    /// A runtime failure at or before the site may prevent any event emission.
    OutputOrdinal
);
stable_id!(
    /// Dense ordinal of a command nested directly inside one [`FailBlock`].
    FailCommandOrdinal
);
stable_id!(
    /// Dense per-row fresh value slot in an encoded input plan.
    InputFreshSlotId
);

/// A prefix-sensitive source name resolution frozen at the command position.
///
/// Missing names are admitted late runtime failures.  They are never revisited
/// against declarations that happen to occur later in the final catalog.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResolvedOrMissing<T> {
    Resolved(T),
    Missing { name: String },
}

/// The frontend capability context selected for a primitive call site.
///
/// This is portable frontend vocabulary, not [`crate::Context`] and not a
/// backend callback token.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PrimitiveCallContext {
    Pure,
    Write,
    Read,
    Full,
}

/// Exact set of frontend contexts in which a primitive specialization is valid.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PrimitiveContextMask(u8);

impl PrimitiveContextMask {
    const PURE_BIT: u8 = 1 << 0;
    const WRITE_BIT: u8 = 1 << 1;
    const READ_BIT: u8 = 1 << 2;
    const FULL_BIT: u8 = 1 << 3;
    const KNOWN_BITS: u8 = Self::PURE_BIT | Self::WRITE_BIT | Self::READ_BIT | Self::FULL_BIT;

    pub const EMPTY: Self = Self(0);
    pub const PURE: Self = Self(Self::PURE_BIT);
    pub const WRITE: Self = Self(Self::WRITE_BIT);
    pub const READ: Self = Self(Self::READ_BIT);
    pub const FULL: Self = Self(Self::FULL_BIT);
    pub const ALL: Self = Self(Self::KNOWN_BITS);

    pub const fn from_context(context: PrimitiveCallContext) -> Self {
        match context {
            PrimitiveCallContext::Pure => Self::PURE,
            PrimitiveCallContext::Write => Self::WRITE,
            PrimitiveCallContext::Read => Self::READ,
            PrimitiveCallContext::Full => Self::FULL,
        }
    }

    /// Construct a mask only when every bit is part of the public vocabulary.
    pub const fn from_bits(bits: u8) -> Option<Self> {
        if bits & !Self::KNOWN_BITS == 0 {
            Some(Self(bits))
        } else {
            None
        }
    }

    pub const fn bits(self) -> u8 {
        self.0
    }

    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }

    pub const fn contains(self, context: PrimitiveCallContext) -> bool {
        self.0 & Self::from_context(context).0 != 0
    }
}

impl BitOr for PrimitiveContextMask {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0 | rhs.0)
    }
}

impl BitOrAssign for PrimitiveContextMask {
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0;
    }
}

/// Portable semantic effects of a primitive specialization.
///
/// These bits are intentionally independent of [`PrimitiveContextMask`].  The
/// current frontend, for example, invokes a generic view-column read from a
/// `Write` or `Full` call context.  `READS_STATE` and `WRITES_STATE` describe
/// relation/storage effects; `MINTS_FRESH` describes the distinct authoritative
/// fresh-ID state.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PrimitiveEffectMask(u8);

impl PrimitiveEffectMask {
    const READS_STATE_BIT: u8 = 1 << 0;
    const WRITES_STATE_BIT: u8 = 1 << 1;
    const MINTS_FRESH_BIT: u8 = 1 << 2;
    const KNOWN_BITS: u8 = Self::READS_STATE_BIT | Self::WRITES_STATE_BIT | Self::MINTS_FRESH_BIT;

    pub const NONE: Self = Self(0);
    pub const READS_STATE: Self = Self(Self::READS_STATE_BIT);
    pub const WRITES_STATE: Self = Self(Self::WRITES_STATE_BIT);
    pub const MINTS_FRESH: Self = Self(Self::MINTS_FRESH_BIT);
    pub const ALL: Self = Self(Self::KNOWN_BITS);

    /// Construct a mask only when every bit is part of the public vocabulary.
    pub const fn from_bits(bits: u8) -> Option<Self> {
        if bits & !Self::KNOWN_BITS == 0 {
            Some(Self(bits))
        } else {
            None
        }
    }

    pub const fn bits(self) -> u8 {
        self.0
    }

    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }

    pub const fn contains(self, required: Self) -> bool {
        self.0 & required.0 == required.0
    }
}

impl BitOr for PrimitiveEffectMask {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0 | rhs.0)
    }
}

impl BitOrAssign for PrimitiveEffectMask {
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0;
    }
}

/// Command-sensitive metadata for one exact primitive specialization.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrimitiveMetadata {
    pub primitive: PrimitiveId,
    pub valid_contexts: PrimitiveContextMask,
    pub effects: PrimitiveEffectMask,
}

/// Exact declaration of a read-only occurrence index.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IndexDecl {
    pub id: IndexId,
    /// Diagnostic/source spelling only.
    pub name: String,
    pub target: FunctionId,
    /// Ordered, duplicate-preserving columns of the target's complete row.
    pub any_of: Vec<usize>,
}

/// Exact declaration kind for one nominal ruleset.
///
/// Concrete membership remains in the core [`crate::frontend_snapshot::RulesetDecl`].
/// A combined ruleset instead retains its ordered, duplicate-preserving child
/// identities and computes membership recursively at each Run prefix.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RulesetKind {
    Concrete,
    Combined { children: Vec<RulesetReference> },
}

/// How a ruleset becomes available in a command prefix.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RulesetAvailability {
    /// The frontend's exact built-in default identity, available before command
    /// zero without inferring that role from its diagnostic name.
    ImplicitDefault,
    /// Availability begins at an explicit catalog/combined command.
    Declared,
}

/// One ordered combined-ruleset child reference.
///
/// `target` records final-catalog nominal resolution, while Run expansion still
/// checks whether that exact declaration was present at the particular command
/// prefix. `name` and the spelling inside a missing target are diagnostics only:
/// neither is consulted to recover a semantic target during validation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RulesetReference {
    pub name: String,
    pub target: ResolvedOrMissing<RulesetId>,
}

fn resolutions_have_same_authority<T: PartialEq>(
    left: &ResolvedOrMissing<T>,
    right: &ResolvedOrMissing<T>,
) -> bool {
    match (left, right) {
        (ResolvedOrMissing::Resolved(left), ResolvedOrMissing::Resolved(right)) => left == right,
        (ResolvedOrMissing::Missing { .. }, ResolvedOrMissing::Missing { .. }) => true,
        _ => false,
    }
}

fn ruleset_references_have_same_authority(
    left: &RulesetReference,
    right: &RulesetReference,
) -> bool {
    resolutions_have_same_authority(&left.target, &right.target)
}

fn ruleset_reference_lists_have_same_authority(
    left: &[RulesetReference],
    right: &[RulesetReference],
) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left, right)| ruleset_references_have_same_authority(left, right))
}

/// Command-sensitive metadata for one exact core ruleset identity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RulesetMetadata {
    pub ruleset: RulesetId,
    pub availability: RulesetAvailability,
    pub kind: RulesetKind,
}

/// Extraction/display metadata omitted from the command-neutral function core.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionMetadata {
    pub function: FunctionId,
    /// The source override. `None` means the frontend's default extraction cost.
    pub extraction_cost: Option<u64>,
    pub unextractable: bool,
    /// Primitive calls in this function's lazy merge program use this context.
    pub merge_context: PrimitiveCallContext,
}

/// Full source rule evaluation vocabulary.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RuleEvaluationMode {
    Seminaive,
    Naive,
    UnsafeSeminaive,
}

/// Exact declaration identity for an index-shaped core body occurrence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RuleIndexUse {
    /// Zero-based ordinal in [`crate::frontend_snapshot::RuleSpec::body`].
    pub body_ordinal: u32,
    pub index: IndexId,
}

/// Source/effective metadata extending one exact core rule.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RuleMetadata {
    pub rule: RuleId,
    pub evaluation: RuleEvaluationMode,
    pub source_no_decomp: bool,
    pub include_subsumed: bool,
    pub query_context: PrimitiveCallContext,
    pub action_context: PrimitiveCallContext,
    /// One exact binding for every `IndexTable` body occurrence, in body order.
    pub index_uses: Vec<RuleIndexUse>,
}

/// An exact query call used by checks and `:until` conditions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum QueryCall {
    Table { target: FunctionId, read: ReadMode },
    Index { index: IndexId, read: ReadMode },
    Primitive { primitive: PrimitiveId },
}

/// One typed query atom. As in core rules, terms include the output term.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QueryAtom {
    pub call: QueryCall,
    pub terms: Vec<RuleTerm>,
}

/// A conjunctive existential query with one exact primitive call context.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FactQuery {
    pub primitive_context: PrimitiveCallContext,
    pub atoms: Vec<QueryAtom>,
}

/// Prefix-frozen result of recursively expanding a Run's ruleset.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RulesetExpansion {
    Complete {
        /// Ordered membership, preserving duplicates from combined children.
        rules: Vec<RuleId>,
    },
    Missing {
        /// Exact traversal path from the requested root through the first child
        /// unavailable at this Run prefix. The last element is the failure.
        path: Vec<RulesetReference>,
    },
}

fn ruleset_expansions_have_same_authority(
    left: &RulesetExpansion,
    right: &RulesetExpansion,
) -> bool {
    match (left, right) {
        (
            RulesetExpansion::Complete { rules: left },
            RulesetExpansion::Complete { rules: right },
        ) => left == right,
        (RulesetExpansion::Missing { path: left }, RulesetExpansion::Missing { path: right }) => {
            ruleset_reference_lists_have_same_authority(left, right)
        }
        _ => false,
    }
}

/// Whether a known late failure is returned to `Fail` or escapes as a panic in
/// the current reference runtime.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FrontendFailureClass {
    CatchableError,
    UncatchablePanic,
}

impl RulesetExpansion {
    /// Classify a frozen missing Run. A missing requested root is returned as a
    /// normal runtime error; a missing recursive combined child currently
    /// escapes through the reference ruleset index operation as a panic.
    pub fn missing_failure_class(
        &self,
        root: &ResolvedOrMissing<RulesetId>,
    ) -> Option<FrontendFailureClass> {
        match (self, root) {
            (Self::Missing { .. }, ResolvedOrMissing::Missing { .. }) => {
                Some(FrontendFailureClass::CatchableError)
            }
            (Self::Missing { .. }, ResolvedOrMissing::Resolved(_)) => {
                Some(FrontendFailureClass::UncatchablePanic)
            }
            (Self::Complete { .. }, _) => None,
        }
    }
}

/// A schedule tree retained without expanding repetition or saturation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Schedule {
    Sequence(Vec<Schedule>),
    Repeat {
        limit: u64,
        schedule: Box<Schedule>,
    },
    Saturate(Box<Schedule>),
    Run {
        /// Exact resolution outcome at this schedule's command prefix.
        ruleset: ResolvedOrMissing<RulesetId>,
        /// Exact successful membership or first missing recursive child path.
        expansion: RulesetExpansion,
        until: Option<FactQuery>,
    },
}

/// Which returned child-report flag controls a composite schedule.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ScheduleControlFlag {
    None,
    CanStopTrue,
    UpdatedFalse,
}

/// How a returned report flag is formed.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ScheduleFlagSource {
    Leaf,
    AnyCompletedChild,
    AllCompletedChildren,
}

/// Static report/control metadata derived from one schedule node.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ScheduleReportMetadata {
    /// Repeat and Saturate inspect the most recently completed immediate child,
    /// while still returning aggregate flags to their own parent.
    pub control: ScheduleControlFlag,
    pub returned_updated: ScheduleFlagSource,
    pub returned_can_stop: ScheduleFlagSource,
    /// Saturate is the only composite that mandates a first child execution.
    pub child_runs_at_least_once: bool,
    /// Sequence executes every child even if an earlier report can stop a loop.
    pub visits_every_sequence_child: bool,
}

impl Schedule {
    /// Return the exact current frontend report/control contract for this node.
    pub const fn report_metadata(&self) -> ScheduleReportMetadata {
        match self {
            Self::Run { .. } => ScheduleReportMetadata {
                control: ScheduleControlFlag::None,
                returned_updated: ScheduleFlagSource::Leaf,
                returned_can_stop: ScheduleFlagSource::Leaf,
                child_runs_at_least_once: true,
                visits_every_sequence_child: false,
            },
            Self::Sequence(_) => ScheduleReportMetadata {
                control: ScheduleControlFlag::None,
                returned_updated: ScheduleFlagSource::AnyCompletedChild,
                returned_can_stop: ScheduleFlagSource::AllCompletedChildren,
                child_runs_at_least_once: false,
                visits_every_sequence_child: true,
            },
            Self::Repeat { .. } => ScheduleReportMetadata {
                control: ScheduleControlFlag::CanStopTrue,
                returned_updated: ScheduleFlagSource::AnyCompletedChild,
                returned_can_stop: ScheduleFlagSource::AllCompletedChildren,
                child_runs_at_least_once: false,
                visits_every_sequence_child: false,
            },
            Self::Saturate(_) => ScheduleReportMetadata {
                control: ScheduleControlFlag::UpdatedFalse,
                returned_updated: ScheduleFlagSource::AnyCompletedChild,
                returned_can_stop: ScheduleFlagSource::AllCompletedChildren,
                child_runs_at_least_once: true,
                visits_every_sequence_child: false,
            },
        }
    }

    /// Count nodes iteratively. Repeat limits do not change the retained shape.
    pub fn node_count(&self) -> usize {
        let mut count = 0usize;
        let mut stack = vec![self];
        while let Some(schedule) = stack.pop() {
            count = count.saturating_add(1);
            match schedule {
                Self::Sequence(children) => stack.extend(children.iter().rev()),
                Self::Repeat { schedule, .. } | Self::Saturate(schedule) => stack.push(schedule),
                Self::Run { .. } => {}
            }
        }
        count
    }
}

/// One top-level schedule declaration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScheduleDecl {
    pub id: ScheduleId,
    pub schedule: Schedule,
}

/// One owned input payload shared by the execution and proof projections.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InputPayload {
    pub id: InputPayloadId,
    pub path: InputPathMetadata,
    /// Exact bytes from the one shared file read.
    pub bytes: Vec<u8>,
    /// Parsed content with no view-local nominal target identity.
    pub input: InputPayloadData,
}

/// Target-neutral typed input content shared by independently nominal views.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InputPayloadData {
    pub subtype: InputFunctionSubtype,
    pub declared_inputs: Vec<DeclaredInputSort>,
    pub declared_outputs: Vec<DeclaredInputSort>,
    pub effective_inputs: Vec<InputScalarKind>,
    pub effective_outputs: Vec<InputScalarKind>,
    pub rows: Vec<TypedInputRow>,
}

impl InputPayloadData {
    pub fn row_arity(&self) -> usize {
        self.effective_inputs.len() + self.effective_outputs.len()
    }
}

impl InputPayload {
    /// Preserve an already-read, target-neutral parsed file as shared content.
    /// Each [`ProgramCommand::Input`] supplies and validates its own exact
    /// view-local target plan.
    pub fn from_typed_file(id: InputPayloadId, file: TypedInputFile) -> Self {
        let TypedInputFile { path, bytes, input } = file;
        let schema = input.schema;
        Self {
            id,
            path,
            bytes,
            input: InputPayloadData {
                subtype: schema.subtype,
                declared_inputs: schema.declared_inputs,
                declared_outputs: schema.declared_outputs,
                effective_inputs: schema.effective_inputs,
                effective_outputs: schema.effective_outputs,
                rows: input.rows,
            },
        }
    }
}

/// Semantic role of one per-row fresh value in an encoded input batch.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InputFreshRole {
    Term,
    AstLeft,
    AstRight,
    FiatProof,
}

/// One exact, nominally typed fresh slot allocated for every payload row.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InputFreshSlot {
    pub id: InputFreshSlotId,
    pub role: InputFreshRole,
    pub sort: SortId,
}

/// Portable source of one value in an input-row operation template.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InputRowValue {
    PayloadColumn { role: InputColumnRole, column: u32 },
    Fresh(InputFreshSlotId),
    Unit,
}

/// Why an ordered input write exists.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InputWriteRole {
    Direct,
    LoweredAction,
    TermRelation,
    AstLeft,
    AstRight,
    Fiat,
    TermProof,
    View,
}

/// Exact frontend table operation performed for each payload row.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InputWriteMode {
    /// Insert the complete key/value row.
    Insert,
    /// Constructor call: look up keys or mint/insert a missing value.
    LookupOrInsert,
    /// Lowered custom-function action: set keys to supplied values.
    Set,
}

/// One ordered, backend-free per-row write template.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InputWrite {
    pub role: InputWriteRole,
    pub target: FunctionId,
    pub mode: InputWriteMode,
    pub values: Vec<InputRowValue>,
}

/// Exact view-local use of one target-neutral shared payload.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InputTargetPlan {
    /// Plain execution: exactly one constructor lookup-or-insert or custom row
    /// insert against the source function.
    Direct { write: InputWrite },
    /// Term/proof execution: fresh slots and writes are repeated in this exact
    /// order for every payload row. Exact term/view/AST/fiat/proof targets are
    /// stamped here; none are rediscovered from names or schema shape.
    Encoded {
        fresh_slots: Vec<InputFreshSlot>,
        writes: Vec<InputWrite>,
    },
    /// Proof-check projection of the logical input into one action per payload
    /// row: constructor call or custom Set, retaining the exact nominal target.
    LoweredActions { write: InputWrite },
}

/// Exact deterministic failure before an input payload can be published.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RejectedInputReason {
    IndexReadOnly(IndexId),
    MissingTarget {
        name: String,
    },
    FileRead {
        target: FunctionId,
        kind: IoErrorKind,
        message: String,
    },
    InvalidUtf8 {
        target: FunctionId,
        valid_up_to: usize,
        error_len: Option<usize>,
    },
    /// The exact target has a sort authority that the current input loader
    /// rejects by panicking before it opens the file. This is deliberately
    /// distinct from a catchable row-format parse failure.
    UnsupportedSchema {
        target: FunctionId,
        error: TypedInputParseError,
    },
    TypedParse {
        target: FunctionId,
        error: TypedInputParseError,
    },
}

impl RejectedInputReason {
    pub const fn failure_class(&self) -> FrontendFailureClass {
        match self {
            Self::MissingTarget { .. } | Self::UnsupportedSchema { .. } => {
                FrontendFailureClass::UncatchablePanic
            }
            Self::IndexReadOnly(_)
            | Self::FileRead { .. }
            | Self::InvalidUtf8 { .. }
            | Self::TypedParse { .. } => FrontendFailureClass::CatchableError,
        }
    }
}

/// Nested-Fail-only input failure. No payload ID is allocated because no
/// successfully read and typed shared content exists.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RejectedInput {
    pub requested_target: String,
    pub path: InputPathMetadata,
    pub reason: RejectedInputReason,
}

/// Exact identity of one parsed subcommand inside a physical source group.
///
/// Both components are nominal. Display text and byte-range contents never
/// participate in command provenance.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SourceSubcommandRef {
    pub group: SourceGroupId,
    pub subcommand: SourceSubcommandId,
}

impl SourceSubcommandRef {
    pub const fn new(group: SourceGroupId, subcommand: SourceSubcommandId) -> Self {
        Self { group, subcommand }
    }
}

/// One parsed subcommand retained by its dense group-local identity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceSubcommand {
    pub id: SourceSubcommandId,
}

/// One physical source transaction and its parsed subcommands.
///
/// `leading_trivia` followed by `command` is this group's exact contribution to
/// [`SourceDocument::contents`]. Parsed subcommands share that physical command
/// range while retaining separate dense identities for direct provenance.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceGroup {
    pub id: SourceGroupId,
    pub leading_trivia: Range<usize>,
    pub command: Range<usize>,
    pub subcommands: Vec<SourceSubcommand>,
}

/// Lossless source text and its physical transaction partition.
///
/// Source bytes occur exactly once, in `contents`. All other source structure is
/// expressed as UTF-8 byte ranges into that string. The final range owns every
/// byte after the last physical command, including trailing comments/trivia.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceDocument {
    pub logical_name: Option<String>,
    pub contents: String,
    pub groups: Vec<SourceGroup>,
    pub eof_trailer: Range<usize>,
}

/// Closed origin roles for commands introduced by frontend passes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GeneratedCommandRole {
    FrontendPrelude,
    MacroExpansion,
    FrontendDesugaring,
    GlobalElimination,
    TermEncoding,
    ProofHeader,
    ProofInstrumentation,
    ProofMaintenance,
    /// Mapper diagnostic only. Validation rejects this until the vocabulary is
    /// deliberately extended.
    Other(String),
}

/// Relationship between a finalized command and original source order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CommandOrigin {
    Source(SourceSubcommandRef),
    Generated {
        /// The exact triggering parsed subcommand, absent only for a global
        /// proof header or frontend prelude.
        trigger: Option<SourceSubcommandRef>,
        role: GeneratedCommandRole,
    },
}

impl CommandOrigin {
    fn source_trigger(&self) -> Option<SourceSubcommandRef> {
        match self {
            Self::Source(source) => Some(*source),
            Self::Generated { trigger, .. } => *trigger,
        }
    }

    fn direct_source(&self) -> Option<SourceSubcommandRef> {
        match self {
            Self::Source(source) => Some(*source),
            Self::Generated { .. } => None,
        }
    }
}

/// Stable display strings attached to one finalized resolved command.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CommandDisplay {
    /// Exact resolved rendering captured before runtime linking.
    pub resolved: String,
    /// Optional exact mapper comment explaining a generated command.
    pub comment: Option<String>,
}

/// Exact nominal catalog entry introduced at this command position.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CatalogDeclaration {
    Sort(SortId),
    Primitive(PrimitiveId),
    Function(FunctionId),
    Index(IndexId),
    Ruleset(RulesetId),
}

/// A top-level action program with one shared local scope.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ActionBlock {
    pub primitive_context: PrimitiveCallContext,
    pub actions: Vec<CoreAction>,
}

/// Prefix-resolved print-size target.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrintSizeTarget {
    Named {
        /// Exact source spelling. A missing result must retain this same name.
        requested_name: String,
        target: ResolvedOrMissing<FunctionId>,
    },
    All {
        /// Exact visible functions in final display order at this command.
        functions: Vec<FunctionId>,
    },
}

/// Print-statistics destinations are distinct because only the display form
/// produces an output event. File output remains structurally representable so
/// preflight can issue an exact error, but is not admitted by validation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrintStatsDestination {
    Display,
    File(PathBuf),
}

/// Unsupported command vocabulary retained only for fail-closed diagnostics.
/// A validated program never contains one of these variants.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum UnsupportedCommand {
    Push {
        levels: u64,
    },
    Pop {
        levels: u64,
    },
    Include {
        file: PathBuf,
    },
    Extract,
    PrintFunction {
        target: Option<FunctionId>,
        file: Option<PathBuf>,
    },
    Output {
        file: PathBuf,
    },
    ProveExists {
        target: Option<FunctionId>,
    },
    UserDefined {
        name: String,
    },
    CustomSchedule {
        name: String,
    },
    UnsupportedProofForm {
        description: String,
    },
    Other {
        description: String,
    },
}

impl UnsupportedCommand {
    fn kind(&self) -> &'static str {
        match self {
            Self::Push { .. } => "push",
            Self::Pop { .. } => "pop",
            Self::Include { .. } => "include",
            Self::Extract => "extract",
            Self::PrintFunction { .. } => "print-function",
            Self::Output { .. } => "output",
            Self::ProveExists { .. } => "prove-exists",
            Self::UserDefined { .. } => "user-defined command",
            Self::CustomSchedule { .. } => "custom schedule",
            Self::UnsupportedProofForm { .. } => "unsupported proof form",
            Self::Other { .. } => "unsupported command",
        }
    }
}

/// Nested `Fail` commands stop at the first returned, catchable error. A known
/// [`FrontendFailureClass::UncatchablePanic`] still escapes the block.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FailErrorPolicy {
    FirstError,
}

/// Nested command outputs are evaluated only for their effects and discarded.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FailOutputPolicy {
    SuppressAll,
}

/// One finalized command nested directly inside a [`FailBlock`].
///
/// There is deliberately no output ordinal: even a nested Run or print command
/// cannot publish its result outside the block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FailCommand {
    pub ordinal: FailCommandOrdinal,
    pub origin: CommandOrigin,
    pub display: CommandDisplay,
    pub command: ProgramCommand,
}

/// Recursive `Fail` body retaining reference first-error behavior exactly.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FailBlock {
    pub error_policy: FailErrorPolicy,
    pub output_policy: FailOutputPolicy,
    pub commands: Vec<FailCommand>,
}

/// Deterministic pre-lowering failure of a typed rule declaration.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RejectedRuleReason {
    MissingRuleset,
    CombinedRuleset,
}

/// A rule command whose target check fails before canonical core lowering.
///
/// It deliberately owns no [`RuleId`] or [`crate::frontend_snapshot::RuleSpec`]:
/// the current runtime rejects this command before its body/actions can have
/// semantic effects. Other rule failure classes are not representable here.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RejectedRuleDeclaration {
    pub rule_name: String,
    pub target: ResolvedOrMissing<RulesetId>,
    pub reason: RejectedRuleReason,
}

/// One admitted or explicitly rejected top-level command form.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProgramCommand {
    Catalog(CatalogDeclaration),
    /// Admitted `unstable-combined-ruleset` declaration. Children are ordered
    /// and may repeat. Their exact final-catalog identities may be declared
    /// later; recursive membership is resolved only when a Run is reached.
    CombinedRulesetDeclaration {
        ruleset: RulesetId,
        children: Vec<RulesetReference>,
    },
    RuleDeclaration(RuleId),
    RejectedRuleDeclaration(RejectedRuleDeclaration),
    ActionBlock(ActionBlock),
    Input {
        payload: InputPayloadId,
        plan: InputTargetPlan,
    },
    RejectedInput(RejectedInput),
    Run {
        schedule: ScheduleId,
    },
    Check {
        facts: FactQuery,
    },
    PrintSize(PrintSizeTarget),
    PrintStats(PrintStatsDestination),
    Fail(FailBlock),
    Unsupported(UnsupportedCommand),
}

/// One finalized command, including total/source/output order and rendering.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CommandEnvelope {
    pub ordinal: CommandOrdinal,
    pub origin: CommandOrigin,
    /// User-visible print event identity. Always `None` for [`ProgramCommand::Run`].
    pub output: Option<OutputOrdinal>,
    pub display: CommandDisplay,
    pub command: ProgramCommand,
}

/// One resolved program view with its own nominal identity namespace.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProgramView {
    pub core: ResolvedCoreSnapshot,
    pub indexes: Vec<IndexDecl>,
    pub ruleset_metadata: Vec<RulesetMetadata>,
    pub primitive_metadata: Vec<PrimitiveMetadata>,
    pub function_metadata: Vec<FunctionMetadata>,
    pub rule_metadata: Vec<RuleMetadata>,
    pub schedules: Vec<ScheduleDecl>,
    pub commands: Vec<CommandEnvelope>,
}

/// Whether the frontend produced only an execution view or a paired proof view.
#[derive(Clone, Debug, PartialEq, Eq)]
#[allow(clippy::large_enum_variant)]
pub enum ProgramStreams {
    ExecutionOnly {
        execution: ProgramView,
    },
    ProofInstrumented {
        execution: ProgramView,
        proof_check: ProgramView,
    },
}

impl ProgramStreams {
    pub fn execution(&self) -> &ProgramView {
        match self {
            Self::ExecutionOnly { execution } | Self::ProofInstrumented { execution, .. } => {
                execution
            }
        }
    }

    pub fn proof_check(&self) -> Option<&ProgramView> {
        match self {
            Self::ExecutionOnly { .. } => None,
            Self::ProofInstrumented { proof_check, .. } => Some(proof_check),
        }
    }
}

/// Complete owned frontend program envelope.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FrontendProgram {
    pub source: SourceDocument,
    pub inputs: Vec<InputPayload>,
    pub streams: ProgramStreams,
}

/// A fail-closed structural error in a program envelope.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProgramValidationError {
    pub path: String,
    pub message: String,
}

impl Display for ProgramValidationError {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}: {}", self.path, self.message)
    }
}

impl Error for ProgramValidationError {}

type ValidationResult<T = ()> = Result<T, ProgramValidationError>;

fn invalid(path: impl Into<String>, message: impl Into<String>) -> ProgramValidationError {
    ProgramValidationError {
        path: path.into(),
        message: message.into(),
    }
}

fn validate_dense_id(ordinal: u32, index: usize, arena: &str) -> ValidationResult {
    let expected = u32::try_from(index).map_err(|_| {
        invalid(
            arena,
            format!("{arena} arena exceeds the u32 identity domain"),
        )
    })?;
    if ordinal != expected {
        return Err(invalid(
            format!("{arena}[{index}]"),
            format!("expected dense ID {expected}, got {ordinal}"),
        ));
    }
    Ok(())
}

impl FrontendProgram {
    /// Validate both nominal views, shared inputs, provenance, prefix-sensitive
    /// schedules/prints, and output order without consulting a backend.
    pub fn validate(&self) -> ValidationResult {
        validate_source(&self.source)?;
        validate_inputs(&self.inputs, "inputs")?;

        match &self.streams {
            ProgramStreams::ExecutionOnly { execution } => {
                execution.validate("execution", &self.source, &self.inputs, true)?;
                validate_input_uses(
                    &execution.input_uses(InputProjection::Execution)?,
                    &self.inputs,
                    "execution.inputs",
                )?;
                validate_direct_source_coverage(
                    &self.source,
                    &execution.direct_source_uses(),
                    "execution",
                )?;
            }
            ProgramStreams::ProofInstrumented {
                execution,
                proof_check,
            } => {
                execution.validate("execution", &self.source, &self.inputs, true)?;
                proof_check.validate("proof_check", &self.source, &self.inputs, false)?;
                let execution_inputs = execution.input_uses(InputProjection::Execution)?;
                let proof_inputs = proof_check.input_uses(InputProjection::ProofCheck)?;
                validate_input_uses(&execution_inputs, &self.inputs, "execution.inputs")?;
                validate_input_uses(&proof_inputs, &self.inputs, "proof_check.inputs")?;
                if proof_inputs != execution_inputs {
                    return Err(invalid(
                        "streams.inputs",
                        "execution and proof-check projections do not share the exact payload sequence per source subcommand",
                    ));
                }
                validate_direct_source_coverage(
                    &self.source,
                    &execution.direct_source_uses(),
                    "execution",
                )?;
                validate_direct_source_coverage(
                    &self.source,
                    &proof_check.direct_source_uses(),
                    "proof_check",
                )?;
            }
        }

        Ok(())
    }
}

fn validate_direct_source_coverage(
    source: &SourceDocument,
    directly_used_sources: &BTreeSet<SourceSubcommandRef>,
    stream: &str,
) -> ValidationResult {
    for group in &source.groups {
        for subcommand in &group.subcommands {
            let source = SourceSubcommandRef::new(group.id, subcommand.id);
            if !directly_used_sources.contains(&source) {
                return Err(invalid(
                    format!(
                        "{stream}.source.groups[{}].subcommands[{}]",
                        group.id.ordinal(),
                        subcommand.id.ordinal()
                    ),
                    format!(
                        "parsed source subcommand has no direct Source origin in the {stream} retained view"
                    ),
                ));
            }
        }
    }
    Ok(())
}

fn validate_source(source: &SourceDocument) -> ValidationResult {
    let mut previous_end = 0usize;
    for (group_index, group) in source.groups.iter().enumerate() {
        validate_dense_id(group.id.ordinal(), group_index, "source.group")?;

        let trivia_path = format!("source.groups[{group_index}].leading_trivia");
        validate_source_range(&source.contents, &group.leading_trivia, &trivia_path, true)?;
        validate_partition_start(group.leading_trivia.start, previous_end, &trivia_path)?;
        previous_end = group.leading_trivia.end;

        let command_path = format!("source.groups[{group_index}].command");
        validate_source_range(&source.contents, &group.command, &command_path, false)?;
        validate_partition_start(group.command.start, previous_end, &command_path)?;
        previous_end = group.command.end;

        for (subcommand_index, subcommand) in group.subcommands.iter().enumerate() {
            validate_dense_id(
                subcommand.id.ordinal(),
                subcommand_index,
                &format!("source.groups[{group_index}].subcommand"),
            )?;
        }
    }

    validate_source_range(
        &source.contents,
        &source.eof_trailer,
        "source.eof_trailer",
        true,
    )?;
    validate_partition_start(source.eof_trailer.start, previous_end, "source.eof_trailer")?;
    if source.eof_trailer.end != source.contents.len() {
        return Err(invalid(
            "source.eof_trailer",
            format!(
                "EOF trailer must end at byte {}, got {}",
                source.contents.len(),
                source.eof_trailer.end
            ),
        ));
    }
    Ok(())
}

fn validate_source_range(
    contents: &str,
    range: &Range<usize>,
    path: &str,
    allow_empty: bool,
) -> ValidationResult {
    if range.start > range.end {
        return Err(invalid(path, "source byte range is inverted"));
    }
    if range.end > contents.len() {
        return Err(invalid(
            path,
            format!(
                "source byte range {}..{} exceeds contents length {}",
                range.start,
                range.end,
                contents.len()
            ),
        ));
    }
    if !contents.is_char_boundary(range.start) || !contents.is_char_boundary(range.end) {
        return Err(invalid(
            path,
            "source byte range endpoint is not a UTF-8 character boundary",
        ));
    }
    if !allow_empty && range.is_empty() {
        return Err(invalid(path, "physical source command range is empty"));
    }
    Ok(())
}

fn validate_partition_start(start: usize, expected: usize, path: &str) -> ValidationResult {
    if start != expected {
        let relation = if start < expected {
            "overlaps"
        } else {
            "leaves a gap after"
        };
        return Err(invalid(
            path,
            format!(
                "source partition {relation} the previous range: expected start {expected}, got {start}"
            ),
        ));
    }
    Ok(())
}

impl ProgramView {
    fn direct_source_uses(&self) -> BTreeSet<SourceSubcommandRef> {
        let mut uses = BTreeSet::new();
        for envelope in &self.commands {
            let mut stack = vec![(&envelope.command, &envelope.origin)];
            while let Some((command, origin)) = stack.pop() {
                if let Some(source) = origin.direct_source() {
                    uses.insert(source);
                }
                if let ProgramCommand::Fail(block) = command {
                    stack.extend(
                        block
                            .commands
                            .iter()
                            .rev()
                            .map(|nested| (&nested.command, &nested.origin)),
                    );
                }
            }
        }
        uses
    }

    fn validate(
        &self,
        path: &str,
        source: &SourceDocument,
        inputs: &[InputPayload],
        execution_outputs: bool,
    ) -> ValidationResult {
        self.core
            .validate()
            .map_err(|error| invalid(format!("{path}.core.{}", error.path), error.message))?;
        let catalog = Catalog::new(self, path)?;
        catalog.validate_extensions()?;
        catalog.validate_schedules()?;
        catalog.validate_commands(source, inputs, execution_outputs)?;
        Ok(())
    }

    fn input_uses(
        &self,
        projection: InputProjection,
    ) -> ValidationResult<BTreeMap<SourceSubcommandRef, Vec<InputPayloadId>>> {
        let mut uses = BTreeMap::<SourceSubcommandRef, Vec<InputPayloadId>>::new();
        for envelope in &self.commands {
            let mut stack = vec![(&envelope.command, &envelope.origin)];
            while let Some((command, origin)) = stack.pop() {
                match command {
                    ProgramCommand::Input { payload, plan } => {
                        let valid_projection = matches!(
                            (projection, plan),
                            (
                                InputProjection::Execution,
                                InputTargetPlan::Direct { .. } | InputTargetPlan::Encoded { .. }
                            ) | (
                                InputProjection::ProofCheck,
                                InputTargetPlan::LoweredActions { .. }
                            )
                        );
                        if !valid_projection {
                            return Err(invalid(
                                "streams.inputs",
                                "input target plan is attached to the wrong program projection",
                            ));
                        }
                        let source = origin.source_trigger().ok_or_else(|| {
                            invalid(
                                "streams.inputs",
                                "input command has no exact source-subcommand association",
                            )
                        })?;
                        uses.entry(source).or_default().push(*payload);
                    }
                    ProgramCommand::Fail(block) => {
                        stack.extend(
                            block
                                .commands
                                .iter()
                                .rev()
                                .map(|nested| (&nested.command, &nested.origin)),
                        );
                    }
                    ProgramCommand::Catalog(_)
                    | ProgramCommand::CombinedRulesetDeclaration { .. }
                    | ProgramCommand::RuleDeclaration(_)
                    | ProgramCommand::RejectedRuleDeclaration(_)
                    | ProgramCommand::ActionBlock(_)
                    | ProgramCommand::RejectedInput(_)
                    | ProgramCommand::Run { .. }
                    | ProgramCommand::Check { .. }
                    | ProgramCommand::PrintSize(_)
                    | ProgramCommand::PrintStats(_)
                    | ProgramCommand::Unsupported(_) => {}
                }
            }
        }
        Ok(uses)
    }
}

#[derive(Clone, Copy)]
enum InputProjection {
    Execution,
    ProofCheck,
}

fn validate_input_uses(
    uses: &BTreeMap<SourceSubcommandRef, Vec<InputPayloadId>>,
    inputs: &[InputPayload],
    path: &str,
) -> ValidationResult {
    let mut seen = BTreeSet::new();
    for payload in uses.values().flatten().copied() {
        if !seen.insert(payload) {
            return Err(invalid(
                path,
                "shared input payload is reused within one view",
            ));
        }
    }
    let expected = inputs
        .iter()
        .map(|payload| payload.id)
        .collect::<BTreeSet<_>>();
    if seen != expected {
        return Err(invalid(
            path,
            "input payload arena is not covered exactly once by this view",
        ));
    }
    Ok(())
}

struct Catalog<'a> {
    view: &'a ProgramView,
    path: String,
    indexes: BTreeMap<IndexId, &'a IndexDecl>,
    rule_metadata: BTreeMap<RuleId, &'a RuleMetadata>,
    ruleset_metadata: BTreeMap<RulesetId, &'a RulesetMetadata>,
}

impl<'a> Catalog<'a> {
    fn new(view: &'a ProgramView, path: &str) -> ValidationResult<Self> {
        let mut indexes = BTreeMap::new();
        for (index, declaration) in view.indexes.iter().enumerate() {
            validate_dense_id(declaration.id.ordinal(), index, &format!("{path}.index"))?;
            if indexes.insert(declaration.id, declaration).is_some() {
                return Err(invalid(
                    format!("{path}.index[{index}]"),
                    "duplicate index ID",
                ));
            }
        }

        let mut rule_metadata = BTreeMap::new();
        for (index, metadata) in view.rule_metadata.iter().enumerate() {
            let expected = view.core.rules.get(index).ok_or_else(|| {
                invalid(
                    format!("{path}.rule_metadata[{index}]"),
                    "metadata has no corresponding core rule",
                )
            })?;
            if metadata.rule != expected.id {
                return Err(invalid(
                    format!("{path}.rule_metadata[{index}].rule"),
                    format!(
                        "expected exact rule ID {}, got {}",
                        expected.id.ordinal(),
                        metadata.rule.ordinal()
                    ),
                ));
            }
            if rule_metadata.insert(metadata.rule, metadata).is_some() {
                return Err(invalid(
                    format!("{path}.rule_metadata[{index}]"),
                    "duplicate rule metadata",
                ));
            }
        }
        if view.rule_metadata.len() != view.core.rules.len() {
            return Err(invalid(
                format!("{path}.rule_metadata"),
                format!(
                    "expected {} entries, got {}",
                    view.core.rules.len(),
                    view.rule_metadata.len()
                ),
            ));
        }

        let mut ruleset_metadata = BTreeMap::new();
        for (index, metadata) in view.ruleset_metadata.iter().enumerate() {
            let expected = view.core.rulesets.get(index).ok_or_else(|| {
                invalid(
                    format!("{path}.ruleset_metadata[{index}]"),
                    "metadata has no corresponding core ruleset",
                )
            })?;
            if metadata.ruleset != expected.id {
                return Err(invalid(
                    format!("{path}.ruleset_metadata[{index}].ruleset"),
                    format!(
                        "expected exact ruleset ID {}, got {}",
                        expected.id.ordinal(),
                        metadata.ruleset.ordinal()
                    ),
                ));
            }
            if ruleset_metadata
                .insert(metadata.ruleset, metadata)
                .is_some()
            {
                return Err(invalid(
                    format!("{path}.ruleset_metadata[{index}]"),
                    "duplicate ruleset metadata",
                ));
            }
        }
        if view.ruleset_metadata.len() != view.core.rulesets.len() {
            return Err(invalid(
                format!("{path}.ruleset_metadata"),
                format!(
                    "expected {} entries, got {}",
                    view.core.rulesets.len(),
                    view.ruleset_metadata.len()
                ),
            ));
        }

        Ok(Self {
            view,
            path: path.to_owned(),
            indexes,
            rule_metadata,
            ruleset_metadata,
        })
    }

    fn function(
        &self,
        id: FunctionId,
        path: &str,
    ) -> ValidationResult<&'a crate::frontend_snapshot::FunctionConfig> {
        let index = usize::try_from(id.ordinal()).map_err(|_| {
            invalid(
                path,
                format!("function ID {} is not addressable", id.ordinal()),
            )
        })?;
        self.view
            .core
            .functions
            .get(index)
            .filter(|function| function.id == id)
            .ok_or_else(|| invalid(path, format!("dangling function ID {}", id.ordinal())))
    }

    fn primitive(
        &self,
        id: PrimitiveId,
        path: &str,
    ) -> ValidationResult<&'a crate::frontend_snapshot::PrimitiveDecl> {
        let index = usize::try_from(id.ordinal()).map_err(|_| {
            invalid(
                path,
                format!("primitive ID {} is not addressable", id.ordinal()),
            )
        })?;
        self.view
            .core
            .primitives
            .get(index)
            .filter(|primitive| primitive.id == id)
            .ok_or_else(|| invalid(path, format!("dangling primitive ID {}", id.ordinal())))
    }

    fn sort(
        &self,
        id: SortId,
        path: &str,
    ) -> ValidationResult<&'a crate::frontend_snapshot::SortDecl> {
        let index = usize::try_from(id.ordinal())
            .map_err(|_| invalid(path, format!("sort ID {} is not addressable", id.ordinal())))?;
        self.view
            .core
            .sorts
            .get(index)
            .filter(|sort| sort.id == id)
            .ok_or_else(|| invalid(path, format!("dangling sort ID {}", id.ordinal())))
    }

    fn rule(
        &self,
        id: RuleId,
        path: &str,
    ) -> ValidationResult<&'a crate::frontend_snapshot::RuleSpec> {
        let index = usize::try_from(id.ordinal())
            .map_err(|_| invalid(path, format!("rule ID {} is not addressable", id.ordinal())))?;
        self.view
            .core
            .rules
            .get(index)
            .filter(|rule| rule.id == id)
            .ok_or_else(|| invalid(path, format!("dangling rule ID {}", id.ordinal())))
    }

    fn ruleset(
        &self,
        id: RulesetId,
        path: &str,
    ) -> ValidationResult<&'a crate::frontend_snapshot::RulesetDecl> {
        let index = usize::try_from(id.ordinal()).map_err(|_| {
            invalid(
                path,
                format!("ruleset ID {} is not addressable", id.ordinal()),
            )
        })?;
        self.view
            .core
            .rulesets
            .get(index)
            .filter(|ruleset| ruleset.id == id)
            .ok_or_else(|| invalid(path, format!("dangling ruleset ID {}", id.ordinal())))
    }

    fn index(&self, id: IndexId, path: &str) -> ValidationResult<&'a IndexDecl> {
        self.indexes
            .get(&id)
            .copied()
            .ok_or_else(|| invalid(path, format!("dangling index ID {}", id.ordinal())))
    }

    fn ruleset_metadata(&self, id: RulesetId, path: &str) -> ValidationResult<&'a RulesetMetadata> {
        self.ruleset_metadata
            .get(&id)
            .copied()
            .ok_or_else(|| invalid(path, format!("dangling ruleset ID {}", id.ordinal())))
    }

    fn schedule(&self, id: ScheduleId, path: &str) -> ValidationResult<&'a ScheduleDecl> {
        let index = usize::try_from(id.ordinal()).map_err(|_| {
            invalid(
                path,
                format!("schedule ID {} is not addressable", id.ordinal()),
            )
        })?;
        self.view
            .schedules
            .get(index)
            .filter(|schedule| schedule.id == id)
            .ok_or_else(|| invalid(path, format!("dangling schedule ID {}", id.ordinal())))
    }

    fn validate_extensions(&self) -> ValidationResult {
        self.validate_primitive_metadata()?;
        self.validate_function_metadata()?;
        self.validate_indexes()?;
        self.validate_ruleset_metadata()?;
        self.validate_rule_metadata()?;
        Ok(())
    }

    fn validate_primitive_metadata(&self) -> ValidationResult {
        if self.view.primitive_metadata.len() != self.view.core.primitives.len() {
            return Err(invalid(
                format!("{}.primitive_metadata", self.path),
                format!(
                    "expected {} entries, got {}",
                    self.view.core.primitives.len(),
                    self.view.primitive_metadata.len()
                ),
            ));
        }
        for (index, metadata) in self.view.primitive_metadata.iter().enumerate() {
            let path = format!("{}.primitive_metadata[{index}]", self.path);
            let primitive = self.primitive(metadata.primitive, &format!("{path}.primitive"))?;
            if metadata.primitive.ordinal() != u32::try_from(index).unwrap_or(u32::MAX) {
                return Err(invalid(
                    &path,
                    "primitive metadata is not in exact dense primitive-ID order",
                ));
            }
            if metadata.valid_contexts.is_empty() {
                return Err(invalid(
                    format!("{path}.valid_contexts"),
                    "primitive has no valid call context",
                ));
            }
            let write_or_full = PrimitiveContextMask::WRITE | PrimitiveContextMask::FULL;
            let expected_contexts = match primitive.semantics {
                PrimitiveSemantics::NativeRaw(_) | PrimitiveSemantics::NativeScalar(_) => {
                    Some(PrimitiveContextMask::ALL)
                }
                PrimitiveSemantics::Fresh
                | PrimitiveSemantics::SetIfEmpty { .. }
                | PrimitiveSemantics::ViewColumn { .. } => Some(write_or_full),
                PrimitiveSemantics::Opaque { .. } => None,
            };
            if let Some(expected) = expected_contexts
                && metadata.valid_contexts != expected
            {
                return Err(invalid(
                    format!("{path}.valid_contexts"),
                    format!(
                        "context mask {} does not match closed primitive semantics (expected {})",
                        metadata.valid_contexts.bits(),
                        expected.bits()
                    ),
                ));
            }
            let expected_effects = match primitive.semantics {
                PrimitiveSemantics::NativeRaw(_) | PrimitiveSemantics::NativeScalar(_) => {
                    Some(PrimitiveEffectMask::NONE)
                }
                PrimitiveSemantics::Fresh => Some(PrimitiveEffectMask::MINTS_FRESH),
                PrimitiveSemantics::SetIfEmpty { .. } => {
                    Some(PrimitiveEffectMask::READS_STATE | PrimitiveEffectMask::WRITES_STATE)
                }
                PrimitiveSemantics::ViewColumn { .. } => Some(PrimitiveEffectMask::READS_STATE),
                PrimitiveSemantics::Opaque { .. } => None,
            };
            if let Some(expected) = expected_effects
                && metadata.effects != expected
            {
                return Err(invalid(
                    format!("{path}.effects"),
                    format!(
                        "effect mask {} does not match closed primitive semantics (expected {})",
                        metadata.effects.bits(),
                        expected.bits()
                    ),
                ));
            }
        }
        Ok(())
    }

    fn validate_function_metadata(&self) -> ValidationResult {
        if self.view.function_metadata.len() != self.view.core.functions.len() {
            return Err(invalid(
                format!("{}.function_metadata", self.path),
                format!(
                    "expected {} entries, got {}",
                    self.view.core.functions.len(),
                    self.view.function_metadata.len()
                ),
            ));
        }
        for (index, metadata) in self.view.function_metadata.iter().enumerate() {
            let path = format!("{}.function_metadata[{index}]", self.path);
            let function = self.function(metadata.function, &format!("{path}.function"))?;
            if metadata.function.ordinal() != u32::try_from(index).unwrap_or(u32::MAX) {
                return Err(invalid(
                    &path,
                    "function metadata is not in exact dense function-ID order",
                ));
            }
            if metadata.merge_context != PrimitiveCallContext::Write {
                return Err(invalid(
                    format!("{path}.merge_context"),
                    "function merge context must preserve the frontend Write context",
                ));
            }
            for node in &function.merge.values {
                if let MergeValueOperation::Primitive { primitive, .. } = node.operation {
                    let primitive = self.primitive(
                        primitive,
                        &format!("{path}.merge.values[{}].primitive", node.id.ordinal()),
                    )?;
                    let primitive_metadata =
                        &self.view.primitive_metadata[usize::try_from(primitive.id.ordinal())
                            .map_err(|_| {
                                invalid(&path, "merge primitive ID is not addressable")
                            })?];
                    if !primitive_metadata
                        .valid_contexts
                        .contains(metadata.merge_context)
                    {
                        return Err(invalid(
                            format!("{path}.merge_context"),
                            format!(
                                "primitive {} is not valid in {:?} merge context",
                                primitive.id.ordinal(),
                                metadata.merge_context
                            ),
                        ));
                    }
                }
            }
        }
        Ok(())
    }

    fn validate_indexes(&self) -> ValidationResult {
        for declaration in &self.view.indexes {
            let path = format!("{}.index[{}]", self.path, declaration.id.ordinal());
            let target = self.function(declaration.target, &format!("{path}.target"))?;
            if declaration.any_of.is_empty() {
                return Err(invalid(format!("{path}.any_of"), "index any_of is empty"));
            }
            let mut expected_sort = None;
            for (choice, column) in declaration.any_of.iter().copied().enumerate() {
                let sort = target.schema.get(column).copied().ok_or_else(|| {
                    invalid(
                        format!("{path}.any_of[{choice}]"),
                        format!("indexed column {column} is out of range"),
                    )
                })?;
                match expected_sort {
                    None => expected_sort = Some(sort),
                    Some(expected) if expected == sort => {}
                    Some(_) => {
                        return Err(invalid(
                            format!("{path}.any_of[{choice}]"),
                            "indexed columns do not have one exact nominal sort",
                        ));
                    }
                }
            }
        }
        Ok(())
    }

    fn validate_ruleset_metadata(&self) -> ValidationResult {
        let mut implicit_default = None;
        for (index, metadata) in self.view.ruleset_metadata.iter().enumerate() {
            let path = format!("{}.ruleset_metadata[{index}]", self.path);
            let declaration = self.ruleset(metadata.ruleset, &format!("{path}.ruleset"))?;
            if metadata.availability == RulesetAvailability::ImplicitDefault {
                if implicit_default.replace(metadata.ruleset).is_some() {
                    return Err(invalid(
                        format!("{path}.availability"),
                        "more than one implicit default ruleset identity",
                    ));
                }
                if !matches!(&metadata.kind, RulesetKind::Concrete) {
                    return Err(invalid(
                        format!("{path}.availability"),
                        "implicit default ruleset is not concrete",
                    ));
                }
            }
            match &metadata.kind {
                RulesetKind::Concrete => {}
                RulesetKind::Combined { children } => {
                    if !declaration.rules.is_empty() {
                        return Err(invalid(
                            format!("{path}.kind"),
                            "combined ruleset has direct core rule membership",
                        ));
                    }
                    for (child_index, child) in children.iter().enumerate() {
                        self.validate_ruleset_reference(
                            child,
                            &format!("{path}.children[{child_index}]"),
                        )?;
                    }
                }
            }
        }
        if implicit_default.is_none() {
            return Err(invalid(
                format!("{}.ruleset_metadata", self.path),
                "missing explicit implicit-default ruleset identity",
            ));
        }

        for rule in &self.view.core.rules {
            if !matches!(
                &self
                    .ruleset_metadata(rule.ruleset, "rule ruleset metadata")?
                    .kind,
                RulesetKind::Concrete
            ) {
                return Err(invalid(
                    format!("{}.rule[{}].ruleset", self.path, rule.id.ordinal()),
                    "rule belongs directly to a combined ruleset",
                ));
            }
        }

        // Validate the ordered combined-ruleset graph without recursive calls;
        // declaration-order command validation is a second, prefix-local gate.
        let mut states = vec![0u8; self.view.core.rulesets.len()];
        for root in &self.view.core.rulesets {
            let root_index = usize::try_from(root.id.ordinal())
                .map_err(|_| invalid(&self.path, "ruleset ID is not addressable"))?;
            if states[root_index] == 2 {
                continue;
            }
            let mut stack = vec![(root.id, false)];
            while let Some((ruleset, exiting)) = stack.pop() {
                let index = usize::try_from(ruleset.ordinal())
                    .map_err(|_| invalid(&self.path, "ruleset ID is not addressable"))?;
                if exiting {
                    states[index] = 2;
                    continue;
                }
                match states[index] {
                    2 => continue,
                    1 => {
                        return Err(invalid(
                            format!("{}.ruleset_metadata[{index}]", self.path),
                            "combined ruleset dependency cycle",
                        ));
                    }
                    0 => {}
                    _ => unreachable!("closed ruleset traversal state"),
                }
                states[index] = 1;
                stack.push((ruleset, true));
                if let RulesetKind::Combined { children } =
                    &self.ruleset_metadata(ruleset, "ruleset traversal")?.kind
                {
                    for child in children.iter().rev() {
                        let ResolvedOrMissing::Resolved(child) = child.target else {
                            continue;
                        };
                        let child_index = usize::try_from(child.ordinal()).map_err(|_| {
                            invalid(&self.path, "child ruleset ID is not addressable")
                        })?;
                        if states[child_index] == 1 {
                            return Err(invalid(
                                format!("{}.ruleset_metadata[{index}]", self.path),
                                "combined ruleset dependency cycle",
                            ));
                        }
                        if states[child_index] == 0 {
                            stack.push((child, false));
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn validate_ruleset_reference(
        &self,
        reference: &RulesetReference,
        path: &str,
    ) -> ValidationResult {
        match &reference.target {
            ResolvedOrMissing::Resolved(ruleset) => {
                self.ruleset(*ruleset, &format!("{path}.target"))?;
            }
            ResolvedOrMissing::Missing { name } => {
                if reference.name.is_empty() || name.is_empty() {
                    return Err(invalid(
                        path,
                        "missing combined child has an empty diagnostic name",
                    ));
                }
            }
        }
        Ok(())
    }

    fn validate_rule_metadata(&self) -> ValidationResult {
        for metadata in &self.view.rule_metadata {
            let rule = self.rule(metadata.rule, &format!("{}.rule_metadata.rule", self.path))?;
            let path = format!("{}.rule_metadata[{}]", self.path, rule.id.ordinal());

            if metadata.source_no_decomp && !rule.no_decomp {
                return Err(invalid(
                    format!("{path}.source_no_decomp"),
                    "source no-decomp cannot map to an effective false flag",
                ));
            }
            if metadata.evaluation == RuleEvaluationMode::Naive && rule.seminaive {
                return Err(invalid(
                    format!("{path}.evaluation"),
                    "a Naive source rule cannot have effective seminaive execution",
                ));
            }

            let requires_read = !rule.seminaive
                || matches!(
                    metadata.evaluation,
                    RuleEvaluationMode::Naive | RuleEvaluationMode::UnsafeSeminaive
                );
            let expected_query = if requires_read {
                PrimitiveCallContext::Read
            } else {
                PrimitiveCallContext::Pure
            };
            let expected_action = if requires_read {
                PrimitiveCallContext::Full
            } else {
                PrimitiveCallContext::Write
            };
            if metadata.query_context != expected_query
                || metadata.action_context != expected_action
            {
                return Err(invalid(
                    &path,
                    format!(
                        "rule contexts must be {:?}/{:?}, got {:?}/{:?}",
                        expected_query,
                        expected_action,
                        metadata.query_context,
                        metadata.action_context
                    ),
                ));
            }

            let mut expected_index_body_ordinals = Vec::new();
            for (body_index, atom) in rule.body.iter().enumerate() {
                let atom_path = format!("{path}.body[{body_index}]");
                match atom.call {
                    RuleBodyCall::Table { read, .. } | RuleBodyCall::IndexTable { read, .. } => {
                        let expected = if metadata.include_subsumed {
                            ReadMode::All
                        } else {
                            ReadMode::Live
                        };
                        if read != expected {
                            return Err(invalid(
                                &atom_path,
                                "table read mode is not the exact source include_subsumed lowering",
                            ));
                        }
                    }
                    RuleBodyCall::Primitive { primitive } => {
                        self.validate_primitive_context(
                            primitive,
                            metadata.query_context,
                            &atom_path,
                        )?;
                    }
                }
                if matches!(atom.call, RuleBodyCall::IndexTable { .. }) {
                    expected_index_body_ordinals.push(body_index);
                }
            }

            if metadata.index_uses.len() != expected_index_body_ordinals.len() {
                return Err(invalid(
                    format!("{path}.index_uses"),
                    format!(
                        "expected {} exact index bindings, got {}",
                        expected_index_body_ordinals.len(),
                        metadata.index_uses.len()
                    ),
                ));
            }
            for (use_index, (binding, expected_body)) in metadata
                .index_uses
                .iter()
                .zip(expected_index_body_ordinals)
                .enumerate()
            {
                let binding_path = format!("{path}.index_uses[{use_index}]");
                if usize::try_from(binding.body_ordinal).ok() != Some(expected_body) {
                    return Err(invalid(
                        &binding_path,
                        format!("expected body ordinal {expected_body}"),
                    ));
                }
                let declaration = self.index(binding.index, &format!("{binding_path}.index"))?;
                let RuleBodyCall::IndexTable {
                    target, ref any_of, ..
                } = rule.body[expected_body].call
                else {
                    return Err(invalid(
                        &binding_path,
                        "binding does not name an index atom",
                    ));
                };
                if declaration.target != target || declaration.any_of != *any_of {
                    return Err(invalid(
                        &binding_path,
                        "exact index declaration does not match the core index occurrence",
                    ));
                }
            }

            for (action_index, action) in rule.actions.iter().enumerate() {
                if let CoreAction::Let {
                    call: RuleActionCall::Primitive(primitive),
                    ..
                } = action
                {
                    self.validate_primitive_context(
                        *primitive,
                        metadata.action_context,
                        &format!("{path}.actions[{action_index}]"),
                    )?;
                }
            }
        }
        Ok(())
    }

    fn validate_primitive_context(
        &self,
        primitive: PrimitiveId,
        context: PrimitiveCallContext,
        path: &str,
    ) -> ValidationResult {
        self.primitive(primitive, &format!("{path}.primitive"))?;
        let index = usize::try_from(primitive.ordinal())
            .map_err(|_| invalid(path, "primitive ID is not addressable"))?;
        let metadata = &self.view.primitive_metadata[index];
        if !metadata.valid_contexts.contains(context) {
            return Err(invalid(
                path,
                format!(
                    "primitive {} is not valid in {context:?} context",
                    primitive.ordinal()
                ),
            ));
        }
        Ok(())
    }

    fn validate_schedules(&self) -> ValidationResult {
        for (index, declaration) in self.view.schedules.iter().enumerate() {
            validate_dense_id(
                declaration.id.ordinal(),
                index,
                &format!("{}.schedule", self.path),
            )?;
            let mut node_ordinal = 0usize;
            let mut stack = vec![&declaration.schedule];
            while let Some(schedule) = stack.pop() {
                let path = format!(
                    "{}.schedule[{}].nodes[{node_ordinal}]",
                    self.path,
                    declaration.id.ordinal()
                );
                node_ordinal = node_ordinal.saturating_add(1);
                match schedule {
                    Schedule::Sequence(children) => stack.extend(children.iter().rev()),
                    Schedule::Repeat { schedule, .. } | Schedule::Saturate(schedule) => {
                        stack.push(schedule)
                    }
                    Schedule::Run {
                        ruleset,
                        expansion,
                        until,
                    } => {
                        if let ResolvedOrMissing::Missing { name } = ruleset
                            && name.is_empty()
                        {
                            return Err(invalid(
                                format!("{path}.ruleset"),
                                "missing ruleset name is empty",
                            ));
                        }
                        match expansion {
                            RulesetExpansion::Missing { path: missing_path } => {
                                self.validate_ruleset_path(
                                    ruleset,
                                    missing_path,
                                    &format!("{path}.expansion"),
                                )?;
                            }
                            RulesetExpansion::Complete { rules } => {
                                let ResolvedOrMissing::Resolved(ruleset) = ruleset else {
                                    return Err(invalid(
                                        format!("{path}.expansion"),
                                        "missing root ruleset has a complete expansion",
                                    ));
                                };
                                let metadata =
                                    self.ruleset_metadata(*ruleset, &format!("{path}.ruleset"))?;
                                let concrete = matches!(&metadata.kind, RulesetKind::Concrete);
                                let mut unique = BTreeSet::new();
                                for (rule_index, rule) in rules.iter().copied().enumerate() {
                                    let rule = self.rule(
                                        rule,
                                        &format!("{path}.expansion.rules[{rule_index}]"),
                                    )?;
                                    if concrete && rule.ruleset != *ruleset {
                                        return Err(invalid(
                                            format!("{path}.expansion.rules[{rule_index}]"),
                                            "Run member belongs to a different concrete ruleset",
                                        ));
                                    }
                                    if !concrete
                                        && !self.ruleset_reaches_concrete(
                                            *ruleset,
                                            rule.ruleset,
                                            &format!("{path}.expansion.rules[{rule_index}]"),
                                        )?
                                    {
                                        return Err(invalid(
                                            format!("{path}.expansion.rules[{rule_index}]"),
                                            "Run member is outside the combined ruleset graph",
                                        ));
                                    }
                                    if concrete && !unique.insert(rule.id) {
                                        return Err(invalid(
                                            format!("{path}.expansion.rules[{rule_index}]"),
                                            "duplicate concrete Run member",
                                        ));
                                    }
                                }
                            }
                        }
                        if let Some(until) = until {
                            self.validate_query(until, &format!("{path}.until"))?;
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn validate_ruleset_path(
        &self,
        root: &ResolvedOrMissing<RulesetId>,
        path: &[RulesetReference],
        error_path: &str,
    ) -> ValidationResult {
        let first = path
            .first()
            .ok_or_else(|| invalid(error_path, "missing ruleset path is empty"))?;
        match root {
            ResolvedOrMissing::Resolved(root) => {
                if first.target != ResolvedOrMissing::Resolved(*root) {
                    return Err(invalid(
                        error_path,
                        "missing path does not begin at the resolved Run root",
                    ));
                }
            }
            ResolvedOrMissing::Missing { name } => {
                if name.is_empty() || path.len() != 1 {
                    return Err(invalid(
                        error_path,
                        "missing root Run must retain one exact root path segment",
                    ));
                }
            }
        }
        for (index, reference) in path.iter().enumerate() {
            self.validate_ruleset_reference(reference, &format!("{error_path}.path[{index}]"))?;
            if let Some(next) = path.get(index + 1) {
                let ResolvedOrMissing::Resolved(parent) = reference.target else {
                    return Err(invalid(
                        format!("{error_path}.path[{index}]"),
                        "missing path continues after a final-catalog missing segment",
                    ));
                };
                let RulesetKind::Combined { children } =
                    &self.ruleset_metadata(parent, error_path)?.kind
                else {
                    return Err(invalid(
                        format!("{error_path}.path[{index}]"),
                        "missing path continues through a concrete ruleset",
                    ));
                };
                if !children
                    .iter()
                    .any(|child| ruleset_references_have_same_authority(child, next))
                {
                    return Err(invalid(
                        format!("{error_path}.path[{}]", index + 1),
                        "missing path is not an exact combined child authority edge",
                    ));
                }
            }
        }
        Ok(())
    }

    fn ruleset_reaches_concrete(
        &self,
        root: RulesetId,
        target: RulesetId,
        path: &str,
    ) -> ValidationResult<bool> {
        let mut seen = BTreeSet::new();
        let mut stack = vec![root];
        while let Some(ruleset) = stack.pop() {
            if !seen.insert(ruleset) {
                continue;
            }
            match &self.ruleset_metadata(ruleset, path)?.kind {
                RulesetKind::Concrete => {
                    if ruleset == target {
                        return Ok(true);
                    }
                }
                RulesetKind::Combined { children } => {
                    stack.extend(
                        children
                            .iter()
                            .rev()
                            .filter_map(|child| match child.target {
                                ResolvedOrMissing::Resolved(ruleset) => Some(ruleset),
                                ResolvedOrMissing::Missing { .. } => None,
                            }),
                    );
                }
            }
        }
        Ok(false)
    }

    fn validate_commands(
        &self,
        source: &SourceDocument,
        inputs: &[InputPayload],
        execution_outputs: bool,
    ) -> ValidationResult {
        let mut prefix = PrefixState::new(self);
        let mut source_order = SourceOrder::default();
        let mut next_output = 0u32;
        let mut used_schedules = BTreeSet::new();

        for (index, envelope) in self.view.commands.iter().enumerate() {
            let path = format!("{}.commands[{index}]", self.path);
            validate_dense_id(
                envelope.ordinal.ordinal(),
                index,
                &format!("{}.command", self.path),
            )?;
            if envelope.display.resolved.is_empty() {
                return Err(invalid(
                    format!("{path}.display.resolved"),
                    "resolved command rendering is empty",
                ));
            }
            validate_ordered_origin(&envelope.origin, source, &mut source_order, &path)?;

            self.validate_command(
                &envelope.command,
                &mut prefix,
                inputs,
                source,
                &mut source_order,
                &mut used_schedules,
                envelope.origin.source_trigger(),
                &path,
            )?;

            let produces_output = matches!(
                envelope.command,
                ProgramCommand::PrintSize(_)
                    | ProgramCommand::PrintStats(PrintStatsDestination::Display)
            );
            if execution_outputs && produces_output {
                let Some(output) = envelope.output else {
                    return Err(invalid(
                        format!("{path}.output"),
                        "output-producing execution command has no output ordinal",
                    ));
                };
                if output.ordinal() != next_output {
                    return Err(invalid(
                        format!("{path}.output"),
                        format!(
                            "expected dense output ordinal {next_output}, got {}",
                            output.ordinal()
                        ),
                    ));
                }
                next_output = next_output.checked_add(1).ok_or_else(|| {
                    invalid(format!("{path}.output"), "output ordinal space exhausted")
                })?;
            } else if envelope.output.is_some() {
                return Err(invalid(
                    format!("{path}.output"),
                    "command cannot publish an output in this stream",
                ));
            }
        }
        if used_schedules.len() != self.view.schedules.len() {
            return Err(invalid(
                format!("{}.schedules", self.path),
                "every schedule identity must be referenced by exactly one Run command",
            ));
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn validate_command(
        &self,
        command: &ProgramCommand,
        prefix: &mut PrefixState,
        inputs: &[InputPayload],
        source: &SourceDocument,
        source_order: &mut SourceOrder,
        used_schedules: &mut BTreeSet<ScheduleId>,
        enclosing_source: Option<SourceSubcommandRef>,
        path: &str,
    ) -> ValidationResult {
        // Fail blocks may nest arbitrarily; preserve their sequential catalog
        // effects while validating without using the Rust call stack.
        struct PendingCommand<'a> {
            command: &'a ProgramCommand,
            path: String,
            nested: Option<(&'a FailCommand, usize, String)>,
            inside_fail: bool,
            enclosing_source: Option<SourceSubcommandRef>,
        }

        let mut stack = vec![PendingCommand {
            command,
            path: path.to_owned(),
            nested: None,
            inside_fail: false,
            enclosing_source,
        }];
        while let Some(pending) = stack.pop() {
            let PendingCommand {
                command,
                path,
                nested,
                inside_fail,
                enclosing_source,
            } = pending;
            let mut current_source = enclosing_source;
            if let Some((nested, index, arena)) = nested {
                validate_dense_id(nested.ordinal.ordinal(), index, &arena)?;
                if nested.display.resolved.is_empty() {
                    return Err(invalid(
                        format!("{path}.display.resolved"),
                        "resolved nested command rendering is empty",
                    ));
                }
                validate_ordered_origin(&nested.origin, source, source_order, &path)?;
                if nested.origin.source_trigger() != enclosing_source {
                    return Err(invalid(
                        format!("{path}.origin"),
                        "nested Fail command is not associated with its enclosing source trigger",
                    ));
                }
                current_source = nested.origin.source_trigger();
            }
            if inside_fail
                && matches!(
                    command,
                    ProgramCommand::Catalog(_)
                        | ProgramCommand::CombinedRulesetDeclaration { .. }
                        | ProgramCommand::RuleDeclaration(_)
                )
            {
                return Err(invalid(
                    &path,
                    "Fail blocks containing static catalog or membership mutations require guarded activation and are not admitted",
                ));
            }
            match command {
                ProgramCommand::Catalog(declaration) => {
                    prefix.declare(self, *declaration, &path)?;
                }
                ProgramCommand::CombinedRulesetDeclaration { ruleset, children } => {
                    prefix.declare_combined(self, *ruleset, children, &path)?;
                }
                ProgramCommand::RuleDeclaration(rule) => {
                    let rule = self.rule(*rule, &format!("{path}.rule"))?;
                    prefix.validate_rule(self, rule, &path)?;
                    if !prefix.rules.insert(rule.id) {
                        return Err(invalid(&path, "rule is declared more than once"));
                    }
                }
                ProgramCommand::RejectedRuleDeclaration(declaration) => {
                    prefix.validate_rejected_rule(self, declaration, &path)?;
                }
                ProgramCommand::ActionBlock(block) => {
                    self.validate_action_block(block, prefix, &format!("{path}.actions"))?;
                }
                ProgramCommand::Input { payload, plan } => {
                    let payload_index = usize::try_from(payload.ordinal())
                        .map_err(|_| invalid(&path, "input payload ID is not addressable"))?;
                    let payload = inputs
                        .get(payload_index)
                        .filter(|candidate| candidate.id == *payload)
                        .ok_or_else(|| {
                            invalid(
                                format!("{path}.payload"),
                                format!("dangling input payload ID {}", payload.ordinal()),
                            )
                        })?;
                    self.validate_input_plan(payload, plan, prefix, &path)?;
                }
                ProgramCommand::RejectedInput(rejected) => {
                    if !inside_fail {
                        return Err(invalid(
                            &path,
                            "RejectedInput is admitted only inside a Fail block",
                        ));
                    }
                    prefix.validate_rejected_input(self, rejected, &path)?;
                }
                ProgramCommand::Run { schedule } => {
                    let schedule = self.schedule(*schedule, &format!("{path}.schedule"))?;
                    if !used_schedules.insert(schedule.id) {
                        return Err(invalid(
                            &path,
                            format!(
                                "schedule ID {} is referenced by more than one Run command",
                                schedule.id.ordinal()
                            ),
                        ));
                    }
                    prefix.validate_schedule(self, &schedule.schedule, &path)?;
                }
                ProgramCommand::Check { facts } => {
                    self.validate_query(facts, &format!("{path}.facts"))?;
                    prefix.validate_query(self, facts, &path)?;
                }
                ProgramCommand::PrintSize(target) => match target {
                    PrintSizeTarget::Named {
                        requested_name,
                        target: ResolvedOrMissing::Resolved(target),
                    } => {
                        if requested_name.is_empty() {
                            return Err(invalid(
                                format!("{path}.requested_name"),
                                "resolved print-size target has an empty diagnostic name",
                            ));
                        }
                        prefix.validate_print_size_function(self, *target, &path)?;
                    }
                    PrintSizeTarget::Named {
                        requested_name,
                        target: ResolvedOrMissing::Missing { name },
                    } => {
                        if requested_name.is_empty() || name.is_empty() {
                            return Err(invalid(
                                &path,
                                "missing print-size target has an empty diagnostic name",
                            ));
                        }
                    }
                    PrintSizeTarget::All { functions } => {
                        prefix.validate_all_print_size_functions(self, functions, &path)?;
                    }
                },
                ProgramCommand::PrintStats(PrintStatsDestination::Display) => {}
                ProgramCommand::PrintStats(PrintStatsDestination::File(file)) => {
                    return Err(invalid(
                        &path,
                        format!(
                            "file-targeted print-stats is unsupported: {}",
                            file.display()
                        ),
                    ));
                }
                ProgramCommand::Fail(block) => {
                    let arena = format!("{path}.fail.command");
                    stack.extend(
                        block
                            .commands
                            .iter()
                            .enumerate()
                            .rev()
                            .map(|(index, nested)| PendingCommand {
                                command: &nested.command,
                                path: format!("{path}.fail.commands[{index}]"),
                                nested: Some((nested, index, arena.clone())),
                                inside_fail: true,
                                enclosing_source: current_source,
                            }),
                    );
                }
                ProgramCommand::Unsupported(unsupported) => {
                    return Err(invalid(
                        &path,
                        format!("{} is not admitted", unsupported.kind()),
                    ));
                }
            }
        }
        Ok(())
    }

    fn validate_input_plan(
        &self,
        payload: &InputPayload,
        plan: &InputTargetPlan,
        prefix: &PrefixState,
        path: &str,
    ) -> ValidationResult {
        let payload_values = payload
            .input
            .effective_inputs
            .iter()
            .enumerate()
            .map(|(column, _)| (InputColumnRole::Input, column))
            .chain(
                payload
                    .input
                    .effective_outputs
                    .iter()
                    .enumerate()
                    .map(|(column, _)| (InputColumnRole::Output, column)),
            )
            .map(|(role, column)| {
                u32::try_from(column)
                    .map(|column| InputRowValue::PayloadColumn { role, column })
                    .map_err(|_| invalid(path, "input payload column space exceeds u32"))
            })
            .collect::<ValidationResult<Vec<_>>>()?;
        match plan {
            InputTargetPlan::Direct { write } => {
                if write.role != InputWriteRole::Direct {
                    return Err(invalid(
                        path,
                        "Direct input write has the wrong semantic role",
                    ));
                }
                self.validate_source_input_target(payload, write.target, path)?;
                let expected_mode = match payload.input.subtype {
                    InputFunctionSubtype::Constructor => InputWriteMode::LookupOrInsert,
                    InputFunctionSubtype::Custom => InputWriteMode::Insert,
                };
                if write.mode != expected_mode || write.values != payload_values {
                    return Err(invalid(
                        path,
                        "Direct input does not preserve its exact per-row source operation",
                    ));
                }
                self.validate_input_write(write, payload, &[], prefix, path)?;
            }
            InputTargetPlan::LoweredActions { write } => {
                if write.role != InputWriteRole::LoweredAction {
                    return Err(invalid(
                        path,
                        "lowered input action has the wrong semantic role",
                    ));
                }
                self.validate_source_input_target(payload, write.target, path)?;
                let expected_mode = match payload.input.subtype {
                    InputFunctionSubtype::Constructor => InputWriteMode::LookupOrInsert,
                    InputFunctionSubtype::Custom => InputWriteMode::Set,
                };
                if write.mode != expected_mode || write.values != payload_values {
                    return Err(invalid(
                        path,
                        "lowered input does not preserve its exact per-row action template",
                    ));
                }
                self.validate_input_write(write, payload, &[], prefix, path)?;
            }
            InputTargetPlan::Encoded {
                fresh_slots,
                writes,
            } => {
                let expected_roles: &[InputFreshRole] = match fresh_slots.len() {
                    1 => &[InputFreshRole::Term],
                    4 => &[
                        InputFreshRole::Term,
                        InputFreshRole::AstLeft,
                        InputFreshRole::AstRight,
                        InputFreshRole::FiatProof,
                    ],
                    _ => {
                        return Err(invalid(
                            format!("{path}.fresh_slots"),
                            "encoded input must retain one term slot or the four proof slots",
                        ));
                    }
                };
                for (index, (slot, expected_role)) in
                    fresh_slots.iter().zip(expected_roles).enumerate()
                {
                    validate_dense_id(slot.id.ordinal(), index, &format!("{path}.fresh_slot"))?;
                    if slot.role != *expected_role {
                        return Err(invalid(
                            format!("{path}.fresh_slots[{index}].role"),
                            "encoded input fresh-slot role is out of exact allocation order",
                        ));
                    }
                    self.sort(slot.sort, &format!("{path}.fresh_slots[{index}].sort"))?;
                }

                let proofs = fresh_slots.len() == 4;
                let expected_roles = if proofs {
                    match payload.input.subtype {
                        InputFunctionSubtype::Constructor => vec![
                            InputWriteRole::TermRelation,
                            InputWriteRole::AstLeft,
                            InputWriteRole::AstRight,
                            InputWriteRole::Fiat,
                            InputWriteRole::TermProof,
                            InputWriteRole::View,
                        ],
                        InputFunctionSubtype::Custom => vec![
                            InputWriteRole::TermRelation,
                            InputWriteRole::AstLeft,
                            InputWriteRole::AstRight,
                            InputWriteRole::Fiat,
                            InputWriteRole::View,
                        ],
                    }
                } else {
                    vec![InputWriteRole::TermRelation, InputWriteRole::View]
                };
                if writes.iter().map(|write| write.role).collect::<Vec<_>>() != expected_roles {
                    return Err(invalid(
                        format!("{path}.writes"),
                        "encoded input writes are not in exact term/proof/view order",
                    ));
                }

                let term_write = &writes[0];
                if !self
                    .function(term_write.target, &format!("{path}.writes[0].target"))?
                    .internal_term_node
                {
                    return Err(invalid(
                        format!("{path}.writes[0].target"),
                        "encoded term-relation target is not an exact internal term node",
                    ));
                }
                let view_index = writes.len() - 1;
                if self
                    .function(
                        writes[view_index].target,
                        &format!("{path}.writes[{view_index}].target"),
                    )?
                    .term_constructor
                    != Some(term_write.target)
                {
                    return Err(invalid(
                        format!("{path}.writes[{view_index}].target"),
                        "encoded view does not point back to the exact term-relation target",
                    ));
                }
                if proofs && writes[1].target != writes[2].target {
                    return Err(invalid(
                        format!("{path}.writes[2].target"),
                        "encoded AST writes do not share the exact nominal target",
                    ));
                }

                let term = InputFreshSlotId::new(0);
                let mut expected_values = Vec::with_capacity(writes.len());
                let mut term_values = payload_values.clone();
                term_values.extend([InputRowValue::Fresh(term), InputRowValue::Unit]);
                expected_values.push(term_values);
                if proofs {
                    let ast_left = InputFreshSlotId::new(1);
                    let ast_right = InputFreshSlotId::new(2);
                    let proof = InputFreshSlotId::new(3);
                    expected_values.push(vec![
                        InputRowValue::Fresh(term),
                        InputRowValue::Fresh(ast_left),
                        InputRowValue::Unit,
                    ]);
                    expected_values.push(vec![
                        InputRowValue::Fresh(term),
                        InputRowValue::Fresh(ast_right),
                        InputRowValue::Unit,
                    ]);
                    expected_values.push(vec![
                        InputRowValue::Fresh(ast_left),
                        InputRowValue::Fresh(ast_right),
                        InputRowValue::Fresh(proof),
                        InputRowValue::Unit,
                    ]);
                    if payload.input.subtype == InputFunctionSubtype::Constructor {
                        expected_values.push(vec![
                            InputRowValue::Fresh(term),
                            InputRowValue::Fresh(proof),
                        ]);
                    }
                }
                let mut view_values = payload_values;
                if payload.input.subtype == InputFunctionSubtype::Constructor {
                    view_values.push(InputRowValue::Fresh(term));
                }
                view_values.push(if proofs {
                    InputRowValue::Fresh(InputFreshSlotId::new(3))
                } else {
                    InputRowValue::Unit
                });
                expected_values.push(view_values);

                for (index, (write, expected)) in writes.iter().zip(expected_values).enumerate() {
                    if write.mode != InputWriteMode::Insert || write.values != expected {
                        return Err(invalid(
                            format!("{path}.writes[{index}]"),
                            "encoded input write does not match its exact row template",
                        ));
                    }
                    self.validate_input_write(
                        write,
                        payload,
                        fresh_slots,
                        prefix,
                        &format!("{path}.writes[{index}]"),
                    )?;
                }
            }
        }
        Ok(())
    }

    fn validate_source_input_target(
        &self,
        payload: &InputPayload,
        target: FunctionId,
        path: &str,
    ) -> ValidationResult {
        let input = &payload.input;
        let function = self.function(target, &format!("{path}.target"))?;
        let expected_subtype = match function.kind {
            FunctionKind::Constructor => InputFunctionSubtype::Constructor,
            FunctionKind::Custom => InputFunctionSubtype::Custom,
        };
        if input.subtype != expected_subtype {
            return Err(invalid(
                path,
                "input subtype does not match the view-local exact target",
            ));
        }
        let expected_inputs = &function.schema[..function.n_keys()];
        let expected_outputs = function.value_sorts();
        if input.declared_inputs.len() != expected_inputs.len()
            || input.declared_outputs.len() != expected_outputs.len()
        {
            return Err(invalid(path, "declared input schema arity mismatch"));
        }
        for (column, (declared, sort)) in input
            .declared_inputs
            .iter()
            .zip(expected_inputs)
            .enumerate()
        {
            let sort = self.sort(*sort, path)?;
            if declared.authority != input_sort_authority(sort) {
                return Err(invalid(
                    format!("{path}.declared_inputs[{column}]"),
                    "declared input sort does not match the view-local exact sort authority",
                ));
            }
        }
        for (column, (declared, sort)) in input
            .declared_outputs
            .iter()
            .zip(expected_outputs)
            .enumerate()
        {
            let sort = self.sort(*sort, path)?;
            if declared.authority != input_sort_authority(sort) {
                return Err(invalid(
                    format!("{path}.declared_outputs[{column}]"),
                    "declared output sort does not match the view-local exact sort authority",
                ));
            }
        }
        let effective_outputs = match input.subtype {
            InputFunctionSubtype::Constructor => &[][..],
            InputFunctionSubtype::Custom => expected_outputs,
        };
        validate_input_scalar_kinds(
            &input.effective_inputs,
            expected_inputs,
            self,
            &format!("{path}.effective_inputs"),
        )?;
        validate_input_scalar_kinds(
            &input.effective_outputs,
            effective_outputs,
            self,
            &format!("{path}.effective_outputs"),
        )?;
        Ok(())
    }

    fn validate_input_write(
        &self,
        write: &InputWrite,
        payload: &InputPayload,
        fresh_slots: &[InputFreshSlot],
        prefix: &PrefixState,
        path: &str,
    ) -> ValidationResult {
        prefix.require_function(write.target, &format!("{path}.target"))?;
        let function = self.function(write.target, &format!("{path}.target"))?;
        let expected_sorts = match write.mode {
            InputWriteMode::Insert | InputWriteMode::Set => function.schema.as_slice(),
            InputWriteMode::LookupOrInsert => &function.schema[..function.n_keys()],
        };
        if write.values.len() != expected_sorts.len() {
            return Err(invalid(
                path,
                "input write row arity does not match exact target",
            ));
        }
        for (index, (value, expected_sort)) in write.values.iter().zip(expected_sorts).enumerate() {
            let actual_sort = match value {
                InputRowValue::PayloadColumn { role, column } => {
                    let column = usize::try_from(*column)
                        .map_err(|_| invalid(path, "input payload column is not addressable"))?;
                    let kinds = match role {
                        InputColumnRole::Input => &payload.input.effective_inputs,
                        InputColumnRole::Output => &payload.input.effective_outputs,
                    };
                    let kind = kinds.get(column).copied().ok_or_else(|| {
                        invalid(
                            format!("{path}.values[{index}]"),
                            "dangling payload column reference",
                        )
                    })?;
                    if !input_kind_matches_sort(kind, self.sort(*expected_sort, path)?) {
                        return Err(invalid(
                            format!("{path}.values[{index}]"),
                            "payload scalar kind does not match exact target sort",
                        ));
                    }
                    continue;
                }
                InputRowValue::Fresh(slot) => {
                    let slot_index = usize::try_from(slot.ordinal())
                        .map_err(|_| invalid(path, "input fresh slot is not addressable"))?;
                    fresh_slots
                        .get(slot_index)
                        .filter(|candidate| candidate.id == *slot)
                        .map(|slot| slot.sort)
                        .ok_or_else(|| {
                            invalid(
                                format!("{path}.values[{index}]"),
                                "dangling input fresh-slot reference",
                            )
                        })?
                }
                InputRowValue::Unit => self.unit_sort(path)?,
            };
            if actual_sort != *expected_sort {
                return Err(invalid(
                    format!("{path}.values[{index}]"),
                    "input row value has the wrong exact nominal sort",
                ));
            }
        }
        Ok(())
    }

    fn validate_query(&self, query: &FactQuery, path: &str) -> ValidationResult {
        if query.primitive_context != PrimitiveCallContext::Read {
            return Err(invalid(
                format!("{path}.primitive_context"),
                "check and until queries must preserve the frontend Read context",
            ));
        }
        let mut variables = VariableCatalog::default();
        for (atom_index, atom) in query.atoms.iter().enumerate() {
            let atom_path = format!("{path}.atoms[{atom_index}]");
            match atom.call {
                QueryCall::Table { read, .. } | QueryCall::Index { read, .. }
                    if read != ReadMode::All =>
                {
                    return Err(invalid(
                        &atom_path,
                        "check and until table reads must include subsumed rows",
                    ));
                }
                QueryCall::Table { .. } | QueryCall::Index { .. } | QueryCall::Primitive { .. } => {
                }
            }
            let expected = match atom.call {
                QueryCall::Table { target, .. } => self
                    .function(target, &format!("{atom_path}.target"))?
                    .schema
                    .clone(),
                QueryCall::Index { index, .. } => {
                    let declaration = self.index(index, &format!("{atom_path}.index"))?;
                    let target =
                        self.function(declaration.target, &format!("{atom_path}.index.target"))?;
                    let probe_sort = target.schema[declaration.any_of[0]];
                    let unit = self.unit_sort(&atom_path)?;
                    let mut expected = Vec::with_capacity(target.schema.len() + 2);
                    expected.push(probe_sort);
                    expected.extend(target.schema.iter().copied());
                    expected.push(unit);
                    expected
                }
                QueryCall::Primitive { primitive } => {
                    let primitive = self.primitive(primitive, &format!("{atom_path}.primitive"))?;
                    self.validate_primitive_context(
                        primitive.id,
                        query.primitive_context,
                        &atom_path,
                    )?;
                    let mut expected = primitive.input.clone();
                    expected.push(primitive.output);
                    expected
                }
            };
            validate_terms(self, &mut variables, &atom.terms, &expected, &atom_path)?;
            if let QueryCall::Index { .. } = atom.call {
                let trailing = atom.terms.last().expect("validated index arity");
                if !matches!(
                    trailing,
                    RuleTerm::Literal(TypedLiteral {
                        value: LiteralValue::Unit,
                        ..
                    })
                ) {
                    return Err(invalid(
                        &atom_path,
                        "index query atom must end in canonical typed Unit",
                    ));
                }
            }
        }
        variables.validate_dense(path)?;
        validate_query_reachability(query, path)
    }

    fn validate_action_block(
        &self,
        block: &ActionBlock,
        prefix: &PrefixState,
        path: &str,
    ) -> ValidationResult {
        if block.primitive_context != PrimitiveCallContext::Full {
            return Err(invalid(
                format!("{path}.primitive_context"),
                "top-level action blocks must preserve the frontend Full context",
            ));
        }
        let mut variables = VariableCatalog::default();
        for (action_index, action) in block.actions.iter().enumerate() {
            let action_path = format!("{path}[{action_index}]");
            collect_action_terms(self, &mut variables, action, &action_path)?;
        }
        variables.validate_dense(path)?;

        let mut bound = BTreeSet::new();
        for (action_index, action) in block.actions.iter().enumerate() {
            let action_path = format!("{path}[{action_index}]");
            match action {
                CoreAction::Let {
                    binding,
                    call,
                    arguments,
                } => {
                    ensure_terms_bound(arguments, &bound, &action_path)?;
                    let (inputs, output) = match call {
                        RuleActionCall::Table(target) => {
                            prefix.require_function(*target, &action_path)?;
                            let function = self.function(*target, &action_path)?;
                            if function.n_values != 1 {
                                return Err(invalid(
                                    &action_path,
                                    "action lookup of tuple-output function is not admitted",
                                ));
                            }
                            (
                                function.schema[..function.n_keys()].to_vec(),
                                function.value_sorts()[0],
                            )
                        }
                        RuleActionCall::Primitive(primitive) => {
                            let primitive = self.primitive(*primitive, &action_path)?;
                            self.validate_primitive_context(
                                primitive.id,
                                block.primitive_context,
                                &action_path,
                            )?;
                            (primitive.input.clone(), primitive.output)
                        }
                    };
                    validate_term_sorts(arguments, &inputs, &action_path)?;
                    if binding.sort != output {
                        return Err(invalid(&action_path, "action let output sort mismatch"));
                    }
                    if !bound.insert(binding.id) {
                        return Err(invalid(&action_path, "action rebinds a local variable"));
                    }
                }
                CoreAction::LetValue { binding, value } => {
                    ensure_term_bound(value, &bound, &action_path)?;
                    if binding.sort != value.sort() {
                        return Err(invalid(&action_path, "let-value sort mismatch"));
                    }
                    if !bound.insert(binding.id) {
                        return Err(invalid(&action_path, "action rebinds a local variable"));
                    }
                }
                CoreAction::Set {
                    target,
                    keys,
                    values,
                } => {
                    prefix.require_function(*target, &action_path)?;
                    let function = self.function(*target, &action_path)?;
                    ensure_terms_bound(keys, &bound, &action_path)?;
                    ensure_terms_bound(values, &bound, &action_path)?;
                    validate_term_sorts(keys, &function.schema[..function.n_keys()], &action_path)?;
                    validate_term_sorts(values, function.value_sorts(), &action_path)?;
                }
                CoreAction::Change { kind, target, keys } => {
                    prefix.require_function(*target, &action_path)?;
                    let function = self.function(*target, &action_path)?;
                    if *kind == ChangeKind::Subsume && !function.can_subsume {
                        return Err(invalid(
                            &action_path,
                            "Subsume target does not support subsumption",
                        ));
                    }
                    ensure_terms_bound(keys, &bound, &action_path)?;
                    validate_term_sorts(keys, &function.schema[..function.n_keys()], &action_path)?;
                }
                CoreAction::Union { left, right } => {
                    ensure_term_bound(left, &bound, &action_path)?;
                    ensure_term_bound(right, &bound, &action_path)?;
                    if left.sort() != right.sort()
                        || !matches!(
                            self.sort(left.sort(), &action_path)?.semantics,
                            SortSemantics::Eq
                        )
                        || !self.sort(left.sort(), &action_path)?.unionable
                    {
                        return Err(invalid(
                            &action_path,
                            "Union requires one exact unionable Eq sort",
                        ));
                    }
                }
                CoreAction::Panic { .. } => {}
            }
        }
        Ok(())
    }

    fn unit_sort(&self, path: &str) -> ValidationResult<SortId> {
        self.view
            .core
            .sorts
            .iter()
            .find(|sort| matches!(sort.semantics, SortSemantics::Unit))
            .map(|sort| sort.id)
            .ok_or_else(|| invalid(path, "snapshot has no nominal Unit sort"))
    }
}

fn validate_origin(
    origin: &CommandOrigin,
    source: &SourceDocument,
    path: &str,
) -> ValidationResult {
    let validate_group = |group: SourceGroupId| {
        let index = usize::try_from(group.ordinal())
            .map_err(|_| invalid(path, "source group ID is not addressable"))?;
        source
            .groups
            .get(index)
            .filter(|candidate| candidate.id == group)
            .ok_or_else(|| {
                invalid(
                    format!("{path}.origin"),
                    format!("dangling source group ID {}", group.ordinal()),
                )
            })
    };

    match origin {
        CommandOrigin::Source(source_ref) => {
            let group = validate_group(source_ref.group)?;
            let index = usize::try_from(source_ref.subcommand.ordinal())
                .map_err(|_| invalid(path, "source subcommand ID is not addressable"))?;
            group
                .subcommands
                .get(index)
                .filter(|candidate| candidate.id == source_ref.subcommand)
                .ok_or_else(|| {
                    invalid(
                        format!("{path}.origin"),
                        format!(
                            "dangling source subcommand ID {} in group {}",
                            source_ref.subcommand.ordinal(),
                            source_ref.group.ordinal()
                        ),
                    )
                })?;
            Ok(())
        }
        CommandOrigin::Generated { trigger, role } => {
            if let Some(source_ref) = trigger {
                let group = validate_group(source_ref.group)?;
                let index = usize::try_from(source_ref.subcommand.ordinal())
                    .map_err(|_| invalid(path, "source subcommand ID is not addressable"))?;
                group
                    .subcommands
                    .get(index)
                    .filter(|candidate| candidate.id == source_ref.subcommand)
                    .ok_or_else(|| {
                        invalid(
                            format!("{path}.origin"),
                            format!(
                                "dangling source subcommand ID {} in group {}",
                                source_ref.subcommand.ordinal(),
                                source_ref.group.ordinal()
                            ),
                        )
                    })?;
            }
            if let GeneratedCommandRole::Other(description) = role {
                return Err(invalid(
                    format!("{path}.origin.role"),
                    format!("unadmitted generated-command role: {description}"),
                ));
            }
            let source_less = matches!(
                role,
                GeneratedCommandRole::FrontendPrelude | GeneratedCommandRole::ProofHeader
            );
            if source_less != trigger.is_none() {
                return Err(invalid(
                    format!("{path}.origin"),
                    "generated-command role has the wrong source-trigger association",
                ));
            }
            Ok(())
        }
    }
}

#[derive(Default)]
struct SourceOrder {
    previous_source: Option<SourceSubcommandRef>,
    saw_source_associated: bool,
}

fn validate_ordered_origin(
    origin: &CommandOrigin,
    source: &SourceDocument,
    order: &mut SourceOrder,
    path: &str,
) -> ValidationResult {
    validate_origin(origin, source, path)?;
    if let Some(current) = origin.source_trigger() {
        if order
            .previous_source
            .is_some_and(|previous| current < previous)
        {
            return Err(invalid(
                format!("{path}.origin"),
                "source trigger moved backwards",
            ));
        }
        order.previous_source = Some(current);
        order.saw_source_associated = true;
    } else if order.saw_source_associated {
        return Err(invalid(
            format!("{path}.origin"),
            "source-less generated command appears after source-associated commands",
        ));
    }
    Ok(())
}

#[derive(Clone)]
struct PrefixState {
    sorts: BTreeSet<SortId>,
    primitives: BTreeSet<PrimitiveId>,
    functions: BTreeSet<FunctionId>,
    function_order: Vec<FunctionId>,
    indexes: BTreeSet<IndexId>,
    rulesets: BTreeSet<RulesetId>,
    rules: BTreeSet<RuleId>,
}

impl PrefixState {
    fn new(catalog: &Catalog<'_>) -> Self {
        let rulesets = catalog
            .view
            .ruleset_metadata
            .iter()
            .filter(|metadata| metadata.availability == RulesetAvailability::ImplicitDefault)
            .map(|metadata| metadata.ruleset)
            .collect();
        Self {
            sorts: BTreeSet::new(),
            primitives: BTreeSet::new(),
            functions: BTreeSet::new(),
            function_order: Vec::new(),
            indexes: BTreeSet::new(),
            rulesets,
            rules: BTreeSet::new(),
        }
    }

    fn declare(
        &mut self,
        catalog: &Catalog<'_>,
        declaration: CatalogDeclaration,
        path: &str,
    ) -> ValidationResult {
        let inserted = match declaration {
            CatalogDeclaration::Sort(id) => {
                catalog.sort(id, &format!("{path}.sort"))?;
                self.sorts.insert(id)
            }
            CatalogDeclaration::Primitive(id) => {
                catalog.primitive(id, &format!("{path}.primitive"))?;
                self.primitives.insert(id)
            }
            CatalogDeclaration::Function(id) => {
                catalog.function(id, &format!("{path}.function"))?;
                let inserted = self.functions.insert(id);
                if inserted {
                    self.function_order.push(id);
                }
                inserted
            }
            CatalogDeclaration::Index(id) => {
                let index = catalog.index(id, &format!("{path}.index"))?;
                self.require_function(index.target, &format!("{path}.index.target"))?;
                self.indexes.insert(id)
            }
            CatalogDeclaration::Ruleset(id) => {
                catalog.ruleset(id, &format!("{path}.ruleset"))?;
                let metadata = catalog.ruleset_metadata(id, &format!("{path}.ruleset"))?;
                if metadata.availability != RulesetAvailability::Declared
                    || !matches!(&metadata.kind, RulesetKind::Concrete)
                {
                    return Err(invalid(
                        path,
                        "ruleset requires its exact declared concrete availability command",
                    ));
                }
                self.rulesets.insert(id)
            }
        };
        if !inserted {
            return Err(invalid(path, "catalog identity is declared more than once"));
        }
        Ok(())
    }

    fn declare_combined(
        &mut self,
        catalog: &Catalog<'_>,
        ruleset: RulesetId,
        children: &[RulesetReference],
        path: &str,
    ) -> ValidationResult {
        catalog.ruleset(ruleset, &format!("{path}.ruleset"))?;
        let RulesetKind::Combined { children: expected } = &catalog
            .ruleset_metadata(ruleset, &format!("{path}.ruleset"))?
            .kind
        else {
            return Err(invalid(
                path,
                "combined declaration names a concrete ruleset",
            ));
        };
        if catalog
            .ruleset_metadata(ruleset, &format!("{path}.ruleset"))?
            .availability
            != RulesetAvailability::Declared
        {
            return Err(invalid(
                path,
                "combined declaration names an implicitly available ruleset",
            ));
        }
        if !ruleset_reference_lists_have_same_authority(children, expected) {
            return Err(invalid(
                format!("{path}.children"),
                "combined declaration does not retain the exact ordered child authorities",
            ));
        }
        if !self.rulesets.insert(ruleset) {
            return Err(invalid(path, "catalog identity is declared more than once"));
        }
        Ok(())
    }

    fn require_function(&self, function: FunctionId, path: &str) -> ValidationResult {
        if !self.functions.contains(&function) {
            return Err(invalid(
                path,
                format!(
                    "function ID {} is not available at this command prefix",
                    function.ordinal()
                ),
            ));
        }
        Ok(())
    }

    fn validate_print_size_function(
        &self,
        catalog: &Catalog<'_>,
        target: FunctionId,
        path: &str,
    ) -> ValidationResult {
        self.require_function(target, path)?;
        let declaration = catalog.function(target, path)?;
        if declaration.internal_hidden || declaration.internal_let {
            return Err(invalid(
                path,
                "print-size target is an exact hidden or let function identity",
            ));
        }
        Ok(())
    }

    fn validate_all_print_size_functions(
        &self,
        catalog: &Catalog<'_>,
        functions: &[FunctionId],
        path: &str,
    ) -> ValidationResult {
        let mut expected = Vec::new();
        for function in self.function_order.iter().copied() {
            let declaration = catalog.function(function, path)?;
            if !declaration.internal_hidden && !declaration.internal_let {
                expected.push((declaration.display.print_size_name.clone(), function));
            }
        }
        expected.sort();
        let expected = expected
            .into_iter()
            .map(|(_, function)| function)
            .collect::<Vec<_>>();
        let actual = functions.iter().copied().collect::<BTreeSet<_>>();
        if actual.len() != functions.len() {
            return Err(invalid(
                path,
                "all-functions print-size list repeats an exact ID",
            ));
        }
        if actual != expected.iter().copied().collect::<BTreeSet<_>>() {
            return Err(invalid(
                path,
                "all-functions print-size list does not contain every exact prefix-visible public ID",
            ));
        }
        if functions != expected {
            return Err(invalid(
                path,
                "all-functions print-size list is not in lexical display-name order",
            ));
        }
        Ok(())
    }

    fn validate_rule(
        &self,
        catalog: &Catalog<'_>,
        rule: &crate::frontend_snapshot::RuleSpec,
        path: &str,
    ) -> ValidationResult {
        if !self.rulesets.contains(&rule.ruleset) {
            return Err(invalid(
                path,
                format!(
                    "ruleset ID {} is not available at this command prefix",
                    rule.ruleset.ordinal()
                ),
            ));
        }
        let metadata = catalog
            .rule_metadata
            .get(&rule.id)
            .copied()
            .ok_or_else(|| {
                invalid(
                    path,
                    format!("missing metadata for rule {}", rule.id.ordinal()),
                )
            })?;
        let index_bindings = metadata
            .index_uses
            .iter()
            .map(|binding| (binding.body_ordinal, binding.index))
            .collect::<BTreeMap<_, _>>();
        for (body_index, atom) in rule.body.iter().enumerate() {
            match atom.call {
                RuleBodyCall::Table { target, .. } => self.require_function(target, path)?,
                RuleBodyCall::IndexTable { .. } => {
                    let body_index = u32::try_from(body_index)
                        .map_err(|_| invalid(path, "rule body ordinal space exhausted"))?;
                    let index = index_bindings.get(&body_index).ok_or_else(|| {
                        invalid(path, "rule index occurrence has no exact index binding")
                    })?;
                    if !self.indexes.contains(index) {
                        return Err(invalid(
                            path,
                            format!(
                                "index ID {} is not available at this command prefix",
                                index.ordinal()
                            ),
                        ));
                    }
                }
                RuleBodyCall::Primitive { .. } => {}
            }
        }
        for action in &rule.actions {
            match action {
                CoreAction::Let {
                    call: RuleActionCall::Table(target),
                    ..
                }
                | CoreAction::Set { target, .. }
                | CoreAction::Change { target, .. } => self.require_function(*target, path)?,
                CoreAction::Let {
                    call: RuleActionCall::Primitive(_),
                    ..
                }
                | CoreAction::LetValue { .. }
                | CoreAction::Union { .. }
                | CoreAction::Panic { .. } => {}
            }
        }
        Ok(())
    }

    fn validate_rejected_rule(
        &self,
        catalog: &Catalog<'_>,
        declaration: &RejectedRuleDeclaration,
        path: &str,
    ) -> ValidationResult {
        if declaration.rule_name.is_empty() {
            return Err(invalid(
                format!("{path}.rule_name"),
                "rejected rule diagnostic name is empty",
            ));
        }
        match (&declaration.reason, &declaration.target) {
            (RejectedRuleReason::MissingRuleset, ResolvedOrMissing::Missing { name }) => {
                if name.is_empty() {
                    return Err(invalid(
                        path,
                        "missing ruleset has an empty diagnostic name",
                    ));
                }
            }
            (RejectedRuleReason::CombinedRuleset, ResolvedOrMissing::Resolved(ruleset)) => {
                if !self.rulesets.contains(ruleset) {
                    return Err(invalid(
                        path,
                        "combined rejected-rule target is not prefix-visible",
                    ));
                }
                if !matches!(
                    &catalog.ruleset_metadata(*ruleset, path)?.kind,
                    RulesetKind::Combined { .. }
                ) {
                    return Err(invalid(
                        path,
                        "CombinedRuleset rejection names a concrete ruleset",
                    ));
                }
            }
            _ => {
                return Err(invalid(
                    path,
                    "rejected rule reason does not match its exact target outcome",
                ));
            }
        }
        Ok(())
    }

    fn validate_rejected_input(
        &self,
        catalog: &Catalog<'_>,
        rejected: &RejectedInput,
        path: &str,
    ) -> ValidationResult {
        if rejected.requested_target.is_empty() {
            return Err(invalid(
                format!("{path}.requested_target"),
                "rejected input target name is empty",
            ));
        }
        match &rejected.reason {
            RejectedInputReason::IndexReadOnly(index) => {
                if !self.indexes.contains(index) {
                    return Err(invalid(path, "read-only input index is not prefix-visible"));
                }
                catalog.index(*index, path)?;
            }
            RejectedInputReason::MissingTarget { name } => {
                if name.is_empty() {
                    return Err(invalid(
                        path,
                        "missing input target has an empty diagnostic name",
                    ));
                }
            }
            RejectedInputReason::FileRead { target, .. }
            | RejectedInputReason::InvalidUtf8 { target, .. } => {
                self.require_function(*target, path)?;
                catalog.function(*target, path)?;
            }
            RejectedInputReason::UnsupportedSchema { target, error } => {
                self.require_function(*target, path)?;
                self.validate_unsupported_input_schema(catalog, *target, error, path)?;
            }
            RejectedInputReason::TypedParse { target, error } => {
                self.require_function(*target, path)?;
                catalog.function(*target, path)?;
                if !matches!(
                    error,
                    TypedInputParseError::MalformedField { .. }
                        | TypedInputParseError::MissingField { .. }
                        | TypedInputParseError::ExtraField { .. }
                        | TypedInputParseError::SourcePositionOverflow
                ) {
                    return Err(invalid(
                        path,
                        "TypedParse carries a schema-authority failure instead of a catchable row-format failure",
                    ));
                }
            }
        }
        Ok(())
    }

    fn validate_unsupported_input_schema(
        &self,
        catalog: &Catalog<'_>,
        target: FunctionId,
        error: &TypedInputParseError,
        path: &str,
    ) -> ValidationResult {
        let TypedInputParseError::UnsupportedSort {
            role,
            column_ordinal,
            ..
        } = error
        else {
            return Err(invalid(
                path,
                "UnsupportedSchema does not carry an exact unsupported-sort authority failure",
            ));
        };
        let function = catalog.function(target, path)?;
        let sort = match *role {
            InputColumnRole::Input => function
                .schema
                .get(..function.n_keys())
                .and_then(|sorts| sorts.get(*column_ordinal)),
            InputColumnRole::Output if function.kind == FunctionKind::Custom => {
                function.value_sorts().get(*column_ordinal)
            }
            InputColumnRole::Output => None,
        }
        .copied()
        .ok_or_else(|| {
            invalid(
                path,
                "UnsupportedSchema column does not address a loader-validated target sort",
            )
        })?;
        let authority = input_sort_authority(catalog.sort(sort, path)?);
        let supported = matches!(
            (*role, authority),
            (
                InputColumnRole::Input,
                InputSortAuthority::I64 | InputSortAuthority::F64 | InputSortAuthority::String
            ) | (
                InputColumnRole::Output,
                InputSortAuthority::I64 | InputSortAuthority::String | InputSortAuthority::Unit
            )
        );
        if supported {
            return Err(invalid(
                path,
                "UnsupportedSchema points at an exactly supported input sort authority",
            ));
        }
        Ok(())
    }

    fn validate_schedule(
        &self,
        catalog: &Catalog<'_>,
        schedule: &Schedule,
        path: &str,
    ) -> ValidationResult {
        let mut stack = vec![schedule];
        while let Some(schedule) = stack.pop() {
            match schedule {
                Schedule::Sequence(children) => stack.extend(children.iter().rev()),
                Schedule::Repeat { schedule, .. } | Schedule::Saturate(schedule) => {
                    stack.push(schedule)
                }
                Schedule::Run {
                    ruleset, expansion, ..
                } => match ruleset {
                    ResolvedOrMissing::Missing { name } => {
                        if name.is_empty() {
                            return Err(invalid(
                                path,
                                "missing Run ruleset has an empty diagnostic name",
                            ));
                        }
                        let RulesetExpansion::Missing { path: missing_path } = expansion else {
                            return Err(invalid(path, "missing Run root has a complete expansion"));
                        };
                        let Some(reference) = missing_path.first() else {
                            return Err(invalid(path, "missing Run root has an empty frozen path"));
                        };
                        if missing_path.len() != 1 {
                            return Err(invalid(
                                path,
                                "missing Run root does not retain one frozen root segment",
                            ));
                        }
                        if let ResolvedOrMissing::Resolved(target) = reference.target
                            && self.rulesets.contains(&target)
                        {
                            return Err(invalid(
                                path,
                                "missing Run root's exact final-catalog ID is prefix-visible",
                            ));
                        }
                    }
                    ResolvedOrMissing::Resolved(ruleset) => {
                        if !self.rulesets.contains(ruleset) {
                            return Err(invalid(
                                path,
                                format!(
                                    "ruleset ID {} is not available at this Run prefix",
                                    ruleset.ordinal()
                                ),
                            ));
                        }
                        let expected = self.expand_ruleset(catalog, *ruleset, path)?;
                        if !ruleset_expansions_have_same_authority(expansion, &expected) {
                            return Err(invalid(
                                path,
                                "Run does not retain the exact prefix-frozen recursive expansion",
                            ));
                        }
                    }
                },
            }
        }
        Ok(())
    }

    fn expand_ruleset(
        &self,
        catalog: &Catalog<'_>,
        root: RulesetId,
        path: &str,
    ) -> ValidationResult<RulesetExpansion> {
        enum Work {
            Enter(RulesetReference),
            Exit,
        }

        let mut result = Vec::new();
        let mut current_path = Vec::new();
        let root_decl = catalog.ruleset(root, path)?;
        let mut stack = vec![Work::Enter(RulesetReference {
            name: root_decl.name.clone(),
            target: ResolvedOrMissing::Resolved(root),
        })];
        while let Some(work) = stack.pop() {
            match work {
                Work::Exit => {
                    current_path.pop();
                }
                Work::Enter(reference) => {
                    current_path.push(reference.clone());
                    let ResolvedOrMissing::Resolved(ruleset) = reference.target else {
                        return Ok(RulesetExpansion::Missing { path: current_path });
                    };
                    if !self.rulesets.contains(&ruleset) {
                        return Ok(RulesetExpansion::Missing { path: current_path });
                    }
                    match &catalog.ruleset_metadata(ruleset, path)?.kind {
                        RulesetKind::Concrete => {
                            result.extend(
                                catalog
                                    .ruleset(ruleset, path)?
                                    .rules
                                    .iter()
                                    .copied()
                                    .filter(|rule| self.rules.contains(rule)),
                            );
                            current_path.pop();
                        }
                        RulesetKind::Combined { children } => {
                            stack.push(Work::Exit);
                            stack.extend(children.iter().rev().cloned().map(Work::Enter));
                        }
                    }
                }
            }
        }
        Ok(RulesetExpansion::Complete { rules: result })
    }

    fn validate_query(
        &self,
        catalog: &Catalog<'_>,
        query: &FactQuery,
        path: &str,
    ) -> ValidationResult {
        for atom in &query.atoms {
            match atom.call {
                QueryCall::Table { target, .. } => self.require_function(target, path)?,
                QueryCall::Index { index, .. } => {
                    if !self.indexes.contains(&index) {
                        return Err(invalid(
                            path,
                            format!(
                                "index ID {} is not available at this command prefix",
                                index.ordinal()
                            ),
                        ));
                    }
                    let declaration = catalog.index(index, path)?;
                    self.require_function(declaration.target, path)?;
                }
                QueryCall::Primitive { .. } => {}
            }
        }
        Ok(())
    }
}

#[derive(Default)]
struct VariableCatalog {
    entries: BTreeMap<RuleVarId, SortId>,
    order: Vec<RuleVarId>,
}

impl VariableCatalog {
    fn collect(
        &mut self,
        catalog: &Catalog<'_>,
        variable: &RuleVar,
        path: &str,
    ) -> ValidationResult {
        catalog.sort(variable.sort, path)?;
        match self.entries.get(&variable.id) {
            Some(sort) if *sort != variable.sort => Err(invalid(
                path,
                format!(
                    "variable ID {} is reused with a different sort",
                    variable.id.ordinal()
                ),
            )),
            Some(_) => Ok(()),
            None => {
                self.entries.insert(variable.id, variable.sort);
                self.order.push(variable.id);
                Ok(())
            }
        }
    }

    fn validate_dense(&self, path: &str) -> ValidationResult {
        for (index, id) in self.order.iter().copied().enumerate() {
            validate_dense_id(id.ordinal(), index, &format!("{path}.variables"))?;
        }
        Ok(())
    }
}

fn validate_terms(
    catalog: &Catalog<'_>,
    variables: &mut VariableCatalog,
    terms: &[RuleTerm],
    expected: &[SortId],
    path: &str,
) -> ValidationResult {
    validate_term_sorts(terms, expected, path)?;
    for (term_index, term) in terms.iter().enumerate() {
        match term {
            RuleTerm::Variable(variable) => {
                variables.collect(catalog, variable, &format!("{path}.terms[{term_index}]"))?
            }
            RuleTerm::Literal(literal) => {
                validate_literal(catalog, literal, &format!("{path}.terms[{term_index}]"))?
            }
        }
    }
    Ok(())
}

fn validate_term_sorts(terms: &[RuleTerm], expected: &[SortId], path: &str) -> ValidationResult {
    if terms.len() != expected.len() {
        return Err(invalid(
            path,
            format!("term arity {}, expected {}", terms.len(), expected.len()),
        ));
    }
    for (index, (term, expected)) in terms.iter().zip(expected).enumerate() {
        if term.sort() != *expected {
            return Err(invalid(
                format!("{path}.terms[{index}]"),
                "nominal term sort mismatch",
            ));
        }
    }
    Ok(())
}

fn validate_literal(catalog: &Catalog<'_>, literal: &TypedLiteral, path: &str) -> ValidationResult {
    let sort = catalog.sort(literal.sort, &format!("{path}.sort"))?;
    let valid = matches!(
        (&sort.semantics, &literal.value),
        (SortSemantics::Unit, LiteralValue::Unit)
            | (SortSemantics::Bool, LiteralValue::Bool(_))
            | (SortSemantics::I64, LiteralValue::I64(_))
            | (SortSemantics::F64, LiteralValue::F64Bits(_))
            | (SortSemantics::String, LiteralValue::String(_))
            | (SortSemantics::BigInt, LiteralValue::BigIntDecimal(_))
            | (SortSemantics::BigRat, LiteralValue::BigRat { .. })
            | (SortSemantics::Opaque { .. }, LiteralValue::Opaque(_))
    );
    if !valid {
        return Err(invalid(path, "literal payload does not match nominal sort"));
    }
    Ok(())
}

fn collect_action_terms(
    catalog: &Catalog<'_>,
    variables: &mut VariableCatalog,
    action: &CoreAction,
    path: &str,
) -> ValidationResult {
    match action {
        CoreAction::Let {
            binding, arguments, ..
        } => {
            variables.collect(catalog, binding, path)?;
            for term in arguments {
                collect_action_term(catalog, variables, term, path)?;
            }
        }
        CoreAction::LetValue { binding, value } => {
            variables.collect(catalog, binding, path)?;
            collect_action_term(catalog, variables, value, path)?;
        }
        CoreAction::Set { keys, values, .. } => {
            for term in keys.iter().chain(values) {
                collect_action_term(catalog, variables, term, path)?;
            }
        }
        CoreAction::Change { keys, .. } => {
            for term in keys {
                collect_action_term(catalog, variables, term, path)?;
            }
        }
        CoreAction::Union { left, right } => {
            collect_action_term(catalog, variables, left, path)?;
            collect_action_term(catalog, variables, right, path)?;
        }
        CoreAction::Panic { .. } => {}
    }
    Ok(())
}

fn collect_action_term(
    catalog: &Catalog<'_>,
    variables: &mut VariableCatalog,
    term: &RuleTerm,
    path: &str,
) -> ValidationResult {
    match term {
        RuleTerm::Variable(variable) => variables.collect(catalog, variable, path),
        RuleTerm::Literal(literal) => validate_literal(catalog, literal, path),
    }
}

fn ensure_terms_bound(
    terms: &[RuleTerm],
    bound: &BTreeSet<RuleVarId>,
    path: &str,
) -> ValidationResult {
    for term in terms {
        ensure_term_bound(term, bound, path)?;
    }
    Ok(())
}

fn ensure_term_bound(term: &RuleTerm, bound: &BTreeSet<RuleVarId>, path: &str) -> ValidationResult {
    if let RuleTerm::Variable(variable) = term
        && !bound.contains(&variable.id)
    {
        return Err(invalid(
            path,
            format!(
                "variable ID {} is used before it is bound",
                variable.id.ordinal()
            ),
        ));
    }
    Ok(())
}

fn validate_query_reachability(query: &FactQuery, path: &str) -> ValidationResult {
    let mut bound = BTreeSet::new();
    for atom in &query.atoms {
        if matches!(atom.call, QueryCall::Table { .. }) {
            add_term_variables(&mut bound, &atom.terms);
        }
    }
    let mut unresolved = query
        .atoms
        .iter()
        .enumerate()
        .filter_map(|(index, atom)| {
            matches!(
                atom.call,
                QueryCall::Index { .. } | QueryCall::Primitive { .. }
            )
            .then_some(index)
        })
        .collect::<BTreeSet<_>>();
    loop {
        let ready = unresolved
            .iter()
            .copied()
            .filter(|index| {
                let atom = &query.atoms[*index];
                match atom.call {
                    QueryCall::Index { .. } => term_is_bound(&atom.terms[0], &bound),
                    QueryCall::Primitive { .. } => atom.terms[..atom.terms.len() - 1]
                        .iter()
                        .all(|term| term_is_bound(term, &bound)),
                    QueryCall::Table { .. } => false,
                }
            })
            .collect::<Vec<_>>();
        if ready.is_empty() {
            break;
        }
        for index in ready {
            let atom = &query.atoms[index];
            match atom.call {
                QueryCall::Index { .. } => {
                    add_term_variables(&mut bound, &atom.terms[1..atom.terms.len() - 1]);
                }
                QueryCall::Primitive { .. } => {
                    if let Some(RuleTerm::Variable(output)) = atom.terms.last() {
                        bound.insert(output.id);
                    }
                }
                QueryCall::Table { .. } => {}
            }
            unresolved.remove(&index);
        }
    }
    if let Some(index) = unresolved.first() {
        return Err(invalid(
            format!("{path}.atoms[{index}]"),
            "query occurrence is not reachable from table/occurrence outputs",
        ));
    }
    Ok(())
}

fn add_term_variables(bound: &mut BTreeSet<RuleVarId>, terms: &[RuleTerm]) {
    for term in terms {
        if let RuleTerm::Variable(variable) = term {
            bound.insert(variable.id);
        }
    }
}

fn term_is_bound(term: &RuleTerm, bound: &BTreeSet<RuleVarId>) -> bool {
    match term {
        RuleTerm::Variable(variable) => bound.contains(&variable.id),
        RuleTerm::Literal(_) => true,
    }
}

fn validate_inputs(inputs: &[InputPayload], path: &str) -> ValidationResult {
    for (index, payload) in inputs.iter().enumerate() {
        validate_dense_id(payload.id.ordinal(), index, path)?;
        let input_path = format!("{path}[{index}]");
        let input = &payload.input;
        let resolved_path = resolve_input_path(
            payload.path.fact_directory.as_deref(),
            &payload.path.declared,
        );
        if payload.path != resolved_path {
            return Err(invalid(
                format!("{input_path}.path"),
                "input effective path is not the exact pure resolution of its declared path and fact directory",
            ));
        }
        let contents = std::str::from_utf8(&payload.bytes).map_err(|error| {
            invalid(
                format!("{input_path}.bytes"),
                format!(
                    "successful input payload bytes are not UTF-8 at byte {}",
                    error.valid_up_to()
                ),
            )
        })?;
        let schema = TypedInputSchema {
            subtype: input.subtype,
            declared_inputs: input.declared_inputs.clone(),
            declared_outputs: input.declared_outputs.clone(),
            effective_inputs: input.effective_inputs.clone(),
            effective_outputs: input.effective_outputs.clone(),
        };
        let parsed = parse_tsv_with_resolved_schema(contents, &schema).map_err(|error| {
            invalid(
                format!("{input_path}.bytes"),
                format!("successful input payload bytes do not parse: {error}"),
            )
        })?;
        let reparsed = InputPayloadData {
            subtype: parsed.schema.subtype,
            declared_inputs: parsed.schema.declared_inputs,
            declared_outputs: parsed.schema.declared_outputs,
            effective_inputs: parsed.schema.effective_inputs,
            effective_outputs: parsed.schema.effective_outputs,
            rows: parsed.rows,
        };
        if *input != reparsed {
            return Err(invalid(
                format!("{input_path}.input"),
                "stored typed input is not the exact parse of the retained one-read byte buffer",
            ));
        }
        if input.effective_inputs.len() != input.declared_inputs.len() {
            return Err(invalid(
                format!("{input_path}.effective_inputs"),
                "effective input arity does not match declared input arity",
            ));
        }
        match input.subtype {
            InputFunctionSubtype::Constructor => {
                if input.declared_outputs.len() != 1 || !input.effective_outputs.is_empty() {
                    return Err(invalid(
                        format!("{input_path}.effective_outputs"),
                        "constructor payload must declare one minted output and store no output column",
                    ));
                }
            }
            InputFunctionSubtype::Custom => {
                if input.declared_outputs.is_empty()
                    || input.effective_outputs.len() != input.declared_outputs.len()
                {
                    return Err(invalid(
                        format!("{input_path}.effective_outputs"),
                        "custom payload effective outputs do not match its nonempty declaration",
                    ));
                }
            }
        }

        let mut previous_line = None;
        for (row_index, row) in input.rows.iter().enumerate() {
            let expected_ordinal = u64::try_from(row_index)
                .map_err(|_| invalid(&input_path, "input row ordinal space exhausted"))?;
            if row.source_row_ordinal != expected_ordinal {
                return Err(invalid(
                    format!("{input_path}.rows[{row_index}]"),
                    format!(
                        "expected dense source row ordinal {expected_ordinal}, got {}",
                        row.source_row_ordinal
                    ),
                ));
            }
            if row.physical_line == 0
                || previous_line.is_some_and(|previous| row.physical_line <= previous)
            {
                return Err(invalid(
                    format!("{input_path}.rows[{row_index}].physical_line"),
                    "physical line numbers must be positive and strictly increasing",
                ));
            }
            previous_line = Some(row.physical_line);
            let expected_kinds = input
                .effective_inputs
                .iter()
                .chain(&input.effective_outputs);
            if row.values.len() != input.row_arity() {
                return Err(invalid(
                    format!("{input_path}.rows[{row_index}]"),
                    "typed input row arity mismatch",
                ));
            }
            for (column, (value, expected)) in row.values.iter().zip(expected_kinds).enumerate() {
                let valid = matches!(
                    (value, expected),
                    (InputLiteral::Unit, InputScalarKind::Unit)
                        | (InputLiteral::I64(_), InputScalarKind::I64)
                        | (InputLiteral::F64Bits(_), InputScalarKind::F64)
                        | (InputLiteral::String(_), InputScalarKind::String)
                );
                if !valid {
                    return Err(invalid(
                        format!("{input_path}.rows[{row_index}].values[{column}]"),
                        "typed input literal kind mismatch",
                    ));
                }
            }
        }
    }
    Ok(())
}

fn validate_input_scalar_kinds(
    actual: &[InputScalarKind],
    expected: &[SortId],
    catalog: &Catalog<'_>,
    path: &str,
) -> ValidationResult {
    if actual.len() != expected.len() {
        return Err(invalid(path, "effective input schema arity mismatch"));
    }
    for (index, (actual, expected)) in actual.iter().zip(expected).enumerate() {
        let expected = match catalog.sort(*expected, path)?.semantics {
            SortSemantics::Unit => Some(InputScalarKind::Unit),
            SortSemantics::I64 => Some(InputScalarKind::I64),
            SortSemantics::F64 => Some(InputScalarKind::F64),
            SortSemantics::String => Some(InputScalarKind::String),
            SortSemantics::Eq
            | SortSemantics::Bool
            | SortSemantics::BigInt
            | SortSemantics::BigRat
            | SortSemantics::Container { .. }
            | SortSemantics::Opaque { .. } => None,
        }
        .ok_or_else(|| invalid(format!("{path}[{index}]"), "unsupported typed-input sort"))?;
        if *actual != expected {
            return Err(invalid(
                format!("{path}[{index}]"),
                "effective scalar kind does not match exact nominal sort",
            ));
        }
    }
    Ok(())
}

fn input_kind_matches_sort(
    kind: InputScalarKind,
    sort: &crate::frontend_snapshot::SortDecl,
) -> bool {
    matches!(
        (kind, &sort.semantics),
        (InputScalarKind::Unit, SortSemantics::Unit)
            | (InputScalarKind::I64, SortSemantics::I64)
            | (InputScalarKind::F64, SortSemantics::F64)
            | (InputScalarKind::String, SortSemantics::String)
    )
}

fn input_sort_authority(sort: &crate::frontend_snapshot::SortDecl) -> InputSortAuthority {
    match &sort.semantics {
        SortSemantics::Unit => InputSortAuthority::Unit,
        SortSemantics::I64 => InputSortAuthority::I64,
        SortSemantics::F64 => InputSortAuthority::F64,
        SortSemantics::String => InputSortAuthority::String,
        SortSemantics::Eq
        | SortSemantics::Bool
        | SortSemantics::BigInt
        | SortSemantics::BigRat
        | SortSemantics::Container { .. }
        | SortSemantics::Opaque { .. } => InputSortAuthority::Unsupported,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend_snapshot::{
        FunctionConfig, FunctionDefault, FunctionDisplay, MergeProgram, MergeValueId,
        MergeValueNode, MissingOwnerPolicy, NativeScalarPrimitive, PrimitiveDecl, RuleSpec,
        RulesetDecl, SortDecl,
    };

    const UNIT: SortId = SortId::new(0);
    const I64: SortId = SortId::new(1);
    const ADD: PrimitiveId = PrimitiveId::new(0);
    const LEFT: FunctionId = FunctionId::new(0);
    const RIGHT: FunctionId = FunctionId::new(1);
    const DEFAULT_RULESET: RulesetId = RulesetId::new(0);
    const RULE: RuleId = RuleId::new(0);

    fn function(id: FunctionId, name: &str) -> FunctionConfig {
        FunctionConfig {
            id,
            name: name.to_owned(),
            kind: FunctionKind::Custom,
            schema: vec![I64, I64],
            n_values: 1,
            identity_values: None,
            default: FunctionDefault::Fail,
            merge: MergeProgram {
                owner: id,
                missing_owner: MissingOwnerPolicy::InsertCandidateWithoutMerge,
                values: vec![MergeValueNode {
                    id: MergeValueId::new(0),
                    sort: I64,
                    operation: MergeValueOperation::OldValue { column: 0 },
                }],
                actions: Vec::new(),
                results: vec![MergeValueId::new(0)],
            },
            can_subsume: true,
            internal_hidden: false,
            internal_let: false,
            term_constructor: None,
            internal_term_node: false,
            display: FunctionDisplay {
                print_size_name: name.to_owned(),
            },
        }
    }

    fn base_view() -> ProgramView {
        let core = ResolvedCoreSnapshot {
            sorts: vec![
                SortDecl {
                    id: UNIT,
                    name: "Unit".to_owned(),
                    semantics: SortSemantics::Unit,
                    unionable: false,
                },
                SortDecl {
                    id: I64,
                    name: "i64".to_owned(),
                    semantics: SortSemantics::I64,
                    unionable: false,
                },
            ],
            primitives: vec![PrimitiveDecl {
                id: ADD,
                name: "+".to_owned(),
                input: vec![I64, I64],
                output: I64,
                semantics: PrimitiveSemantics::NativeScalar(NativeScalarPrimitive::I64Add),
            }],
            functions: vec![function(LEFT, "left"), function(RIGHT, "right")],
            rulesets: vec![RulesetDecl {
                id: DEFAULT_RULESET,
                name: String::new(),
                rules: vec![RULE],
            }],
            rules: vec![RuleSpec {
                id: RULE,
                name: "copy".to_owned(),
                ruleset: DEFAULT_RULESET,
                seminaive: true,
                no_decomp: false,
                body: Vec::new(),
                actions: Vec::new(),
            }],
        };
        ProgramView {
            core,
            indexes: vec![IndexDecl {
                id: IndexId::new(0),
                name: "left-index".to_owned(),
                target: LEFT,
                any_of: vec![0],
            }],
            ruleset_metadata: vec![RulesetMetadata {
                ruleset: DEFAULT_RULESET,
                availability: RulesetAvailability::ImplicitDefault,
                kind: RulesetKind::Concrete,
            }],
            primitive_metadata: vec![PrimitiveMetadata {
                primitive: ADD,
                valid_contexts: PrimitiveContextMask::ALL,
                effects: PrimitiveEffectMask::NONE,
            }],
            function_metadata: vec![
                FunctionMetadata {
                    function: LEFT,
                    extraction_cost: None,
                    unextractable: false,
                    merge_context: PrimitiveCallContext::Write,
                },
                FunctionMetadata {
                    function: RIGHT,
                    extraction_cost: None,
                    unextractable: false,
                    merge_context: PrimitiveCallContext::Write,
                },
            ],
            rule_metadata: vec![RuleMetadata {
                rule: RULE,
                evaluation: RuleEvaluationMode::Seminaive,
                source_no_decomp: false,
                include_subsumed: false,
                query_context: PrimitiveCallContext::Pure,
                action_context: PrimitiveCallContext::Write,
                index_uses: Vec::new(),
            }],
            schedules: vec![ScheduleDecl {
                id: ScheduleId::new(0),
                schedule: Schedule::Run {
                    ruleset: ResolvedOrMissing::Resolved(DEFAULT_RULESET),
                    expansion: RulesetExpansion::Complete { rules: vec![RULE] },
                    until: None,
                },
            }],
            commands: vec![
                command(
                    0,
                    ProgramCommand::Catalog(CatalogDeclaration::Function(LEFT)),
                ),
                command(
                    1,
                    ProgramCommand::Catalog(CatalogDeclaration::Function(RIGHT)),
                ),
                command(
                    2,
                    ProgramCommand::Catalog(CatalogDeclaration::Index(IndexId::new(0))),
                ),
                command(3, ProgramCommand::RuleDeclaration(RULE)),
                command(
                    4,
                    ProgramCommand::Run {
                        schedule: ScheduleId::new(0),
                    },
                ),
            ],
        }
    }

    fn source_ref(group: u32, subcommand: u32) -> SourceSubcommandRef {
        SourceSubcommandRef::new(
            SourceGroupId::new(group),
            SourceSubcommandId::new(subcommand),
        )
    }

    fn source_document_with(groups: &[(&str, &str, usize)], eof_trailer: &str) -> SourceDocument {
        let mut contents = String::new();
        let mut source_groups = Vec::with_capacity(groups.len());
        for (group_index, (leading_trivia, command, subcommand_count)) in groups.iter().enumerate()
        {
            let trivia_start = contents.len();
            contents.push_str(leading_trivia);
            let command_start = contents.len();
            contents.push_str(command);
            let command_end = contents.len();
            source_groups.push(SourceGroup {
                id: SourceGroupId::new(u32::try_from(group_index).unwrap()),
                leading_trivia: trivia_start..command_start,
                command: command_start..command_end,
                subcommands: (0..*subcommand_count)
                    .map(|subcommand_index| SourceSubcommand {
                        id: SourceSubcommandId::new(u32::try_from(subcommand_index).unwrap()),
                    })
                    .collect(),
            });
        }
        let eof_start = contents.len();
        contents.push_str(eof_trailer);
        let eof_end = contents.len();
        SourceDocument {
            logical_name: None,
            contents,
            groups: source_groups,
            eof_trailer: eof_start..eof_end,
        }
    }

    fn source_document() -> SourceDocument {
        source_document_with(&[("; source comment\n", "(run)", 1)], "")
    }

    fn command(ordinal: u32, command: ProgramCommand) -> CommandEnvelope {
        CommandEnvelope {
            ordinal: CommandOrdinal::new(ordinal),
            origin: CommandOrigin::Source(source_ref(0, 0)),
            output: None,
            display: CommandDisplay {
                resolved: format!("resolved-{ordinal}"),
                comment: None,
            },
            command,
        }
    }

    fn output_command(ordinal: u32, output: u32, semantic: ProgramCommand) -> CommandEnvelope {
        let mut envelope = command(ordinal, semantic);
        envelope.output = Some(OutputOrdinal::new(output));
        envelope
    }

    fn fail_command(ordinal: u32, command: ProgramCommand) -> FailCommand {
        FailCommand {
            ordinal: FailCommandOrdinal::new(ordinal),
            origin: CommandOrigin::Source(source_ref(0, 0)),
            display: CommandDisplay {
                resolved: format!("resolved-fail-{ordinal}"),
                comment: None,
            },
            command,
        }
    }

    fn ruleset_reference(id: RulesetId, name: &str) -> RulesetReference {
        RulesetReference {
            name: name.to_owned(),
            target: ResolvedOrMissing::Resolved(id),
        }
    }

    fn program(view: ProgramView) -> FrontendProgram {
        FrontendProgram {
            source: source_document(),
            inputs: Vec::new(),
            streams: ProgramStreams::ExecutionOnly { execution: view },
        }
    }

    #[test]
    fn nested_schedule_retains_last_child_and_aggregate_flag_metadata() {
        let schedule = Schedule::Repeat {
            limit: 2,
            schedule: Box::new(Schedule::Saturate(Box::new(Schedule::Sequence(vec![
                Schedule::Run {
                    ruleset: ResolvedOrMissing::Resolved(DEFAULT_RULESET),
                    expansion: RulesetExpansion::Complete { rules: vec![RULE] },
                    until: None,
                },
            ])))),
        };

        let Schedule::Repeat {
            schedule: inner, ..
        } = &schedule
        else {
            unreachable!()
        };
        let outer = schedule.report_metadata();
        let inner = inner.report_metadata();
        assert_eq!(outer.control, ScheduleControlFlag::CanStopTrue);
        assert_eq!(
            outer.returned_updated,
            ScheduleFlagSource::AnyCompletedChild
        );
        assert_eq!(
            outer.returned_can_stop,
            ScheduleFlagSource::AllCompletedChildren
        );
        assert_eq!(inner.control, ScheduleControlFlag::UpdatedFalse);
        assert!(inner.child_runs_at_least_once);
        assert_eq!(schedule.node_count(), 4);
    }

    #[test]
    fn repeat_limits_zero_one_and_large_retain_the_same_shape() {
        fn repeated(limit: u64) -> Schedule {
            Schedule::Repeat {
                limit,
                schedule: Box::new(Schedule::Run {
                    ruleset: ResolvedOrMissing::Resolved(DEFAULT_RULESET),
                    expansion: RulesetExpansion::Complete { rules: vec![RULE] },
                    until: None,
                }),
            }
        }

        for schedule in [repeated(0), repeated(1), repeated(100_000)] {
            assert_eq!(schedule.node_count(), 2);
            assert_eq!(
                schedule.report_metadata().control,
                ScheduleControlFlag::CanStopTrue
            );
        }
    }

    #[test]
    fn source_document_reconstructs_unicode_and_trivia_losslessly() {
        let source = source_document_with(
            &[
                ("; λ-leading\n  ", "(let café 1)", 1),
                ("\n; 中間\n", "(run)", 1),
            ],
            "\n; eof 尾\n",
        );
        validate_source(&source).unwrap();

        let mut reconstructed = String::new();
        for group in &source.groups {
            reconstructed.push_str(&source.contents[group.leading_trivia.clone()]);
            reconstructed.push_str(&source.contents[group.command.clone()]);
        }
        reconstructed.push_str(&source.contents[source.eof_trailer.clone()]);
        assert_eq!(reconstructed, source.contents);
    }

    #[test]
    fn comment_only_document_is_one_exact_eof_trailer() {
        let source = source_document_with(&[], "; λ-only comment\n");
        validate_source(&source).unwrap();
        assert!(source.groups.is_empty());
        assert_eq!(source.eof_trailer, 0..source.contents.len());

        let mut view = base_view();
        for command in &mut view.commands {
            command.origin = CommandOrigin::Generated {
                trigger: None,
                role: GeneratedCommandRole::FrontendPrelude,
            };
        }
        FrontendProgram {
            source,
            inputs: Vec::new(),
            streams: ProgramStreams::ExecutionOnly { execution: view },
        }
        .validate()
        .unwrap();
    }

    #[test]
    fn trailing_trivia_belongs_exactly_to_the_eof_range() {
        let source = source_document_with(&[("", "(run)", 1)], "\n  ; trailing λ\n");
        validate_source(&source).unwrap();
        assert_eq!(
            &source.contents[source.eof_trailer.clone()],
            "\n  ; trailing λ\n"
        );
        assert_eq!(source.groups[0].command.end, source.eof_trailer.start);
    }

    #[test]
    fn malformed_source_partitions_fail_closed() {
        let base = source_document_with(&[(" ", "(run)", 1)], "\n");

        let mut gap = base.clone();
        gap.groups[0].command.start += 1;
        assert!(validate_source(&gap).unwrap_err().message.contains("gap"));

        let mut overlap = base.clone();
        overlap.groups[0].command.start -= 1;
        assert!(
            validate_source(&overlap)
                .unwrap_err()
                .message
                .contains("overlaps")
        );

        let mut out_of_bounds = base.clone();
        out_of_bounds.groups[0].command.end = out_of_bounds.contents.len() + 1;
        assert!(
            validate_source(&out_of_bounds)
                .unwrap_err()
                .message
                .contains("exceeds contents length")
        );

        let mut empty = base;
        empty.groups[0].command.end = empty.groups[0].command.start;
        assert!(
            validate_source(&empty)
                .unwrap_err()
                .message
                .contains("command range is empty")
        );

        let mut non_char = source_document_with(&[("", "λ", 1)], "");
        non_char.groups[0].command.end = 1;
        assert!(
            validate_source(&non_char)
                .unwrap_err()
                .message
                .contains("UTF-8 character boundary")
        );
    }

    #[test]
    fn source_group_and_local_subcommand_ids_are_dense() {
        let source = source_document_with(&[("", "(one)", 1), (" ", "(two)", 2)], "");
        validate_source(&source).unwrap();

        let mut sparse_group = source.clone();
        sparse_group.groups[1].id = SourceGroupId::new(7);
        assert!(
            validate_source(&sparse_group)
                .unwrap_err()
                .message
                .contains("expected dense ID 1")
        );

        let mut sparse_subcommand = source;
        sparse_subcommand.groups[1].subcommands[1].id = SourceSubcommandId::new(7);
        assert!(
            validate_source(&sparse_subcommand)
                .unwrap_err()
                .message
                .contains("expected dense ID 1")
        );
    }

    #[test]
    fn dangling_direct_origins_and_generated_triggers_are_rejected() {
        for origin in [
            CommandOrigin::Source(source_ref(9, 0)),
            CommandOrigin::Source(source_ref(0, 9)),
            CommandOrigin::Generated {
                trigger: Some(source_ref(9, 0)),
                role: GeneratedCommandRole::ProofMaintenance,
            },
        ] {
            let mut view = base_view();
            view.commands[0].origin = origin;
            let error = program(view).validate().unwrap_err();
            assert!(error.message.contains("dangling source"));
        }

        for origin in [
            CommandOrigin::Generated {
                trigger: Some(source_ref(0, 0)),
                role: GeneratedCommandRole::ProofHeader,
            },
            CommandOrigin::Generated {
                trigger: None,
                role: GeneratedCommandRole::ProofMaintenance,
            },
        ] {
            let mut view = base_view();
            view.commands[0].origin = origin;
            let error = program(view).validate().unwrap_err();
            assert!(error.message.contains("wrong source-trigger association"));
        }
    }

    #[test]
    fn direct_subcommands_are_nondecreasing_within_one_group() {
        let mut view = base_view();
        view.commands[0].origin = CommandOrigin::Source(source_ref(0, 0));
        view.commands[1].origin = CommandOrigin::Generated {
            trigger: Some(source_ref(0, 0)),
            role: GeneratedCommandRole::FrontendDesugaring,
        };
        for command in &mut view.commands[2..] {
            command.origin = CommandOrigin::Source(source_ref(0, 1));
        }
        let exact = FrontendProgram {
            source: source_document_with(&[("", "(fail (one) (two))", 2)], ""),
            inputs: Vec::new(),
            streams: ProgramStreams::ExecutionOnly { execution: view },
        };
        exact.validate().unwrap();

        let mut reversed = exact;
        let ProgramStreams::ExecutionOnly { execution } = &mut reversed.streams else {
            unreachable!()
        };
        execution.commands[0].origin = CommandOrigin::Source(source_ref(0, 1));
        execution.commands[2].origin = CommandOrigin::Source(source_ref(0, 0));
        let error = reversed.validate().unwrap_err();
        assert!(error.message.contains("source trigger moved backwards"));
    }

    #[test]
    fn generated_triggers_are_ordered_and_source_less_headers_form_a_prefix() {
        let mut view = base_view();
        view.commands[0].origin = CommandOrigin::Source(source_ref(0, 0));
        view.commands[1].origin = CommandOrigin::Source(source_ref(0, 1));
        for command in &mut view.commands[2..] {
            command.origin = CommandOrigin::Generated {
                trigger: Some(source_ref(0, 1)),
                role: GeneratedCommandRole::FrontendDesugaring,
            };
        }
        let exact = FrontendProgram {
            source: source_document_with(&[("", "(two-command-macro)", 2)], ""),
            inputs: Vec::new(),
            streams: ProgramStreams::ExecutionOnly { execution: view },
        };
        exact.validate().unwrap();

        let mut reversed = exact.clone();
        let ProgramStreams::ExecutionOnly { execution } = &mut reversed.streams else {
            unreachable!()
        };
        execution.commands[2].origin = CommandOrigin::Generated {
            trigger: Some(source_ref(0, 0)),
            role: GeneratedCommandRole::FrontendDesugaring,
        };
        let error = reversed.validate().unwrap_err();
        assert!(error.message.contains("source trigger moved backwards"));

        let mut late_header = exact;
        let ProgramStreams::ExecutionOnly { execution } = &mut late_header.streams else {
            unreachable!()
        };
        execution.commands[2].origin = CommandOrigin::Generated {
            trigger: None,
            role: GeneratedCommandRole::ProofHeader,
        };
        let error = late_header.validate().unwrap_err();
        assert!(
            error
                .message
                .contains("source-less generated command appears after")
        );
    }

    #[test]
    fn source_associated_groups_never_move_backwards() {
        let mut view = base_view();
        view.commands[0].origin = CommandOrigin::Source(source_ref(0, 0));
        for command in &mut view.commands[1..] {
            command.origin = CommandOrigin::Source(source_ref(1, 0));
        }
        let exact = FrontendProgram {
            source: source_document_with(&[("", "(one)", 1), (" ", "(two)", 1)], ""),
            inputs: Vec::new(),
            streams: ProgramStreams::ExecutionOnly { execution: view },
        };
        exact.validate().unwrap();

        let mut reversed = exact;
        let ProgramStreams::ExecutionOnly { execution } = &mut reversed.streams else {
            unreachable!()
        };
        execution.commands[0].origin = CommandOrigin::Source(source_ref(1, 0));
        execution.commands[1].origin = CommandOrigin::Source(source_ref(0, 0));
        let error = reversed.validate().unwrap_err();
        assert!(error.message.contains("source trigger moved backwards"));
    }

    #[test]
    fn zero_subcommand_source_groups_are_representable() {
        let mut view = base_view();
        for command in &mut view.commands {
            command.origin = CommandOrigin::Source(source_ref(1, 0));
        }
        FrontendProgram {
            source: source_document_with(&[("", "(empty-macro)", 0), (" ", "(run)", 1)], ""),
            inputs: Vec::new(),
            streams: ProgramStreams::ExecutionOnly { execution: view },
        }
        .validate()
        .unwrap();
    }

    #[test]
    fn silent_run_does_not_consume_user_output_ordinals() {
        let mut view = base_view();
        view.commands.push(output_command(
            5,
            0,
            ProgramCommand::PrintSize(PrintSizeTarget::Named {
                requested_name: "left".to_owned(),
                target: ResolvedOrMissing::Resolved(LEFT),
            }),
        ));
        view.commands.push(output_command(
            6,
            1,
            ProgramCommand::PrintStats(PrintStatsDestination::Display),
        ));
        program(view.clone()).validate().unwrap();

        view.commands[6].output = Some(OutputOrdinal::new(0));
        let error = program(view).validate().unwrap_err();
        assert!(error.message.contains("dense output ordinal 1"));
    }

    #[test]
    fn source_and_generated_runs_cannot_publish_stdout_events() {
        for origin in [
            CommandOrigin::Source(source_ref(0, 0)),
            CommandOrigin::Generated {
                trigger: Some(source_ref(0, 0)),
                role: GeneratedCommandRole::ProofMaintenance,
            },
        ] {
            let mut view = base_view();
            view.commands[4].origin = origin;
            program(view.clone()).validate().unwrap();

            view.commands[4].output = Some(OutputOrdinal::new(0));
            let error = program(view).validate().unwrap_err();
            assert!(error.message.contains("cannot publish an output"));
        }
    }

    #[test]
    fn every_parsed_subcommand_has_a_direct_retained_stream_origin() {
        let mut program = FrontendProgram {
            source: source_document_with(&[("", "(fail (check) (check))", 2)], ""),
            inputs: Vec::new(),
            streams: ProgramStreams::ExecutionOnly {
                execution: base_view(),
            },
        };
        let error = program.validate().unwrap_err();
        assert!(error.message.contains("no direct Source origin"));

        let ProgramStreams::ExecutionOnly { execution } = &mut program.streams else {
            unreachable!()
        };
        for command in &mut execution.commands[1..] {
            command.origin = CommandOrigin::Source(source_ref(0, 1));
        }
        program.validate().unwrap();
    }

    #[test]
    fn every_proof_view_independently_anchors_each_parsed_subcommand() {
        let execution = base_view();
        let mut proof_check = base_view();
        for command in &mut proof_check.commands {
            command.origin = CommandOrigin::Generated {
                trigger: Some(source_ref(0, 0)),
                role: GeneratedCommandRole::ProofInstrumentation,
            };
        }
        let mut missing_proof_anchor = FrontendProgram {
            source: source_document(),
            inputs: Vec::new(),
            streams: ProgramStreams::ProofInstrumented {
                execution,
                proof_check,
            },
        };

        let error = missing_proof_anchor.validate().unwrap_err();
        assert_eq!(error.path, "proof_check.source.groups[0].subcommands[0]");
        assert!(error.message.contains("proof_check retained view"));

        let ProgramStreams::ProofInstrumented {
            execution,
            proof_check,
        } = &mut missing_proof_anchor.streams
        else {
            unreachable!()
        };
        proof_check.commands[0].origin = CommandOrigin::Source(source_ref(0, 0));
        execution.commands[0].origin = CommandOrigin::Generated {
            trigger: Some(source_ref(0, 0)),
            role: GeneratedCommandRole::TermEncoding,
        };
        for command in &mut execution.commands[1..] {
            command.origin = CommandOrigin::Generated {
                trigger: Some(source_ref(0, 0)),
                role: GeneratedCommandRole::TermEncoding,
            };
        }

        let error = missing_proof_anchor.validate().unwrap_err();
        assert_eq!(error.path, "execution.source.groups[0].subcommands[0]");
        assert!(error.message.contains("execution retained view"));
    }

    #[test]
    fn generated_group_association_does_not_cover_a_parsed_subcommand() {
        let mut view = base_view();
        for command in &mut view.commands {
            command.origin = CommandOrigin::Generated {
                trigger: Some(source_ref(0, 0)),
                role: GeneratedCommandRole::FrontendDesugaring,
            };
        }
        let error = FrontendProgram {
            source: source_document(),
            inputs: Vec::new(),
            streams: ProgramStreams::ExecutionOnly { execution: view },
        }
        .validate()
        .unwrap_err();
        assert!(error.message.contains("no direct Source origin"));
    }

    #[test]
    fn design_b_frontend_pass_roles_are_admitted_with_source_provenance() {
        for role in [
            GeneratedCommandRole::FrontendDesugaring,
            GeneratedCommandRole::GlobalElimination,
            GeneratedCommandRole::TermEncoding,
        ] {
            let mut view = base_view();
            view.commands[0].origin = CommandOrigin::Generated {
                trigger: Some(source_ref(0, 0)),
                role,
            };
            program(view).validate().unwrap();
        }
    }

    #[test]
    fn named_print_size_uses_the_exact_target_not_its_diagnostic_name() {
        let mut view = base_view();
        view.commands = vec![
            command(
                0,
                ProgramCommand::Catalog(CatalogDeclaration::Function(LEFT)),
            ),
            output_command(
                1,
                0,
                ProgramCommand::PrintSize(PrintSizeTarget::Named {
                    requested_name: "right".to_owned(),
                    target: ResolvedOrMissing::Resolved(LEFT),
                }),
            ),
            command(
                2,
                ProgramCommand::Catalog(CatalogDeclaration::Function(RIGHT)),
            ),
            command(
                3,
                ProgramCommand::Catalog(CatalogDeclaration::Index(IndexId::new(0))),
            ),
            command(4, ProgramCommand::RuleDeclaration(RULE)),
            command(
                5,
                ProgramCommand::Run {
                    schedule: ScheduleId::new(0),
                },
            ),
        ];
        program(view.clone()).validate().unwrap();

        let ProgramCommand::PrintSize(PrintSizeTarget::Named { requested_name, .. }) =
            &mut view.commands[1].command
        else {
            unreachable!()
        };
        *requested_name = "renamed-diagnostic".to_owned();
        program(view.clone()).validate().unwrap();

        let ProgramCommand::PrintSize(PrintSizeTarget::Named { target, .. }) =
            &mut view.commands[1].command
        else {
            unreachable!()
        };
        *target = ResolvedOrMissing::Resolved(RIGHT);
        let error = program(view).validate().unwrap_err();
        assert!(
            error
                .message
                .contains("not available at this command prefix")
        );
    }

    #[test]
    fn all_print_size_membership_is_exact_and_display_order_is_lexical() {
        let mut view = base_view();
        view.commands.insert(
            4,
            output_command(
                4,
                0,
                ProgramCommand::PrintSize(PrintSizeTarget::All {
                    functions: vec![LEFT, RIGHT],
                }),
            ),
        );
        for (ordinal, command) in view.commands.iter_mut().enumerate() {
            command.ordinal = CommandOrdinal::new(u32::try_from(ordinal).unwrap());
        }
        view.core.functions[0].name = "z-renamed".to_owned();
        view.core.functions[0].display.print_size_name = "z-renamed".to_owned();
        view.core.functions[1].name = "a-renamed".to_owned();
        view.core.functions[1].display.print_size_name = "a-renamed".to_owned();
        let error = program(view.clone()).validate().unwrap_err();
        assert!(error.message.contains("lexical display-name order"));

        let ProgramCommand::PrintSize(PrintSizeTarget::All { functions }) =
            &mut view.commands[4].command
        else {
            unreachable!()
        };
        functions.reverse();
        program(view.clone()).validate().unwrap();

        let ProgramCommand::PrintSize(PrintSizeTarget::All { functions }) =
            &mut view.commands[4].command
        else {
            unreachable!()
        };
        functions.pop();
        let error = program(view).validate().unwrap_err();
        assert!(
            error
                .message
                .contains("every exact prefix-visible public ID")
        );
    }

    #[test]
    fn exact_index_identity_is_not_inferred_from_equal_shape() {
        let mut view = base_view();
        let duplicate_diagnostic = view.core.functions[0].name.clone();
        view.indexes.push(IndexDecl {
            id: IndexId::new(1),
            // A diagnostic may collide with a function or another index after
            // resolution. IndexId, not this spelling, remains authoritative.
            name: duplicate_diagnostic,
            target: LEFT,
            any_of: vec![0],
        });
        view.commands.insert(
            3,
            command(
                3,
                ProgramCommand::Catalog(CatalogDeclaration::Index(IndexId::new(1))),
            ),
        );
        view.commands.insert(
            4,
            command(
                4,
                ProgramCommand::Check {
                    facts: FactQuery {
                        primitive_context: PrimitiveCallContext::Read,
                        atoms: vec![QueryAtom {
                            call: QueryCall::Index {
                                index: IndexId::new(1),
                                read: ReadMode::All,
                            },
                            terms: vec![
                                RuleTerm::Literal(TypedLiteral {
                                    sort: I64,
                                    value: LiteralValue::I64(7),
                                }),
                                RuleTerm::Variable(RuleVar {
                                    id: RuleVarId::new(0),
                                    name: "key".to_owned(),
                                    sort: I64,
                                }),
                                RuleTerm::Variable(RuleVar {
                                    id: RuleVarId::new(1),
                                    name: "value".to_owned(),
                                    sort: I64,
                                }),
                                RuleTerm::Literal(TypedLiteral {
                                    sort: UNIT,
                                    value: LiteralValue::Unit,
                                }),
                            ],
                        }],
                    },
                },
            ),
        );
        for (ordinal, command) in view.commands.iter_mut().enumerate() {
            command.ordinal = CommandOrdinal::new(u32::try_from(ordinal).unwrap());
        }
        program(view.clone()).validate().unwrap();

        assert_ne!(view.indexes[0].id, view.indexes[1].id);
        assert_eq!(view.indexes[0].target, view.indexes[1].target);
        assert_eq!(view.indexes[0].any_of, view.indexes[1].any_of);

        view.commands.remove(3);
        for (ordinal, command) in view.commands.iter_mut().enumerate() {
            command.ordinal = CommandOrdinal::new(u32::try_from(ordinal).unwrap());
        }
        let error = program(view).validate().unwrap_err();
        assert!(error.message.contains("index ID 1 is not available"));
    }

    #[test]
    fn query_variable_identity_ignores_diagnostic_spelling_but_not_sort() {
        let mut view = base_view();
        view.commands.push(command(
            5,
            ProgramCommand::Check {
                facts: FactQuery {
                    primitive_context: PrimitiveCallContext::Read,
                    atoms: vec![QueryAtom {
                        call: QueryCall::Table {
                            target: LEFT,
                            read: ReadMode::All,
                        },
                        terms: vec![
                            RuleTerm::Variable(RuleVar {
                                id: RuleVarId::new(0),
                                name: "first-diagnostic".to_owned(),
                                sort: I64,
                            }),
                            RuleTerm::Variable(RuleVar {
                                id: RuleVarId::new(0),
                                name: "second-diagnostic".to_owned(),
                                sort: I64,
                            }),
                        ],
                    }],
                },
            },
        ));
        program(view.clone()).validate().unwrap();

        let ProgramCommand::Check { facts } = &mut view.commands[5].command else {
            unreachable!()
        };
        let RuleTerm::Variable(second) = &mut facts.atoms[0].terms[1] else {
            unreachable!()
        };
        second.sort = UNIT;
        let error = program(view).validate().unwrap_err();
        assert!(error.message.contains("sort"), "{error:?}");
    }

    #[test]
    fn malformed_nominal_references_fail_closed() {
        let mut view = base_view();
        view.schedules[0].schedule = Schedule::Run {
            ruleset: ResolvedOrMissing::Resolved(RulesetId::new(9)),
            expansion: RulesetExpansion::Complete { rules: vec![RULE] },
            until: None,
        };
        let error = program(view).validate().unwrap_err();
        assert!(error.message.contains("dangling ruleset ID 9"));
    }

    #[test]
    fn combined_rulesets_expand_ordered_children_at_each_run_prefix() {
        const LATER_RULESET: RulesetId = RulesetId::new(1);
        const COMBINED: RulesetId = RulesetId::new(2);
        const LATER_RULE: RuleId = RuleId::new(1);

        let mut view = base_view();
        view.core.rulesets.extend([
            RulesetDecl {
                id: LATER_RULESET,
                name: "later".to_owned(),
                rules: vec![LATER_RULE],
            },
            RulesetDecl {
                id: COMBINED,
                name: "both".to_owned(),
                rules: Vec::new(),
            },
        ]);
        view.core.rules.push(RuleSpec {
            id: LATER_RULE,
            name: "later-rule".to_owned(),
            ruleset: LATER_RULESET,
            seminaive: true,
            no_decomp: false,
            body: Vec::new(),
            actions: Vec::new(),
        });
        view.ruleset_metadata.extend([
            RulesetMetadata {
                ruleset: LATER_RULESET,
                availability: RulesetAvailability::Declared,
                kind: RulesetKind::Concrete,
            },
            RulesetMetadata {
                ruleset: COMBINED,
                availability: RulesetAvailability::Declared,
                kind: RulesetKind::Combined {
                    children: vec![
                        ruleset_reference(LATER_RULESET, "later"),
                        ruleset_reference(DEFAULT_RULESET, ""),
                        ruleset_reference(LATER_RULESET, "later"),
                    ],
                },
            },
        ]);
        view.rule_metadata.push(RuleMetadata {
            rule: LATER_RULE,
            evaluation: RuleEvaluationMode::Seminaive,
            source_no_decomp: false,
            include_subsumed: false,
            query_context: PrimitiveCallContext::Pure,
            action_context: PrimitiveCallContext::Write,
            index_uses: Vec::new(),
        });
        view.schedules = vec![
            ScheduleDecl {
                id: ScheduleId::new(0),
                schedule: Schedule::Run {
                    ruleset: ResolvedOrMissing::Resolved(COMBINED),
                    expansion: RulesetExpansion::Missing {
                        path: vec![
                            ruleset_reference(COMBINED, "both"),
                            ruleset_reference(LATER_RULESET, "later"),
                        ],
                    },
                    until: None,
                },
            },
            ScheduleDecl {
                id: ScheduleId::new(1),
                schedule: Schedule::Run {
                    ruleset: ResolvedOrMissing::Resolved(COMBINED),
                    expansion: RulesetExpansion::Complete {
                        rules: vec![LATER_RULE, RULE, LATER_RULE],
                    },
                    until: None,
                },
            },
        ];
        view.commands = vec![
            command(
                0,
                ProgramCommand::Catalog(CatalogDeclaration::Function(LEFT)),
            ),
            command(
                1,
                ProgramCommand::Catalog(CatalogDeclaration::Function(RIGHT)),
            ),
            command(
                2,
                ProgramCommand::Catalog(CatalogDeclaration::Index(IndexId::new(0))),
            ),
            command(
                3,
                ProgramCommand::CombinedRulesetDeclaration {
                    ruleset: COMBINED,
                    children: vec![
                        ruleset_reference(LATER_RULESET, "later"),
                        ruleset_reference(DEFAULT_RULESET, ""),
                        ruleset_reference(LATER_RULESET, "later"),
                    ],
                },
            ),
            command(4, ProgramCommand::RuleDeclaration(RULE)),
            command(
                5,
                ProgramCommand::Run {
                    schedule: ScheduleId::new(0),
                },
            ),
            command(
                6,
                ProgramCommand::Catalog(CatalogDeclaration::Ruleset(LATER_RULESET)),
            ),
            command(7, ProgramCommand::RuleDeclaration(LATER_RULE)),
            command(
                8,
                ProgramCommand::Run {
                    schedule: ScheduleId::new(1),
                },
            ),
        ];
        program(view.clone()).validate().unwrap();

        let mut diagnostic_renamed = view.clone();
        diagnostic_renamed.core.rulesets[1].name = "catalog-later-renamed".to_owned();
        diagnostic_renamed.core.rulesets[2].name = "catalog-combined-renamed".to_owned();
        let RulesetKind::Combined { children } = &mut diagnostic_renamed.ruleset_metadata[2].kind
        else {
            unreachable!()
        };
        children[0].name = "metadata-child-one".to_owned();
        children[1].name = "metadata-default".to_owned();
        children[2].name = "metadata-child-two".to_owned();
        let ProgramCommand::CombinedRulesetDeclaration { children, .. } =
            &mut diagnostic_renamed.commands[3].command
        else {
            unreachable!()
        };
        children[0].name = "command-child-one".to_owned();
        children[1].name = "command-default".to_owned();
        children[2].name = "command-child-two".to_owned();
        let Schedule::Run {
            expansion: RulesetExpansion::Missing { path },
            ..
        } = &mut diagnostic_renamed.schedules[0].schedule
        else {
            unreachable!()
        };
        path[0].name = "schedule-root".to_owned();
        path[1].name = "schedule-child".to_owned();
        program(diagnostic_renamed).validate().unwrap();

        let Schedule::Run {
            expansion: RulesetExpansion::Complete { rules },
            ..
        } = &mut view.schedules[1].schedule
        else {
            unreachable!()
        };
        rules.pop();
        let error = program(view).validate().unwrap_err();
        assert!(error.message.contains("exact prefix-frozen recursive"));
    }

    #[test]
    fn missing_run_and_print_name_stay_missing_after_later_declarations() {
        const LATER_RULESET: RulesetId = RulesetId::new(1);

        let mut view = base_view();
        // The implicit default is already prefix-visible under this spelling,
        // but the frozen missing path below points at a different exact ID.
        view.core.rulesets[0].name = "visible-decoy".to_owned();
        view.core.rulesets.push(RulesetDecl {
            id: LATER_RULESET,
            name: "later".to_owned(),
            rules: Vec::new(),
        });
        view.ruleset_metadata.push(RulesetMetadata {
            ruleset: LATER_RULESET,
            availability: RulesetAvailability::Declared,
            kind: RulesetKind::Concrete,
        });
        view.schedules[0].schedule = Schedule::Run {
            ruleset: ResolvedOrMissing::Missing {
                name: "visible-decoy".to_owned(),
            },
            expansion: RulesetExpansion::Missing {
                path: vec![ruleset_reference(LATER_RULESET, "later")],
            },
            until: None,
        };
        view.commands = vec![
            command(
                0,
                ProgramCommand::Catalog(CatalogDeclaration::Function(LEFT)),
            ),
            output_command(
                1,
                0,
                ProgramCommand::PrintSize(PrintSizeTarget::Named {
                    requested_name: "left".to_owned(),
                    target: ResolvedOrMissing::Missing {
                        name: "diagnostic-only-missing".to_owned(),
                    },
                }),
            ),
            command(
                2,
                ProgramCommand::Catalog(CatalogDeclaration::Function(RIGHT)),
            ),
            command(
                3,
                ProgramCommand::Catalog(CatalogDeclaration::Index(IndexId::new(0))),
            ),
            command(4, ProgramCommand::RuleDeclaration(RULE)),
            command(
                5,
                ProgramCommand::Run {
                    schedule: ScheduleId::new(0),
                },
            ),
            command(
                6,
                ProgramCommand::Catalog(CatalogDeclaration::Ruleset(LATER_RULESET)),
            ),
        ];
        program(view).validate().unwrap();
    }

    #[test]
    fn recursive_fail_has_first_error_and_suppressed_output_shape() {
        let mut view = base_view();
        view.schedules.push(ScheduleDecl {
            id: ScheduleId::new(1),
            schedule: view.schedules[0].schedule.clone(),
        });
        let nested = FailBlock {
            error_policy: FailErrorPolicy::FirstError,
            output_policy: FailOutputPolicy::SuppressAll,
            commands: vec![fail_command(
                0,
                ProgramCommand::PrintSize(PrintSizeTarget::Named {
                    requested_name: "left".to_owned(),
                    target: ResolvedOrMissing::Resolved(LEFT),
                }),
            )],
        };
        let outer = FailBlock {
            error_policy: FailErrorPolicy::FirstError,
            output_policy: FailOutputPolicy::SuppressAll,
            commands: vec![
                fail_command(
                    0,
                    ProgramCommand::Run {
                        schedule: ScheduleId::new(1),
                    },
                ),
                fail_command(1, ProgramCommand::Fail(nested)),
            ],
        };
        view.commands
            .insert(4, command(4, ProgramCommand::Fail(outer)));
        for (ordinal, command) in view.commands.iter_mut().enumerate() {
            command.ordinal = CommandOrdinal::new(u32::try_from(ordinal).unwrap());
        }
        program(view.clone()).validate().unwrap();

        let ProgramCommand::Fail(block) = &mut view.commands[4].command else {
            unreachable!()
        };
        block.commands[1].ordinal = FailCommandOrdinal::new(9);
        let error = program(view).validate().unwrap_err();
        assert!(error.message.contains("expected dense ID 1"));
    }

    #[test]
    fn nested_fail_commands_cannot_cross_the_enclosing_source_trigger() {
        let mut view = base_view();
        let mut nested = fail_command(
            0,
            ProgramCommand::PrintSize(PrintSizeTarget::Named {
                requested_name: "left".to_owned(),
                target: ResolvedOrMissing::Resolved(LEFT),
            }),
        );
        nested.origin = CommandOrigin::Source(source_ref(1, 0));
        view.commands.insert(
            4,
            command(
                4,
                ProgramCommand::Fail(FailBlock {
                    error_policy: FailErrorPolicy::FirstError,
                    output_policy: FailOutputPolicy::SuppressAll,
                    commands: vec![nested],
                }),
            ),
        );
        for (ordinal, command) in view.commands.iter_mut().enumerate() {
            command.ordinal = CommandOrdinal::new(u32::try_from(ordinal).unwrap());
        }
        let error = FrontendProgram {
            source: source_document_with(&[("", "(fail ...)", 1), (" ", "(other)", 1)], ""),
            inputs: Vec::new(),
            streams: ProgramStreams::ExecutionOnly { execution: view },
        }
        .validate()
        .unwrap_err();
        assert!(error.message.contains("enclosing source trigger"));
    }

    #[test]
    fn nested_fail_commands_cannot_switch_subcommands_within_one_group() {
        let mut view = base_view();
        let mut nested = fail_command(
            0,
            ProgramCommand::PrintSize(PrintSizeTarget::Named {
                requested_name: "left".to_owned(),
                target: ResolvedOrMissing::Resolved(LEFT),
            }),
        );
        nested.origin = CommandOrigin::Source(source_ref(0, 1));
        view.commands.insert(
            4,
            command(
                4,
                ProgramCommand::Fail(FailBlock {
                    error_policy: FailErrorPolicy::FirstError,
                    output_policy: FailOutputPolicy::SuppressAll,
                    commands: vec![nested],
                }),
            ),
        );
        for (ordinal, command) in view.commands.iter_mut().enumerate() {
            command.ordinal = CommandOrdinal::new(u32::try_from(ordinal).unwrap());
        }
        let error = FrontendProgram {
            source: source_document_with(&[("", "(two-command-macro)", 2)], ""),
            inputs: Vec::new(),
            streams: ProgramStreams::ExecutionOnly { execution: view },
        }
        .validate()
        .unwrap_err();
        assert!(error.message.contains("enclosing source trigger"));
    }

    #[test]
    fn shared_input_content_uses_view_local_targets() {
        let payload = InputPayload {
            id: InputPayloadId::new(0),
            path: InputPathMetadata {
                declared: PathBuf::from("facts.tsv"),
                fact_directory: None,
                effective: PathBuf::from("facts.tsv"),
            },
            bytes: Vec::new(),
            input: InputPayloadData {
                subtype: InputFunctionSubtype::Custom,
                declared_inputs: vec![DeclaredInputSort::new(
                    "arbitrary-input-diagnostic",
                    InputSortAuthority::I64,
                )],
                declared_outputs: vec![DeclaredInputSort::new(
                    "arbitrary-output-diagnostic",
                    InputSortAuthority::I64,
                )],
                effective_inputs: vec![InputScalarKind::I64],
                effective_outputs: vec![InputScalarKind::I64],
                rows: Vec::new(),
            },
        };
        let mut execution = base_view();
        execution.commands.insert(
            2,
            command(
                2,
                ProgramCommand::Input {
                    payload: InputPayloadId::new(0),
                    plan: InputTargetPlan::Direct {
                        write: InputWrite {
                            role: InputWriteRole::Direct,
                            target: LEFT,
                            mode: InputWriteMode::Insert,
                            values: vec![
                                InputRowValue::PayloadColumn {
                                    role: InputColumnRole::Input,
                                    column: 0,
                                },
                                InputRowValue::PayloadColumn {
                                    role: InputColumnRole::Output,
                                    column: 0,
                                },
                            ],
                        },
                    },
                },
            ),
        );
        for (ordinal, command) in execution.commands.iter_mut().enumerate() {
            command.ordinal = CommandOrdinal::new(u32::try_from(ordinal).unwrap());
        }
        let mut proof_check = execution.clone();
        let ProgramCommand::Input { plan, .. } = &mut proof_check.commands[2].command else {
            unreachable!()
        };
        *plan = InputTargetPlan::LoweredActions {
            write: InputWrite {
                role: InputWriteRole::LoweredAction,
                target: RIGHT,
                mode: InputWriteMode::Set,
                values: vec![
                    InputRowValue::PayloadColumn {
                        role: InputColumnRole::Input,
                        column: 0,
                    },
                    InputRowValue::PayloadColumn {
                        role: InputColumnRole::Output,
                        column: 0,
                    },
                ],
            },
        };
        for command in &mut proof_check.commands {
            command.output = None;
        }
        let exact = FrontendProgram {
            source: source_document(),
            inputs: vec![payload],
            streams: ProgramStreams::ProofInstrumented {
                execution,
                proof_check,
            },
        };
        exact.validate().unwrap();

        let mut retargeted = exact;
        retargeted.source = source_document_with(&[("", "(input-and-run-macro)", 2)], "");
        let ProgramStreams::ProofInstrumented { proof_check, .. } = &mut retargeted.streams else {
            unreachable!()
        };
        proof_check.commands[2].origin = CommandOrigin::Source(source_ref(0, 1));
        for command in &mut proof_check.commands[3..] {
            command.origin = CommandOrigin::Generated {
                trigger: Some(source_ref(0, 1)),
                role: GeneratedCommandRole::ProofInstrumentation,
            };
        }
        let error = retargeted.validate().unwrap_err();
        assert!(
            error
                .message
                .contains("payload sequence per source subcommand")
        );
    }

    #[test]
    fn encoded_input_stamps_exact_ordered_term_and_view_plan() {
        const TERM: SortId = SortId::new(2);

        let mut view = base_view();
        view.core.sorts.push(SortDecl {
            id: TERM,
            name: "Term".to_owned(),
            semantics: SortSemantics::Eq,
            unionable: true,
        });
        let term = &mut view.core.functions[0];
        term.schema = vec![I64, I64, TERM, UNIT];
        term.n_values = 1;
        term.merge.values[0].sort = UNIT;
        term.internal_term_node = true;
        let encoded_view = &mut view.core.functions[1];
        encoded_view.name = "left-view".to_owned();
        encoded_view.schema = vec![I64, I64, UNIT];
        encoded_view.n_values = 2;
        encoded_view.merge.values = vec![
            MergeValueNode {
                id: MergeValueId::new(0),
                sort: I64,
                operation: MergeValueOperation::OldValue { column: 0 },
            },
            MergeValueNode {
                id: MergeValueId::new(1),
                sort: UNIT,
                operation: MergeValueOperation::OldValue { column: 1 },
            },
        ];
        encoded_view.merge.results = vec![MergeValueId::new(0), MergeValueId::new(1)];
        encoded_view.term_constructor = Some(LEFT);
        encoded_view.display.print_size_name = "left".to_owned();

        let payload = InputPayload {
            id: InputPayloadId::new(0),
            path: InputPathMetadata {
                declared: PathBuf::from("facts.tsv"),
                fact_directory: None,
                effective: PathBuf::from("facts.tsv"),
            },
            bytes: Vec::new(),
            input: InputPayloadData {
                subtype: InputFunctionSubtype::Custom,
                declared_inputs: vec![DeclaredInputSort::new("i64", InputSortAuthority::I64)],
                declared_outputs: vec![DeclaredInputSort::new("i64", InputSortAuthority::I64)],
                effective_inputs: vec![InputScalarKind::I64],
                effective_outputs: vec![InputScalarKind::I64],
                rows: Vec::new(),
            },
        };
        let encoded = ProgramCommand::Input {
            payload: InputPayloadId::new(0),
            plan: InputTargetPlan::Encoded {
                fresh_slots: vec![InputFreshSlot {
                    id: InputFreshSlotId::new(0),
                    role: InputFreshRole::Term,
                    sort: TERM,
                }],
                writes: vec![
                    InputWrite {
                        role: InputWriteRole::TermRelation,
                        target: LEFT,
                        mode: InputWriteMode::Insert,
                        values: vec![
                            InputRowValue::PayloadColumn {
                                role: InputColumnRole::Input,
                                column: 0,
                            },
                            InputRowValue::PayloadColumn {
                                role: InputColumnRole::Output,
                                column: 0,
                            },
                            InputRowValue::Fresh(InputFreshSlotId::new(0)),
                            InputRowValue::Unit,
                        ],
                    },
                    InputWrite {
                        role: InputWriteRole::View,
                        target: RIGHT,
                        mode: InputWriteMode::Insert,
                        values: vec![
                            InputRowValue::PayloadColumn {
                                role: InputColumnRole::Input,
                                column: 0,
                            },
                            InputRowValue::PayloadColumn {
                                role: InputColumnRole::Output,
                                column: 0,
                            },
                            InputRowValue::Unit,
                        ],
                    },
                ],
            },
        };
        view.commands.insert(2, command(2, encoded));
        for (ordinal, command) in view.commands.iter_mut().enumerate() {
            command.ordinal = CommandOrdinal::new(u32::try_from(ordinal).unwrap());
        }
        let encoded_program = FrontendProgram {
            source: source_document(),
            inputs: vec![payload],
            streams: ProgramStreams::ExecutionOnly {
                execution: view.clone(),
            },
        };
        encoded_program.validate().unwrap();

        let mut plain_target = encoded_program.clone();
        let ProgramStreams::ExecutionOnly { execution } = &mut plain_target.streams else {
            unreachable!()
        };
        execution.core.functions[0].internal_term_node = false;
        let error = plain_target.validate().unwrap_err();
        assert!(error.message.contains("exact internal term node"));

        let mut unrelated_view = encoded_program.clone();
        let ProgramStreams::ExecutionOnly { execution } = &mut unrelated_view.streams else {
            unreachable!()
        };
        execution.core.functions[1].term_constructor = None;
        execution.core.functions[1].display.print_size_name = "left-view".to_owned();
        let error = unrelated_view.validate().unwrap_err();
        assert!(
            error
                .message
                .contains("point back to the exact term-relation")
        );

        let ProgramCommand::Input {
            plan: InputTargetPlan::Encoded { writes, .. },
            ..
        } = &mut view.commands[2].command
        else {
            unreachable!()
        };
        writes.swap(0, 1);
        let error = FrontendProgram {
            source: source_document(),
            inputs: encoded_program.inputs,
            streams: ProgramStreams::ExecutionOnly { execution: view },
        }
        .validate()
        .unwrap_err();
        assert!(error.message.contains("exact term/proof/view order"));
    }

    #[test]
    fn encoded_proof_input_requires_one_exact_ast_target_for_both_sides() {
        const TERM: SortId = SortId::new(2);
        const AST: SortId = SortId::new(3);
        const PROOF: SortId = SortId::new(4);
        const AST_TARGET: FunctionId = FunctionId::new(2);
        const AST_DECOY: FunctionId = FunctionId::new(3);
        const FIAT: FunctionId = FunctionId::new(4);

        fn eq_sort(id: SortId, name: &str) -> SortDecl {
            SortDecl {
                id,
                name: name.to_owned(),
                semantics: SortSemantics::Eq,
                unionable: true,
            }
        }

        fn unit_relation(
            id: FunctionId,
            name: &str,
            keys: impl IntoIterator<Item = SortId>,
        ) -> FunctionConfig {
            let mut relation = function(id, name);
            relation.schema = keys.into_iter().chain([UNIT]).collect();
            relation.n_values = 1;
            relation.merge.owner = id;
            relation.merge.values[0].sort = UNIT;
            relation
        }

        fn metadata(function: FunctionId) -> FunctionMetadata {
            FunctionMetadata {
                function,
                extraction_cost: None,
                unextractable: false,
                merge_context: PrimitiveCallContext::Write,
            }
        }

        let mut view = base_view();
        view.core.sorts.extend([
            eq_sort(TERM, "Term"),
            eq_sort(AST, "Ast"),
            eq_sort(PROOF, "Proof"),
        ]);
        let term = &mut view.core.functions[0];
        term.schema = vec![I64, I64, TERM, UNIT];
        term.n_values = 1;
        term.merge.values[0].sort = UNIT;
        term.internal_term_node = true;
        let encoded_view = &mut view.core.functions[1];
        encoded_view.name = "left-view".to_owned();
        encoded_view.schema = vec![I64, I64, PROOF];
        encoded_view.n_values = 2;
        encoded_view.merge.values = vec![
            MergeValueNode {
                id: MergeValueId::new(0),
                sort: I64,
                operation: MergeValueOperation::OldValue { column: 0 },
            },
            MergeValueNode {
                id: MergeValueId::new(1),
                sort: PROOF,
                operation: MergeValueOperation::OldValue { column: 1 },
            },
        ];
        encoded_view.merge.results = vec![MergeValueId::new(0), MergeValueId::new(1)];
        encoded_view.term_constructor = Some(LEFT);
        encoded_view.display.print_size_name = "left".to_owned();
        view.core.functions.extend([
            unit_relation(AST_TARGET, "ast", [TERM, AST]),
            unit_relation(AST_DECOY, "ast-decoy", [TERM, AST]),
            unit_relation(FIAT, "fiat", [AST, AST, PROOF]),
        ]);
        view.function_metadata
            .extend([metadata(AST_TARGET), metadata(AST_DECOY), metadata(FIAT)]);

        let payload = InputPayload {
            id: InputPayloadId::new(0),
            path: InputPathMetadata {
                declared: PathBuf::from("facts.tsv"),
                fact_directory: None,
                effective: PathBuf::from("facts.tsv"),
            },
            bytes: Vec::new(),
            input: InputPayloadData {
                subtype: InputFunctionSubtype::Custom,
                declared_inputs: vec![DeclaredInputSort::new("i64", InputSortAuthority::I64)],
                declared_outputs: vec![DeclaredInputSort::new("i64", InputSortAuthority::I64)],
                effective_inputs: vec![InputScalarKind::I64],
                effective_outputs: vec![InputScalarKind::I64],
                rows: Vec::new(),
            },
        };
        let input = ProgramCommand::Input {
            payload: InputPayloadId::new(0),
            plan: InputTargetPlan::Encoded {
                fresh_slots: vec![
                    InputFreshSlot {
                        id: InputFreshSlotId::new(0),
                        role: InputFreshRole::Term,
                        sort: TERM,
                    },
                    InputFreshSlot {
                        id: InputFreshSlotId::new(1),
                        role: InputFreshRole::AstLeft,
                        sort: AST,
                    },
                    InputFreshSlot {
                        id: InputFreshSlotId::new(2),
                        role: InputFreshRole::AstRight,
                        sort: AST,
                    },
                    InputFreshSlot {
                        id: InputFreshSlotId::new(3),
                        role: InputFreshRole::FiatProof,
                        sort: PROOF,
                    },
                ],
                writes: vec![
                    InputWrite {
                        role: InputWriteRole::TermRelation,
                        target: LEFT,
                        mode: InputWriteMode::Insert,
                        values: vec![
                            InputRowValue::PayloadColumn {
                                role: InputColumnRole::Input,
                                column: 0,
                            },
                            InputRowValue::PayloadColumn {
                                role: InputColumnRole::Output,
                                column: 0,
                            },
                            InputRowValue::Fresh(InputFreshSlotId::new(0)),
                            InputRowValue::Unit,
                        ],
                    },
                    InputWrite {
                        role: InputWriteRole::AstLeft,
                        target: AST_TARGET,
                        mode: InputWriteMode::Insert,
                        values: vec![
                            InputRowValue::Fresh(InputFreshSlotId::new(0)),
                            InputRowValue::Fresh(InputFreshSlotId::new(1)),
                            InputRowValue::Unit,
                        ],
                    },
                    InputWrite {
                        role: InputWriteRole::AstRight,
                        target: AST_TARGET,
                        mode: InputWriteMode::Insert,
                        values: vec![
                            InputRowValue::Fresh(InputFreshSlotId::new(0)),
                            InputRowValue::Fresh(InputFreshSlotId::new(2)),
                            InputRowValue::Unit,
                        ],
                    },
                    InputWrite {
                        role: InputWriteRole::Fiat,
                        target: FIAT,
                        mode: InputWriteMode::Insert,
                        values: vec![
                            InputRowValue::Fresh(InputFreshSlotId::new(1)),
                            InputRowValue::Fresh(InputFreshSlotId::new(2)),
                            InputRowValue::Fresh(InputFreshSlotId::new(3)),
                            InputRowValue::Unit,
                        ],
                    },
                    InputWrite {
                        role: InputWriteRole::View,
                        target: RIGHT,
                        mode: InputWriteMode::Insert,
                        values: vec![
                            InputRowValue::PayloadColumn {
                                role: InputColumnRole::Input,
                                column: 0,
                            },
                            InputRowValue::PayloadColumn {
                                role: InputColumnRole::Output,
                                column: 0,
                            },
                            InputRowValue::Fresh(InputFreshSlotId::new(3)),
                        ],
                    },
                ],
            },
        };
        for (offset, target) in [AST_TARGET, AST_DECOY, FIAT].into_iter().enumerate() {
            view.commands.insert(
                2 + offset,
                command(
                    0,
                    ProgramCommand::Catalog(CatalogDeclaration::Function(target)),
                ),
            );
        }
        view.commands.insert(5, command(0, input));
        for (ordinal, command) in view.commands.iter_mut().enumerate() {
            command.ordinal = CommandOrdinal::new(u32::try_from(ordinal).unwrap());
        }
        let exact = FrontendProgram {
            source: source_document(),
            inputs: vec![payload],
            streams: ProgramStreams::ExecutionOnly { execution: view },
        };
        exact.validate().unwrap();

        let mut split = exact.clone();
        let ProgramStreams::ExecutionOnly { execution } = &mut split.streams else {
            unreachable!()
        };
        let ProgramCommand::Input {
            plan: InputTargetPlan::Encoded { writes, .. },
            ..
        } = &mut execution.commands[5].command
        else {
            unreachable!()
        };
        writes[2].target = AST_DECOY;
        let error = split.validate().unwrap_err();
        assert!(error.message.contains("exact nominal target"));

        let mut same_decoy = exact;
        let ProgramStreams::ExecutionOnly { execution } = &mut same_decoy.streams else {
            unreachable!()
        };
        let ProgramCommand::Input {
            plan: InputTargetPlan::Encoded { writes, .. },
            ..
        } = &mut execution.commands[5].command
        else {
            unreachable!()
        };
        writes[1].target = AST_DECOY;
        writes[2].target = AST_DECOY;
        same_decoy.validate().unwrap();
    }

    #[test]
    fn successful_input_payload_is_exactly_reparsed_from_its_path_and_bytes() {
        let schema = TypedInputSchema {
            subtype: InputFunctionSubtype::Custom,
            declared_inputs: vec![DeclaredInputSort::new(
                "diagnostic-input",
                InputSortAuthority::I64,
            )],
            declared_outputs: vec![DeclaredInputSort::new(
                "diagnostic-output",
                InputSortAuthority::I64,
            )],
            effective_inputs: vec![InputScalarKind::I64],
            effective_outputs: vec![InputScalarKind::I64],
        };
        let bytes = b"1\t2\n".to_vec();
        let input =
            parse_tsv_with_resolved_schema(std::str::from_utf8(&bytes).unwrap(), &schema).unwrap();
        let payload = InputPayload::from_typed_file(
            InputPayloadId::new(0),
            TypedInputFile {
                path: resolve_input_path(Some(std::path::Path::new("facts")), "rows.tsv"),
                bytes,
                input,
            },
        );
        validate_inputs(std::slice::from_ref(&payload), "inputs").unwrap();

        let mut wrong_rows = payload.clone();
        wrong_rows.input.rows.clear();
        let error = validate_inputs(&[wrong_rows], "inputs").unwrap_err();
        assert!(error.message.contains("exact parse"));

        let mut wrong_bytes = payload.clone();
        wrong_bytes.bytes = b"9\t2\n".to_vec();
        let error = validate_inputs(&[wrong_bytes], "inputs").unwrap_err();
        assert!(error.message.contains("exact parse"));

        let mut primitive_looking_unsupported = payload.clone();
        primitive_looking_unsupported.input.declared_inputs[0] =
            DeclaredInputSort::new("i64", InputSortAuthority::Unsupported);
        let error = validate_inputs(&[primitive_looking_unsupported], "inputs").unwrap_err();
        assert!(error.message.contains("do not parse"));

        let mut wrong_path = payload;
        wrong_path.path.effective = PathBuf::from("elsewhere/rows.tsv");
        let error = validate_inputs(&[wrong_path], "inputs").unwrap_err();
        assert!(error.message.contains("exact pure resolution"));
    }

    #[test]
    fn fail_admits_exact_pre_lowering_rule_rejection_without_membership() {
        const COMBINED: RulesetId = RulesetId::new(1);

        let mut view = base_view();
        view.core.rulesets.push(RulesetDecl {
            id: COMBINED,
            name: "combined".to_owned(),
            rules: Vec::new(),
        });
        view.ruleset_metadata.push(RulesetMetadata {
            ruleset: COMBINED,
            availability: RulesetAvailability::Declared,
            kind: RulesetKind::Combined {
                children: vec![ruleset_reference(DEFAULT_RULESET, "")],
            },
        });
        view.commands.insert(
            3,
            command(
                3,
                ProgramCommand::CombinedRulesetDeclaration {
                    ruleset: COMBINED,
                    children: vec![ruleset_reference(DEFAULT_RULESET, "")],
                },
            ),
        );
        view.commands.insert(
            5,
            command(
                5,
                ProgramCommand::Fail(FailBlock {
                    error_policy: FailErrorPolicy::FirstError,
                    output_policy: FailOutputPolicy::SuppressAll,
                    commands: vec![fail_command(
                        0,
                        ProgramCommand::RejectedRuleDeclaration(RejectedRuleDeclaration {
                            rule_name: "must-fail".to_owned(),
                            target: ResolvedOrMissing::Resolved(COMBINED),
                            reason: RejectedRuleReason::CombinedRuleset,
                        }),
                    )],
                }),
            ),
        );
        for (ordinal, command) in view.commands.iter_mut().enumerate() {
            command.ordinal = CommandOrdinal::new(u32::try_from(ordinal).unwrap());
        }
        program(view.clone()).validate().unwrap();

        let ProgramCommand::Fail(block) = &mut view.commands[5].command else {
            unreachable!()
        };
        block.commands[0].command = ProgramCommand::RuleDeclaration(RULE);
        let error = program(view).validate().unwrap_err();
        assert!(error.message.contains("guarded activation"));
    }

    #[test]
    fn rejected_input_is_nested_fail_only_and_preserves_exact_index() {
        let rejected = ProgramCommand::RejectedInput(RejectedInput {
            // Deliberately names the same-schema function decoy. The exact
            // IndexId below, not this diagnostic, defines the rejected target.
            requested_target: "right".to_owned(),
            path: InputPathMetadata {
                declared: PathBuf::from("facts.tsv"),
                fact_directory: None,
                effective: PathBuf::from("facts.tsv"),
            },
            reason: RejectedInputReason::IndexReadOnly(IndexId::new(0)),
        });
        let mut view = base_view();
        view.commands.insert(
            3,
            command(
                3,
                ProgramCommand::Fail(FailBlock {
                    error_policy: FailErrorPolicy::FirstError,
                    output_policy: FailOutputPolicy::SuppressAll,
                    commands: vec![fail_command(0, rejected.clone())],
                }),
            ),
        );
        for (ordinal, command) in view.commands.iter_mut().enumerate() {
            command.ordinal = CommandOrdinal::new(u32::try_from(ordinal).unwrap());
        }
        program(view.clone()).validate().unwrap();

        view.commands[3].command = rejected;
        let error = program(view).validate().unwrap_err();
        assert!(error.message.contains("only inside a Fail"));
    }

    #[test]
    fn missing_input_names_are_diagnostics_not_prefix_resolution_queries() {
        let mut view = base_view();
        view.commands.insert(
            3,
            command(
                3,
                ProgramCommand::Fail(FailBlock {
                    error_policy: FailErrorPolicy::FirstError,
                    output_policy: FailOutputPolicy::SuppressAll,
                    commands: vec![fail_command(
                        0,
                        ProgramCommand::RejectedInput(RejectedInput {
                            requested_target: "left".to_owned(),
                            path: InputPathMetadata {
                                declared: PathBuf::from("facts.tsv"),
                                fact_directory: None,
                                effective: PathBuf::from("facts.tsv"),
                            },
                            reason: RejectedInputReason::MissingTarget {
                                name: "right".to_owned(),
                            },
                        }),
                    )],
                }),
            ),
        );
        for (ordinal, command) in view.commands.iter_mut().enumerate() {
            command.ordinal = CommandOrdinal::new(u32::try_from(ordinal).unwrap());
        }
        program(view.clone()).validate().unwrap();

        let ProgramCommand::Fail(block) = &mut view.commands[3].command else {
            unreachable!()
        };
        let ProgramCommand::RejectedInput(rejected) = &mut block.commands[0].command else {
            unreachable!()
        };
        rejected.requested_target = "renamed-request".to_owned();
        let RejectedInputReason::MissingTarget { name } = &mut rejected.reason else {
            unreachable!()
        };
        *name = "renamed-missing".to_owned();
        program(view).validate().unwrap();
    }

    #[test]
    fn unsupported_input_schema_is_an_exact_uncatchable_authority_failure() {
        let mut view = base_view();
        view.core.functions[0].schema[0] = UNIT;
        let unsupported = TypedInputParseError::UnsupportedSort {
            role: InputColumnRole::Input,
            column_ordinal: 0,
            sort: "diagnostic-sort-spelling".into(),
        };
        let rejected = RejectedInput {
            // The diagnostic intentionally spells the supported decoy target.
            requested_target: "right".to_owned(),
            path: InputPathMetadata {
                declared: PathBuf::from("facts.tsv"),
                fact_directory: None,
                effective: PathBuf::from("facts.tsv"),
            },
            reason: RejectedInputReason::UnsupportedSchema {
                target: LEFT,
                error: unsupported.clone(),
            },
        };
        assert_eq!(
            rejected.reason.failure_class(),
            FrontendFailureClass::UncatchablePanic
        );
        view.commands.insert(
            3,
            command(
                3,
                ProgramCommand::Fail(FailBlock {
                    error_policy: FailErrorPolicy::FirstError,
                    output_policy: FailOutputPolicy::SuppressAll,
                    commands: vec![fail_command(
                        0,
                        ProgramCommand::RejectedInput(rejected.clone()),
                    )],
                }),
            ),
        );
        for (ordinal, command) in view.commands.iter_mut().enumerate() {
            command.ordinal = CommandOrdinal::new(u32::try_from(ordinal).unwrap());
        }
        program(view.clone()).validate().unwrap();

        let ProgramCommand::Fail(block) = &mut view.commands[3].command else {
            unreachable!()
        };
        let ProgramCommand::RejectedInput(rejected) = &mut block.commands[0].command else {
            unreachable!()
        };
        rejected.reason = RejectedInputReason::TypedParse {
            target: LEFT,
            error: unsupported,
        };
        let error = program(view.clone()).validate().unwrap_err();
        assert!(error.message.contains("schema-authority failure"));

        let ProgramCommand::Fail(block) = &mut view.commands[3].command else {
            unreachable!()
        };
        let ProgramCommand::RejectedInput(rejected) = &mut block.commands[0].command else {
            unreachable!()
        };
        rejected.reason = RejectedInputReason::UnsupportedSchema {
            target: RIGHT,
            error: TypedInputParseError::UnsupportedSort {
                role: InputColumnRole::Input,
                column_ordinal: 0,
                sort: "same-shape-decoy".into(),
            },
        };
        let error = program(view).validate().unwrap_err();
        assert!(error.message.contains("exactly supported"));
    }

    #[test]
    fn push_and_pop_are_never_admitted_commands() {
        for unsupported in [
            UnsupportedCommand::Push { levels: 0 },
            UnsupportedCommand::Pop { levels: 1 },
        ] {
            let mut view = base_view();
            view.commands[4] = command(4, ProgramCommand::Unsupported(unsupported));
            let error = program(view).validate().unwrap_err();
            assert!(error.message.contains("is not admitted"));
        }
    }
}

//! Owned, backend-neutral vocabulary for a resolved frontend snapshot.
//!
//! This module deliberately contains no capture or execution code.  Its IDs are
//! nominal frontend IDs, not handles from `egglog-bridge` or any other backend.
//! Names are retained for diagnostics and display only; references always use
//! the exact ID selected by the resolved program.
//!
//! This is intentionally the command-neutral core slice, not yet the complete
//! public compilation snapshot.  The capture slice must still add an index
//! declaration identity/catalog, primitive call context and effect, the full
//! rule-evaluation mode and source `include_subsumed` bit, extraction
//! cost/unextractable metadata, schedules, commands, and source ordinals.  The
//! effective per-atom read mode plus `seminaive`/`no_decomp` are retained here.

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt::{self, Display, Formatter};

macro_rules! stable_id {
    ($(#[$meta:meta])* $name:ident) => {
        $(#[$meta])*
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $name(u32);

        impl $name {
            /// Construct an ID from its deterministic snapshot ordinal.
            pub const fn new(ordinal: u32) -> Self {
                Self(ordinal)
            }

            /// Return the deterministic snapshot ordinal.
            pub const fn ordinal(self) -> u32 {
                self.0
            }
        }
    };
}

stable_id!(
    /// Stable identity of a sort in one snapshot.
    SortId
);
stable_id!(
    /// Stable identity of a function table in one snapshot.
    FunctionId
);
stable_id!(
    /// Stable identity of a specialized primitive call signature.
    PrimitiveId
);
stable_id!(
    /// Stable identity of a resolved logical rule.
    RuleId
);
stable_id!(
    /// Stable identity of a resolved ruleset.
    RulesetId
);
stable_id!(
    /// Stable identity of a value expression in a merge arena.
    MergeValueId
);
stable_id!(
    /// Rule-local identity of a typed variable.
    RuleVarId
);
stable_id!(
    /// Merge-local identity of a `let` slot.
    MergeLetSlot
);

/// Semantic storage class of a resolved sort.
///
/// `Opaque` and `Container` make unsupported sorts explicit so a standalone
/// compiler can reject them at admission rather than confusing them with a
/// supported scalar having the same display name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SortSemantics {
    Eq,
    Unit,
    Bool,
    I64,
    F64,
    String,
    BigInt,
    BigRat,
    Container {
        constructor: String,
        parameters: Vec<SortId>,
        contains_eq: bool,
    },
    Opaque {
        type_name: String,
    },
}

/// A nominal sort declaration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SortDecl {
    pub id: SortId,
    pub name: String,
    pub semantics: SortSemantics,
    /// Whether the frontend authorizes semantic union on values of this sort.
    /// This is independent of Eq-shaped storage: encoded relation and term
    /// sorts may use Eq IDs while deliberately forbidding union.
    pub unionable: bool,
}

/// An exact, graph-neutral literal payload.
///
/// Floating-point values are bits, never a host `f64`.  Arbitrary precision
/// numbers are retained as signed decimal components so the snapshot neither
/// interns them into a backend nor loses precision.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LiteralValue {
    Unit,
    Bool(bool),
    I64(i64),
    F64Bits(u64),
    String(String),
    BigIntDecimal(String),
    BigRat {
        numerator_decimal: String,
        denominator_decimal: String,
    },
    Opaque(String),
}

/// A literal paired with its exact nominal sort.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedLiteral {
    pub sort: SortId,
    pub value: LiteralValue,
}

/// Backend-neutral descriptors for raw-value primitives.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NativeRawPrimitive {
    /// Succeeds exactly when both values are equal and returns `Unit`.
    ///
    /// This is a distinct registration-site authority from an opaque
    /// same-name primitive; canonical core lowering selects it by the
    /// frontend's exact `ValueEq` authority.
    ValueEq,
    ValueNeq,
    OrderingMin,
    OrderingMax,
    SelectMinPayload,
    SelectMaxPayload,
    SelectEqPayload,
}

/// Backend-neutral descriptors for reached scalar primitives.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NativeScalarPrimitive {
    I64Add,
    I64Sub,
    I64Mul,
    I64Div,
    I64Rem,
    I64BitAnd,
    I64Min,
    I64Max,
    I64Ge,
    I64Gt,
    I64Le,
    I64Lt,
    I64BoolLt,
    F64Gt,
    F64Lt,
}

/// The authority for a primitive's behavior.
///
/// The display name in [`PrimitiveDecl`] is never consulted to select one of
/// these semantics.  Proof FD operations retain their exact function target.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrimitiveSemantics {
    NativeRaw(NativeRawPrimitive),
    NativeScalar(NativeScalarPrimitive),
    Fresh,
    /// Lookup-or-insert using the target's full key-plus-value schema and
    /// return its fixed primary value column (value column zero). Tuple-output
    /// proof FD views are intentional: every proposed value is an input even
    /// though this primitive returns only the primary column.
    SetIfEmpty {
        target: FunctionId,
    },
    ViewColumn {
        target: FunctionId,
        /// Zero-based value-column index, excluding key columns.
        value_column: usize,
    },
    Opaque {
        authority: String,
    },
}

/// One concretely typed primitive registration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrimitiveDecl {
    pub id: PrimitiveId,
    /// Diagnostic source name only.
    pub name: String,
    pub input: Vec<SortId>,
    pub output: SortId,
    pub semantics: PrimitiveSemantics,
}

/// Coarse source-level function kind.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FunctionKind {
    Constructor,
    Custom,
}

/// Missing-key behavior of a function lookup.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FunctionDefault {
    FreshId,
    Fail,
    Constant(TypedLiteral),
}

/// Frozen user-facing rendering metadata.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionDisplay {
    /// Name used for this table in the all-functions `print-size` rendering.
    pub print_size_name: String,
}

/// What to do when a candidate row has no current owner row.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MissingOwnerPolicy {
    /// Insert the candidate without evaluating merge actions or result roots.
    InsertCandidateWithoutMerge,
}

/// A typed node in a lazy merge arena.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MergeValueNode {
    pub id: MergeValueId,
    pub sort: SortId,
    pub operation: MergeValueOperation,
}

/// The owning old/new values used by a function-based merge short circuit.
///
/// Equality is Egglog value equality for the guard's exact nominal sort: the
/// same equality the reference bridge applies to its resolved `Value`s (not a
/// nullable SQL comparison or a source-name-selected numeric operator).  An
/// evaluator must compare these operands before evaluating any `arguments`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OwnerEqualityGuard {
    pub old: MergeValueId,
    pub new: MergeValueId,
}

/// A lazy merge value operation.
///
/// Child IDs are expression references, not an eager instruction order.  Roots
/// are evaluated in the order stated by [`MergeProgram`].  An ID does not grant
/// permission to hoist or globally precompute a node; each reached occurrence
/// is evaluated in its root's lazy context.  Cross-root reuse is explicit only
/// through [`MergeValueOperation::LetValue`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MergeValueOperation {
    OldValue {
        column: usize,
    },
    NewValue {
        column: usize,
    },
    LetValue {
        slot: MergeLetSlot,
    },
    Constant(TypedLiteral),
    AssertEq {
        old: MergeValueId,
        new: MergeValueId,
    },
    UnionId {
        left: MergeValueId,
        right: MergeValueId,
    },
    Primitive {
        primitive: PrimitiveId,
        arguments: Vec<MergeValueId>,
    },
    /// Reference-compatible function merge call.
    ///
    /// First evaluate only `guard.old` and `guard.new`.  If they are equal,
    /// return the old guard value immediately: do not evaluate arguments and do
    /// not touch `target`.  Otherwise evaluate `arguments` left-to-right and
    /// perform exactly one lookup-or-insert on the exact target.  Return its
    /// value on success.  A target miss with no default, or fresh-ID exhaustion,
    /// is an error; it is not a Lookup-style fallback.  The guard column and
    /// target output must have the same exact nominal sort, so both branches
    /// produce this node's one statically declared sort.
    Function {
        target: FunctionId,
        guard: OwnerEqualityGuard,
        arguments: Vec<MergeValueId>,
    },
    /// Reference-compatible lookup merge call.
    ///
    /// Evaluate `arguments` left-to-right, perform exactly one
    /// lookup-or-insert on the exact target, and return its value on success.
    /// If the target has no result, return `fallback_old`; fresh-ID exhaustion
    /// remains an error.  The fallback is not evaluated or substituted before
    /// the target call.
    Lookup {
        target: FunctionId,
        arguments: Vec<MergeValueId>,
        /// Exact owning old value returned if lookup-or-insert has no result.
        fallback_old: MergeValueId,
    },
}

/// A side effect root in a merge program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MergeAction {
    Let {
        slot: MergeLetSlot,
        value: MergeValueId,
    },
    Set {
        target: FunctionId,
        row: Vec<MergeValueId>,
    },
    Union {
        left: MergeValueId,
        right: MergeValueId,
    },
}

/// A complete typed merge program for one owning function.
///
/// Actions are evaluated in vector order.  Roots inside each action are
/// evaluated left-to-right; result roots are then evaluated left-to-right.
/// `identity_values: None` on the owner does not suppress equal collisions, so
/// this ordering (and all effects) remains observable on such collisions.
/// This DTO validates the normative lazy shape but has no evaluator.  The
/// linker/compiler slice must separately test an equal Function guard with a
/// failing/effectful argument, unequal-guard argument order, and Lookup
/// hit/miss behavior against the reference backend.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MergeProgram {
    pub owner: FunctionId,
    pub missing_owner: MissingOwnerPolicy,
    pub values: Vec<MergeValueNode>,
    pub actions: Vec<MergeAction>,
    pub results: Vec<MergeValueId>,
}

/// An owned function table configuration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionConfig {
    pub id: FunctionId,
    pub name: String,
    pub kind: FunctionKind,
    /// Key sorts followed by value sorts.
    pub schema: Vec<SortId>,
    pub n_values: usize,
    /// An opt-in non-empty prefix of value columns that may suppress a merge.
    /// `None` means even equal collisions evaluate actions and result roots.
    pub identity_values: Option<usize>,
    pub default: FunctionDefault,
    pub merge: MergeProgram,
    pub can_subsume: bool,
    pub internal_hidden: bool,
    pub internal_let: bool,
    /// Exact source/term relation whose user-facing constructor view this
    /// table implements. The target's name is display metadata only.
    pub term_constructor: Option<FunctionId>,
    pub internal_term_node: bool,
    pub display: FunctionDisplay,
}

impl FunctionConfig {
    /// Number of leading key columns.
    pub fn n_keys(&self) -> usize {
        self.schema.len().saturating_sub(self.n_values)
    }

    /// Exact value-column sorts.
    pub fn value_sorts(&self) -> &[SortId] {
        &self.schema[self.n_keys()..]
    }
}

/// Which physical row view a rule atom reads.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReadMode {
    Live,
    Subsumed,
    All,
}

/// A rule-local typed variable.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RuleVar {
    pub id: RuleVarId,
    pub name: String,
    pub sort: SortId,
}

/// A typed term in core rule syntax.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RuleTerm {
    Variable(RuleVar),
    Literal(TypedLiteral),
}

impl RuleTerm {
    pub fn sort(&self) -> SortId {
        match self {
            Self::Variable(variable) => variable.sort,
            Self::Literal(literal) => literal.sort,
        }
    }
}

/// Exact call identity for a rule body atom.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RuleBodyCall {
    Table {
        target: FunctionId,
        read: ReadMode,
    },
    IndexTable {
        target: FunctionId,
        any_of: Vec<usize>,
        read: ReadMode,
    },
    Primitive {
        primitive: PrimitiveId,
    },
}

/// One core query atom; its terms include the output term.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RuleBodyAtom {
    pub call: RuleBodyCall,
    pub terms: Vec<RuleTerm>,
}

/// Exact call identity for an action `let`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RuleActionCall {
    Table(FunctionId),
    Primitive(PrimitiveId),
}

/// A destructive change to a function key.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ChangeKind {
    Delete,
    Subsume,
}

/// Portable core action syntax.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CoreAction {
    Let {
        binding: RuleVar,
        call: RuleActionCall,
        arguments: Vec<RuleTerm>,
    },
    LetValue {
        binding: RuleVar,
        value: RuleTerm,
    },
    Set {
        target: FunctionId,
        keys: Vec<RuleTerm>,
        values: Vec<RuleTerm>,
    },
    Change {
        kind: ChangeKind,
        target: FunctionId,
        keys: Vec<RuleTerm>,
    },
    Union {
        left: RuleTerm,
        right: RuleTerm,
    },
    Panic {
        message: String,
    },
}

/// A complete resolved logical rule.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RuleSpec {
    pub id: RuleId,
    pub name: String,
    pub ruleset: RulesetId,
    pub seminaive: bool,
    pub no_decomp: bool,
    pub body: Vec<RuleBodyAtom>,
    pub actions: Vec<CoreAction>,
}

/// Frozen ordered membership of one ruleset.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RulesetDecl {
    pub id: RulesetId,
    pub name: String,
    pub rules: Vec<RuleId>,
}

/// The command-neutral nominal catalog and rule slice of a frontend snapshot.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResolvedCoreSnapshot {
    pub sorts: Vec<SortDecl>,
    pub primitives: Vec<PrimitiveDecl>,
    pub functions: Vec<FunctionConfig>,
    pub rulesets: Vec<RulesetDecl>,
    pub rules: Vec<RuleSpec>,
}

/// A fail-closed structural or typing error in a snapshot.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SnapshotValidationError {
    pub path: String,
    pub message: String,
}

impl Display for SnapshotValidationError {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}: {}", self.path, self.message)
    }
}

impl Error for SnapshotValidationError {}

type ValidationResult<T = ()> = Result<T, SnapshotValidationError>;

fn invalid(path: impl Into<String>, message: impl Into<String>) -> SnapshotValidationError {
    SnapshotValidationError {
        path: path.into(),
        message: message.into(),
    }
}

struct Catalog<'a> {
    sorts: BTreeMap<SortId, &'a SortDecl>,
    primitives: BTreeMap<PrimitiveId, &'a PrimitiveDecl>,
    functions: BTreeMap<FunctionId, &'a FunctionConfig>,
    rulesets: BTreeMap<RulesetId, &'a RulesetDecl>,
    rules: BTreeMap<RuleId, &'a RuleSpec>,
}

fn validate_dense_id(ordinal: u32, index: usize, arena: &str) -> ValidationResult {
    let expected = u32::try_from(index).map_err(|_| {
        invalid(
            arena,
            format!("{arena} arena exceeds the u32 nominal-ID domain"),
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

impl ResolvedCoreSnapshot {
    /// Look up a function by exact nominal identity.
    pub fn function(&self, id: FunctionId) -> Option<&FunctionConfig> {
        self.functions.iter().find(|function| function.id == id)
    }

    /// Look up a primitive by exact nominal identity.
    pub fn primitive(&self, id: PrimitiveId) -> Option<&PrimitiveDecl> {
        self.primitives.iter().find(|primitive| primitive.id == id)
    }

    /// Validate all IDs, signatures, merge programs, and rules without a backend.
    pub fn validate(&self) -> ValidationResult {
        let catalog = Catalog::new(self)?;
        catalog.validate_sorts()?;
        catalog.validate_functions()?;
        catalog.validate_primitives()?;
        catalog.validate_rulesets()?;
        catalog.validate_rules()?;
        Ok(())
    }
}

impl<'a> Catalog<'a> {
    fn new(snapshot: &'a ResolvedCoreSnapshot) -> ValidationResult<Self> {
        let mut sorts = BTreeMap::new();
        for (index, sort) in snapshot.sorts.iter().enumerate() {
            validate_dense_id(sort.id.ordinal(), index, "sort")?;
            if sorts.insert(sort.id, sort).is_some() {
                return Err(invalid(
                    format!("sort[{}]", sort.id.ordinal()),
                    "duplicate sort ID",
                ));
            }
        }

        let mut primitives = BTreeMap::new();
        for (index, primitive) in snapshot.primitives.iter().enumerate() {
            validate_dense_id(primitive.id.ordinal(), index, "primitive")?;
            if primitives.insert(primitive.id, primitive).is_some() {
                return Err(invalid(
                    format!("primitive[{}]", primitive.id.ordinal()),
                    "duplicate primitive ID",
                ));
            }
        }

        let mut functions = BTreeMap::new();
        for (index, function) in snapshot.functions.iter().enumerate() {
            validate_dense_id(function.id.ordinal(), index, "function")?;
            if functions.insert(function.id, function).is_some() {
                return Err(invalid(
                    format!("function[{}]", function.id.ordinal()),
                    "duplicate function ID",
                ));
            }
        }

        let mut rulesets = BTreeMap::new();
        for (index, ruleset) in snapshot.rulesets.iter().enumerate() {
            validate_dense_id(ruleset.id.ordinal(), index, "ruleset")?;
            if rulesets.insert(ruleset.id, ruleset).is_some() {
                return Err(invalid(
                    format!("ruleset[{}]", ruleset.id.ordinal()),
                    "duplicate ruleset ID",
                ));
            }
        }

        let mut rules = BTreeMap::new();
        for (index, rule) in snapshot.rules.iter().enumerate() {
            validate_dense_id(rule.id.ordinal(), index, "rule")?;
            if rules.insert(rule.id, rule).is_some() {
                return Err(invalid(
                    format!("rule[{}]", rule.id.ordinal()),
                    "duplicate rule ID",
                ));
            }
        }

        Ok(Self {
            sorts,
            primitives,
            functions,
            rulesets,
            rules,
        })
    }

    fn sort(&self, id: SortId, path: &str) -> ValidationResult<&SortDecl> {
        self.sorts
            .get(&id)
            .copied()
            .ok_or_else(|| invalid(path, format!("dangling sort ID {}", id.ordinal())))
    }

    fn function(&self, id: FunctionId, path: &str) -> ValidationResult<&FunctionConfig> {
        self.functions
            .get(&id)
            .copied()
            .ok_or_else(|| invalid(path, format!("dangling function ID {}", id.ordinal())))
    }

    fn primitive(&self, id: PrimitiveId, path: &str) -> ValidationResult<&PrimitiveDecl> {
        self.primitives
            .get(&id)
            .copied()
            .ok_or_else(|| invalid(path, format!("dangling primitive ID {}", id.ordinal())))
    }

    fn validate_sorts(&self) -> ValidationResult {
        let mut names = BTreeSet::new();
        let mut scalar_semantics = BTreeMap::new();
        for sort in self.sorts.values() {
            let path = format!("sort[{}]", sort.id.ordinal());
            if !names.insert(sort.name.as_str()) {
                return Err(invalid(
                    path,
                    format!("duplicate sort name `{}`", sort.name),
                ));
            }
            if sort.unionable && !matches!(sort.semantics, SortSemantics::Eq) {
                return Err(invalid(&path, "only an Eq sort may be marked unionable"));
            }
            let scalar_name = match sort.semantics {
                SortSemantics::Unit => Some("Unit"),
                SortSemantics::Bool => Some("Bool"),
                SortSemantics::I64 => Some("I64"),
                SortSemantics::F64 => Some("F64"),
                SortSemantics::String => Some("String"),
                SortSemantics::BigInt => Some("BigInt"),
                SortSemantics::BigRat => Some("BigRat"),
                SortSemantics::Eq
                | SortSemantics::Container { .. }
                | SortSemantics::Opaque { .. } => None,
            };
            if let Some(scalar_name) = scalar_name
                && let Some(previous) = scalar_semantics.insert(scalar_name, sort.id)
            {
                return Err(invalid(
                    &path,
                    format!(
                        "duplicate {scalar_name} semantics on nominal sorts {} and {}",
                        previous.ordinal(),
                        sort.id.ordinal()
                    ),
                ));
            }
            if let SortSemantics::Container { parameters, .. } = &sort.semantics {
                for (index, parameter) in parameters.iter().enumerate() {
                    self.sort(*parameter, &format!("{path}.parameters[{index}]"))?;
                }
            }
        }
        Ok(())
    }

    fn validate_literal(&self, literal: &TypedLiteral, path: &str) -> ValidationResult {
        let sort = self.sort(literal.sort, &format!("{path}.sort"))?;
        let valid_kind = matches!(
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
        if !valid_kind {
            return Err(invalid(
                path,
                format!("literal payload does not match sort `{}`", sort.name),
            ));
        }

        match &literal.value {
            LiteralValue::BigIntDecimal(value) => {
                validate_signed_decimal(value, path)?;
            }
            LiteralValue::BigRat {
                numerator_decimal,
                denominator_decimal,
            } => {
                validate_signed_decimal(numerator_decimal, path)?;
                validate_signed_decimal(denominator_decimal, path)?;
                if decimal_is_zero(denominator_decimal) {
                    return Err(invalid(path, "BigRat denominator is zero"));
                }
            }
            LiteralValue::Unit
            | LiteralValue::Bool(_)
            | LiteralValue::I64(_)
            | LiteralValue::F64Bits(_)
            | LiteralValue::String(_)
            | LiteralValue::Opaque(_) => {}
        }
        Ok(())
    }

    fn validate_functions(&self) -> ValidationResult {
        let mut names = BTreeSet::new();
        for function in self.functions.values() {
            let path = format!("function[{}]", function.id.ordinal());
            if !names.insert(function.name.as_str()) {
                return Err(invalid(
                    &path,
                    format!("duplicate function name `{}`", function.name),
                ));
            }
            if !(1..=function.schema.len()).contains(&function.n_values) {
                return Err(invalid(
                    format!("{path}.n_values"),
                    format!(
                        "expected 1..={}, got {}",
                        function.schema.len(),
                        function.n_values
                    ),
                ));
            }
            for (index, sort) in function.schema.iter().enumerate() {
                self.sort(*sort, &format!("{path}.schema[{index}]"))?;
            }
            if let Some(identity_values) = function.identity_values
                && !(1..=function.n_values).contains(&identity_values)
            {
                return Err(invalid(
                    format!("{path}.identity_values"),
                    format!("expected 1..={}, got {identity_values}", function.n_values),
                ));
            }

            let expected_display = match function.term_constructor {
                Some(term_constructor) => self
                    .function(term_constructor, &format!("{path}.term_constructor"))?
                    .name
                    .as_str(),
                None => function.name.as_str(),
            };
            if function.display.print_size_name != expected_display {
                return Err(invalid(
                    format!("{path}.display.print_size_name"),
                    format!("expected exact display name `{expected_display}`"),
                ));
            }

            match &function.default {
                FunctionDefault::FreshId => {
                    if function.n_values != 1
                        || !matches!(
                            self.sort(function.value_sorts()[0], &format!("{path}.default"))?
                                .semantics,
                            SortSemantics::Eq
                        )
                    {
                        return Err(invalid(
                            format!("{path}.default"),
                            "FreshId requires exactly one Eq value column",
                        ));
                    }
                }
                FunctionDefault::Fail => {}
                FunctionDefault::Constant(literal) => {
                    if function.n_values != 1 || literal.sort != function.value_sorts()[0] {
                        return Err(invalid(
                            format!("{path}.default"),
                            "constant default must match the sole value column",
                        ));
                    }
                    self.validate_literal(literal, &format!("{path}.default"))?;
                }
            }
        }

        for function in self.functions.values() {
            MergeValidator::new(self, function)?.validate()?;
        }
        self.validate_merge_read_dependencies()?;
        Ok(())
    }

    fn validate_merge_read_dependencies(&self) -> ValidationResult {
        let mut dependencies = BTreeMap::new();
        for function in self.functions.values() {
            let mut targets = BTreeSet::new();
            for node in &function.merge.values {
                match &node.operation {
                    MergeValueOperation::Function { target, .. }
                    | MergeValueOperation::Lookup { target, .. } => {
                        targets.insert(*target);
                    }
                    MergeValueOperation::Primitive { primitive, .. } => {
                        let primitive = self.primitive(
                            *primitive,
                            &format!(
                                "function[{}].merge.values[{}].primitive",
                                function.id.ordinal(),
                                node.id.ordinal()
                            ),
                        )?;
                        match primitive.semantics {
                            PrimitiveSemantics::SetIfEmpty { target }
                            | PrimitiveSemantics::ViewColumn { target, .. } => {
                                targets.insert(target);
                            }
                            PrimitiveSemantics::NativeRaw(_)
                            | PrimitiveSemantics::NativeScalar(_)
                            | PrimitiveSemantics::Fresh
                            | PrimitiveSemantics::Opaque { .. } => {}
                        }
                    }
                    MergeValueOperation::OldValue { .. }
                    | MergeValueOperation::NewValue { .. }
                    | MergeValueOperation::LetValue { .. }
                    | MergeValueOperation::Constant(_)
                    | MergeValueOperation::AssertEq { .. }
                    | MergeValueOperation::UnionId { .. } => {}
                }
            }
            // MergeAction::Set is deliberately a write edge, not a read
            // dependency, and therefore does not participate in this DAG.
            dependencies.insert(function.id, targets.into_iter().collect::<Vec<_>>());
        }

        let mut states = BTreeMap::new();
        for start in self.functions.keys().copied() {
            if states.get(&start) == Some(&2) {
                continue;
            }
            let mut stack = vec![(start, false)];
            while let Some((id, exiting)) = stack.pop() {
                if exiting {
                    states.insert(id, 2);
                    continue;
                }
                match states.get(&id) {
                    Some(1) => {
                        return Err(invalid(
                            format!("function[{}].merge", id.ordinal()),
                            "cycle in Function/Lookup merge read dependencies",
                        ));
                    }
                    Some(2) => continue,
                    Some(_) | None => {}
                }
                states.insert(id, 1);
                stack.push((id, true));
                let targets = dependencies.get(&id).ok_or_else(|| {
                    invalid(
                        format!("function[{}].merge", id.ordinal()),
                        "missing merge dependency node",
                    )
                })?;
                for target in targets.iter().rev() {
                    self.function(*target, "merge read dependency")?;
                    stack.push((*target, false));
                }
            }
        }
        Ok(())
    }

    fn validate_primitives(&self) -> ValidationResult {
        for primitive in self.primitives.values() {
            let path = format!("primitive[{}]", primitive.id.ordinal());
            for (index, sort) in primitive.input.iter().enumerate() {
                self.sort(*sort, &format!("{path}.input[{index}]"))?;
            }
            self.sort(primitive.output, &format!("{path}.output"))?;

            match &primitive.semantics {
                PrimitiveSemantics::NativeRaw(operation) => {
                    self.validate_native_raw(primitive, *operation, &path)?;
                }
                PrimitiveSemantics::NativeScalar(operation) => {
                    self.validate_native_scalar(primitive, *operation, &path)?;
                }
                PrimitiveSemantics::Fresh => {
                    if primitive.input.len() != 1
                        || !self.sort_is(primitive.input[0], |sort| {
                            matches!(sort, SortSemantics::String)
                        })
                        || !self.sort_is(primitive.output, |sort| matches!(sort, SortSemantics::Eq))
                    {
                        return Err(invalid(
                            path,
                            "Fresh requires the exact signature (String) -> Eq",
                        ));
                    }
                }
                PrimitiveSemantics::SetIfEmpty { target } => {
                    let target = self.function(*target, &format!("{path}.target"))?;
                    if !matches!(target.default, FunctionDefault::Fail)
                        || primitive.input != target.schema
                        || primitive.output != target.value_sorts()[0]
                    {
                        return Err(invalid(
                            path,
                            "SetIfEmpty signature/default disagrees with its exact target",
                        ));
                    }
                }
                PrimitiveSemantics::ViewColumn {
                    target,
                    value_column,
                } => {
                    let target = self.function(*target, &format!("{path}.target"))?;
                    if !matches!(target.default, FunctionDefault::Fail) {
                        return Err(invalid(
                            &path,
                            "ViewColumn target must use the Fail default",
                        ));
                    }
                    if *value_column >= target.n_values {
                        return Err(invalid(
                            format!("{path}.value_column"),
                            "value-column index is out of range",
                        ));
                    }
                    let selected = target.value_sorts()[*value_column];
                    let mut expected_input = target.schema[..target.n_keys()].to_vec();
                    expected_input.push(selected);
                    if primitive.input != expected_input || primitive.output != selected {
                        return Err(invalid(
                            path,
                            "ViewColumn signature disagrees with its exact target column",
                        ));
                    }
                }
                PrimitiveSemantics::Opaque { .. } => {}
            }
        }
        Ok(())
    }

    fn sort_is(&self, id: SortId, predicate: impl FnOnce(&SortSemantics) -> bool) -> bool {
        self.sorts
            .get(&id)
            .is_some_and(|sort| predicate(&sort.semantics))
    }

    fn sort_is_unionable(&self, id: SortId) -> bool {
        self.sorts
            .get(&id)
            .is_some_and(|sort| sort.unionable && matches!(sort.semantics, SortSemantics::Eq))
    }

    fn validate_native_raw(
        &self,
        primitive: &PrimitiveDecl,
        operation: NativeRawPrimitive,
        path: &str,
    ) -> ValidationResult {
        let unit_output =
            self.sort_is(primitive.output, |sort| matches!(sort, SortSemantics::Unit));
        let valid = match operation {
            NativeRawPrimitive::ValueEq | NativeRawPrimitive::ValueNeq => {
                primitive.input.len() == 2
                    && primitive.input[0] == primitive.input[1]
                    && unit_output
            }
            NativeRawPrimitive::OrderingMin | NativeRawPrimitive::OrderingMax => {
                primitive.input.len() == 2
                    && primitive.input[0] == primitive.input[1]
                    && primitive.output == primitive.input[0]
            }
            NativeRawPrimitive::SelectMinPayload | NativeRawPrimitive::SelectMaxPayload => {
                primitive.input.len() == 4
                    && primitive.input[0] == primitive.input[2]
                    && primitive.input[1] == primitive.input[3]
                    && primitive.output == primitive.input[1]
            }
            NativeRawPrimitive::SelectEqPayload => {
                primitive.input.len() == 4
                    && primitive.input[0] == primitive.input[1]
                    && primitive.input[2] == primitive.input[3]
                    && primitive.output == primitive.input[2]
            }
        };
        if valid {
            Ok(())
        } else {
            Err(invalid(path, "invalid signature for native raw primitive"))
        }
    }

    fn validate_native_scalar(
        &self,
        primitive: &PrimitiveDecl,
        operation: NativeScalarPrimitive,
        path: &str,
    ) -> ValidationResult {
        let binary_i64 = || {
            primitive.input.len() == 2
                && primitive.input[0] == primitive.input[1]
                && self.sort_is(primitive.input[0], |semantics| {
                    matches!(semantics, SortSemantics::I64)
                })
        };
        let binary_f64 = || {
            primitive.input.len() == 2
                && primitive.input[0] == primitive.input[1]
                && self.sort_is(primitive.input[0], |semantics| {
                    matches!(semantics, SortSemantics::F64)
                })
        };
        let output_unit = self.sort_is(primitive.output, |semantics| {
            matches!(semantics, SortSemantics::Unit)
        });
        let valid = match operation {
            NativeScalarPrimitive::I64Add
            | NativeScalarPrimitive::I64Sub
            | NativeScalarPrimitive::I64Mul
            | NativeScalarPrimitive::I64Div
            | NativeScalarPrimitive::I64Rem
            | NativeScalarPrimitive::I64BitAnd
            | NativeScalarPrimitive::I64Min
            | NativeScalarPrimitive::I64Max => {
                binary_i64() && primitive.output == primitive.input[0]
            }
            NativeScalarPrimitive::I64Ge
            | NativeScalarPrimitive::I64Gt
            | NativeScalarPrimitive::I64Le
            | NativeScalarPrimitive::I64Lt => binary_i64() && output_unit,
            NativeScalarPrimitive::I64BoolLt => {
                binary_i64()
                    && self.sort_is(primitive.output, |semantics| {
                        matches!(semantics, SortSemantics::Bool)
                    })
            }
            NativeScalarPrimitive::F64Gt | NativeScalarPrimitive::F64Lt => {
                binary_f64() && output_unit
            }
        };
        if valid {
            Ok(())
        } else {
            Err(invalid(
                path,
                "invalid signature for native scalar primitive",
            ))
        }
    }

    fn validate_rulesets(&self) -> ValidationResult {
        let mut names = BTreeSet::new();
        let mut memberships = BTreeMap::new();
        for ruleset in self.rulesets.values() {
            let path = format!("ruleset[{}]", ruleset.id.ordinal());
            if !names.insert(ruleset.name.as_str()) {
                return Err(invalid(
                    &path,
                    format!("duplicate ruleset name `{}`", ruleset.name),
                ));
            }
            let mut local = BTreeSet::new();
            for (index, rule_id) in ruleset.rules.iter().enumerate() {
                let rule = self.rules.get(rule_id).copied().ok_or_else(|| {
                    invalid(
                        format!("{path}.rules[{index}]"),
                        format!("dangling rule ID {}", rule_id.ordinal()),
                    )
                })?;
                if !local.insert(*rule_id) {
                    return Err(invalid(
                        format!("{path}.rules[{index}]"),
                        "duplicate rule in ruleset",
                    ));
                }
                if rule.ruleset != ruleset.id {
                    return Err(invalid(
                        format!("{path}.rules[{index}]"),
                        "rule points at a different ruleset ID",
                    ));
                }
                if memberships.insert(*rule_id, ruleset.id).is_some() {
                    return Err(invalid(
                        format!("{path}.rules[{index}]"),
                        "rule appears in more than one ruleset",
                    ));
                }
            }
        }
        for rule in self.rules.values() {
            if !self.rulesets.contains_key(&rule.ruleset) {
                return Err(invalid(
                    format!("rule[{}].ruleset", rule.id.ordinal()),
                    format!("dangling ruleset ID {}", rule.ruleset.ordinal()),
                ));
            }
            if memberships.get(&rule.id) != Some(&rule.ruleset) {
                return Err(invalid(
                    format!("rule[{}].ruleset", rule.id.ordinal()),
                    "rule is absent from its ruleset's frozen membership",
                ));
            }
        }
        Ok(())
    }

    fn validate_rules(&self) -> ValidationResult {
        let mut names_by_ruleset = BTreeMap::<RulesetId, BTreeSet<&str>>::new();
        for rule in self.rules.values() {
            if !names_by_ruleset
                .entry(rule.ruleset)
                .or_default()
                .insert(rule.name.as_str())
            {
                return Err(invalid(
                    format!("rule[{}]", rule.id.ordinal()),
                    format!(
                        "duplicate rule name `{}` in ruleset {}",
                        rule.name,
                        rule.ruleset.ordinal()
                    ),
                ));
            }
            RuleValidator::new(self, rule).validate()?;
        }
        Ok(())
    }
}

fn validate_signed_decimal(value: &str, path: &str) -> ValidationResult {
    let digits = value.strip_prefix('-').unwrap_or(value);
    if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_digit()) {
        return Err(invalid(path, "invalid signed decimal encoding"));
    }
    Ok(())
}

fn decimal_is_zero(value: &str) -> bool {
    value
        .strip_prefix('-')
        .unwrap_or(value)
        .bytes()
        .all(|byte| byte == b'0')
}

struct MergeValidator<'a> {
    catalog: &'a Catalog<'a>,
    owner: &'a FunctionConfig,
    nodes: BTreeMap<MergeValueId, &'a MergeValueNode>,
}

impl<'a> MergeValidator<'a> {
    fn new(catalog: &'a Catalog<'a>, owner: &'a FunctionConfig) -> ValidationResult<Self> {
        let path = format!("function[{}].merge", owner.id.ordinal());
        if owner.merge.owner != owner.id {
            return Err(invalid(
                format!("{path}.owner"),
                format!(
                    "merge owner ID {} does not match function ID {}",
                    owner.merge.owner.ordinal(),
                    owner.id.ordinal()
                ),
            ));
        }
        let mut nodes = BTreeMap::new();
        for (index, node) in owner.merge.values.iter().enumerate() {
            validate_dense_id(node.id.ordinal(), index, &format!("{path}.values"))?;
            if nodes.insert(node.id, node).is_some() {
                return Err(invalid(
                    format!("{path}.values[{}]", node.id.ordinal()),
                    "duplicate merge value ID",
                ));
            }
        }
        Ok(Self {
            catalog,
            owner,
            nodes,
        })
    }

    fn path(&self) -> String {
        format!("function[{}].merge", self.owner.id.ordinal())
    }

    fn node(&self, id: MergeValueId, path: &str) -> ValidationResult<&MergeValueNode> {
        self.nodes
            .get(&id)
            .copied()
            .ok_or_else(|| invalid(path, format!("dangling merge value ID {}", id.ordinal())))
    }

    fn validate(self) -> ValidationResult {
        let path = self.path();
        for node in self.nodes.values() {
            self.catalog.sort(
                node.sort,
                &format!("{path}.values[{}].sort", node.id.ordinal()),
            )?;
            self.validate_node(node)?;
        }
        self.validate_acyclic()?;

        let mut slots = Vec::new();
        let mut reachable = BTreeSet::new();
        for (action_index, action) in self.owner.merge.actions.iter().enumerate() {
            let action_path = format!("{path}.actions[{action_index}]");
            match action {
                MergeAction::Let { slot, value } => {
                    if usize::try_from(slot.ordinal()).ok() != Some(slots.len()) {
                        return Err(invalid(
                            format!("{action_path}.slot"),
                            format!(
                                "expected dense let slot {}, got {}",
                                slots.len(),
                                slot.ordinal()
                            ),
                        ));
                    }
                    self.validate_root(*value, 0, &slots, &action_path, &mut reachable)?;
                    slots.push(self.node(*value, &action_path)?.sort);
                }
                MergeAction::Set { target, row } => {
                    let target = self
                        .catalog
                        .function(*target, &format!("{action_path}.target"))?;
                    if row.len() != target.schema.len() {
                        return Err(invalid(
                            &action_path,
                            format!(
                                "Set row has {} columns, target requires {}",
                                row.len(),
                                target.schema.len()
                            ),
                        ));
                    }
                    for (column, (root, expected)) in
                        row.iter().zip(target.schema.iter()).enumerate()
                    {
                        let root_path = format!("{action_path}.row[{column}]");
                        self.validate_root(*root, 0, &slots, &root_path, &mut reachable)?;
                        if self.node(*root, &root_path)?.sort != *expected {
                            return Err(invalid(root_path, "Set row sort mismatch"));
                        }
                    }
                }
                MergeAction::Union { left, right } => {
                    self.validate_root(*left, 0, &slots, &action_path, &mut reachable)?;
                    self.validate_root(*right, 0, &slots, &action_path, &mut reachable)?;
                    let left_sort = self.node(*left, &action_path)?.sort;
                    let right_sort = self.node(*right, &action_path)?.sort;
                    if left_sort != right_sort || !self.catalog.sort_is_unionable(left_sort) {
                        return Err(invalid(
                            action_path,
                            "Union operands must have the same unionable Eq sort",
                        ));
                    }
                }
            }
        }

        if self.owner.merge.results.len() != self.owner.n_values {
            return Err(invalid(
                format!("{path}.results"),
                format!(
                    "merge has {} result roots, owner requires {}",
                    self.owner.merge.results.len(),
                    self.owner.n_values
                ),
            ));
        }
        for (column, (root, expected)) in self
            .owner
            .merge
            .results
            .iter()
            .zip(self.owner.value_sorts())
            .enumerate()
        {
            let root_path = format!("{path}.results[{column}]");
            self.validate_root(*root, column, &slots, &root_path, &mut reachable)?;
            if self.node(*root, &root_path)?.sort != *expected {
                return Err(invalid(root_path, "merge result sort mismatch"));
            }
        }

        if reachable.len() != self.nodes.len() {
            let unused = self
                .nodes
                .keys()
                .find(|id| !reachable.contains(id))
                .ok_or_else(|| invalid(&path, "merge reachability accounting failed"))?;
            return Err(invalid(
                format!("{path}.values[{}]", unused.ordinal()),
                "merge value is unreachable from ordered action/result roots",
            ));
        }
        Ok(())
    }

    fn validate_node(&self, node: &MergeValueNode) -> ValidationResult {
        let path = format!("{}.values[{}]", self.path(), node.id.ordinal());
        match &node.operation {
            MergeValueOperation::OldValue { column } | MergeValueOperation::NewValue { column } => {
                let expected = self.owner.value_sorts().get(*column).ok_or_else(|| {
                    invalid(
                        &path,
                        format!("owner value column {column} is out of range"),
                    )
                })?;
                if node.sort != *expected {
                    return Err(invalid(path, "owner value column sort mismatch"));
                }
            }
            MergeValueOperation::LetValue { .. } => {
                // Slot availability and type depend on the ordered root context.
            }
            MergeValueOperation::Constant(literal) => {
                if literal.sort != node.sort {
                    return Err(invalid(&path, "constant sort differs from node sort"));
                }
                self.catalog.validate_literal(literal, &path)?;
            }
            MergeValueOperation::AssertEq { old, new } => {
                let column = self.validate_owner_pair(*old, *new, &path)?;
                if node.sort != self.owner.value_sorts()[column] {
                    return Err(invalid(path, "AssertEq result sort mismatch"));
                }
            }
            MergeValueOperation::UnionId { left, right } => {
                let column = self.validate_owner_pair(*left, *right, &path)?;
                if node.sort != self.owner.value_sorts()[column] {
                    return Err(invalid(path, "UnionId result sort mismatch"));
                }
                if !self.catalog.sort_is_unionable(node.sort) {
                    return Err(invalid(
                        path,
                        "UnionId result must have a unionable Eq sort",
                    ));
                }
            }
            MergeValueOperation::Primitive {
                primitive,
                arguments,
            } => {
                let primitive = self
                    .catalog
                    .primitive(*primitive, &format!("{path}.primitive"))?;
                if arguments.len() != primitive.input.len() || node.sort != primitive.output {
                    return Err(invalid(path, "primitive merge signature mismatch"));
                }
                self.validate_argument_sorts(arguments, &primitive.input, &path)?;
            }
            MergeValueOperation::Function {
                target,
                guard,
                arguments,
            } => {
                let target_config = self.catalog.function(*target, &format!("{path}.target"))?;
                if *target == self.owner.id {
                    return Err(invalid(path, "merge Function may not read its owner"));
                }
                if target_config.n_values != 1 {
                    return Err(invalid(path, "tuple-output merge Function is not admitted"));
                }
                let target_output = target_config.value_sorts()[0];
                if node.sort != target_output || arguments.len() != target_config.n_keys() {
                    return Err(invalid(path, "merge Function signature mismatch"));
                }
                let guard_column = self.validate_owner_pair(guard.old, guard.new, &path)?;
                if node.sort != self.owner.value_sorts()[guard_column] {
                    return Err(invalid(
                        path,
                        "Function guard column sort must match its result sort",
                    ));
                }
                self.validate_argument_sorts(
                    arguments,
                    &target_config.schema[..target_config.n_keys()],
                    &path,
                )?;
            }
            MergeValueOperation::Lookup {
                target,
                arguments,
                fallback_old,
            } => {
                let target_config = self.catalog.function(*target, &format!("{path}.target"))?;
                if *target == self.owner.id {
                    return Err(invalid(path, "merge Lookup may not read its owner"));
                }
                if target_config.n_values != 1 {
                    return Err(invalid(path, "tuple-output merge Lookup is not admitted"));
                }
                if node.sort != target_config.value_sorts()[0]
                    || arguments.len() != target_config.n_keys()
                {
                    return Err(invalid(path, "merge Lookup signature mismatch"));
                }
                self.validate_argument_sorts(
                    arguments,
                    &target_config.schema[..target_config.n_keys()],
                    &path,
                )?;
                let fallback = self.node(*fallback_old, &format!("{path}.fallback_old"))?;
                if fallback.sort != node.sort
                    || !matches!(fallback.operation, MergeValueOperation::OldValue { .. })
                {
                    return Err(invalid(
                        path,
                        "Lookup fallback must be an exact owning old-value node",
                    ));
                }
            }
        }
        Ok(())
    }

    fn validate_owner_pair(
        &self,
        old: MergeValueId,
        new: MergeValueId,
        path: &str,
    ) -> ValidationResult<usize> {
        let old_node = self.node(old, &format!("{path}.old"))?;
        let new_node = self.node(new, &format!("{path}.new"))?;
        let MergeValueOperation::OldValue { column: old_column } = old_node.operation else {
            return Err(invalid(path, "old guard operand is not an owner old value"));
        };
        let MergeValueOperation::NewValue { column: new_column } = new_node.operation else {
            return Err(invalid(path, "new guard operand is not an owner new value"));
        };
        let Some(expected) = self.owner.value_sorts().get(old_column) else {
            return Err(invalid(path, "owner old/new column is out of range"));
        };
        if old_column != new_column || old_node.sort != *expected || new_node.sort != *expected {
            return Err(invalid(
                path,
                "owner old/new operands must name one same-typed value column",
            ));
        }
        Ok(old_column)
    }

    fn validate_argument_sorts(
        &self,
        arguments: &[MergeValueId],
        expected: &[SortId],
        path: &str,
    ) -> ValidationResult {
        if arguments.len() != expected.len() {
            return Err(invalid(path, "merge argument arity mismatch"));
        }
        for (index, (argument, expected)) in arguments.iter().zip(expected).enumerate() {
            if self
                .node(*argument, &format!("{path}.arguments[{index}]"))?
                .sort
                != *expected
            {
                return Err(invalid(
                    format!("{path}.arguments[{index}]"),
                    "merge argument sort mismatch",
                ));
            }
        }
        Ok(())
    }

    fn children(&self, node: &MergeValueNode) -> Vec<MergeValueId> {
        match &node.operation {
            MergeValueOperation::OldValue { .. }
            | MergeValueOperation::NewValue { .. }
            | MergeValueOperation::LetValue { .. }
            | MergeValueOperation::Constant(_) => Vec::new(),
            MergeValueOperation::AssertEq { old, new } => vec![*old, *new],
            MergeValueOperation::UnionId { left, right } => vec![*left, *right],
            MergeValueOperation::Primitive { arguments, .. } => arguments.clone(),
            MergeValueOperation::Function {
                guard, arguments, ..
            } => {
                let mut children = vec![guard.old, guard.new];
                children.extend(arguments);
                children
            }
            MergeValueOperation::Lookup {
                arguments,
                fallback_old,
                ..
            } => {
                let mut children = arguments.clone();
                children.push(*fallback_old);
                children
            }
        }
    }

    fn validate_acyclic(&self) -> ValidationResult {
        let mut states = BTreeMap::new();
        for start in self.nodes.keys().copied() {
            if states.get(&start) == Some(&2) {
                continue;
            }
            let mut stack = vec![(start, false)];
            while let Some((id, exiting)) = stack.pop() {
                if exiting {
                    states.insert(id, 2);
                    continue;
                }
                match states.get(&id) {
                    Some(1) => {
                        return Err(invalid(
                            format!("{}.values[{}]", self.path(), id.ordinal()),
                            "cycle in lazy merge arena",
                        ));
                    }
                    Some(2) => continue,
                    Some(_) | None => {}
                }
                states.insert(id, 1);
                stack.push((id, true));
                let node = self.node(id, &self.path())?;
                let children = self.children(node);
                for child in children.into_iter().rev() {
                    self.node(child, &self.path())?;
                    stack.push((child, false));
                }
            }
        }
        Ok(())
    }

    fn validate_root(
        &self,
        root: MergeValueId,
        self_column: usize,
        slots: &[SortId],
        path: &str,
        reachable: &mut BTreeSet<MergeValueId>,
    ) -> ValidationResult {
        let mut local = BTreeSet::new();
        let mut stack = vec![root];
        while let Some(id) = stack.pop() {
            if !local.insert(id) {
                continue;
            }
            let node = self.node(id, path)?;
            reachable.insert(id);
            self.validate_self_column(node, self_column, path)?;
            if let MergeValueOperation::LetValue { slot } = node.operation {
                let slot_index = usize::try_from(slot.ordinal()).map_err(|_| {
                    invalid(
                        path,
                        format!("let slot {} is not addressable", slot.ordinal()),
                    )
                })?;
                let Some(expected) = slots.get(slot_index) else {
                    return Err(invalid(
                        path,
                        format!("merge let slot {slot_index} is used before it is bound"),
                    ));
                };
                if node.sort != *expected {
                    return Err(invalid(path, "merge let-slot sort mismatch"));
                }
            }
            let children = self.children(node);
            stack.extend(children.into_iter().rev());
        }
        Ok(())
    }

    fn validate_self_column(
        &self,
        node: &MergeValueNode,
        self_column: usize,
        path: &str,
    ) -> ValidationResult {
        let actual = match &node.operation {
            MergeValueOperation::AssertEq { old, new } => {
                Some(self.validate_owner_pair(*old, *new, path)?)
            }
            MergeValueOperation::UnionId { left, right } => {
                Some(self.validate_owner_pair(*left, *right, path)?)
            }
            MergeValueOperation::Function { guard, .. } => {
                Some(self.validate_owner_pair(guard.old, guard.new, path)?)
            }
            MergeValueOperation::Lookup { fallback_old, .. } => {
                let fallback = self.node(*fallback_old, path)?;
                let MergeValueOperation::OldValue { column } = fallback.operation else {
                    return Err(invalid(
                        path,
                        "Lookup fallback is not an owning old-value node",
                    ));
                };
                Some(column)
            }
            MergeValueOperation::OldValue { .. }
            | MergeValueOperation::NewValue { .. }
            | MergeValueOperation::LetValue { .. }
            | MergeValueOperation::Constant(_)
            | MergeValueOperation::Primitive { .. } => None,
        };
        if let Some(actual) = actual
            && actual != self_column
        {
            return Err(invalid(
                path,
                format!(
                    "contextual owner operand uses self column {actual}, expected {self_column}"
                ),
            ));
        }
        Ok(())
    }
}

struct RuleValidator<'a> {
    catalog: &'a Catalog<'a>,
    rule: &'a RuleSpec,
    variables: BTreeMap<RuleVarId, (String, SortId)>,
    variable_order: Vec<RuleVarId>,
}

impl<'a> RuleValidator<'a> {
    fn new(catalog: &'a Catalog<'a>, rule: &'a RuleSpec) -> Self {
        Self {
            catalog,
            rule,
            variables: BTreeMap::new(),
            variable_order: Vec::new(),
        }
    }

    fn path(&self) -> String {
        format!("rule[{}]", self.rule.id.ordinal())
    }

    fn validate(mut self) -> ValidationResult {
        self.collect_variables_and_literals()?;
        for (index, id) in self.variable_order.iter().enumerate() {
            validate_dense_id(id.ordinal(), index, &format!("{}.variables", self.path()))?;
        }

        let mut table_bound = BTreeSet::new();
        for (atom_index, atom) in self.rule.body.iter().enumerate() {
            let path = format!("{}.body[{atom_index}]", self.path());
            match &atom.call {
                RuleBodyCall::Table { target, .. } => {
                    let function = self.catalog.function(*target, &format!("{path}.target"))?;
                    self.validate_terms(&atom.terms, &function.schema, &path)?;
                    add_term_variables(&mut table_bound, &atom.terms);
                }
                RuleBodyCall::IndexTable { target, any_of, .. } => {
                    let function = self.catalog.function(*target, &format!("{path}.target"))?;
                    if any_of.is_empty() {
                        return Err(invalid(format!("{path}.any_of"), "index any_of is empty"));
                    }
                    if atom.terms.len() != function.schema.len() + 2 {
                        return Err(invalid(
                            &path,
                            format!(
                                "index atom has {} terms, expected probe + {} row columns + Unit",
                                atom.terms.len(),
                                function.schema.len()
                            ),
                        ));
                    }
                    let probe_sort = atom.terms[0].sort();
                    for (choice_index, column) in any_of.iter().enumerate() {
                        let Some(column_sort) = function.schema.get(*column) else {
                            return Err(invalid(
                                format!("{path}.any_of[{choice_index}]"),
                                format!("indexed column {column} is out of range"),
                            ));
                        };
                        if *column_sort != probe_sort {
                            return Err(invalid(
                                format!("{path}.any_of[{choice_index}]"),
                                "indexed columns are not nominally type-compatible with the probe",
                            ));
                        }
                    }
                    self.validate_terms(
                        &atom.terms[1..1 + function.schema.len()],
                        &function.schema,
                        &path,
                    )?;
                    let trailing = &atom.terms[function.schema.len() + 1];
                    if !matches!(
                        trailing,
                        RuleTerm::Literal(TypedLiteral {
                            value: LiteralValue::Unit,
                            ..
                        })
                    ) || !self.catalog.sort_is(trailing.sort(), |semantics| {
                        matches!(semantics, SortSemantics::Unit)
                    }) {
                        return Err(invalid(
                            &path,
                            "index atom must end in the canonical typed Unit literal",
                        ));
                    }
                }
                RuleBodyCall::Primitive { primitive } => {
                    let primitive = self
                        .catalog
                        .primitive(*primitive, &format!("{path}.primitive"))?;
                    let mut signature = primitive.input.clone();
                    signature.push(primitive.output);
                    self.validate_terms(&atom.terms, &signature, &path)?;
                }
            }
        }

        // Table rows seed a fixed point.  A reached index occurrence binds its
        // complete base row; a reached primitive binds its output.  Either may
        // unlock a later occurrence, while an all-index/all-primitive cycle is
        // rejected instead of being treated as an accidental scan.
        let mut bound = table_bound;
        let mut unresolved = self
            .rule
            .body
            .iter()
            .enumerate()
            .filter_map(|(index, atom)| {
                matches!(
                    atom.call,
                    RuleBodyCall::IndexTable { .. } | RuleBodyCall::Primitive { .. }
                )
                .then_some(index)
            })
            .collect::<BTreeSet<_>>();
        loop {
            let ready = unresolved
                .iter()
                .copied()
                .filter(|index| {
                    let atom = &self.rule.body[*index];
                    match atom.call {
                        RuleBodyCall::IndexTable { .. } => term_is_bound(&atom.terms[0], &bound),
                        RuleBodyCall::Primitive { .. } => atom.terms[..atom.terms.len() - 1]
                            .iter()
                            .all(|term| term_is_bound(term, &bound)),
                        RuleBodyCall::Table { .. } => false,
                    }
                })
                .collect::<Vec<_>>();
            if ready.is_empty() {
                break;
            }
            for index in ready {
                let atom = &self.rule.body[index];
                match atom.call {
                    RuleBodyCall::IndexTable { .. } => {
                        add_term_variables(&mut bound, &atom.terms[1..atom.terms.len() - 1]);
                    }
                    RuleBodyCall::Primitive { .. } => {
                        if let Some(RuleTerm::Variable(output)) = atom.terms.last() {
                            bound.insert(output.id);
                        }
                    }
                    RuleBodyCall::Table { .. } => {
                        return Err(invalid(
                            format!("{}.body[{index}]", self.path()),
                            "internal table occurrence entered the reachability frontier",
                        ));
                    }
                }
                unresolved.remove(&index);
            }
        }
        if let Some(index) = unresolved.first() {
            let message = match self.rule.body[*index].call {
                RuleBodyCall::IndexTable { .. } => {
                    "index probe is not reachable from table/occurrence outputs"
                }
                RuleBodyCall::Primitive { .. } => {
                    "primitive inputs are not reachable from table/occurrence outputs"
                }
                RuleBodyCall::Table { .. } => "internal table reachability error",
            };
            return Err(invalid(format!("{}.body[{index}]", self.path()), message));
        }

        for (action_index, action) in self.rule.actions.iter().enumerate() {
            let path = format!("{}.actions[{action_index}]", self.path());
            match action {
                CoreAction::Let {
                    binding,
                    call,
                    arguments,
                } => {
                    self.ensure_terms_bound(arguments, &bound, &path)?;
                    let (expected_input, expected_output) = match call {
                        RuleActionCall::Table(target) => {
                            let function =
                                self.catalog.function(*target, &format!("{path}.target"))?;
                            if function.n_values != 1 {
                                return Err(invalid(
                                    &path,
                                    "action lookup of a tuple-output function is not admitted",
                                ));
                            }
                            (
                                function.schema[..function.n_keys()].to_vec(),
                                function.value_sorts()[0],
                            )
                        }
                        RuleActionCall::Primitive(primitive) => {
                            let primitive = self
                                .catalog
                                .primitive(*primitive, &format!("{path}.primitive"))?;
                            (primitive.input.clone(), primitive.output)
                        }
                    };
                    self.validate_terms(arguments, &expected_input, &path)?;
                    if binding.sort != expected_output {
                        return Err(invalid(&path, "action let result sort mismatch"));
                    }
                    if !bound.insert(binding.id) {
                        return Err(invalid(&path, "action let rebinds an existing variable ID"));
                    }
                }
                CoreAction::LetValue { binding, value } => {
                    self.ensure_term_bound(value, &bound, &path)?;
                    if binding.sort != value.sort() {
                        return Err(invalid(&path, "let-value result sort mismatch"));
                    }
                    if !bound.insert(binding.id) {
                        return Err(invalid(&path, "let-value rebinds an existing variable ID"));
                    }
                }
                CoreAction::Set {
                    target,
                    keys,
                    values,
                } => {
                    let function = self.catalog.function(*target, &format!("{path}.target"))?;
                    self.ensure_terms_bound(keys, &bound, &path)?;
                    self.ensure_terms_bound(values, &bound, &path)?;
                    self.validate_terms(keys, &function.schema[..function.n_keys()], &path)?;
                    self.validate_terms(values, function.value_sorts(), &path)?;
                }
                CoreAction::Change { kind, target, keys } => {
                    let function = self.catalog.function(*target, &format!("{path}.target"))?;
                    if *kind == ChangeKind::Subsume && !function.can_subsume {
                        return Err(invalid(
                            &path,
                            "Subsume target does not support subsumption",
                        ));
                    }
                    self.ensure_terms_bound(keys, &bound, &path)?;
                    self.validate_terms(keys, &function.schema[..function.n_keys()], &path)?;
                }
                CoreAction::Union { left, right } => {
                    self.ensure_term_bound(left, &bound, &path)?;
                    self.ensure_term_bound(right, &bound, &path)?;
                    if left.sort() != right.sort() || !self.catalog.sort_is_unionable(left.sort()) {
                        return Err(invalid(
                            path,
                            "rule Union requires one exact unionable Eq sort",
                        ));
                    }
                }
                CoreAction::Panic { .. } => {}
            }
        }
        Ok(())
    }

    fn collect_variables_and_literals(&mut self) -> ValidationResult {
        for (atom_index, atom) in self.rule.body.iter().enumerate() {
            for (term_index, term) in atom.terms.iter().enumerate() {
                self.collect_term(
                    term,
                    &format!("{}.body[{atom_index}].terms[{term_index}]", self.path()),
                )?;
            }
        }
        for (action_index, action) in self.rule.actions.iter().enumerate() {
            let path = format!("{}.actions[{action_index}]", self.path());
            match action {
                CoreAction::Let {
                    binding, arguments, ..
                } => {
                    self.collect_variable(binding, &path)?;
                    for term in arguments {
                        self.collect_term(term, &path)?;
                    }
                }
                CoreAction::LetValue { binding, value } => {
                    self.collect_variable(binding, &path)?;
                    self.collect_term(value, &path)?;
                }
                CoreAction::Set { keys, values, .. } => {
                    for term in keys.iter().chain(values) {
                        self.collect_term(term, &path)?;
                    }
                }
                CoreAction::Change { keys, .. } => {
                    for term in keys {
                        self.collect_term(term, &path)?;
                    }
                }
                CoreAction::Union { left, right } => {
                    self.collect_term(left, &path)?;
                    self.collect_term(right, &path)?;
                }
                CoreAction::Panic { .. } => {}
            }
        }
        Ok(())
    }

    fn collect_term(&mut self, term: &RuleTerm, path: &str) -> ValidationResult {
        match term {
            RuleTerm::Variable(variable) => self.collect_variable(variable, path),
            RuleTerm::Literal(literal) => self.catalog.validate_literal(literal, path),
        }
    }

    fn collect_variable(&mut self, variable: &RuleVar, path: &str) -> ValidationResult {
        self.catalog.sort(variable.sort, path)?;
        match self.variables.get(&variable.id) {
            Some((name, sort)) if name != &variable.name || *sort != variable.sort => Err(invalid(
                path,
                format!(
                    "variable ID {} is reused with a different name or sort",
                    variable.id.ordinal()
                ),
            )),
            Some(_) => Ok(()),
            None => {
                self.variables
                    .insert(variable.id, (variable.name.clone(), variable.sort));
                self.variable_order.push(variable.id);
                Ok(())
            }
        }
    }

    fn validate_terms(
        &self,
        terms: &[RuleTerm],
        expected: &[SortId],
        path: &str,
    ) -> ValidationResult {
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

    fn ensure_terms_bound(
        &self,
        terms: &[RuleTerm],
        bound: &BTreeSet<RuleVarId>,
        path: &str,
    ) -> ValidationResult {
        for term in terms {
            self.ensure_term_bound(term, bound, path)?;
        }
        Ok(())
    }

    fn ensure_term_bound(
        &self,
        term: &RuleTerm,
        bound: &BTreeSet<RuleVarId>,
        path: &str,
    ) -> ValidationResult {
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

#[cfg(test)]
mod tests {
    use super::*;

    const UNIT: SortId = SortId::new(0);
    const I64: SortId = SortId::new(1);
    const BOOL: SortId = SortId::new(2);
    const DECOY: FunctionId = FunctionId::new(0);
    const SINK: FunctionId = FunctionId::new(1);
    const OWNER: FunctionId = FunctionId::new(2);
    const ADD: PrimitiveId = PrimitiveId::new(0);
    const OPAQUE_SAME_NAME: PrimitiveId = PrimitiveId::new(1);

    fn literal_i64(value: i64) -> TypedLiteral {
        TypedLiteral {
            sort: I64,
            value: LiteralValue::I64(value),
        }
    }

    fn variable(id: u32, name: &str, sort: SortId) -> RuleVar {
        RuleVar {
            id: RuleVarId::new(id),
            name: name.into(),
            sort,
        }
    }

    fn unit_term() -> RuleTerm {
        RuleTerm::Literal(TypedLiteral {
            sort: UNIT,
            value: LiteralValue::Unit,
        })
    }

    fn old_value_merge(owner: FunctionId) -> MergeProgram {
        MergeProgram {
            owner,
            missing_owner: MissingOwnerPolicy::InsertCandidateWithoutMerge,
            values: vec![MergeValueNode {
                id: MergeValueId::new(0),
                sort: I64,
                operation: MergeValueOperation::OldValue { column: 0 },
            }],
            actions: Vec::new(),
            results: vec![MergeValueId::new(0)],
        }
    }

    fn function(id: FunctionId, name: &str, merge: MergeProgram) -> FunctionConfig {
        FunctionConfig {
            id,
            name: name.into(),
            kind: FunctionKind::Custom,
            schema: vec![I64, I64],
            n_values: 1,
            identity_values: None,
            default: FunctionDefault::Fail,
            merge,
            can_subsume: true,
            internal_hidden: false,
            internal_let: false,
            term_constructor: None,
            internal_term_node: false,
            display: FunctionDisplay {
                print_size_name: name.into(),
            },
        }
    }

    fn owner(snapshot: &mut ResolvedCoreSnapshot) -> &mut FunctionConfig {
        snapshot
            .functions
            .iter_mut()
            .find(|function| function.id == OWNER)
            .unwrap()
    }

    fn fixture() -> ResolvedCoreSnapshot {
        let owner_merge = MergeProgram {
            owner: OWNER,
            missing_owner: MissingOwnerPolicy::InsertCandidateWithoutMerge,
            values: vec![
                MergeValueNode {
                    id: MergeValueId::new(0),
                    sort: I64,
                    operation: MergeValueOperation::Constant(literal_i64(7)),
                },
                MergeValueNode {
                    id: MergeValueId::new(1),
                    sort: I64,
                    operation: MergeValueOperation::Constant(literal_i64(9)),
                },
                MergeValueNode {
                    id: MergeValueId::new(2),
                    sort: I64,
                    operation: MergeValueOperation::OldValue { column: 0 },
                },
            ],
            actions: vec![MergeAction::Set {
                target: SINK,
                row: vec![MergeValueId::new(0), MergeValueId::new(1)],
            }],
            results: vec![MergeValueId::new(2)],
        };

        let key = variable(0, "key", I64);
        let value = variable(1, "value", I64);
        let sum = variable(2, "sum", I64);
        let rule = RuleSpec {
            id: RuleId::new(0),
            name: "exact-target-rule".into(),
            ruleset: RulesetId::new(0),
            seminaive: true,
            no_decomp: false,
            body: vec![
                RuleBodyAtom {
                    call: RuleBodyCall::Table {
                        target: DECOY,
                        read: ReadMode::Live,
                    },
                    terms: vec![
                        RuleTerm::Variable(key.clone()),
                        RuleTerm::Variable(value.clone()),
                    ],
                },
                RuleBodyAtom {
                    call: RuleBodyCall::IndexTable {
                        target: DECOY,
                        any_of: vec![0, 0],
                        read: ReadMode::All,
                    },
                    terms: vec![
                        RuleTerm::Variable(key.clone()),
                        RuleTerm::Variable(key.clone()),
                        RuleTerm::Variable(value.clone()),
                        RuleTerm::Literal(TypedLiteral {
                            sort: UNIT,
                            value: LiteralValue::Unit,
                        }),
                    ],
                },
                RuleBodyAtom {
                    call: RuleBodyCall::Primitive { primitive: ADD },
                    terms: vec![
                        RuleTerm::Variable(key.clone()),
                        RuleTerm::Variable(value),
                        RuleTerm::Variable(sum.clone()),
                    ],
                },
            ],
            actions: vec![CoreAction::Set {
                target: SINK,
                keys: vec![RuleTerm::Variable(key)],
                values: vec![RuleTerm::Variable(sum)],
            }],
        };

        ResolvedCoreSnapshot {
            sorts: vec![
                SortDecl {
                    id: UNIT,
                    name: "Unit".into(),
                    semantics: SortSemantics::Unit,
                    unionable: false,
                },
                SortDecl {
                    id: I64,
                    name: "i64".into(),
                    semantics: SortSemantics::I64,
                    unionable: false,
                },
                SortDecl {
                    id: BOOL,
                    name: "bool".into(),
                    semantics: SortSemantics::Bool,
                    unionable: false,
                },
            ],
            primitives: vec![
                PrimitiveDecl {
                    id: ADD,
                    name: "misleading-shared-name".into(),
                    input: vec![I64, I64],
                    output: I64,
                    semantics: PrimitiveSemantics::NativeScalar(NativeScalarPrimitive::I64Add),
                },
                PrimitiveDecl {
                    id: OPAQUE_SAME_NAME,
                    name: "misleading-shared-name".into(),
                    input: vec![I64, I64],
                    output: I64,
                    semantics: PrimitiveSemantics::Opaque {
                        authority: "not-add".into(),
                    },
                },
            ],
            functions: vec![
                function(DECOY, "same-schema-decoy", old_value_merge(DECOY)),
                function(SINK, "same-schema-sink", old_value_merge(SINK)),
                function(OWNER, "merge-owner", owner_merge),
            ],
            rulesets: vec![RulesetDecl {
                id: RulesetId::new(0),
                name: String::new(),
                rules: vec![RuleId::new(0)],
            }],
            rules: vec![rule],
        }
    }

    #[test]
    fn exact_ids_select_same_schema_targets_and_primitive_semantics() {
        let snapshot = fixture();
        snapshot.validate().unwrap();

        let CoreAction::Set { target, .. } = &snapshot.rules[0].actions[0] else {
            panic!("fixture action must be Set");
        };
        assert_eq!(*target, SINK);
        let MergeAction::Set { target, .. } = &snapshot.function(OWNER).unwrap().merge.actions[0]
        else {
            panic!("fixture merge action must be Set");
        };
        assert_eq!(*target, SINK);
        assert_eq!(
            snapshot.function(DECOY).unwrap().schema,
            snapshot.function(SINK).unwrap().schema
        );
        assert!(matches!(
            snapshot.primitive(ADD).unwrap().semantics,
            PrimitiveSemantics::NativeScalar(NativeScalarPrimitive::I64Add)
        ));
        assert!(matches!(
            snapshot.primitive(OPAQUE_SAME_NAME).unwrap().semantics,
            PrimitiveSemantics::Opaque { .. }
        ));

        let RuleBodyCall::IndexTable { any_of, read, .. } = &snapshot.rules[0].body[1].call else {
            panic!("fixture body must retain the index occurrence");
        };
        assert_eq!(any_of, &[0, 0]);
        assert_eq!(*read, ReadMode::All);
    }

    #[test]
    fn value_equality_is_explicit_authority_with_a_checked_signature() {
        let mut snapshot = fixture();
        snapshot.primitives.push(PrimitiveDecl {
            id: PrimitiveId::new(2),
            name: "diagnostic-value-eq".into(),
            input: vec![I64, I64],
            output: UNIT,
            semantics: PrimitiveSemantics::NativeRaw(NativeRawPrimitive::ValueEq),
        });

        snapshot.validate().unwrap();
        snapshot.primitives[2].output = I64;
        assert!(
            snapshot
                .validate()
                .unwrap_err()
                .message
                .contains("invalid signature for native raw primitive")
        );
    }

    #[test]
    fn eggcc_i64_comparisons_are_exact_authorities_with_checked_signatures() {
        let mut snapshot = fixture();
        for (ordinal, operation, output) in [
            (2, NativeScalarPrimitive::I64Gt, UNIT),
            (3, NativeScalarPrimitive::I64Le, UNIT),
            (4, NativeScalarPrimitive::I64BoolLt, BOOL),
        ] {
            snapshot.primitives.push(PrimitiveDecl {
                id: PrimitiveId::new(ordinal),
                // Deliberately identical and misleading: only the stamped
                // registration-site authority selects semantics.
                name: "same-diagnostic-comparison".into(),
                input: vec![I64, I64],
                output,
                semantics: PrimitiveSemantics::NativeScalar(operation),
            });
        }

        snapshot.validate().unwrap();
        snapshot.primitives[4].output = UNIT;
        assert!(
            snapshot
                .validate()
                .unwrap_err()
                .message
                .contains("invalid signature for native scalar primitive")
        );
    }

    #[test]
    fn proof_select_eq_is_exact_authority_with_polymorphic_checked_signature() {
        let mut snapshot = fixture();
        snapshot.primitives.push(PrimitiveDecl {
            id: PrimitiveId::new(2),
            name: "misleading-payload-selector".into(),
            input: vec![I64, I64, BOOL, BOOL],
            output: BOOL,
            semantics: PrimitiveSemantics::NativeRaw(NativeRawPrimitive::SelectEqPayload),
        });
        snapshot.primitives.push(PrimitiveDecl {
            id: PrimitiveId::new(3),
            name: "misleading-payload-selector".into(),
            input: vec![I64, I64, BOOL, BOOL],
            output: BOOL,
            semantics: PrimitiveSemantics::Opaque {
                authority: "same-name-same-schema-decoy".into(),
            },
        });

        snapshot.validate().unwrap();
        snapshot.primitives[2].input[1] = BOOL;
        assert!(
            snapshot
                .validate()
                .unwrap_err()
                .message
                .contains("invalid signature for native raw primitive")
        );
    }

    #[test]
    fn constructor_view_display_uses_the_exact_target_identity() {
        let mut snapshot = fixture();
        let decoy_name = snapshot.function(DECOY).unwrap().name.clone();
        let owner_config = owner(&mut snapshot);
        owner_config.term_constructor = Some(DECOY);
        owner_config.display.print_size_name = decoy_name;
        snapshot.validate().unwrap();

        // DECOY and SINK have the same typed schema. Changing only the exact
        // target must not silently preserve constructor-view semantics.
        owner(&mut snapshot).term_constructor = Some(SINK);
        assert!(
            snapshot
                .validate()
                .unwrap_err()
                .message
                .contains("expected exact display name")
        );
    }

    #[test]
    fn set_if_empty_accepts_tuple_target_and_returns_primary_column() {
        let mut snapshot = fixture();
        let tuple = FunctionId::new(3);
        snapshot.functions.push(FunctionConfig {
            id: tuple,
            name: "tuple-target".into(),
            kind: FunctionKind::Custom,
            schema: vec![I64, I64, BOOL],
            n_values: 2,
            identity_values: None,
            default: FunctionDefault::Fail,
            merge: MergeProgram {
                owner: tuple,
                missing_owner: MissingOwnerPolicy::InsertCandidateWithoutMerge,
                values: vec![
                    MergeValueNode {
                        id: MergeValueId::new(0),
                        sort: I64,
                        operation: MergeValueOperation::OldValue { column: 0 },
                    },
                    MergeValueNode {
                        id: MergeValueId::new(1),
                        sort: BOOL,
                        operation: MergeValueOperation::OldValue { column: 1 },
                    },
                ],
                actions: Vec::new(),
                results: vec![MergeValueId::new(0), MergeValueId::new(1)],
            },
            can_subsume: true,
            internal_hidden: false,
            internal_let: false,
            term_constructor: None,
            internal_term_node: false,
            display: FunctionDisplay {
                print_size_name: "tuple-target".into(),
            },
        });
        snapshot.primitives.push(PrimitiveDecl {
            id: PrimitiveId::new(2),
            name: "set-if-empty-tuple".into(),
            input: vec![I64, I64, BOOL],
            output: I64,
            semantics: PrimitiveSemantics::SetIfEmpty { target: tuple },
        });

        snapshot.validate().unwrap();
        snapshot.primitives[2].output = BOOL;
        assert!(
            snapshot
                .validate()
                .unwrap_err()
                .message
                .contains("signature/default disagrees")
        );
    }

    #[test]
    fn rule_names_are_diagnostic_keys_scoped_to_their_ruleset() {
        let mut snapshot = fixture();
        let mut second_rule = snapshot.rules[0].clone();
        second_rule.id = RuleId::new(1);
        second_rule.ruleset = RulesetId::new(1);
        snapshot.rules.push(second_rule);
        snapshot.rulesets.push(RulesetDecl {
            id: RulesetId::new(1),
            name: "other".into(),
            rules: vec![RuleId::new(1)],
        });

        snapshot.validate().unwrap();

        snapshot.rules[1].ruleset = RulesetId::new(0);
        snapshot.rulesets[0].rules.push(RuleId::new(1));
        snapshot.rulesets[1].rules.clear();
        assert!(
            snapshot
                .validate()
                .unwrap_err()
                .message
                .contains("duplicate rule name")
        );
    }

    #[test]
    fn occurrence_reachability_is_a_fixed_point_and_cycles_fail_closed() {
        let mut chained = fixture();
        let key = variable(0, "key", I64);
        let value = variable(1, "value", I64);
        let middle = variable(2, "middle", I64);
        let last = variable(3, "last", I64);
        chained.rules[0].body = vec![
            RuleBodyAtom {
                call: RuleBodyCall::Table {
                    target: DECOY,
                    read: ReadMode::Live,
                },
                terms: vec![RuleTerm::Variable(key.clone()), RuleTerm::Variable(value)],
            },
            RuleBodyAtom {
                call: RuleBodyCall::IndexTable {
                    target: DECOY,
                    any_of: vec![0],
                    read: ReadMode::All,
                },
                terms: vec![
                    RuleTerm::Variable(key.clone()),
                    RuleTerm::Variable(key.clone()),
                    RuleTerm::Variable(middle.clone()),
                    unit_term(),
                ],
            },
            RuleBodyAtom {
                call: RuleBodyCall::IndexTable {
                    target: DECOY,
                    any_of: vec![0],
                    read: ReadMode::Subsumed,
                },
                terms: vec![
                    RuleTerm::Variable(middle.clone()),
                    RuleTerm::Variable(middle),
                    RuleTerm::Variable(last.clone()),
                    unit_term(),
                ],
            },
        ];
        chained.rules[0].actions = vec![CoreAction::Set {
            target: SINK,
            keys: vec![RuleTerm::Variable(key)],
            values: vec![RuleTerm::Variable(last)],
        }];
        chained.validate().unwrap();

        let mut cyclic = fixture();
        let first = variable(0, "first", I64);
        let second = variable(1, "second", I64);
        cyclic.rules[0].body = vec![
            RuleBodyAtom {
                call: RuleBodyCall::Table {
                    target: DECOY,
                    read: ReadMode::Live,
                },
                terms: vec![
                    RuleTerm::Literal(literal_i64(1)),
                    RuleTerm::Literal(literal_i64(2)),
                ],
            },
            RuleBodyAtom {
                call: RuleBodyCall::IndexTable {
                    target: DECOY,
                    any_of: vec![0],
                    read: ReadMode::Live,
                },
                terms: vec![
                    RuleTerm::Variable(first.clone()),
                    RuleTerm::Variable(first.clone()),
                    RuleTerm::Variable(second.clone()),
                    unit_term(),
                ],
            },
            RuleBodyAtom {
                call: RuleBodyCall::IndexTable {
                    target: DECOY,
                    any_of: vec![0],
                    read: ReadMode::Live,
                },
                terms: vec![
                    RuleTerm::Variable(second.clone()),
                    RuleTerm::Variable(second),
                    RuleTerm::Variable(first),
                    unit_term(),
                ],
            },
        ];
        cyclic.rules[0].actions = vec![CoreAction::Panic {
            message: "not reached".into(),
        }];
        assert!(
            cyclic
                .validate()
                .unwrap_err()
                .message
                .contains("index probe is not reachable")
        );
    }

    #[test]
    fn nominal_arenas_require_dense_vector_order() {
        let mut top_level = fixture();
        top_level.functions.swap(0, 1);
        assert!(
            top_level
                .validate()
                .unwrap_err()
                .message
                .contains("expected dense ID")
        );

        let mut merge = fixture();
        owner(&mut merge).merge.values[0].id = MergeValueId::new(8);
        assert!(
            merge
                .validate()
                .unwrap_err()
                .message
                .contains("expected dense ID")
        );

        let mut variables = fixture();
        let RuleTerm::Variable(variable) = &mut variables.rules[0].body[0].terms[0] else {
            unreachable!();
        };
        variable.id = RuleVarId::new(8);
        assert!(
            variables
                .validate()
                .unwrap_err()
                .message
                .contains("expected dense ID")
        );
    }

    #[test]
    fn deep_merge_arenas_validate_iteratively_and_cycles_are_errors() {
        const NODE_COUNT: usize = 20_000;

        let mut snapshot = fixture();
        snapshot.primitives.push(PrimitiveDecl {
            id: PrimitiveId::new(2),
            name: "unary-chain".into(),
            input: vec![I64],
            output: I64,
            semantics: PrimitiveSemantics::Opaque {
                authority: "test-only".into(),
            },
        });
        let mut values = Vec::with_capacity(NODE_COUNT);
        values.push(MergeValueNode {
            id: MergeValueId::new(0),
            sort: I64,
            operation: MergeValueOperation::OldValue { column: 0 },
        });
        for index in 1..NODE_COUNT {
            values.push(MergeValueNode {
                id: MergeValueId::new(u32::try_from(index).unwrap()),
                sort: I64,
                operation: MergeValueOperation::Primitive {
                    primitive: PrimitiveId::new(2),
                    arguments: vec![MergeValueId::new(u32::try_from(index - 1).unwrap())],
                },
            });
        }
        owner(&mut snapshot).merge = MergeProgram {
            owner: OWNER,
            missing_owner: MissingOwnerPolicy::InsertCandidateWithoutMerge,
            values,
            actions: Vec::new(),
            results: vec![MergeValueId::new(u32::try_from(NODE_COUNT - 1).unwrap())],
        };
        snapshot.validate().unwrap();

        owner(&mut snapshot).merge.values[0].operation = MergeValueOperation::Primitive {
            primitive: PrimitiveId::new(2),
            arguments: vec![MergeValueId::new(u32::try_from(NODE_COUNT - 1).unwrap())],
        };
        assert!(
            snapshot
                .validate()
                .unwrap_err()
                .message
                .contains("cycle in lazy merge arena")
        );
    }

    #[test]
    fn union_authority_is_not_inferred_from_eq_storage() {
        let mut snapshot = fixture();
        let eq_sort = SortId::new(3);
        let relation = FunctionId::new(3);
        snapshot.sorts.push(SortDecl {
            id: eq_sort,
            name: "non-unionable-relation-id".into(),
            semantics: SortSemantics::Eq,
            unionable: false,
        });
        snapshot.functions.push(FunctionConfig {
            id: relation,
            name: "non-unionable-relation".into(),
            kind: FunctionKind::Custom,
            schema: vec![eq_sort, eq_sort],
            n_values: 1,
            identity_values: None,
            default: FunctionDefault::Fail,
            merge: MergeProgram {
                owner: relation,
                missing_owner: MissingOwnerPolicy::InsertCandidateWithoutMerge,
                values: vec![
                    MergeValueNode {
                        id: MergeValueId::new(0),
                        sort: eq_sort,
                        operation: MergeValueOperation::OldValue { column: 0 },
                    },
                    MergeValueNode {
                        id: MergeValueId::new(1),
                        sort: eq_sort,
                        operation: MergeValueOperation::NewValue { column: 0 },
                    },
                    MergeValueNode {
                        id: MergeValueId::new(2),
                        sort: eq_sort,
                        operation: MergeValueOperation::AssertEq {
                            old: MergeValueId::new(0),
                            new: MergeValueId::new(1),
                        },
                    },
                ],
                actions: Vec::new(),
                results: vec![MergeValueId::new(2)],
            },
            can_subsume: false,
            internal_hidden: false,
            internal_let: false,
            term_constructor: None,
            internal_term_node: true,
            display: FunctionDisplay {
                print_size_name: "non-unionable-relation".into(),
            },
        });
        let left = variable(0, "left", eq_sort);
        let right = variable(1, "right", eq_sort);
        snapshot.rules[0].body = vec![RuleBodyAtom {
            call: RuleBodyCall::Table {
                target: relation,
                read: ReadMode::Live,
            },
            terms: vec![
                RuleTerm::Variable(left.clone()),
                RuleTerm::Variable(right.clone()),
            ],
        }];
        snapshot.rules[0].actions = vec![CoreAction::Union {
            left: RuleTerm::Variable(left),
            right: RuleTerm::Variable(right),
        }];

        assert!(
            snapshot
                .validate()
                .unwrap_err()
                .message
                .contains("unionable Eq sort")
        );
        snapshot.sorts[3].unionable = true;
        snapshot.validate().unwrap();
    }

    #[test]
    fn compatible_target_mutation_is_generic_semantics_not_role_inference() {
        let mut snapshot = fixture();
        let CoreAction::Set { target, .. } = &mut snapshot.rules[0].actions[0] else {
            unreachable!();
        };
        *target = DECOY;
        let MergeAction::Set { target, .. } = &mut snapshot
            .functions
            .iter_mut()
            .find(|function| function.id == OWNER)
            .unwrap()
            .merge
            .actions[0]
        else {
            unreachable!();
        };
        *target = DECOY;
        snapshot.validate().unwrap();
    }

    #[test]
    fn function_guard_and_lookup_fallback_are_explicit_lazy_operands() {
        let mut function_snapshot = fixture();
        let merge = &mut owner(&mut function_snapshot).merge;
        merge.values.push(MergeValueNode {
            id: MergeValueId::new(3),
            sort: I64,
            operation: MergeValueOperation::NewValue { column: 0 },
        });
        merge.values.push(MergeValueNode {
            id: MergeValueId::new(4),
            sort: I64,
            operation: MergeValueOperation::Function {
                target: SINK,
                guard: OwnerEqualityGuard {
                    old: MergeValueId::new(2),
                    new: MergeValueId::new(3),
                },
                arguments: vec![MergeValueId::new(0)],
            },
        });
        merge.results[0] = MergeValueId::new(4);
        function_snapshot.validate().unwrap();

        let MergeValueOperation::Function { target, guard, .. } =
            &owner(&mut function_snapshot).merge.values[4].operation
        else {
            unreachable!();
        };
        assert_eq!(*target, SINK);
        assert_eq!(guard.old, MergeValueId::new(2));
        assert_eq!(guard.new, MergeValueId::new(3));

        let mut lookup_snapshot = fixture();
        let merge = &mut owner(&mut lookup_snapshot).merge;
        merge.values.push(MergeValueNode {
            id: MergeValueId::new(3),
            sort: I64,
            operation: MergeValueOperation::Lookup {
                target: SINK,
                arguments: vec![MergeValueId::new(0)],
                fallback_old: MergeValueId::new(2),
            },
        });
        merge.results[0] = MergeValueId::new(3);
        lookup_snapshot.validate().unwrap();
        let MergeValueOperation::Lookup {
            target,
            fallback_old,
            ..
        } = &owner(&mut lookup_snapshot).merge.values[3].operation
        else {
            unreachable!();
        };
        assert_eq!(*target, SINK);
        assert_eq!(*fallback_old, MergeValueId::new(2));

        let mut invalid_guard = function_snapshot;
        let MergeValueOperation::Function { guard, .. } =
            &mut owner(&mut invalid_guard).merge.values[4].operation
        else {
            unreachable!();
        };
        guard.old = MergeValueId::new(0);
        assert!(
            invalid_guard
                .validate()
                .unwrap_err()
                .message
                .contains("old guard operand")
        );

        let mut mixed_sort = fixture();
        let merge = &mut owner(&mut mixed_sort).merge;
        merge.values[2].sort = BOOL;
        merge.values.push(MergeValueNode {
            id: MergeValueId::new(3),
            sort: BOOL,
            operation: MergeValueOperation::NewValue { column: 0 },
        });
        merge.values.push(MergeValueNode {
            id: MergeValueId::new(4),
            sort: I64,
            operation: MergeValueOperation::Function {
                target: SINK,
                guard: OwnerEqualityGuard {
                    old: MergeValueId::new(2),
                    new: MergeValueId::new(3),
                },
                arguments: vec![MergeValueId::new(0)],
            },
        });
        merge.actions.push(MergeAction::Set {
            target: SINK,
            row: vec![MergeValueId::new(0), MergeValueId::new(4)],
        });
        owner(&mut mixed_sort).schema[1] = BOOL;
        assert!(
            mixed_sort
                .validate()
                .unwrap_err()
                .message
                .contains("guard column sort must match its result sort")
        );
    }

    #[test]
    fn contextual_owner_operands_use_the_current_result_column() {
        let mut wrong_function = fixture();
        let merge = &mut owner(&mut wrong_function).merge;
        merge.values.push(MergeValueNode {
            id: MergeValueId::new(3),
            sort: I64,
            operation: MergeValueOperation::NewValue { column: 0 },
        });
        merge.values.push(MergeValueNode {
            id: MergeValueId::new(4),
            sort: I64,
            operation: MergeValueOperation::Function {
                target: SINK,
                guard: OwnerEqualityGuard {
                    old: MergeValueId::new(2),
                    new: MergeValueId::new(3),
                },
                arguments: vec![MergeValueId::new(0)],
            },
        });
        merge.results.push(MergeValueId::new(4));
        let owner_config = owner(&mut wrong_function);
        owner_config.schema.push(I64);
        owner_config.n_values = 2;
        assert!(
            wrong_function
                .validate()
                .unwrap_err()
                .message
                .contains("uses self column 0, expected 1")
        );

        let mut wrong_lookup = fixture();
        let merge = &mut owner(&mut wrong_lookup).merge;
        merge.values.push(MergeValueNode {
            id: MergeValueId::new(3),
            sort: I64,
            operation: MergeValueOperation::Lookup {
                target: SINK,
                arguments: vec![MergeValueId::new(0)],
                fallback_old: MergeValueId::new(2),
            },
        });
        merge.results.push(MergeValueId::new(3));
        let owner_config = owner(&mut wrong_lookup);
        owner_config.schema.push(I64);
        owner_config.n_values = 2;
        assert!(
            wrong_lookup
                .validate()
                .unwrap_err()
                .message
                .contains("uses self column 0, expected 1")
        );

        let mut correct = fixture();
        let merge = &mut owner(&mut correct).merge;
        merge.values.push(MergeValueNode {
            id: MergeValueId::new(3),
            sort: I64,
            operation: MergeValueOperation::OldValue { column: 1 },
        });
        merge.values.push(MergeValueNode {
            id: MergeValueId::new(4),
            sort: I64,
            operation: MergeValueOperation::NewValue { column: 1 },
        });
        merge.values.push(MergeValueNode {
            id: MergeValueId::new(5),
            sort: I64,
            operation: MergeValueOperation::Function {
                target: SINK,
                guard: OwnerEqualityGuard {
                    old: MergeValueId::new(3),
                    new: MergeValueId::new(4),
                },
                arguments: vec![MergeValueId::new(0)],
            },
        });
        merge.results.push(MergeValueId::new(5));
        let owner_config = owner(&mut correct);
        owner_config.schema.push(I64);
        owner_config.n_values = 2;
        correct.validate().unwrap();
    }

    #[test]
    fn function_lookup_read_dependencies_are_an_iterative_dag() {
        fn lookup_merge(owner: FunctionId, target: FunctionId) -> MergeProgram {
            MergeProgram {
                owner,
                missing_owner: MissingOwnerPolicy::InsertCandidateWithoutMerge,
                values: vec![
                    MergeValueNode {
                        id: MergeValueId::new(0),
                        sort: I64,
                        operation: MergeValueOperation::OldValue { column: 0 },
                    },
                    MergeValueNode {
                        id: MergeValueId::new(1),
                        sort: I64,
                        operation: MergeValueOperation::Constant(literal_i64(1)),
                    },
                    MergeValueNode {
                        id: MergeValueId::new(2),
                        sort: I64,
                        operation: MergeValueOperation::Lookup {
                            target,
                            arguments: vec![MergeValueId::new(1)],
                            fallback_old: MergeValueId::new(0),
                        },
                    },
                ],
                actions: Vec::new(),
                results: vec![MergeValueId::new(2)],
            }
        }

        let mut snapshot = fixture();
        snapshot.functions[0].merge = lookup_merge(DECOY, SINK);
        snapshot.functions[1].merge = lookup_merge(SINK, DECOY);
        assert!(
            snapshot
                .validate()
                .unwrap_err()
                .message
                .contains("cycle in Function/Lookup merge read dependencies")
        );

        snapshot.functions[1].merge = old_value_merge(SINK);
        // OWNER still has a merge-action Set to SINK.  That write edge is not a
        // read dependency and therefore does not create a false cycle.
        snapshot.validate().unwrap();
    }

    #[test]
    fn scalar_semantics_have_one_exact_nominal_sort() {
        let mut snapshot = fixture();
        snapshot.sorts.push(SortDecl {
            id: SortId::new(3),
            name: "second-i64".into(),
            semantics: SortSemantics::I64,
            unionable: false,
        });
        assert!(
            snapshot
                .validate()
                .unwrap_err()
                .message
                .contains("duplicate I64 semantics")
        );
    }

    #[test]
    fn subsume_requires_target_capability_but_delete_does_not() {
        let mut snapshot = fixture();
        snapshot.functions[1].can_subsume = false;
        let key = snapshot.rules[0].body[0].terms[0].clone();
        snapshot.rules[0].actions = vec![CoreAction::Change {
            kind: ChangeKind::Subsume,
            target: SINK,
            keys: vec![key.clone()],
        }];
        assert!(
            snapshot
                .validate()
                .unwrap_err()
                .message
                .contains("Subsume target does not support subsumption")
        );

        snapshot.rules[0].actions = vec![CoreAction::Change {
            kind: ChangeKind::Delete,
            target: SINK,
            keys: vec![key],
        }];
        snapshot.validate().unwrap();
    }

    #[test]
    fn validation_rejects_dangling_arity_and_nominal_type_errors() {
        let mut dangling = fixture();
        let CoreAction::Set { target, .. } = &mut dangling.rules[0].actions[0] else {
            unreachable!();
        };
        *target = FunctionId::new(99);
        assert!(
            dangling
                .validate()
                .unwrap_err()
                .message
                .contains("dangling function")
        );

        let mut arity = fixture();
        let CoreAction::Set { values, .. } = &mut arity.rules[0].actions[0] else {
            unreachable!();
        };
        values.clear();
        assert!(arity.validate().unwrap_err().message.contains("term arity"));

        let mut typed = fixture();
        let CoreAction::Set { values, .. } = &mut typed.rules[0].actions[0] else {
            unreachable!();
        };
        values[0] = RuleTerm::Literal(TypedLiteral {
            sort: BOOL,
            value: LiteralValue::Bool(false),
        });
        assert!(
            typed
                .validate()
                .unwrap_err()
                .message
                .contains("nominal term sort")
        );
    }

    #[test]
    fn validation_rejects_merge_column_slot_and_result_errors() {
        let mut column = fixture();
        let MergeValueOperation::OldValue { column: index } =
            &mut owner(&mut column).merge.values[2].operation
        else {
            unreachable!();
        };
        *index = 1;
        assert!(
            column
                .validate()
                .unwrap_err()
                .message
                .contains("out of range")
        );

        let mut slot = fixture();
        let merge = &mut owner(&mut slot).merge;
        merge.values[2] = MergeValueNode {
            id: MergeValueId::new(2),
            sort: I64,
            operation: MergeValueOperation::LetValue {
                slot: MergeLetSlot::new(0),
            },
        };
        assert!(
            slot.validate()
                .unwrap_err()
                .message
                .contains("before it is bound")
        );

        let mut result = fixture();
        owner(&mut result).merge.results.clear();
        assert!(
            result
                .validate()
                .unwrap_err()
                .message
                .contains("result roots")
        );
    }

    #[test]
    fn function_and_lookup_are_lazy_explicit_and_reject_tuple_targets() {
        let mut snapshot = fixture();
        let tuple = FunctionId::new(3);
        let mut tuple_function = function(tuple, "tuple-target", old_value_merge(tuple));
        tuple_function.schema.push(I64);
        tuple_function.n_values = 2;
        tuple_function.merge.values.push(MergeValueNode {
            id: MergeValueId::new(1),
            sort: I64,
            operation: MergeValueOperation::OldValue { column: 1 },
        });
        tuple_function.merge.results.push(MergeValueId::new(1));
        snapshot.functions.push(tuple_function);

        let merge = &mut snapshot
            .functions
            .iter_mut()
            .find(|function| function.id == OWNER)
            .unwrap()
            .merge;
        merge.values.push(MergeValueNode {
            id: MergeValueId::new(3),
            sort: I64,
            operation: MergeValueOperation::NewValue { column: 0 },
        });
        merge.values.push(MergeValueNode {
            id: MergeValueId::new(4),
            sort: I64,
            operation: MergeValueOperation::Function {
                target: tuple,
                guard: OwnerEqualityGuard {
                    old: MergeValueId::new(2),
                    new: MergeValueId::new(3),
                },
                arguments: vec![MergeValueId::new(0)],
            },
        });
        merge.results[0] = MergeValueId::new(4);
        assert!(
            snapshot
                .validate()
                .unwrap_err()
                .message
                .contains("tuple-output merge Function")
        );

        let MergeValueOperation::Function {
            target, arguments, ..
        } = &snapshot
            .functions
            .iter()
            .find(|function| function.id == OWNER)
            .unwrap()
            .merge
            .values[4]
            .operation
        else {
            unreachable!();
        };
        let tuple = *target;
        let arguments = arguments.clone();
        owner(&mut snapshot).merge.values[4].operation = MergeValueOperation::Lookup {
            target: tuple,
            arguments,
            fallback_old: MergeValueId::new(2),
        };
        assert!(
            snapshot
                .validate()
                .unwrap_err()
                .message
                .contains("tuple-output merge Lookup")
        );

        let mut fallback = fixture();
        let merge = &mut owner(&mut fallback).merge;
        merge.values.push(MergeValueNode {
            id: MergeValueId::new(3),
            sort: I64,
            operation: MergeValueOperation::Lookup {
                target: SINK,
                arguments: vec![MergeValueId::new(0)],
                fallback_old: MergeValueId::new(1),
            },
        });
        merge.results[0] = MergeValueId::new(3);
        assert!(
            fallback
                .validate()
                .unwrap_err()
                .message
                .contains("Lookup fallback must be an exact owning old-value node")
        );
    }
}

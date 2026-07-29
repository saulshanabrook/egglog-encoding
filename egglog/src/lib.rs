#![doc = include_str!("lib.md")]
pub mod api;
pub mod ast;
#[cfg(feature = "bin")]
mod cli;
mod command_macro;
pub mod constraint;
mod core;
mod exec_state;
pub mod extract;
pub mod prelude;
mod proofs;
pub mod slicing;

pub mod scheduler;
mod serialize;
pub mod sort;
mod termdag;
mod typechecking;
pub mod util;
pub use command_macro::{CommandMacro, CommandMacroRegistry};

// This is used to allow the `add_primitive` macro to work in
// both this crate and other crates by referring to `::egglog`.
extern crate self as egglog;
pub use ast::{ResolvedExpr, ResolvedFact, ResolvedVar};
#[cfg(feature = "bin")]
pub use cli::*;
use constraint::{Constraint, Problem, SimpleTypeConstraint, TypeConstraint};
pub use core::{Atom, AtomTerm};
use core::{CoreActionContext, ResolvedAtomTerm};
pub use core::{ResolvedCall, SpecializedPrimitive};
#[cfg(test)]
use core_relations::ReplayTerm;
pub use core_relations::{
    BaseValue, CausalContainerKind, ContainerValue, TraceView, TraceViewError, Value,
};
use core_relations::{ExecutionState, ExternalFunctionId, make_external_func};
use csv::Writer;
pub use egglog_add_primitive::add_literal_prim;
pub use egglog_add_primitive::add_primitive;
pub use egglog_add_primitive::add_primitive_with_validator;
use egglog_ast::generic_ast::{Change, GenericExpr, Literal};
use egglog_ast::span::Span;
use egglog_ast::util::ListDisplay;
/// The pluggable backend interface. Re-exported so downstream crates can
/// implement their own backend (see [`EGraph::with_backend`]).
pub use egglog_backend_trait::{Backend, BackendExt};
use egglog_backend_trait::{
    CriterionCapturePremise, CriterionCaptureSpec, FiringCaptureBinding, FiringCaptureSpec,
    FunctionReplaySpec, ReadMode, ReplayConstructorSpec, ReplayLiteral, ReplayOpId, ReplaySortId,
    ReplayTableKind, ReplayTermId, RuleActionCall, RuleBodyCall, RuleSetRun, RuleSpec, RuleValue,
    RuleVar, SourceCaptureSpec, SourceRef,
};
use egglog_bridge::ColumnTy;
use egglog_core_relations as core_relations;
use egglog_numeric_id as numeric_id;
use egglog_reports::{ReportLevel, RunReport};
pub use exec_state::{
    Context, Core, Enode, FullState, FunctionEntry, PureState, Read, ReadState, Write, WriteState,
};
use extract::{DefaultCost, Extractor, TreeAdditiveCostModel};
use indexmap::map::Entry;
use log::{Level, log_enabled};
use numeric_id::DenseIdMap;
use prelude::*;
pub use proofs::proof_encoding_helpers::{
    file_supports_proofs, file_supports_proofs_with_egraph, program_supports_proofs,
};

/// Read-only proof reconstruction API.
pub mod proof {
    pub use crate::proofs::proof_format::{Justification, Proof, ProofId, ProofStore, Proposition};
}
use scheduler::{SchedulerId, SchedulerRecord};
pub use serialize::{SerializeConfig, SerializeOutput, SerializedNode};
use sha2::{Digest, Sha256};
use sort::*;
use std::any::{Any, TypeId};
use std::fmt::{Debug, Display, Formatter};
use std::fs::File;
use std::hash::Hash;
use std::io::Write as _;
use std::iter::once;
use std::ops::Deref;
use std::path::PathBuf;
use std::sync::Arc;
pub use termdag::{OrdTerm, Term, TermDag, TermId};
use thiserror::Error;
use typechecking::FuncType;
pub use typechecking::PrimitiveValidator;
pub use typechecking::TypeError;
pub use typechecking::TypeInfo;
use util::*;

use crate::ast::desugar::desugar_command;
use crate::ast::*;
use crate::core::{GenericActionsExt, ResolvedRuleExt};
use crate::proofs::proof_encoding::{EncodingState, ProofInstrumentor};
use crate::proofs::proof_encoding_helpers::{
    ProofEncodingUnsupportedReason, command_supports_proof_encoding,
};
use crate::proofs::proof_extraction::ProveExistsError;
use crate::proofs::proof_format::{ProofId, ProofStore};
use crate::proofs::proof_normal_form::proof_form;

pub const GLOBAL_NAME_PREFIX: &str = "$";

/// Whether a merge primitive is semantically guaranteed to return exactly one of its two
/// arguments. Trace capture uses this narrow opt-in to attribute the selected input without
/// recording or re-running an arbitrary primitive. Keep the default closed: a primitive belongs
/// here only when its implementation has that exact contract.
fn primitive_merge_returns_one_input(name: &str) -> bool {
    matches!(
        name,
        "min"
            | "max"
            | "pair-min-by-second-i64"
            | "maybe-either-i64-bool-min"
            | "maybe-either-i64-bool-max"
    )
}

pub type ArcSort = Arc<dyn Sort>;

/// Methods shared by every kind-specific primitive trait.
///
/// `name` and `get_type_constraints` aren't capability-dependent, so
/// the four kind-specific traits ([`PurePrim`], [`WritePrim`],
/// [`ReadPrim`], [`FullPrim`]) share this supertrait.
pub trait Primitive: Send + Sync + 'static {
    /// Returns the name of this primitive.
    fn name(&self) -> &str;

    /// Constructs a type constraint for this primitive.
    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint>;
}

/// A primitive whose body sees a [`PureState`]. Register via
/// [`EGraph::add_pure_primitive`].
pub trait PurePrim: Primitive {
    fn apply<'a, 'db>(&self, state: PureState<'a, 'db>, args: &[Value]) -> Option<Value>;
}

/// A primitive whose body sees a [`WriteState`]. Register via
/// [`EGraph::add_write_primitive`].
pub trait WritePrim: Primitive {
    fn apply<'a, 'db>(&self, state: WriteState<'a, 'db>, args: &[Value]) -> Option<Value>;
}

/// A primitive whose body sees a [`ReadState`]. Register via
/// [`EGraph::add_read_primitive`].
pub trait ReadPrim: Primitive {
    fn apply<'a, 'db>(&self, state: ReadState<'a, 'db>, args: &[Value]) -> Option<Value>;
}

/// A primitive whose body sees a [`FullState`]. Register via
/// [`EGraph::add_full_primitive`].
pub trait FullPrim: Primitive {
    fn apply<'a, 'db>(&self, state: FullState<'a, 'db>, args: &[Value]) -> Option<Value>;
}

/// A user-defined command output trait.
pub trait UserDefinedCommandOutput: Debug + std::fmt::Display + Send + Sync {}
impl<T> UserDefinedCommandOutput for T where T: Debug + std::fmt::Display + Send + Sync {}

/// Output from a command.
#[derive(Clone, Debug)]
#[allow(clippy::large_enum_variant)]
pub enum CommandOutput {
    /// The size of a function
    PrintFunctionSize(usize),
    /// The name of all functions and their sizes
    PrintAllFunctionsSize(Vec<(String, usize)>),
    /// The best term found after extracting
    ExtractBest(TermDag, DefaultCost, TermId),
    /// The variants of a function found after extracting. Like normal extraction, but has to choose one extraction per e-node in the e-class.
    ExtractVariants(TermDag, Vec<TermId>),
    /// A high-level proof witnessing constructor existence
    ProveExists {
        proof_store: ProofStore,
        proof_id: ProofId,
    },
    /// The report from all runs
    OverallStatistics(RunReport),
    /// A printed function and all its values
    PrintFunction(Function, TermDag, Vec<(TermId, TermId)>, PrintFunctionMode),
    /// The report from a single run
    RunSchedule(RunReport),
    /// A user defined output
    UserDefined(Arc<dyn UserDefinedCommandOutput>),
}

impl CommandOutput {
    /// Render command outputs to a string that is identical whether the program
    /// ran normally or under proof encoding (`--proofs`). Drops outputs that
    /// legitimately differ or are non-deterministic (timing, `PrintFunction`
    /// per #793, extraction variants) and reduces `ExtractBest` to its cost.
    pub fn snapshot_stable_under_proof_encoding(outputs: &[CommandOutput]) -> String {
        Self::snapshot_stable(outputs, true)
    }

    /// Render only proof outputs. This keeps proof snapshots focused on the
    /// proof certificate and leaves ordinary outputs to the shared snapshots.
    pub fn snapshot_proofs_only(outputs: &[CommandOutput]) -> String {
        outputs
            .iter()
            .filter_map(|output| match output {
                CommandOutput::ProveExists { .. } => Some(output.to_string()),
                _ => None,
            })
            .collect::<Vec<_>>()
            .join("")
    }

    /// Render the non-proof outputs that should still match the normal-mode
    /// shared snapshot when proof-testing rewrites checks into prove commands.
    pub fn snapshot_non_proof_stable_under_proof_encoding(outputs: &[CommandOutput]) -> String {
        Self::snapshot_stable(outputs, false)
    }

    fn snapshot_stable(outputs: &[CommandOutput], include_proofs: bool) -> String {
        outputs
            .iter()
            .filter_map(|output| match output {
                CommandOutput::OverallStatistics(_) => None,
                CommandOutput::PrintFunction(..) => None,
                CommandOutput::ExtractBest(_, cost, _) => {
                    Some(format!("(extraction-costs {cost})\n"))
                }
                CommandOutput::ExtractVariants(..) => None,
                CommandOutput::ProveExists { .. } if !include_proofs => None,
                other => Some(other.to_string()),
            })
            .collect::<Vec<_>>()
            .join("")
    }
}

impl std::fmt::Display for CommandOutput {
    /// Format the command output for display, ending with a newline.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CommandOutput::PrintFunctionSize(size) => writeln!(f, "{size}"),
            CommandOutput::PrintAllFunctionsSize(names_and_sizes) => {
                write!(f, "(")?;
                for (i, (name, size)) in names_and_sizes.iter().enumerate() {
                    // indent except for the first line
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    // write the pair of funciton symbol and size
                    write!(f, "({name} {size})")?;
                    // add a newline except at the end
                    if i < names_and_sizes.len() - 1 {
                        writeln!(f)?;
                    }
                }
                writeln!(f, ")")
            }
            CommandOutput::ExtractBest(termdag, _cost, term) => {
                writeln!(f, "{}", termdag.to_string(*term))
            }
            CommandOutput::ExtractVariants(termdag, terms) => {
                writeln!(f, "(")?;
                for expr in terms {
                    writeln!(f, "   {}", termdag.to_string(*expr))?;
                }
                writeln!(f, ")")
            }
            CommandOutput::ProveExists {
                proof_store,
                proof_id,
            } => writeln!(f, "{}", proof_store.proof_to_string(*proof_id)),
            CommandOutput::OverallStatistics(run_report) => {
                write!(f, "Overall statistics:\n{run_report}")
            }
            CommandOutput::PrintFunction(function, termdag, terms_and_outputs, mode) => {
                let out_is_unit = function.schema.output().name() == UnitSort.name();
                if *mode == PrintFunctionMode::CSV {
                    let mut wtr = Writer::from_writer(vec![]);
                    for (term_id, output) in terms_and_outputs {
                        let term = termdag.get(*term_id);
                        match term {
                            Term::App(name, children) => {
                                let mut values = vec![name.clone()];
                                for child_id in children {
                                    values.push(termdag.to_string(*child_id));
                                }

                                if !out_is_unit {
                                    values.push(termdag.to_string(*output));
                                }
                                wtr.write_record(&values).map_err(|_| std::fmt::Error)?;
                            }
                            _ => panic!("Expect function_to_dag to return a list of apps."),
                        }
                    }
                    let csv_bytes = wtr.into_inner().map_err(|_| std::fmt::Error)?;
                    f.write_str(&String::from_utf8(csv_bytes).map_err(|_| std::fmt::Error)?)
                } else {
                    writeln!(f, "(")?;
                    for (term, output) in terms_and_outputs.iter() {
                        write!(f, "   {}", termdag.to_string(*term))?;
                        if !out_is_unit {
                            write!(f, " -> {}", termdag.to_string(*output))?;
                        }
                        writeln!(f)?;
                    }
                    writeln!(f, ")")
                }
            }
            CommandOutput::RunSchedule(_report) => Ok(()),
            CommandOutput::UserDefined(output) => {
                write!(f, "{}", *output)
            }
        }
    }
}

/// The main interface for an e-graph in egglog.
///
/// An [`EGraph`] maintains a collection of equivalence classes of terms and provides
/// operations for adding facts, running rules, and extracting optimal terms.
///
/// # Examples
///
/// ```
/// use egglog::*;
///
/// let mut egraph = EGraph::default();
/// egraph.parse_and_run_program(None, "(datatype Math (Num i64) (Add Math Math))").unwrap();
/// ```
trait ExtensionStateValue: Any + dyn_clone::DynClone + Send + Sync {}

impl<T> ExtensionStateValue for T where T: Any + Clone + Send + Sync {}

dyn_clone::clone_trait_object!(ExtensionStateValue);

/// A frontend-only replay alias. Unlike an ordinary global `let`, this owns no
/// backend function row and contributes no proof or trace fact.
#[derive(Clone, Debug)]
struct CheckedAlias {
    value: Value,
}

#[derive(Clone, Debug)]
struct CheckedAliasType {
    declaration_span: Span,
    sort: ArcSort,
    /// Source expression retained for commands that deliberately expand
    /// aliases (checks and open schedules). A later `let-check` keeps alias
    /// variables intact so it can reuse their persistent graph-local values.
    closed_expr: Expr,
}

#[derive(Clone)]
pub struct EGraph {
    backend: Box<dyn egglog_backend_trait::Backend>,
    pub parser: Parser,
    names: check_shadowing::Names,
    /// pushed_egraph forms a linked list of pushed egraphs.
    /// Pop reverts the egraph to the last pushed egraph.
    pushed_egraph: Option<Box<Self>>,
    functions: IndexMap<String, Function>,
    checked_aliases: IndexMap<String, CheckedAlias>,
    /// Type-only mirror used while resolving later proof-mode commands on the
    /// original typechecking graph. It deliberately contains no backend Value.
    checked_alias_types: IndexMap<String, CheckedAliasType>,
    /// Surface declarations that originated from `(relation ...)` before
    /// desugaring rewrote them to non-unionable constructors.
    relation_names: HashSet<String>,
    rulesets: IndexMap<String, Ruleset>,
    /// Panic callbacks embedded in `FunctionContainer` values must remain live
    /// for as long as the e-graph can retain those values. Cache one callback
    /// per unstable-function target for the lifetime of this `EGraph`.
    unstable_fn_panic_ids: HashMap<String, ExternalFunctionId>,
    pub fact_directory: Option<PathBuf>,
    pub seminaive: bool,
    pub no_decomp: bool,
    type_info: TypeInfo,
    /// The run report unioned over all runs so far.
    overall_run_report: RunReport,
    schedulers: DenseIdMap<SchedulerId, SchedulerRecord>,
    commands: IndexMap<String, Arc<dyn UserDefinedCommand>>,
    extension_state: HashMap<TypeId, Box<dyn ExtensionStateValue>>,
    strict_mode: bool,
    warned_about_global_prefix: bool,
    /// Registry for command-level macros
    command_macros: CommandMacroRegistry,
    proof_state: EncodingState,
    /// In proof mode, this is the program before proof instrumentation and the version we use for proof checking.
    proof_check_program: Vec<ResolvedNCommand>,
    /// Frontend-owned stable names for the backend's compact replay DAG.
    /// Present only while native trace capture is enabled.
    capture_catalog: Option<CaptureCatalog>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct ReplayOpKey {
    name: String,
    inputs: Vec<String>,
    output: String,
}

#[derive(Clone)]
struct CaptureCatalog {
    sort_ids: IndexMap<String, ReplaySortId>,
    op_ids: IndexMap<ReplayOpKey, ReplayOpId>,
    next_source: u64,
    next_check: u32,
    next_wave: u64,
    /// Graph-neutral normalized commands in their true expanded execution
    /// order. These commands never retain an `ArcSort`, backend id, or runtime
    /// value from the recording graph.
    command_catalog: Vec<CatalogCommand>,
    /// Macro-expanded source commands in source order. Replay emits static
    /// declarations from this catalog so the inspectable artifact never leaks
    /// normalized, parser-reserved implementation names such as `@RSort`.
    surface_command_catalog: Vec<Option<Command>>,
    /// Stable replay catalog indexed by the capture rule ordinal carried by
    /// native firings.
    rule_catalog: Vec<RuleCatalogEntry>,
    /// Exact command and direct immutable-global dependencies for source
    /// actions. Input rows use `input_commands` because their physical line is
    /// already part of `SourceRef`.
    source_commands: HashMap<SourceRef, SourceCatalogEntry>,
    /// `(input ...)` source-command ordinal to immutable file identity and
    /// normalized command. Physical rows remain cold and are reread only for
    /// selected `SourceRef::InputRow`s.
    input_commands: HashMap<u64, InputCatalogEntry>,
    /// Exact normalized command for each successful recorded check.
    check_commands: HashMap<u32, usize>,
    /// Command currently crossing the execution boundary. It is set only by
    /// `process_program_internal` and consumed synchronously by capture ids.
    active_command: Option<ActiveCatalogCommand>,
    /// Typechecking is stateful in the current frontend (sort declarations and
    /// primitive registration mutate the graph). This bit grants that mutation
    /// only to the normalized `run_program` resolution seam; public
    /// `resolve_program` is rejected after capture starts.
    resolving_command: bool,
    active_rule_origin: Option<RuleOrigin>,
    immutable_globals: HashMap<String, SourceRef>,
    has_run: bool,
    /// Once a command crosses the native execution boundary and then fails,
    /// its backend effects cannot be rolled back independently of the graph.
    /// Keep the exact history, consume every reserved identity, and make the
    /// capture unusable instead of pretending the frontend catalog rolled the
    /// command back.
    poisoned: Option<String>,
}

#[derive(Clone, Debug)]
struct CatalogCommand {
    command: Command,
    surface_command: usize,
}

#[derive(Clone, Copy, Debug)]
struct ActiveCatalogCommand {
    command: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RewriteDirection {
    Forward,
    Reverse,
}

#[derive(Clone, Copy, Debug)]
enum RuleOriginKind {
    Rule,
    Rewrite,
    BiRewrite(RewriteDirection),
}

#[derive(Clone, Debug)]
struct RuleOrigin {
    kind: RuleOriginKind,
    name: String,
    anonymous: bool,
    surface_variables: Box<[String]>,
    rewrite_root: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum RuleBindingRole {
    SurfaceVar,
    RewriteRoot,
    DerivedGlobal(String),
}

#[derive(Clone, Debug)]
struct RuleCatalogVariable {
    name: String,
    sort: String,
    role: RuleBindingRole,
}

struct CapturedRuleInputs {
    variables: Vec<ResolvedVar>,
    derived_global_by_var: HashMap<String, String>,
}

#[derive(Clone, Debug)]
enum CatalogRuleSurface {
    Normalized,
    Rewrite {
        surface_command: usize,
        direction: RewriteDirection,
        bidirectional: bool,
        base_name: String,
    },
}

#[derive(Clone, Debug)]
struct RuleCatalogEntry {
    ruleset: String,
    replay_name: String,
    variables: Box<[RuleCatalogVariable]>,
    command: usize,
    surface: CatalogRuleSurface,
}

#[derive(Clone, Debug)]
struct InputCatalogEntry {
    command: usize,
    function: String,
    file: String,
    resolved_path: PathBuf,
    digest: [u8; 32],
    unsupported: Option<String>,
}

#[derive(Clone, Debug)]
struct SourceCatalogEntry {
    command: usize,
    dependencies: Box<[SourceRef]>,
    unsupported: Option<String>,
}

struct SourceCaptureAnalysis {
    dependencies: Box<[SourceRef]>,
    produced_global: Option<String>,
    unsupported: Option<String>,
}

struct ParsedInputRow {
    line: u64,
    literals: Vec<Literal>,
}

struct ParsedInputFile {
    path: PathBuf,
    digest: Option<[u8; 32]>,
    rows: Vec<ParsedInputRow>,
}

impl Default for CaptureCatalog {
    fn default() -> Self {
        let mut state = Self {
            sort_ids: IndexMap::default(),
            op_ids: IndexMap::default(),
            next_source: 0,
            next_check: 0,
            next_wave: 1,
            command_catalog: Vec::new(),
            surface_command_catalog: Vec::new(),
            rule_catalog: Vec::new(),
            source_commands: HashMap::default(),
            input_commands: HashMap::default(),
            check_commands: HashMap::default(),
            active_command: None,
            resolving_command: false,
            active_rule_origin: None,
            immutable_globals: HashMap::default(),
            has_run: false,
            poisoned: None,
        };
        for name in ["Unit", "String", "bool", "i64", "f64"] {
            state.sort_id(name);
        }
        state
    }
}

impl CaptureCatalog {
    fn op_id(&mut self, key: ReplayOpKey) -> ReplayOpId {
        if let Some(op) = self.op_ids.get(&key) {
            return *op;
        }
        let op = ReplayOpId::new(
            u32::try_from(self.op_ids.len() + 1).expect("too many replay operations"),
        );
        self.op_ids.insert(key, op);
        op
    }

    fn sort_id(&mut self, name: &str) -> ReplaySortId {
        if let Some(id) = self.sort_ids.get(name) {
            return *id;
        }
        let id = ReplaySortId::new(
            u32::try_from(self.sort_ids.len() + 1).expect("too many replay sorts"),
        );
        self.sort_ids.insert(name.to_owned(), id);
        id
    }

    fn container_sort_spec(
        &mut self,
        sort: &ArcSort,
    ) -> Option<(ReplaySortId, TypeId, Box<[ReplaySortId]>)> {
        if !sort.is_container_sort() {
            return None;
        }
        let logical_sort = self.sort_id(sort.name());
        let child_sorts = sort
            .inner_sorts()
            .iter()
            .map(|child| self.sort_id(child.name()))
            .collect();
        Some((
            logical_sort,
            sort.value_type()
                .expect("container sort must expose its physical value type"),
            child_sorts,
        ))
    }

    fn literal_sort(&self, literal: &Literal) -> ReplaySortId {
        let name = match literal {
            Literal::Unit => "Unit",
            Literal::Bool(_) => "bool",
            Literal::Int(_) => "i64",
            Literal::Float(_) => "f64",
            Literal::String(_) => "String",
        };
        self.sort_ids[name]
    }

    fn replay_literal(literal: &Literal) -> ReplayLiteral {
        match literal {
            Literal::Unit => ReplayLiteral::Unit,
            Literal::Bool(value) => ReplayLiteral::Bool(*value),
            Literal::Int(value) => ReplayLiteral::I64(*value),
            Literal::Float(value) => ReplayLiteral::F64(value.0.to_bits()),
            Literal::String(value) => ReplayLiteral::String(Arc::from(value.as_str())),
        }
    }

    fn function_spec(
        &mut self,
        name: &str,
        schema: &ResolvedSchema,
        subtype: FunctionSubtype,
        is_relation: bool,
    ) -> FunctionReplaySpec {
        let input_names = schema
            .input
            .iter()
            .map(|sort| sort.name().to_owned())
            .collect::<Vec<_>>();
        let output_names = schema
            .outputs
            .iter()
            .map(|sort| sort.name().to_owned())
            .collect::<Vec<_>>();
        let input_sorts = input_names
            .iter()
            .map(|name| self.sort_id(name))
            .collect::<Vec<_>>();
        let output_sorts = output_names
            .iter()
            .map(|name| self.sort_id(name))
            .collect::<Vec<_>>();
        let constructor = (subtype == FunctionSubtype::Constructor).then(|| {
            let key = ReplayOpKey {
                name: name.to_owned(),
                inputs: input_names,
                output: output_names[0].clone(),
            };
            let op = self.op_id(key);
            let replay =
                ReplayConstructorSpec::new(output_sorts[0], op, input_sorts.iter().copied());
            if schema.outputs[0].is_container_sort() {
                replay.with_container_type(
                    schema.outputs[0]
                        .value_type()
                        .expect("container sort must expose its physical value type"),
                )
            } else {
                replay
            }
        });
        let table_kind = match (is_relation, subtype) {
            (true, _) => ReplayTableKind::PresenceRelation,
            (false, FunctionSubtype::Constructor) => ReplayTableKind::Constructor,
            (false, FunctionSubtype::Custom) => ReplayTableKind::ValueFunction,
        };
        FunctionReplaySpec::new(input_sorts.into_iter().chain(output_sorts), constructor)
            .with_table_kind(table_kind)
    }

    fn primitive_key(primitive: &core::SpecializedPrimitive) -> ReplayOpKey {
        ReplayOpKey {
            name: primitive.name().to_owned(),
            inputs: primitive
                .input()
                .iter()
                .map(|sort| sort.name().to_owned())
                .collect(),
            output: primitive.output().name().to_owned(),
        }
    }

    fn register_primitive(&mut self, primitive: &core::SpecializedPrimitive) {
        if !primitive.is_pure() || primitive.validator().is_none() {
            return;
        }
        for sort in primitive
            .input()
            .iter()
            .chain(std::iter::once(primitive.output()))
        {
            self.sort_id(sort.name());
        }
        self.op_id(Self::primitive_key(primitive));
    }

    fn primitive_spec(
        &self,
        primitive: &core::SpecializedPrimitive,
    ) -> Option<Arc<ReplayConstructorSpec>> {
        if !primitive.is_pure() || primitive.validator().is_none() {
            return None;
        }
        let op = *self.op_ids.get(&Self::primitive_key(primitive))?;
        let result_sort = *self.sort_ids.get(primitive.output().name())?;
        let child_sorts = primitive
            .input()
            .iter()
            .map(|sort| self.sort_ids.get(sort.name()).copied())
            .collect::<Option<Vec<_>>>()?;
        let replay = ReplayConstructorSpec::new(result_sort, op, child_sorts);
        Some(Arc::new(if primitive.output().is_container_sort() {
            replay
                .with_container_type(
                    primitive
                        .output()
                        .value_type()
                        .expect("container sort must expose its physical value type"),
                )
                .with_immediate_promotion()
        } else {
            replay
        }))
    }

    fn constructor_term_spec(
        &self,
        function: &typechecking::FuncType,
    ) -> Option<(ReplaySortId, ReplayOpId)> {
        if function.subtype != FunctionSubtype::Constructor || function.num_outputs() != 1 {
            return None;
        }
        let key = ReplayOpKey {
            name: function.name.clone(),
            inputs: function
                .input
                .iter()
                .map(|sort| sort.name().to_owned())
                .collect(),
            output: function.output().name().to_owned(),
        };
        Some((
            *self.sort_ids.get(function.output().name())?,
            *self.op_ids.get(&key)?,
        ))
    }

    fn register_action_primitives(&mut self, actions: &core::ResolvedCoreActions) {
        for action in &actions.0 {
            if let core::GenericCoreAction::Let(_, _, ResolvedCall::Primitive(primitive), _) =
                action
            {
                self.register_primitive(primitive);
            }
        }
    }

    fn register_rule_primitives(&mut self, rule: &core::ResolvedCoreRule) {
        for atom in &rule.body.atoms {
            if let ResolvedCall::Primitive(primitive) = &atom.head {
                self.register_primitive(primitive);
            }
        }
        self.register_action_primitives(&rule.head);
    }

    fn next_source_ordinal(&mut self) -> u64 {
        let ordinal = self.next_source;
        self.next_source = self
            .next_source
            .checked_add(1)
            .expect("too many source captures");
        ordinal
    }

    fn next_source(&mut self) -> SourceRef {
        SourceRef::Synthetic(self.next_source_ordinal())
    }

    fn register_source(&mut self, source: SourceRef, analysis: SourceCaptureAnalysis) {
        let command = self
            .active_command
            .expect("source capture requires an active catalog command")
            .command;
        self.source_commands.insert(
            source.clone(),
            SourceCatalogEntry {
                command,
                dependencies: analysis.dependencies,
                unsupported: analysis.unsupported,
            },
        );
        if let Some(global) = analysis.produced_global {
            self.immutable_globals.insert(global, source);
        }
    }

    fn register_rule(
        &mut self,
        ruleset: &str,
        name: &str,
        inputs: &CapturedRuleInputs,
    ) -> Result<u32, Error> {
        let id = u32::try_from(self.rule_catalog.len()).expect("too many captured rules");
        let command = self
            .active_command
            .expect("firing capture requires an active catalog command")
            .command;
        let origin = self.active_rule_origin.as_ref().ok_or_else(|| {
            Error::BackendError(format!(
                "trace capture cannot classify normalized rule `{name}` without a surface origin"
            ))
        })?;
        let surface_command = self.command_catalog[command].surface_command;
        let generated_name = format!("__slice_replay_rule_s{surface_command}");
        let base_name = if origin.anonymous {
            generated_name
        } else {
            origin.name.clone()
        };
        let (replay_name, surface) = match origin.kind {
            RuleOriginKind::Rule => (
                if origin.anonymous {
                    base_name.clone()
                } else {
                    name.to_owned()
                },
                CatalogRuleSurface::Normalized,
            ),
            RuleOriginKind::Rewrite => (
                base_name.clone(),
                CatalogRuleSurface::Rewrite {
                    surface_command,
                    direction: RewriteDirection::Forward,
                    bidirectional: false,
                    base_name,
                },
            ),
            RuleOriginKind::BiRewrite(direction) => (
                format!(
                    "{base_name}{}",
                    match direction {
                        RewriteDirection::Forward => "=>",
                        RewriteDirection::Reverse => "<=",
                    }
                ),
                CatalogRuleSurface::Rewrite {
                    surface_command,
                    direction,
                    bidirectional: true,
                    base_name,
                },
            ),
        };
        let variables = inputs
            .variables
            .iter()
            .map(|variable| {
                let role = if origin
                    .surface_variables
                    .iter()
                    .any(|surface| surface == &variable.name)
                {
                    RuleBindingRole::SurfaceVar
                } else if origin.rewrite_root.as_deref() == Some(variable.name.as_str()) {
                    RuleBindingRole::RewriteRoot
                } else if let Some(global) = inputs.derived_global_by_var.get(&variable.name) {
                    RuleBindingRole::DerivedGlobal(global.clone())
                } else {
                    return Err(Error::BackendError(format!(
                        "trace capture cannot classify normalized input `{}` of rule `{name}`",
                        variable.name
                    )));
                };
                Ok(RuleCatalogVariable {
                    name: variable.name.clone(),
                    sort: variable.sort.name().to_owned(),
                    role,
                })
            })
            .collect::<Result<Box<[_]>, Error>>()?;
        if matches!(
            origin.kind,
            RuleOriginKind::Rewrite | RuleOriginKind::BiRewrite(_)
        ) && variables
            .iter()
            .filter(|variable| variable.role == RuleBindingRole::RewriteRoot)
            .count()
            != 1
        {
            return Err(Error::BackendError(format!(
                "trace capture expected exactly one hidden root input for rewrite `{name}`"
            )));
        }
        let cataloged = self
            .command_catalog
            .get_mut(command)
            .expect("active captured rule command is not cataloged");
        let Command::Rule { rule } = &mut cataloged.command else {
            panic!("capture rule ordinal points at a non-rule command")
        };
        rule.name.clone_from(&replay_name);
        self.rule_catalog.push(RuleCatalogEntry {
            ruleset: ruleset.to_owned(),
            replay_name,
            variables,
            command,
            surface,
        });
        Ok(id)
    }

    fn next_check(&mut self) -> u32 {
        let check = self.next_check;
        self.next_check = self.next_check.checked_add(1).expect("too many criteria");
        let command = self
            .active_command
            .expect("criterion capture requires an active catalog command")
            .command;
        self.check_commands.insert(check, command);
        check
    }

    fn begin_command(
        &mut self,
        command: &ResolvedNCommand,
        rule_origin: Option<RuleOrigin>,
        surface_command: usize,
    ) -> Result<(), Error> {
        self.ensure_healthy()?;
        if self.active_command.is_some() || self.resolving_command {
            return Err(Error::BackendError(
                "trace capture does not support nested command execution".into(),
            ));
        }
        let command = command.clone().to_command().make_unresolved();
        let id = self.command_catalog.len();
        self.command_catalog.push(CatalogCommand {
            command,
            surface_command,
        });
        self.active_command = Some(ActiveCatalogCommand { command: id });
        self.active_rule_origin = rule_origin;
        Ok(())
    }

    fn register_surface_command(&mut self, command: Option<Command>) -> usize {
        let id = self.surface_command_catalog.len();
        self.surface_command_catalog.push(command);
        id
    }

    fn begin_resolution(&mut self) -> Result<(), Error> {
        self.ensure_healthy()?;
        if self.resolving_command || self.active_command.is_some() {
            return Err(Error::BackendError(
                "trace capture does not support nested command resolution".into(),
            ));
        }
        self.resolving_command = true;
        Ok(())
    }

    fn finish_resolution(&mut self, succeeded: bool) {
        assert!(
            self.resolving_command,
            "trace command resolution was not active"
        );
        self.resolving_command = false;
        if !succeeded {
            self.poison("a command failed during resolution after trace capture began");
        }
    }

    fn finish_command(&mut self, succeeded: bool) {
        let active = self
            .active_command
            .take()
            .expect("trace catalog command was not active");
        if !succeeded {
            self.poison(format!(
                "normalized command {} failed after entering trace capture; its native effects and reserved trace identities cannot be rolled back",
                active.command
            ));
        }
        self.active_rule_origin = None;
    }

    fn poison(&mut self, reason: impl Into<String>) {
        if self.poisoned.is_none() {
            self.poisoned = Some(reason.into());
        }
    }

    fn ensure_healthy(&self) -> Result<(), Error> {
        match &self.poisoned {
            Some(reason) => Err(Error::BackendError(format!(
                "trace capture is poisoned: {reason}"
            ))),
            None => Ok(()),
        }
    }

    fn validate_replay_rule_names(&self) -> Result<(), String> {
        let mut names = HashMap::default();
        for (ordinal, rule) in self.rule_catalog.iter().enumerate() {
            if let Some(previous) = names.insert(rule.replay_name.as_str(), ordinal) {
                return Err(format!(
                    "slice replay rule name `{}` collides between rule ordinals {previous} and {ordinal}",
                    rule.replay_name
                ));
            }
        }
        Ok(())
    }

    fn begin_wave(&mut self) -> u64 {
        let wave = self.next_wave;
        self.next_wave = self
            .next_wave
            .checked_add(1)
            .expect("trace wave counter overflow");
        wave
    }
}

fn source_rule_inputs(
    rule: &ResolvedRule,
    immutable_globals: &HashMap<String, SourceRef>,
) -> Result<CapturedRuleInputs, Error> {
    let mut variables = Vec::new();
    let mut seen = HashSet::default();
    for fact in &rule.body {
        fact.visit_vars(&mut |_span, variable| {
            if !variable.is_global_ref && seen.insert(variable.name.clone()) {
                variables.push(variable.clone());
            }
        });
    }

    fn derived_global(
        left: &ResolvedExpr,
        right: &ResolvedExpr,
        immutable_globals: &HashMap<String, SourceRef>,
    ) -> Option<(String, String)> {
        let (
            ResolvedExpr::Call(_, ResolvedCall::Func(function), children),
            ResolvedExpr::Var(_, variable),
        ) = (left, right)
        else {
            return None;
        };
        (children.is_empty() && immutable_globals.contains_key(&function.name))
            .then(|| (variable.name.clone(), function.name.clone()))
    }

    let mut derived_global_by_var = HashMap::default();
    for fact in &rule.body {
        let ResolvedFact::Eq(_, left, right) = fact else {
            continue;
        };
        let Some((variable, global)) = derived_global(left, right, immutable_globals)
            .or_else(|| derived_global(right, left, immutable_globals))
        else {
            continue;
        };
        if let Some(previous) = derived_global_by_var.insert(variable.clone(), global.clone())
            && previous != global
        {
            return Err(Error::BackendError(format!(
                "trace capture cannot map normalized input `{variable}` to both immutable globals `{previous}` and `{global}`"
            )));
        }
    }
    Ok(CapturedRuleInputs {
        variables,
        derived_global_by_var,
    })
}

fn catalog_rule_origins(command: &Command) -> Vec<RuleOrigin> {
    fn rule_variables(rule: &ast::Rule) -> Box<[String]> {
        let mut variables = IndexSet::default();
        for fact in &rule.body {
            fact.visit_vars(&mut |_span, variable| {
                variables.insert(variable.clone());
            });
        }
        rule.head.visit_vars(&mut |_span, variable| {
            variables.insert(variable.clone());
        });
        variables.into_iter().collect()
    }

    fn rewrite_variables(rewrite: &ast::Rewrite) -> Box<[String]> {
        let mut variables = IndexSet::default();
        rewrite.lhs.visit_vars(&mut |_span, variable| {
            variables.insert(variable.clone());
        });
        rewrite.rhs.visit_vars(&mut |_span, variable| {
            variables.insert(variable.clone());
        });
        for condition in &rewrite.conditions {
            condition.visit_vars(&mut |_span, variable| {
                variables.insert(variable.clone());
            });
        }
        variables.into_iter().collect()
    }

    match command {
        Command::Rule { rule } => vec![RuleOrigin {
            kind: RuleOriginKind::Rule,
            name: rule.name.clone(),
            anonymous: rule.name.is_empty(),
            surface_variables: rule_variables(rule),
            rewrite_root: None,
        }],
        Command::Rewrite(_, rewrite, _) => vec![RuleOrigin {
            kind: RuleOriginKind::Rewrite,
            name: rewrite.name.clone(),
            anonymous: rewrite.name.is_empty(),
            surface_variables: rewrite_variables(rewrite),
            rewrite_root: Some(ast::desugar::rewrite_root_name(rewrite)),
        }],
        Command::BiRewrite(_, rewrite) => {
            let origin = RuleOrigin {
                kind: RuleOriginKind::BiRewrite(RewriteDirection::Forward),
                name: rewrite.name.clone(),
                anonymous: rewrite.name.is_empty(),
                surface_variables: rewrite_variables(rewrite),
                rewrite_root: Some(ast::desugar::rewrite_root_name(rewrite)),
            };
            vec![
                origin.clone(),
                RuleOrigin {
                    kind: RuleOriginKind::BiRewrite(RewriteDirection::Reverse),
                    ..origin
                },
            ]
        }
        Command::Fail(_, commands) => commands.iter().flat_map(catalog_rule_origins).collect(),
        _ => Vec::new(),
    }
}

/// A user-defined command allows users to inject custom command that can be called
/// in an egglog program.
///
/// Compared to an external function, a user-defined command is more powerful because
/// it has an exclusive access to the e-graph.
pub trait UserDefinedCommand: Send + Sync {
    /// Run the command with the given arguments.
    fn update(&self, egraph: &mut EGraph, args: &[Expr]) -> Result<Vec<CommandOutput>, Error>;

    /// Execute the command while trace capture is active, if this command has
    /// an implementation over the deliberately restricted schedule surface.
    /// The context exposes rule stepping only: it cannot evaluate expressions,
    /// forward commands, or mutate tables directly.
    #[doc(hidden)]
    fn update_trace(
        &self,
        _context: &mut TraceScheduleContext<'_>,
        _args: &[Expr],
    ) -> Option<Result<Vec<CommandOutput>, Error>> {
        None
    }
}

/// Restricted execution authority for a user-defined schedule while trace
/// capture is active. Extensions can compose native ruleset steps without
/// receiving `&mut EGraph` and thereby bypassing the normalized command
/// catalog.
#[doc(hidden)]
pub struct TraceScheduleContext<'a> {
    egraph: &'a mut EGraph,
}

impl TraceScheduleContext<'_> {
    /// Run one native ruleset step and record its cumulative trace wave.
    pub fn step_rules(&mut self, ruleset: &str) -> Result<RunReport, Error> {
        self.egraph.step_rules(ruleset)
    }
}

/// A function in the e-graph.
///
/// This contains the schema information of the function and
/// the backend id of the function in the e-graph.
#[derive(Clone)]
pub struct Function {
    decl: ResolvedFunctionDecl,
    schema: ResolvedSchema,
    can_subsume: bool,
    backend_id: egglog_bridge::FunctionId,
}

impl Function {
    /// Get the name of the function.
    pub fn name(&self) -> &str {
        &self.decl.name
    }

    /// Get the schema of the function.
    pub fn schema(&self) -> &ResolvedSchema {
        &self.schema
    }

    /// Whether this function supports subsumption.
    pub fn can_subsume(&self) -> bool {
        self.can_subsume
    }

    /// Whether this table is a constructor/relation or a function.
    pub fn subtype(&self) -> FunctionSubtype {
        self.decl.subtype
    }

    /// Whether this is a let binding
    pub fn is_let_binding(&self) -> bool {
        self.decl.internal_let
    }

    /// Whether this function is internally hidden (e.g., compiler-generated
    /// helper tables that should not appear in user-facing listings).
    pub fn is_hidden(&self) -> bool {
        self.decl.internal_hidden
    }

    /// The term-constructor name associated with this function table, if
    /// any. Set on view tables created by the term/proof encoding to refer
    /// back to the user-visible constructor name.
    pub fn term_constructor(&self) -> Option<&str> {
        self.decl.term_constructor.as_deref()
    }
}

#[derive(Clone, Debug)]
pub struct ResolvedSchema {
    pub input: Vec<ArcSort>,
    /// The output (value-column) sorts, primary first. A tuple-output function has more than one;
    /// ordinary functions have exactly one. Always non-empty.
    pub outputs: Vec<ArcSort>,
}

impl ResolvedSchema {
    /// The primary (first) output sort.
    pub fn output(&self) -> &ArcSort {
        &self.outputs[0]
    }
}

impl Debug for Function {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Function")
            .field("decl", &self.decl)
            .field("schema", &self.schema)
            .finish()
    }
}

impl Default for EGraph {
    fn default() -> Self {
        Self::with_backend(Box::new(egglog_bridge::EGraph::default()))
    }
}

impl EGraph {
    /// Construct an `EGraph` backed by the given [`Backend`] implementation.
    ///
    /// [`EGraph::default`] uses the in-memory reference backend
    /// (`egglog_bridge::EGraph`); downstream crates can supply their own
    /// backend (e.g. a differential-dataflow engine) by implementing
    /// [`Backend`] and passing it here.
    pub fn with_backend(backend: Box<dyn Backend>) -> Self {
        let mut parser = Parser::default();
        let proof_state = EncodingState::new(&mut parser.symbol_gen);
        let mut eg = Self {
            backend,
            parser,
            names: Default::default(),
            pushed_egraph: Default::default(),
            functions: Default::default(),
            checked_aliases: Default::default(),
            checked_alias_types: Default::default(),
            relation_names: Default::default(),
            rulesets: Default::default(),
            unstable_fn_panic_ids: Default::default(),
            fact_directory: None,
            seminaive: true,
            no_decomp: false,
            overall_run_report: Default::default(),
            type_info: Default::default(),
            schedulers: Default::default(),
            commands: Default::default(),
            extension_state: Default::default(),
            strict_mode: false,
            warned_about_global_prefix: false,
            command_macros: Default::default(),
            proof_state,
            proof_check_program: vec![],
            capture_catalog: None,
        };
        add_base_sort(&mut eg, UnitSort, span!()).unwrap();
        add_base_sort(&mut eg, StringSort, span!()).unwrap();
        add_base_sort(&mut eg, BoolSort, span!()).unwrap();
        add_base_sort(&mut eg, I64Sort, span!()).unwrap();
        add_base_sort(&mut eg, F64Sort, span!()).unwrap();
        add_base_sort(&mut eg, BigIntSort, span!()).unwrap();
        add_base_sort(&mut eg, BigRatSort, span!()).unwrap();
        eg.type_info.add_presort::<MapSort>(span!()).unwrap();
        eg.type_info.add_presort::<SetSort>(span!()).unwrap();
        eg.type_info.add_presort::<VecSort>(span!()).unwrap();
        eg.type_info.add_presort::<FunctionSort>(span!()).unwrap();
        eg.type_info.add_presort::<MultiSetSort>(span!()).unwrap();
        eg.type_info.add_presort::<PairSort>(span!()).unwrap();

        // Add != with a validator that computes inequality result
        let neq_validator = |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
            if args.len() == 2 && args[0] != args[1] {
                // Return unit literal for successful inequality
                Some(termdag.lit(Literal::Unit))
            } else {
                None
            }
        };
        add_primitive_with_validator!(
            &mut eg,
            "!=" = |a: #, b: #| -?> () {
                (a != b).then_some(())
            },
            neq_validator
        );

        add_primitive_with_validator!(
            &mut eg,
            "bool-!=" = |a: #, b: #| -> bool {
                (a != b)
            },
            |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
                if args.len() == 2 {
                    Some(termdag.lit(Literal::Bool(args[0] != args[1])))
                } else {
                    None
                }
            }
        );

        add_primitive!(&mut eg, "value-eq" = |a: #, b: #| -?> () {
            (a == b).then_some(())
        });
        add_primitive!(&mut eg, "ordering-min" = |a: #, b: #| -> # {
            if a < b { a } else { b }
        });
        add_primitive!(&mut eg, "ordering-max" = |a: #, b: #| -> # {
            if a > b { a } else { b }
        });

        // Orientation helpers for the proof-encoding UF/view merges; see
        // [`crate::proofs::proof_encoding_helpers::OrientProof`].
        let orient_proof_validator = |take_min: bool| -> PrimitiveValidator {
            Arc::new(move |_: &mut TermDag, args: &[TermId]| -> Option<TermId> {
                let [a, a_proof, b, b_proof] = args else {
                    return None;
                };
                let take_first = if take_min { a < b } else { a > b };
                Some(if take_first { *a_proof } else { *b_proof })
            })
        };
        eg.add_pure_primitive(
            proofs::proof_encoding_helpers::OrientProof::min(),
            Some(orient_proof_validator(true)),
        );
        eg.add_pure_primitive(
            proofs::proof_encoding_helpers::OrientProof::max(),
            Some(orient_proof_validator(false)),
        );
        // `select-eq` keeps a custom FD-view merge's proof column stable; see
        // [`crate::proofs::proof_encoding_helpers::SelectEqProof`].
        let select_eq_validator: PrimitiveValidator =
            Arc::new(|_: &mut TermDag, args: &[TermId]| -> Option<TermId> {
                let [test, cand, if_eq, els] = args else {
                    return None;
                };
                Some(if test == cand { *if_eq } else { *els })
            });
        eg.add_pure_primitive(
            proofs::proof_encoding_helpers::SelectEqProof,
            Some(select_eq_validator),
        );

        eg.rulesets
            .insert("".into(), Ruleset::Rules(Default::default()));

        // The generic `get-fresh!` mint primitive is registered on every e-graph
        // (a no-op without an eclass-id counter). Doing it here — rather than
        // per-eq-sort — means it is present whenever the *encoded* program is run,
        // including when the already-desugared program is replayed in a plain
        // e-graph (e.g. the desugar proof-testing path).
        crate::proofs::proof_fresh::register_get_fresh(&mut eg);

        eg
    }
}

struct ResolvedNCommands {
    desugared: Vec<ResolvedNCommand>,
    /// In proof mode, populated with the desugared program before instrumented with proofs
    desugared_before_proofs: Vec<ResolvedNCommand>,
}

struct ResolvedNCommandsWithOutput {
    outputs: Vec<CommandOutput>,
    resolved: Vec<ResolvedNCommand>,
    /// In proof mode, populated with the desugared program before instrumented with proofs
    resolved_before_proofs: Vec<ResolvedNCommand>,
}

#[derive(Debug, Error)]
#[error("Not found: {0}")]
pub struct NotFoundError(String);

impl EGraph {
    /// Create a new e-graph with the term-encoding pipeline enabled.
    ///
    /// In term-encoding mode the e-graph eagerly instruments every constructor
    /// and function with auxiliary term tables, view tables, and per-sort
    /// union-finds so that canonical representatives and their justifications are
    /// materialized explicitly.  This makes it possible to record and emit
    /// equality proofs while preserving the observable behaviour of supported
    /// commands.
    pub fn new_with_term_encoding() -> Self {
        let mut egraph = EGraph::default();
        let typechecker = egraph.clone();
        egraph.enable_term_encoding(typechecker);
        egraph
    }

    /// Enable the term/proof encoding pipeline with `typechecker` as the head of
    /// the re-typechecking chain.
    fn enable_term_encoding(&mut self, typechecker: EGraph) {
        self.proof_state.original_typechecking = Some(Box::new(typechecker));
    }

    /// Create a new e-graph with proof generation enabled.
    pub fn new_with_proofs() -> Self {
        let mut egraph = EGraph::new_with_term_encoding();
        egraph.proof_state.proofs_enabled = true;
        egraph
    }

    /// Enable the term-encoding pipeline on an existing `EGraph`.
    ///
    /// This method is to support the current CLI implementation with egglog-experimental (https://github.com/egraphs-good/egglog/issues/768)
    #[doc(hidden)]
    pub fn with_term_encoding_enabled(mut self) -> Self {
        assert!(
            self.capture_catalog.is_none(),
            "trace recording graph cannot enable term encoding"
        );
        let typechecker = self.clone();
        self.enable_term_encoding(typechecker);
        self
    }

    /// Enable the term-encoding pipeline for a custom backend.
    ///
    /// Relational backends without a native union-find require this:
    /// congruence and rebuild are lowered to ordinary
    /// rules over `@uf` tables instead of relying on the backend's own
    /// union-find. Re-typechecking after the encoder runs uses a default
    /// (bridge-backed) e-graph, so this backend need not implement typechecking.
    pub fn with_term_encoding(mut self) -> Self {
        assert!(
            self.capture_catalog.is_none(),
            "trace recording graph cannot enable term encoding"
        );
        self.enable_term_encoding(EGraph::default());
        self
    }

    /// Enable the term-encoding pipeline for a custom backend, using the given
    /// bridge-backed e-graph for parsing/typechecking before instrumentation.
    #[doc(hidden)]
    pub fn with_term_encoding_typechecker(mut self, typechecker: EGraph) -> Self {
        assert!(
            self.capture_catalog.is_none(),
            "trace recording graph cannot enable term encoding"
        );
        self.enable_term_encoding(typechecker);
        self
    }

    /// Enable proof generation on this e-graph.
    /// TODO proofs should be turned on during creation of the e-graph, not afterwards.
    /// This method is to support the current CLI implementation with egglog-experimental (https://github.com/egraphs-good/egglog/issues/768)
    #[doc(hidden)]
    pub fn with_proofs_enabled(mut self) -> Self {
        assert!(
            self.capture_catalog.is_none(),
            "trace recording graph cannot enable proofs"
        );
        if self.proof_state.original_typechecking.is_none() {
            self = self.with_term_encoding_enabled();
        }
        self.proof_state.proofs_enabled = true;
        self
    }

    /// Enable native trace capture before loading facts or compiling
    /// rule plans.
    ///
    /// Structural replay identities are owned by this frontend and registered
    /// side-band with the backend. Ordinary execution has no catalog and keeps
    /// its existing instruction tape unchanged.
    pub fn enable_trace(&mut self) -> Result<(), Error> {
        if self.capture_catalog.is_some() {
            return Ok(());
        }
        if self.proof_state.original_typechecking.is_some() {
            return Err(Error::BackendError(
                "trace capture must run on the ordinary, non-proof graph".into(),
            ));
        }
        if self.pushed_egraph.is_some() {
            return Err(Error::BackendError(
                "trace capture cannot be enabled inside push/pop state".into(),
            ));
        }
        // `Rational` is installed by the standard experimental graph factory
        // before trace capture is enabled, and the fresh proof factory
        // installs the identical extension again for replay.
        let builtin_sorts = [
            "Unit", "String", "bool", "i64", "f64", "BigInt", "BigRat", "Rational",
        ];
        if !self.functions.is_empty()
            || self
                .type_info
                .sorts
                .keys()
                .any(|name| !builtin_sorts.contains(&name.as_str()))
        {
            return Err(Error::BackendError(
                "trace capture must be enabled before user declarations so the replay catalog is complete"
                    .into(),
            ));
        }
        if self
            .rulesets
            .values()
            .any(|ruleset| matches!(ruleset, Ruleset::Rules(rules) if !rules.is_empty()))
        {
            return Err(Error::BackendError(
                "trace capture must be enabled before registering rules".into(),
            ));
        }
        self.backend
            .enable_trace()
            .map_err(|error| Error::BackendError(error.to_string()))?;

        let mut catalog = CaptureCatalog::default();
        let container_sorts = self
            .type_info
            .sorts
            .values()
            .filter(|sort| sort.is_container_sort())
            .cloned()
            .collect::<Vec<_>>();
        for sort in container_sorts {
            let (logical_sort, container_type, child_sorts) = catalog
                .container_sort_spec(&sort)
                .expect("filtered container sort lost its metadata");
            self.backend
                .register_container_replay_sort(logical_sort, container_type, &child_sorts)
                .map_err(|error| Error::BackendError(error.to_string()))?;
        }
        let registrations = self
            .functions
            .values()
            .map(|function| {
                (
                    function.backend_id,
                    catalog.function_spec(
                        function.name(),
                        &function.schema,
                        function.subtype(),
                        self.relation_names.contains(function.name()),
                    ),
                )
            })
            .collect::<Vec<_>>();
        for (function, spec) in registrations {
            self.backend
                .register_function_replay(function, spec)
                .map_err(|error| Error::BackendError(error.to_string()))?;
        }
        self.capture_catalog = Some(catalog);
        Ok(())
    }

    /// Inspect a finalized native trace without copying its arena.
    pub fn with_trace_view<R>(
        &self,
        inspect: impl for<'view> FnOnce(&mut TraceView<'view>) -> Result<R, TraceViewError>,
    ) -> Result<R, Error> {
        self.capture_catalog
            .as_ref()
            .ok_or_else(|| Error::BackendError("trace capture is not enabled".into()))?
            .ensure_healthy()?;
        self.backend
            .as_any()
            .downcast_ref::<egglog_bridge::EGraph>()
            .ok_or_else(|| Error::BackendError("trace capture requires the main backend".into()))?
            .with_trace_view(inspect)
            .map_err(|error| Error::BackendError(error.to_string()))
    }

    #[cfg(test)]
    fn replay_term_counters(&self) -> Result<core_relations::TermInternerCounters, Error> {
        self.backend
            .as_any()
            .downcast_ref::<egglog_bridge::EGraph>()
            .ok_or_else(|| Error::BackendError("test backend has no native trace capture".into()))?
            .replay_term_counters()
            .map_err(|error| Error::BackendError(error.to_string()))
    }

    #[cfg(test)]
    fn replay_term(&self, id: ReplayTermId) -> Result<Option<ReplayTerm>, Error> {
        self.capture_catalog
            .as_ref()
            .ok_or_else(|| Error::BackendError("trace capture is not enabled".into()))?
            .ensure_healthy()?;
        self.backend
            .as_any()
            .downcast_ref::<egglog_bridge::EGraph>()
            .ok_or_else(|| Error::BackendError("test backend has no native trace capture".into()))?
            .replay_term(id)
            .map_err(|error| Error::BackendError(error.to_string()))
    }

    fn begin_trace_wave(&mut self) -> Result<(), Error> {
        let Some(catalog) = self.capture_catalog.as_mut() else {
            return Ok(());
        };
        catalog.ensure_healthy()?;
        let wave = catalog.begin_wave();
        self.backend
            .set_trace_wave(wave)
            .map_err(|error| Error::BackendError(error.to_string()))
    }

    pub(crate) fn capture_registration_is_allowed(&self) -> bool {
        self.capture_catalog
            .as_ref()
            .is_none_or(|catalog| catalog.resolving_command || catalog.active_command.is_some())
    }

    fn finalize_trace_wave(&mut self) -> Result<(), Error> {
        let Some(catalog) = self.capture_catalog.as_ref() else {
            return Ok(());
        };
        catalog.ensure_healthy()?;
        self.backend
            .finalize_trace_wave()
            .map_err(|error| Error::BackendError(error.to_string()))
    }

    /// Enable testing of getting proofs for all `check` commands.
    pub fn with_proof_testing(mut self) -> Self {
        assert!(
            self.capture_catalog.is_none(),
            "trace recording graph cannot enable proof testing"
        );
        self.proof_state.proof_testing = true;
        self
    }

    /// Enable proof testing while skipping validation of the extracted proofs.
    #[cfg(any(feature = "bin", test))]
    pub(crate) fn with_proof_extraction(mut self) -> Self {
        self = self.with_proofs_enabled().with_proof_testing();
        self.proof_state.verify_proofs = false;
        self
    }

    /// Set the number of threads used for parallel operations.
    ///
    /// This is a helper that simply configures the global rayon thread pool. It can only be called
    /// once per process; subsequent calls will be ignored.
    ///
    /// # Panics
    ///
    /// Panics on wasm if `num_threads > 1`.
    pub fn set_num_threads(num_threads: usize) {
        #[cfg(target_family = "wasm")]
        if num_threads > 1 {
            panic!("cannot use more than 1 thread on wasm");
        }
        #[cfg(not(target_family = "wasm"))]
        {
            // This will fail silently if the global pool has already been configured.
            let err = rayon::ThreadPoolBuilder::new()
                .num_threads(num_threads)
                .build_global();
            // print log if successful
            if matches!(err, Ok(())) {
                log::info!("Initialize global thread pool with  {num_threads} threads");
            } else {
                log::warn!(
                    "Failed to initialize global thread pool with {num_threads} threads. This may be because the thread pool was already initialized with a different number of threads. Error: {err:?}"
                );
            }
        }
    }

    /// Return the number of threads in the rayon thread pool.
    pub fn num_threads(&self) -> usize {
        rayon::current_num_threads()
    }

    /// Return extension-owned state stored on this e-graph.
    ///
    /// Extension state is keyed by Rust type and follows the same lifecycle as
    /// the rest of the e-graph: cloning an [`EGraph`] clones the state, and
    /// `push`/`pop` snapshots and restores it.
    pub fn extension_state<T>(&self) -> Option<&T>
    where
        T: Send + Sync + 'static,
    {
        let value = self.extension_state.get(&TypeId::of::<T>())?;
        (value.as_ref() as &dyn Any).downcast_ref()
    }

    /// Return mutable extension-owned state, inserting `T::default()` when absent.
    pub fn extension_state_or_default<T>(&mut self) -> &mut T
    where
        T: Default + Clone + Send + Sync + 'static,
    {
        assert!(
            self.capture_catalog.is_none(),
            "trace capture does not support mutable extension state after capture starts"
        );
        let value = self
            .extension_state
            .entry(TypeId::of::<T>())
            .or_insert_with(|| Box::new(T::default()));
        (value.as_mut() as &mut dyn Any)
            .downcast_mut()
            .expect("extension state entry must have the requested type")
    }

    /// Add a user-defined command to the e-graph
    /// Get the type information for this e-graph
    pub fn type_info(&mut self) -> &mut TypeInfo {
        assert!(
            self.capture_catalog.is_none(),
            "trace capture does not support mutable type information after capture starts"
        );
        &mut self.type_info
    }

    /// Get read-only access to the command macro registry
    pub fn command_macros(&self) -> &CommandMacroRegistry {
        &self.command_macros
    }

    /// Get mutable access to the command macro registry
    pub fn command_macros_mut(&mut self) -> &mut CommandMacroRegistry {
        assert!(
            self.capture_catalog.is_none(),
            "trace capture does not support registering macros after capture starts"
        );
        &mut self.command_macros
    }

    pub fn add_command(
        &mut self,
        name: String,
        command: Arc<dyn UserDefinedCommand>,
    ) -> Result<(), Error> {
        if self.capture_catalog.is_some() {
            return Err(Error::BackendError(
                "trace capture does not support registering commands after capture starts".into(),
            ));
        }
        if self.commands.contains_key(&name)
            || self.functions.contains_key(&name)
            || self.type_info.get_prims(&name).is_some()
        {
            return Err(Error::CommandAlreadyExists(name, span!()));
        }
        self.commands.insert(name.clone(), command);
        self.parser.add_user_defined(name)?;
        Ok(())
    }

    /// Configure whether globals missing the required `$` prefix are treated as errors.
    pub fn set_strict_mode(&mut self, strict_mode: bool) {
        assert!(
            self.capture_catalog.is_none(),
            "trace capture does not support changing strict mode after capture starts"
        );
        self.strict_mode = strict_mode;
    }

    /// Returns `true` when missing `$` prefixes on globals are treated as errors.
    pub fn strict_mode(&self) -> bool {
        self.strict_mode
    }

    /// Configure whether the internal reserved symbol (@) is allowed in user-defined names.
    /// WARNING: do not use, this is for testing running egglog after desugaring.
    /// Public so files.rs can use it, hidden from documentation because it is not intended for general use.
    #[doc(hidden)]
    pub fn ensure_no_reserved_symbols(&mut self, should_ensure: bool) {
        assert!(
            self.capture_catalog.is_none(),
            "trace capture does not support changing parser symbol policy after capture starts"
        );
        self.parser.ensure_no_reserved_symbols = should_ensure;
    }

    fn ensure_global_name_prefix(&mut self, span: &Span, name: &str) -> Result<(), TypeError> {
        if name.starts_with(GLOBAL_NAME_PREFIX) {
            return Ok(());
        }
        if self.strict_mode {
            Err(TypeError::GlobalMissingPrefix {
                name: name.to_owned(),
                span: span.clone(),
            })
        } else {
            self.warn_missing_global_prefix(span, name)?;
            Ok(())
        }
    }

    fn warn_missing_global_prefix(
        &mut self,
        span: &Span,
        canonical_name: &str,
    ) -> Result<(), TypeError> {
        if self.strict_mode {
            return Err(TypeError::GlobalMissingPrefix {
                name: format!("{GLOBAL_NAME_PREFIX}{canonical_name}"),
                span: span.clone(),
            });
        }
        if self.warned_about_global_prefix {
            return Ok(());
        }
        self.warned_about_global_prefix = true;
        log::warn!(
            "{span}\nGlobal `{canonical_name}` should start with `{GLOBAL_NAME_PREFIX}`. Enable `--strict-mode` to turn this warning into an error. Suppressing additional warnings of this type."
        );
        Ok(())
    }

    fn warn_prefixed_non_globals(
        &mut self,
        span: &Span,
        canonical_name: &str,
    ) -> Result<(), TypeError> {
        if self.strict_mode {
            return Err(TypeError::NonGlobalPrefixed {
                name: canonical_name.to_string(),
                span: span.clone(),
            });
        }
        if self.warned_about_global_prefix {
            return Ok(());
        }
        self.warned_about_global_prefix = true;
        log::warn!(
            "{span}\nNon-global `{canonical_name}` should not start with `{GLOBAL_NAME_PREFIX}`. Enable `--strict-mode` to turn this warning into an error. Suppressing additional warnings of this type."
        );
        Ok(())
    }

    /// Push a snapshot of the e-graph into the stack.
    ///
    /// See [`EGraph::pop`].
    pub fn push(&mut self) {
        assert!(
            self.capture_catalog.is_none(),
            "trace capture does not support EGraph::push"
        );
        let prev_prev: Option<Box<Self>> = self.pushed_egraph.take();
        let mut prev = self.clone();
        prev.pushed_egraph = prev_prev;
        self.pushed_egraph = Some(Box::new(prev));
    }

    /// Pop the current egraph off the stack, replacing
    /// it with the previously pushed egraph.
    /// It preserves the run report and messages from the popped
    /// egraph.
    pub fn pop(&mut self) -> Result<(), Error> {
        if self.capture_catalog.is_some() {
            return Err(Error::BackendError(
                "trace capture does not support EGraph::pop".into(),
            ));
        }
        match self.pushed_egraph.take() {
            Some(mut e) => {
                // Preserve the overall report from the popped egraph
                std::mem::swap(&mut self.overall_run_report, &mut e.overall_run_report);
                // Preserve the symbol generator so that fresh symbols
                // generated after pop don't collide with ones generated before pop.
                std::mem::swap(&mut self.parser.symbol_gen, &mut e.parser.symbol_gen);
                *self = *e;
                Ok(())
            }
            None => Err(Error::Pop(span!())),
        }
    }

    fn translate_expr_to_mergefn(
        &self,
        expr: &ResolvedExpr,
        lets: &HashMap<String, usize>,
    ) -> Result<egglog_bridge::MergeFn, Error> {
        match expr {
            GenericExpr::Lit(_, literal) => {
                let val = literal_to_value(self.backend.base_values(), literal);
                Ok(egglog_bridge::MergeFn::Const(val))
            }
            GenericExpr::Var(span, resolved_var) => {
                let name = resolved_var.name.as_str();
                // A `let`-bound variable resolves to its environment slot. Otherwise: single-output
                // merges use `old`/`new`; tuple-output merges use `old0`, `new0`, `old1`, ... to
                // refer to the old/new value of a specific output column.
                if let Some(&slot) = lets.get(name) {
                    Ok(egglog_bridge::MergeFn::LetVar(slot))
                } else if name == "old" {
                    Ok(egglog_bridge::MergeFn::Old)
                } else if name == "new" {
                    Ok(egglog_bridge::MergeFn::New)
                } else if let Some(i) = name.strip_prefix("old").and_then(|s| s.parse().ok()) {
                    Ok(egglog_bridge::MergeFn::OldCol(i))
                } else if let Some(i) = name.strip_prefix("new").and_then(|s| s.parse().ok()) {
                    Ok(egglog_bridge::MergeFn::NewCol(i))
                } else {
                    // NB: type-checking should already catch unbound variables here.
                    Err(TypeError::Unbound(resolved_var.name.clone(), span.clone()).into())
                }
            }
            GenericExpr::Call(_, ResolvedCall::Func(f), args) => {
                let translated_args = args
                    .iter()
                    .map(|arg| self.translate_expr_to_mergefn(arg, lets))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(egglog_bridge::MergeFn::Function(
                    self.functions[&f.name].backend_id,
                    translated_args,
                ))
            }
            GenericExpr::Call(_, ResolvedCall::Primitive(p), args) => {
                let mut translated_args = args
                    .iter()
                    .map(|arg| self.translate_expr_to_mergefn(arg, lets))
                    .collect::<Result<Vec<_>, _>>()?;
                if p.name() == "unstable-fn" {
                    let Some(GenericExpr::Lit(_, Literal::String(name))) = args.first() else {
                        return Err(Error::BackendError(
                            "expected string literal after `unstable-fn`".into(),
                        ));
                    };
                    let bridge = self
                        .backend
                        .as_any()
                        .downcast_ref::<egglog_bridge::EGraph>()
                        .ok_or_else(|| {
                            Error::BackendError(
                                "`unstable-fn` merge expressions require the reference bridge backend"
                                    .into(),
                            )
                        })?;
                    let panic_id = bridge.action_registry().read().unwrap().default_panic_id();
                    let resolved = resolve_function_container_target_with_context(
                        bridge,
                        &self.functions,
                        &self.type_info,
                        name,
                        p,
                        panic_id,
                    )?;
                    translated_args[0] =
                        egglog_bridge::MergeFn::Const(self.backend.base_values().get(resolved));
                }
                let primitive = p.external_id(crate::Context::Write);
                if primitive_merge_returns_one_input(p.name()) {
                    Ok(egglog_bridge::MergeFn::InputChoicePrimitive(
                        primitive,
                        translated_args,
                    ))
                } else {
                    Ok(egglog_bridge::MergeFn::Primitive(
                        primitive,
                        translated_args,
                    ))
                }
            }
            // `(values ...)` never legitimately reaches here: a top-level tuple merge is
            // destructured per column in `declare_function`, and any other `(values ...)` is
            // rejected during type-checking. This arm only keeps the match exhaustive.
            GenericExpr::Call(span, ResolvedCall::Values(_), _) => Err(Error::TypeError(
                TypeError::TupleMergeNotValues("<merge>".to_owned(), span.clone()),
            )),
        }
    }

    /// Lower a resolved `:merge` (a value-producing action block) to a backend [`MergeFn`], keeping
    /// the existing merge interpreter. The `result` produces the merged value(s); any `actions` run
    /// first as effects.
    /// `self_ref` names the function this merge belongs to and its (peeked) backend id,
    /// so the merge can write into the table being declared.
    fn translate_merge_to_mergefn(
        &self,
        merge: &ResolvedMerge,
        self_ref: (&str, egglog_bridge::FunctionId),
    ) -> Result<egglog_bridge::MergeFn, Error> {
        use egglog_bridge::MergeFn;
        // Assign each `let`-bound variable an environment slot, in block order, so `set`/`union`
        // args and the result can refer to it via `MergeFn::LetVar`. Built up front because the
        // result is lowered before the actions.
        let mut lets = HashMap::<String, usize>::default();
        for action in merge.actions.iter() {
            if let GenericAction::Let(_, var, _) = action {
                let slot = lets.len();
                lets.insert(var.name.as_str().to_owned(), slot);
            }
        }
        // Lower the result value (a `(values ...)` result becomes one column per element).
        let result = match &merge.result {
            GenericExpr::Call(_, ResolvedCall::Values(_), cols) => MergeFn::Columns(
                cols.iter()
                    .map(|e| self.translate_expr_to_mergefn(e, &lets))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            expr => self.translate_expr_to_mergefn(expr, &lets)?,
        };
        if merge.actions.is_empty() {
            return Ok(result);
        }
        // A value-producing action block: run the effects, then evaluate the result value(s).
        let actions = merge
            .actions
            .iter()
            .map(|a| self.translate_merge_action(a, &lets, self_ref))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(MergeFn::Block {
            actions,
            result: Box::new(result),
        })
    }

    /// Lower a single resolved merge action to a backend [`MergeAction`]. Supports `set`, `let`, and
    /// `union`; other actions (`delete`/`panic`/`extract`/...) are not meaningful during a merge.
    fn translate_merge_action(
        &self,
        action: &ResolvedAction,
        lets: &HashMap<String, usize>,
        self_ref: (&str, egglog_bridge::FunctionId),
    ) -> Result<egglog_bridge::MergeAction, Error> {
        use egglog_bridge::MergeAction;
        match action {
            GenericAction::Let(_, var, expr) => Ok(MergeAction::Let {
                slot: lets[var.name.as_str()],
                value: self.translate_expr_to_mergefn(expr, lets)?,
            }),
            GenericAction::Union(_, a, b) => Ok(MergeAction::Union(
                self.translate_expr_to_mergefn(a, lets)?,
                self.translate_expr_to_mergefn(b, lets)?,
            )),
            GenericAction::Set(_, ResolvedCall::Func(f), keys, val) => {
                // The function being declared is not in `functions` yet; its id was peeked.
                let backend_id = if f.name == self_ref.0 {
                    self_ref.1
                } else {
                    self.functions
                        .get(&f.name)
                        .ok_or_else(|| {
                            Error::BackendError(format!(
                                "merge action sets unknown function `{}`",
                                f.name
                            ))
                        })?
                        .backend_id
                };
                let mut args = keys
                    .iter()
                    .map(|k| self.translate_expr_to_mergefn(k, lets))
                    .collect::<Result<Vec<_>, _>>()?;
                // A tuple-output target is set with `(values ...)`; expand it into value columns.
                match val {
                    GenericExpr::Call(_, ResolvedCall::Values(_), cols) => {
                        for c in cols {
                            args.push(self.translate_expr_to_mergefn(c, lets)?);
                        }
                    }
                    _ => args.push(self.translate_expr_to_mergefn(val, lets)?),
                }
                Ok(MergeAction::Set(backend_id, args))
            }
            other => Err(Error::BackendError(format!(
                "action `{other}` is not supported inside a :merge block (only `set`, `let`, `union`)"
            ))),
        }
    }

    fn declare_function(&mut self, decl: &ResolvedFunctionDecl) -> Result<(), Error> {
        let get_sort = |name: &String| match self.type_info.get_sort_by_name(name) {
            Some(sort) => Ok(sort.clone()),
            None => Err(Error::TypeError(TypeError::UndefinedSort(
                name.to_owned(),
                decl.span.clone(),
            ))),
        };

        let input = decl
            .schema
            .input
            .iter()
            .map(get_sort)
            .collect::<Result<Vec<_>, _>>()?;
        let outputs = decl
            .schema
            .outputs
            .iter()
            .map(get_sort)
            .collect::<Result<Vec<_>, _>>()?;
        let num_outputs = outputs.len();
        let schema = ResolvedSchema { input, outputs };
        let is_relation = self.relation_names.contains(&decl.name);
        let replay = self
            .capture_catalog
            .as_mut()
            .map(|catalog| catalog.function_spec(&decl.name, &schema, decl.subtype, is_relation));

        let can_subsume = match decl.subtype {
            FunctionSubtype::Constructor => true,
            // View tables (functions with term_constructor) need subsumption support
            FunctionSubtype::Custom => decl.term_constructor.is_some(),
        };

        use egglog_bridge::{DefaultVal, MergeFn};
        // This function's backend id (the id `add_table` below will assign, peeked
        // deterministically), so its merge can write into its own table.
        let own_id = self.backend.peek_next_function_id();
        let merge = match decl.subtype {
            FunctionSubtype::Constructor => MergeFn::UnionId,
            FunctionSubtype::Custom => match &decl.merge {
                Some(merge) => self.translate_merge_to_mergefn(merge, (&decl.name, own_id))?,
                // No merge clause: assert equality per output column.
                None if num_outputs > 1 => {
                    MergeFn::Columns((0..num_outputs).map(|_| MergeFn::AssertEq).collect())
                }
                None => MergeFn::AssertEq,
            },
        };
        let backend_id = self
            .backend
            .try_add_table(egglog_bridge::FunctionConfig {
                schema: schema
                    .input
                    .iter()
                    .chain(schema.outputs.iter())
                    .map(|sort| sort.column_ty(self.backend.base_values()))
                    .collect(),
                n_vals: num_outputs,
                n_identity_vals: decl.identity_vals,
                default: match decl.subtype {
                    FunctionSubtype::Constructor => DefaultVal::FreshId,
                    FunctionSubtype::Custom => DefaultVal::Fail,
                },
                merge,
                name: decl.name.to_string(),
                can_subsume,
            })
            .map_err(|error| Error::BackendError(error.to_string()))?;
        assert_eq!(backend_id, own_id);
        if let Some(replay) = replay {
            self.backend
                .register_function_replay(backend_id, replay)
                .map_err(|error| Error::BackendError(error.to_string()))?;
        }

        let function = Function {
            decl: decl.clone(),
            schema,
            can_subsume,
            backend_id,
        };

        let old = self.functions.insert(decl.name.clone(), function);
        if old.is_some() {
            panic!(
                "Typechecking should have caught function already bound: {}",
                decl.name
            );
        }

        Ok(())
    }

    /// Extract rows of a table using the default cost model with name sym
    /// The `include_output` parameter controls whether the output column is always extracted
    /// For functions, the output column is usually useful
    /// Print up to `n` the tuples in a given function.
    /// Print all tuples if `n` is not provided.
    pub fn print_function(
        &mut self,
        sym: &str,
        n: Option<usize>,
        file: Option<File>,
        mode: PrintFunctionMode,
    ) -> Result<Option<CommandOutput>, Error> {
        let n = match n {
            Some(n) => {
                log::info!("Printing up to {n} tuples of function {sym} as {mode}");
                n
            }
            None => {
                log::info!("Printing all tuples of function {sym} as {mode}");
                usize::MAX
            }
        };

        let (terms, outputs, termdag) = self.function_to_dag(sym, n, true)?;
        let f = self
            .functions
            .get(sym)
            // function_to_dag should have checked this
            .unwrap();
        let terms_and_outputs: Vec<_> = terms.into_iter().zip(outputs.unwrap()).collect();
        let output = CommandOutput::PrintFunction(f.clone(), termdag, terms_and_outputs, mode);
        match file {
            Some(mut file) => {
                log::info!("Writing output to file");
                file.write_all(output.to_string().as_bytes())
                    .expect("Error writing to file");
                Ok(None)
            }
            None => Ok(Some(output)),
        }
    }

    /// Provide a program for use in proof checking.
    /// This enables testing of a desugared egglog proof program outside of proof mode.
    /// When proof_testing is true, turns all the `check` commands into `prove` commands.
    /// Not intended for general use but needed in files.rs, so public but hidden.
    #[doc(hidden)]
    pub fn set_proof_checking_program(
        &mut self,
        prog: Vec<Command>,
        proof_testing: bool,
    ) -> Result<(), Error> {
        if self.capture_catalog.is_some() {
            return Err(Error::BackendError(
                "trace capture does not support installing a proof-check program on the recording graph"
                    .into(),
            ));
        }
        // make a new e-graph, desugar the program in proof mode
        let mut proof_check_eg = EGraph::new_with_proofs();
        if proof_testing {
            proof_check_eg = proof_check_eg.with_proof_testing();
        }
        let resolved = proof_check_eg.process_program_internal(prog, false)?;

        self.proof_check_program = resolved.resolved_before_proofs;
        Ok(())
    }

    /// Print the size of a function. If no function name is provided,
    /// print the size of all non-hidden functions as an s-expression list of
    /// `(name size)` pairs, e.g. `((name size) ...)`.
    pub fn print_size(&self, sym: Option<&str>) -> Result<CommandOutput, Error> {
        if let Some(sym) = sym {
            // In proof mode, we have view tables instead of term tables.
            // So we do a linear scan to find the view table first, falling back on the normal table otherwise.
            // (We don't check the proof mode flag so that this still works after desugaring)
            let f = self
                .functions
                .values()
                .find(|f| f.decl.term_constructor.as_deref() == Some(sym))
                .or_else(|| self.functions.get(sym))
                .ok_or(TypeError::UnboundFunction(sym.to_owned(), span!()))?;
            // Skip hidden and let_binding functions
            if f.decl.internal_hidden || f.decl.internal_let {
                return Err(TypeError::UnboundFunction(sym.to_owned(), span!()).into());
            }
            let size = self.backend.table_size(f.backend_id);
            log::info!("Function {sym} has size {size}");
            Ok(CommandOutput::PrintFunctionSize(size))
        } else {
            // Print size of all non-hidden, non-let_binding functions
            // For view tables, use the term_constructor name instead
            let mut lens = self
                .functions
                .iter()
                .filter(|(_, f)| !f.decl.internal_hidden && !f.decl.internal_let)
                .map(|(sym, f)| {
                    let name = f
                        .decl
                        .term_constructor
                        .clone()
                        .unwrap_or_else(|| sym.clone());
                    (name, self.backend.table_size(f.backend_id))
                })
                .collect::<Vec<_>>();

            // Function name's alphabetical order
            lens.sort_by_key(|(name, _)| name.clone());
            if log_enabled!(Level::Info) {
                for (sym, len) in &lens {
                    log::info!("Function {sym} has size {len}");
                }
            }
            Ok(CommandOutput::PrintAllFunctionsSize(lens))
        }
    }

    fn run_schedule(&mut self, sched: &ResolvedSchedule) -> Result<RunReport, Error> {
        match sched {
            ResolvedSchedule::Run(span, config) => self.run_rules(span, config),
            ResolvedSchedule::RunRule(span, configs) => self.run_grounded_rules(span, configs),
            ResolvedSchedule::Repeat(_span, limit, sched) => {
                let mut report = RunReport::default();
                for _i in 0..*limit {
                    let rec = self.run_schedule(sched)?;
                    let can_stop = rec.can_stop;
                    report.union(rec);
                    if can_stop {
                        break;
                    }
                }
                Ok(report)
            }
            ResolvedSchedule::Saturate(_span, sched) => {
                let mut report = RunReport::default();
                let mut i = 0usize;
                loop {
                    i += 1;
                    log::debug!(
                        "Saturate iteration {i} start: {}",
                        Self::schedule_for_log(sched)
                    );
                    let rec = self.run_schedule(sched)?;
                    let updated = rec.updated;
                    log::debug!(
                        "Saturate iteration {i} end: {}",
                        Self::run_report_debug_summary(&rec)
                    );
                    report.union(rec);
                    if !updated {
                        log::debug!("Saturate reached fixpoint after {i} iteration(s)");
                        break;
                    }
                }
                Ok(report)
            }
            ResolvedSchedule::Sequence(_span, scheds) => {
                let mut report = RunReport::default();
                for sched in scheds {
                    report.union(self.run_schedule(sched)?);
                }
                Ok(report)
            }
        }
    }

    fn run_grounded_rules(
        &mut self,
        span: &Span,
        configs: &[ResolvedRunRuleConfig],
    ) -> Result<RunReport, Error> {
        if self.capture_catalog.is_some() {
            return Err(Error::BackendError(
                "trace capture does not support source run-rule schedules".into(),
            ));
        }
        let mut pending = Vec::with_capacity(configs.len());
        let mut rulesets = IndexSet::default();
        for config in configs {
            let (ruleset, rule, substitutions) = self
                .rulesets
                .iter()
                .find_map(|(ruleset_name, ruleset)| match ruleset {
                    Ruleset::Rules(rules) => rules.get(&config.rule).map(|registered| {
                        (
                            ruleset_name.clone(),
                            registered.backend_id,
                            registered.substitutions.clone(),
                        )
                    }),
                    Ruleset::Combined(_) => None,
                })
                .ok_or_else(|| Error::NoSuchRule(config.rule.clone(), span.clone()))?;
            rulesets.insert(ruleset);

            let mut canonical = HashMap::<ResolvedVar, Value>::default();
            for (source, expression) in &config.bindings {
                let value = self.eval_checked_expr(&source.name, expression)?;
                let mut target = ResolvedAtomTerm::Var(expression.span(), source.clone());
                for _ in 0..=substitutions.len() {
                    let ResolvedAtomTerm::Var(_, variable) = &target else {
                        break;
                    };
                    let Some((_, replacement)) = substitutions
                        .iter()
                        .find(|(candidate, _)| candidate == variable)
                    else {
                        break;
                    };
                    target = replacement.clone();
                }
                match target {
                    ResolvedAtomTerm::Var(_, variable) => {
                        let value = self.canonical_checked_value(&variable.sort, value);
                        if let Some(previous) = canonical.insert(variable.clone(), value)
                            && previous != value
                        {
                            return Err(Error::BackendError(format!(
                                "{span}: grounded rule `{}` gives unequal values to canonical variable `{}`",
                                config.rule, variable.name
                            )));
                        }
                    }
                    ResolvedAtomTerm::Literal(_, literal) => {
                        let expected = self.canonical_checked_value(
                            &source.sort,
                            literal_to_value(self.backend.base_values(), &literal),
                        );
                        let value = self.canonical_checked_value(&source.sort, value);
                        if value != expected {
                            return Err(Error::BackendError(format!(
                                "{span}: grounded rule `{}` binding `{}` contradicts canonical literal `{literal}`",
                                config.rule, source.name
                            )));
                        }
                    }
                    ResolvedAtomTerm::Global(_, variable) => {
                        return Err(Error::BackendError(format!(
                            "{span}: grounded rule `{}` retains global `{}` after canonicalization",
                            config.rule, variable.name
                        )));
                    }
                }
            }
            pending.push((config.rule.clone(), rule, canonical));
        }

        let bridge = self
            .backend
            .as_any_mut()
            .downcast_mut::<egglog_bridge::EGraph>()
            .ok_or_else(|| {
                Error::BackendError("run-rule requires the concrete main bridge backend".into())
            })?;
        let mut firings = Vec::with_capacity(pending.len());
        for (index, (name, rule, canonical)) in pending.into_iter().enumerate() {
            let variables = bridge
                .grounded_rule_variables(rule)
                .map_err(|error| Error::BackendError(error.to_string()))?;
            let mut bindings = Vec::with_capacity(canonical.len());
            for (variable, value) in canonical {
                let expected_ty = variable.sort.column_ty(bridge.base_values());
                let mut matches = variables.iter().filter(|candidate| {
                    candidate.name.as_deref() == Some(variable.name.as_str())
                        && candidate.ty == expected_ty
                });
                let descriptor = matches.next().ok_or_else(|| {
                    Error::BackendError(format!(
                        "{span}: grounded rule `{name}` has no compiled variable `{}` of the recorded type",
                        variable.name
                    ))
                })?;
                if matches.next().is_some() {
                    return Err(Error::BackendError(format!(
                        "{span}: grounded rule `{name}` has ambiguous compiled variable `{}`",
                        variable.name
                    )));
                }
                bindings.push(egglog_bridge::GroundedRuleBinding {
                    variable: descriptor.variable,
                    ty: descriptor.ty,
                    value,
                });
            }
            firings.push(egglog_bridge::GroundedRuleRun {
                match_id: index as u64,
                rule,
                bindings: bindings.into_boxed_slice(),
            });
        }

        let names = configs
            .iter()
            .enumerate()
            .map(|(index, config)| format!("{index}:{}", config.rule))
            .collect::<Vec<_>>()
            .join(", ");
        let report = bridge.run_grounded_wave(&firings).map_err(|error| {
            Error::BackendError(format!(
                "{span}: grounded run-rule wave [{names}] failed: {error}"
            ))
        })?;
        let report_name = if rulesets.len() == 1 {
            rulesets.first().expect("one ruleset disappeared").as_str()
        } else {
            "__slice_replay"
        };
        Ok(RunReport::singleton(report_name, report))
    }

    fn run_rules(&mut self, span: &Span, config: &ResolvedRunConfig) -> Result<RunReport, Error> {
        log::debug!("Running ruleset: {}", config.ruleset);
        let mut report: RunReport = Default::default();

        let GenericRunConfig { ruleset, until } = config;

        if !self.rulesets.contains_key(ruleset) {
            return Err(Error::NoSuchRuleset(ruleset.clone(), span.clone()));
        }

        if let Some(facts) = until {
            match self.check_facts(span, facts, false) {
                Ok(()) => {
                    log::info!(
                        "Breaking early because of facts:\n {}!",
                        ListDisplay(facts, "\n")
                    );
                    return Ok(report);
                }
                Err(Error::CheckError(..)) => {}
                Err(error) => return Err(error),
            }
        }

        let subreport = self.step_rules(ruleset)?;
        report.union(subreport);

        if log_enabled!(Level::Debug) {
            log::debug!(
                "Finished ruleset {ruleset}: database size {}, {}",
                self.num_tuples(),
                Self::run_report_debug_summary(&report)
            );
        }

        Ok(report)
    }

    fn run_report_debug_summary(report: &RunReport) -> String {
        let mut rules = report
            .num_matches_per_rule
            .iter()
            .filter(|(_, matches)| **matches > 0)
            .collect::<Vec<_>>();
        rules.sort_by(|(_, left), (_, right)| right.cmp(left));

        let top_rules = rules
            .into_iter()
            .take(5)
            .map(|(rule, matches)| {
                format!("{}={matches}", Self::truncate_for_log(rule.as_ref(), 80))
            })
            .collect::<Vec<_>>()
            .join(", ");

        format!(
            "updated={}, can_stop={}, iterations={}, top_matches=[{}]",
            report.updated,
            report.can_stop,
            report.iterations.len(),
            top_rules
        )
    }

    fn schedule_for_log(sched: &impl Display) -> String {
        Self::truncate_for_log(&sched.to_string(), 160)
    }

    fn truncate_for_log(s: &str, limit: usize) -> String {
        let mut s = s.replace('\n', " ");
        if s.len() > limit {
            s.truncate(limit);
            s.push_str("...");
        }
        s
    }

    /// Runs a ruleset for an iteration.
    ///
    /// This applies every match it finds (under semi-naive).
    /// See [`EGraph::step_rules_with_scheduler`] for more fine-grained control.
    ///
    /// This will return an error if an egglog primitive returns None in an action.
    pub fn step_rules(&mut self, ruleset: &str) -> Result<RunReport, Error> {
        if self
            .capture_catalog
            .as_ref()
            .is_some_and(|catalog| catalog.active_command.is_none())
        {
            return Err(Error::BackendError(
                "trace capture requires ruleset steps to run inside a cataloged schedule command"
                    .into(),
            ));
        }
        fn collect_rule_ids(
            ruleset: &str,
            rulesets: &IndexMap<String, Ruleset>,
            ids: &mut Vec<egglog_bridge::RuleId>,
        ) {
            match &rulesets[ruleset] {
                Ruleset::Rules(rules) => {
                    for rule in rules.values() {
                        ids.push(rule.backend_id);
                    }
                }
                Ruleset::Combined(sub_rulesets) => {
                    for sub_ruleset in sub_rulesets {
                        collect_rule_ids(sub_ruleset, rulesets, ids);
                    }
                }
            }
        }

        let mut rule_ids = Vec::new();
        collect_rule_ids(ruleset, &self.rulesets, &mut rule_ids);

        self.begin_trace_wave()?;
        let iteration_report = match self.backend.run_rules(RuleSetRun {
            name: Some(ruleset),
            rules: &rule_ids,
        }) {
            Ok(report) => report,
            Err(error) => {
                if let Some(catalog) = self.capture_catalog.as_mut() {
                    catalog.poison(format!(
                        "ruleset `{ruleset}` failed after entering trace wave execution"
                    ));
                }
                return Err(Error::BackendError(error.to_string()));
            }
        };
        if let Err(error) = self.finalize_trace_wave() {
            if let Some(catalog) = self.capture_catalog.as_mut() {
                catalog.poison(format!(
                    "ruleset `{ruleset}` failed while finalizing its trace wave"
                ));
            }
            return Err(error);
        }
        if let Some(catalog) = self.capture_catalog.as_mut() {
            catalog.has_run = true;
        }

        Ok(RunReport::singleton(ruleset, iteration_report))
    }

    fn add_rule(&mut self, rule: ast::ResolvedRule) -> Result<String, Error> {
        let rule_name = rule.name.clone();
        let ruleset_name = rule.ruleset.clone();
        // The `:naive` rule option opts a single rule out of seminaive
        // evaluation. This widens primitive-context selection from
        // Pure/Write to Read/Full, so primitives that read or write the
        // database can run inside this rule.
        let seminaive = self.seminaive && !rule.eval_mode.is_naive();
        // The `:no-decomp` rule option (and the global `--no-decomp`
        // flag) skips tree-decomposition in query planning, forcing
        // the single-bag fast path.
        let no_decomp = self.no_decomp || rule.no_decomp;
        let requires_read_context = !seminaive
            || matches!(
                rule.eval_mode,
                RuleEvalMode::Naive | RuleEvalMode::UnsafeSeminaive
            );

        // Disable union_to_set optimization in proof or term encoding mode, since
        // it expects only `union` on constructors (not set).
        let union_to_set = self.proof_state.original_typechecking.is_none();

        match self.rulesets.get(&rule.ruleset) {
            Some(Ruleset::Rules(_)) => {}
            Some(Ruleset::Combined(_)) => {
                return Err(Error::CombinedRulesetError(
                    rule.ruleset.clone(),
                    rule.span.clone(),
                ));
            }
            None => {
                return Err(Error::NoSuchRuleset(
                    rule.ruleset.clone(),
                    rule.span.clone(),
                ));
            }
        }

        let capture_inputs = self
            .capture_catalog
            .as_ref()
            .map(|catalog| source_rule_inputs(&rule, &catalog.immutable_globals))
            .transpose()?;

        let canonicalized = rule.to_canonicalized_core_rule_with_substitutions(
            &self.type_info,
            &mut self.parser.symbol_gen,
            union_to_set,
        )?;
        let rule_capture = if let Some(inputs) = capture_inputs {
            let id = self
                .capture_catalog
                .as_mut()
                .expect("capture inputs require an active catalog")
                .register_rule(&rule.ruleset, &rule.name, &inputs)?;
            Some((id, inputs))
        } else {
            None
        };
        if let Some(catalog) = self.capture_catalog.as_mut() {
            catalog.register_rule_primitives(&canonicalized.core);
        }
        let core_rule = canonicalized.core;
        let (query, actions) = (&core_rule.body, &core_rule.head);
        let rule_id = {
            let mut translator = BackendRule::new(
                &mut *self.backend,
                &self.functions,
                &self.type_info,
                self.capture_catalog.as_ref(),
                &mut self.unstable_fn_panic_ids,
                requires_read_context,
            );
            translator.query(query, rule.include_subsumed)?;
            translator.actions(actions)?;
            if let Some((rule, inputs)) = &rule_capture {
                translator.set_firing_capture(
                    *rule,
                    &inputs.variables,
                    &canonicalized.substitutions,
                )?;
            }
            translator.try_build(&rule.name, seminaive, no_decomp, core_rule.span.clone())?
        };

        let Some(Ruleset::Rules(rules)) = self.rulesets.get_mut(&ruleset_name) else {
            unreachable!("ruleset was validated before compiling the rule")
        };
        match rules.entry(rule_name.clone()) {
            indexmap::map::Entry::Occupied(_) => {
                panic!("Rule '{}' was already present", rule_name)
            }
            indexmap::map::Entry::Vacant(e) => e.insert(RegisteredRule {
                core: core_rule,
                backend_id: rule_id,
                substitutions: canonicalized.substitutions,
            }),
        };
        Ok(rule_name)
    }

    fn visit_source_capture_expr(
        &self,
        catalog: &CaptureCatalog,
        root: &ResolvedExpr,
        dependencies: &mut IndexSet<SourceRef>,
        unsupported: &mut Option<String>,
    ) {
        let mut pending = vec![root];
        while let Some(expr) = pending.pop() {
            let GenericExpr::Call(_, call, children) = expr else {
                continue;
            };
            pending.extend(children.iter());
            match call {
                ResolvedCall::Func(function) => {
                    let immutable = function.input.is_empty()
                        && self
                            .functions
                            .get(&function.name)
                            .is_some_and(|entry| entry.decl.internal_let);
                    if immutable {
                        if let Some(source) = catalog.immutable_globals.get(&function.name) {
                            dependencies.insert(source.clone());
                        } else {
                            unsupported.get_or_insert_with(|| {
                                format!(
                                    "immutable global `{}` has no source capture",
                                    function.name
                                )
                            });
                        }
                    } else if function.subtype != FunctionSubtype::Constructor {
                        unsupported.get_or_insert_with(|| {
                            format!(
                                "top-level source action reads custom function `{}`",
                                function.name
                            )
                        });
                    }
                }
                ResolvedCall::Primitive(primitive)
                    if primitive.is_pure() && primitive.validator().is_some() => {}
                ResolvedCall::Primitive(primitive) => {
                    unsupported.get_or_insert_with(|| {
                        format!(
                            "top-level source action calls effectful primitive `{}`",
                            primitive.name()
                        )
                    });
                }
                ResolvedCall::Values(_) => {}
            }
        }
    }

    fn analyze_source_capture(&self, actions: &ResolvedActions) -> SourceCaptureAnalysis {
        let catalog = self
            .capture_catalog
            .as_ref()
            .expect("source capture requires an active capture catalog");
        let mut dependencies = IndexSet::default();
        let mut unsupported = catalog
            .has_run
            .then(|| "source action executed after a run command".to_owned());
        let mut produced_global = None;

        for action in &actions.0 {
            match action {
                GenericAction::Let(_, _, _) => {
                    unsupported.get_or_insert_with(|| {
                        "top-level let reached source execution without global lowering".into()
                    });
                }
                GenericAction::Set(_, function, keys, value) => {
                    for key in keys {
                        self.visit_source_capture_expr(
                            catalog,
                            key,
                            &mut dependencies,
                            &mut unsupported,
                        );
                    }
                    self.visit_source_capture_expr(
                        catalog,
                        value,
                        &mut dependencies,
                        &mut unsupported,
                    );
                    if let ResolvedCall::Func(function) = function
                        && keys.is_empty()
                        && self
                            .functions
                            .get(&function.name)
                            .is_some_and(|entry| entry.decl.internal_let)
                    {
                        produced_global = Some(function.name.clone());
                    }
                }
                GenericAction::Change(_, change, _, keys) => {
                    for key in keys {
                        self.visit_source_capture_expr(
                            catalog,
                            key,
                            &mut dependencies,
                            &mut unsupported,
                        );
                    }
                    unsupported.get_or_insert_with(|| {
                        format!("top-level source `{change:?}` is not replayable")
                    });
                }
                GenericAction::Union(_, left, right) => {
                    let defined_global = match left {
                        GenericExpr::Call(_, ResolvedCall::Func(function), children)
                            if children.is_empty()
                                && self
                                    .functions
                                    .get(&function.name)
                                    .is_some_and(|entry| entry.decl.internal_let) =>
                        {
                            Some(function.name.clone())
                        }
                        _ => None,
                    };
                    if let Some(global) = defined_global {
                        produced_global = Some(global);
                    } else {
                        self.visit_source_capture_expr(
                            catalog,
                            left,
                            &mut dependencies,
                            &mut unsupported,
                        );
                    }
                    self.visit_source_capture_expr(
                        catalog,
                        right,
                        &mut dependencies,
                        &mut unsupported,
                    );
                }
                GenericAction::Panic(_, _) => {}
                GenericAction::Expr(_, expr) => self.visit_source_capture_expr(
                    catalog,
                    expr,
                    &mut dependencies,
                    &mut unsupported,
                ),
            }
        }

        SourceCaptureAnalysis {
            dependencies: dependencies.into_iter().collect(),
            produced_global,
            unsupported,
        }
    }

    fn eval_actions(&mut self, actions: &ResolvedActions) -> Result<(), Error> {
        let source_analysis = self
            .capture_catalog
            .as_ref()
            .map(|_| self.analyze_source_capture(actions));
        let mut binding = IndexSet::default();
        let mut ctx = CoreActionContext::new(
            &self.type_info,
            &mut binding,
            &mut self.parser.symbol_gen,
            self.proof_state.original_typechecking.is_none(),
        );
        let (actions, _) = actions.to_core_actions(&mut ctx)?;
        if let Some(catalog) = self.capture_catalog.as_mut() {
            catalog.register_action_primitives(&actions);
        }

        let source_capture = self
            .capture_catalog
            .as_mut()
            .map(CaptureCatalog::next_source);
        let mut translator = BackendRule::new(
            &mut *self.backend,
            &self.functions,
            &self.type_info,
            self.capture_catalog.as_ref(),
            &mut self.unstable_fn_panic_ids,
            true, // global action: Read/Full contexts (may read the DB)
        );
        translator.source_capture = source_capture.clone();
        translator.actions(&actions)?;
        let id = translator.try_build("eval_actions", false, false, Span::Panic)?;
        let result = self.backend.run_rules(RuleSetRun {
            name: None,
            rules: &[id],
        });
        let finalize = (result.is_ok() && self.capture_catalog.is_some())
            .then(|| self.backend.finalize_trace_wave())
            .transpose();
        self.backend.free_rule(id);
        finalize.map_err(|error| Error::BackendError(error.to_string()))?;

        match result {
            Ok(_) => {
                if let (Some(source), Some(analysis)) = (source_capture, source_analysis) {
                    self.capture_catalog
                        .as_mut()
                        .expect("source capture lost the capture catalog")
                        .register_source(source, analysis);
                }
                Ok(())
            }
            Err(e) => Err(Error::BackendError(e.to_string())),
        }
    }

    /// Get the list of all functions in the e-graph.
    pub fn get_function_names(&self) -> Vec<String> {
        self.functions.keys().cloned().collect()
    }

    /// Iterate over every `(name, function)` pair registered in the
    /// e-graph, in registration order.
    pub fn functions_iter(&self) -> impl Iterator<Item = (&String, &Function)> {
        self.functions.iter()
    }

    /// Run a read-only closure against the e-graph. The closure receives
    /// a [`ReadState`], so it can read but not write. Because this
    /// borrows `&self`, the closure and its callbacks may also call other
    /// `&self` methods such as [`EGraph::value_to_base`].
    ///
    /// # Panics
    ///
    /// Panics if the selected backend does not provide an action registry.
    /// Use the fallible top-level table iteration methods for backend-generic
    /// reads.
    pub fn read<R>(&self, f: impl FnOnce(ReadState<'_, '_>) -> R) -> R {
        let registry = self
            .backend
            .action_registry()
            .cloned()
            .expect("EGraph::read requires a backend action registry");
        let guard = registry.read().unwrap();
        self.backend
            .with_execution_state_tracked(|es| f(ReadState::wrap(es, &guard, Context::Read)))
            .0
    }

    /// Call `f` on each [`FunctionEntry`] of a function table. Top-level
    /// form of [`Read::function_entries`]; errors if `name` is a
    /// constructor or unregistered.
    pub fn function_entries(
        &self,
        name: &str,
        mut f: impl FnMut(FunctionEntry<'_>),
    ) -> Result<(), Error> {
        self.function_entries_while(name, |entry| {
            f(entry);
            true
        })
    }

    /// Like [`EGraph::function_entries`], but stops when `f` returns `false`.
    pub fn function_entries_while(
        &self,
        name: &str,
        mut f: impl FnMut(FunctionEntry<'_>) -> bool,
    ) -> Result<(), Error> {
        let function =
            self.functions
                .get(name)
                .ok_or_else(|| crate::api::ApiError::MissingTable {
                    name: name.to_owned(),
                })?;
        // An internal term relation (under term encoding) has `Custom` subtype but
        // is not a user-facing function table — it reads as enodes via
        // `constructor_enodes`, so reject it here.
        if function.subtype() != FunctionSubtype::Custom || function.is_relation_term() {
            return Err(crate::api::ApiError::WrongSubtype {
                name: name.to_owned(),
                expected: "function",
                actual: "constructor",
            }
            .into());
        }
        if function.schema.outputs.len() != 1 {
            return Err(crate::api::ApiError::TupleOutputUnsupported {
                name: name.to_owned(),
                method: "function_entries",
            }
            .into());
        }
        self.backend.for_each_while(function.backend_id, |row| {
            let (output, inputs) = row
                .vals
                .split_last()
                .expect("function row has at least an output column");
            f(FunctionEntry {
                inputs,
                output: *output,
                subsumed: row.subsumed,
            })
        });
        Ok(())
    }

    /// Call `f` on each [`Enode`] of a constructor / relation table.
    /// Top-level form of [`Read::constructor_enodes`]; errors if `name`
    /// is a function or unregistered.
    pub fn constructor_enodes(
        &self,
        name: &str,
        mut f: impl FnMut(Enode<'_>),
    ) -> Result<(), Error> {
        self.constructor_enodes_while(name, |enode| {
            f(enode);
            true
        })
    }

    /// Like [`EGraph::constructor_enodes`], but stops when `f` returns `false`.
    pub fn constructor_enodes_while(
        &self,
        name: &str,
        mut f: impl FnMut(Enode<'_>) -> bool,
    ) -> Result<(), Error> {
        let function =
            self.functions
                .get(name)
                .ok_or_else(|| crate::api::ApiError::MissingTable {
                    name: name.to_owned(),
                })?;
        // A real constructor, or (under term encoding) an internal term relation,
        // reads as enodes. The eclass id is the row's output column for a real
        // constructor, or the last input column for a term relation (whose trailing
        // `Unit` output is then ignored) — `extraction_output_index` picks the right
        // one and `extraction_num_children` the matching children count.
        if function.subtype() != FunctionSubtype::Constructor && !function.is_relation_term() {
            return Err(crate::api::ApiError::WrongSubtype {
                name: name.to_owned(),
                expected: "constructor",
                actual: "function",
            }
            .into());
        }
        let num_children = function.extraction_num_children();
        let eclass_idx = function.extraction_output_index();
        self.backend.for_each_while(function.backend_id, |row| {
            f(Enode {
                children: &row.vals[..num_children],
                eclass: row.vals[eclass_idx],
                subsumed: row.subsumed,
            })
        });
        Ok(())
    }

    /// Remove every row from the named function in bulk.
    ///
    /// This is intended as a faster alternative to issuing a `(delete …)` for
    /// every row of the function: it drops the backing row storage in
    /// O(1)-in-row-count time, rather than O(n) per-row teardown. Any pending
    /// staged inserts/removes for this function are dropped as part of the
    /// clear, so callers that have staged updates they want to land first
    /// should arrange for those to be flushed beforehand.
    ///
    /// Cached indexes and subsets that reference this table are invalidated by
    /// a generation bump and are lazily rebuilt against the now-empty table on
    /// next access.
    ///
    /// Raises an error if the function does not exist.
    pub fn clear_function(&mut self, func_name: &str) -> Result<(), Error> {
        if self.capture_catalog.is_some() {
            return Err(Error::BackendError(
                "trace capture does not support EGraph::clear_function".into(),
            ));
        }
        let backend_id = self
            .functions
            .get(func_name)
            .ok_or_else(|| TypeError::UnboundFunction(func_name.to_string(), span!()))?
            .backend_id;
        self.backend.clear_table(backend_id);
        Ok(())
    }

    /// Evaluates an expression, returns the sort of the expression and the evaluation result.
    pub fn eval_expr(&mut self, expr: &Expr) -> Result<(ArcSort, Value), Error> {
        if self.capture_catalog.is_some() {
            return Err(Error::BackendError(
                "trace capture does not support EGraph::eval_expr".into(),
            ));
        }
        let span = expr.span();
        let command = Command::Action(Action::Expr(span.clone(), expr.clone()));
        let resolved = self.resolve_command(command)?;
        if self.are_proofs_enabled() {
            self.proof_check_program
                .extend(resolved.desugared_before_proofs);
        }
        let resolved_commands = resolved.desugared;

        assert_eq!(resolved_commands.len(), 1);
        let resolved_command = resolved_commands.into_iter().next().unwrap();
        let resolved_expr = match resolved_command {
            ResolvedNCommand::CoreAction(ResolvedAction::Expr(_, resolved_expr)) => resolved_expr,
            _ => unreachable!(),
        };
        let sort = resolved_expr.output_type();
        let value = self.eval_resolved_expr(span, &resolved_expr)?;
        Ok((sort, value))
    }

    /// Typecheck an expression under explicit local bindings, an expected
    /// output sort, and a primitive call context.
    ///
    /// `bindings` contains the local variables in scope while resolving `expr`.
    /// Each tuple is `(name, span, sort)`, where `span` is used for diagnostics
    /// tied to that binding. `output_sort` constrains overload resolution and
    /// output-type inference for the expression. Global references are rewritten
    /// into the same zero-argument function calls used during command execution.
    /// `context` should match the runtime context where the resolved expression
    /// will be evaluated.
    pub fn typecheck_expr_with_bindings_and_output(
        &mut self,
        expr: &Expr,
        bindings: &[(String, Span, ArcSort)],
        output_sort: ArcSort,
        context: Context,
    ) -> Result<ResolvedExpr, TypeError> {
        let mut binding_map = IndexMap::default();
        binding_map.reserve(bindings.len());
        for (name, span, sort) in bindings {
            if binding_map
                .insert(name.as_str(), (span.clone(), sort.clone()))
                .is_some()
            {
                return Err(TypeError::AlreadyDefined(name.clone(), span.clone()));
            }
        }
        let resolved = self.type_info.typecheck_expr_with_output(
            &mut self.parser.symbol_gen,
            expr,
            &binding_map,
            output_sort,
            context,
        )?;
        Ok(remove_globals::remove_globals_expr(resolved))
    }

    /// Replace literal `(unstable-fn "...")` targets with hidden evaluator bindings.
    ///
    /// The returned expression must be evaluated with the returned bindings in
    /// scope before any caller-supplied local bindings. This lets direct
    /// execution-state evaluation use the same hidden `ResolvedFunction` value
    /// that backend rule lowering injects for `unstable-fn`.
    ///
    /// For example, a resolved body like `(unstable-app (unstable-fn "f") _0)`
    /// cannot evaluate the string literal `"f"` directly. This helper replaces
    /// the `(unstable-fn "f")` sub-expression with a fresh hidden variable and
    /// returns a binding from that variable to the prepared function value.
    pub fn prepare_unstable_fn_targets_for_eval(
        &mut self,
        expr: &ResolvedExpr,
    ) -> Result<(ResolvedExpr, Vec<(String, Value)>), Error> {
        let mut bindings = Vec::new();
        let mut pending = HashMap::default();
        match self.prepare_unstable_fn_targets_for_eval_inner(expr, &mut bindings, &mut pending) {
            Ok(expr) => {
                commit_unstable_fn_panics(&mut self.unstable_fn_panic_ids, &mut pending);
                Ok((expr, bindings))
            }
            Err(error) => {
                free_pending_unstable_fn_panics(&mut *self.backend, &mut pending);
                Err(error)
            }
        }
    }

    fn prepare_unstable_fn_targets_for_eval_inner(
        &mut self,
        expr: &ResolvedExpr,
        bindings: &mut Vec<(String, Value)>,
        pending: &mut HashMap<String, ExternalFunctionId>,
    ) -> Result<ResolvedExpr, Error> {
        match expr {
            ResolvedExpr::Lit(..) | ResolvedExpr::Var(..) => Ok(expr.clone()),
            ResolvedExpr::Call(span, resolved_call, children) => {
                if let ResolvedCall::Primitive(prim) = resolved_call
                    && prim.name() == "unstable-fn"
                {
                    let Some(ResolvedExpr::Lit(target_span, Literal::String(name))) =
                        children.first()
                    else {
                        return Err(Error::BackendError(format!(
                            "{}\nunstable-fn requires a literal string function name",
                            children
                                .first()
                                .map(ResolvedExpr::span)
                                .unwrap_or_else(|| Span::Panic)
                        )));
                    };
                    if !self.backend.as_any().is::<egglog_bridge::EGraph>() {
                        return Err(Error::BackendError(
                            "`unstable-fn` is only supported on the reference bridge backend"
                                .into(),
                        ));
                    }
                    let panic_id = get_or_register_unstable_fn_panic(
                        &mut *self.backend,
                        &self.unstable_fn_panic_ids,
                        pending,
                        name,
                    );
                    let resolved_function = {
                        let bridge = self
                            .backend
                            .as_any()
                            .downcast_ref::<egglog_bridge::EGraph>()
                            .ok_or_else(|| {
                                Error::BackendError(
                                    "`unstable-fn` is only supported on the reference bridge backend"
                                        .into(),
                                )
                            })?;
                        resolve_function_container_target_with_context(
                            bridge,
                            &self.functions,
                            &self.type_info,
                            name,
                            prim,
                            panic_id,
                        )
                    };
                    let resolved_function = resolved_function?;
                    let fn_value = self.backend.base_values().get(resolved_function);
                    let binding_name = self.parser.symbol_gen.fresh("unstable_fn_target");
                    bindings.push((binding_name.clone(), fn_value));
                    let mut prepared_children = Vec::with_capacity(children.len());
                    prepared_children.push(ResolvedExpr::Var(
                        target_span.clone(),
                        ResolvedVar {
                            name: binding_name,
                            sort: children[0].output_type(),
                            is_global_ref: false,
                        },
                    ));
                    for child in &children[1..] {
                        prepared_children.push(self.prepare_unstable_fn_targets_for_eval_inner(
                            child, bindings, pending,
                        )?);
                    }
                    return Ok(ResolvedExpr::Call(
                        span.clone(),
                        resolved_call.clone(),
                        prepared_children,
                    ));
                }

                let prepared_children = children
                    .iter()
                    .map(|child| {
                        self.prepare_unstable_fn_targets_for_eval_inner(child, bindings, pending)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(ResolvedExpr::Call(
                    span.clone(),
                    resolved_call.clone(),
                    prepared_children,
                ))
            }
        }
    }

    fn eval_resolved_expr(&mut self, span: Span, expr: &ResolvedExpr) -> Result<Value, Error> {
        let unit_id = self.backend.base_values().get_ty::<()>();
        let unit_val = self.backend.base_values().get(());

        let result: egglog_bridge::SideChannel<Value> = Default::default();
        let result_ref = result.clone();
        let ext_id = self
            .backend
            .register_external_func(Box::new(make_external_func(move |_es, vals| {
                debug_assert!(vals.len() == 1);
                *result_ref.lock().unwrap() = Some(vals[0]);
                Some(unit_val)
            })));

        let mut translator = BackendRule::new(
            &mut *self.backend,
            &self.functions,
            &self.type_info,
            self.capture_catalog.as_ref(),
            &mut self.unstable_fn_panic_ids,
            true, // global action: Read/Full contexts (may read the DB)
        );
        translator.rollback_external_funcs.push(ext_id);

        let result_var = ResolvedVar {
            name: self.parser.symbol_gen.fresh("eval_resolved_expr"),
            sort: expr.output_type(),
            is_global_ref: false,
        };
        let actions = ResolvedActions::singleton(ResolvedAction::Let(
            span.clone(),
            result_var.clone(),
            expr.clone(),
        ));
        let mut binding = IndexSet::default();
        let mut ctx = CoreActionContext::new(
            &self.type_info,
            &mut binding,
            &mut self.parser.symbol_gen,
            self.proof_state.original_typechecking.is_none(),
        );
        let actions = actions.to_core_actions(&mut ctx)?.0;
        translator.actions(&actions)?;

        let arg = translator.entry(&ResolvedAtomTerm::Var(span.clone(), result_var))?;
        translator.call_external_func(
            span.clone(),
            ext_id,
            "eval_resolved_expr_result",
            vec![arg],
            egglog_bridge::ColumnTy::Base(unit_id),
        );

        let id = translator.try_build("eval_resolved_expr", false, false, span)?;
        let rule_result = self.backend.run_rules(RuleSetRun {
            name: None,
            rules: &[id],
        });
        self.backend.free_rule(id);
        let _ = rule_result.map_err(|e| {
            Error::BackendError(format!("Failed to evaluate expression '{expr}': {e}"))
        })?;

        let result = result.lock().unwrap().unwrap();
        Ok(result)
    }

    fn checked_alias_error(span: &Span, alias: &str, reason: impl Into<String>) -> Error {
        Error::CheckedAlias {
            alias: alias.to_owned(),
            reason: reason.into(),
            span: span.clone(),
        }
    }

    fn canonical_checked_value(&self, sort: &ArcSort, value: Value) -> Value {
        let value = self
            .backend
            .get_canon_repr(value, sort.column_ty(self.backend.base_values()));
        // Proof mode represents source EqSort equality in the existing
        // explicit `UF_<Sort>` table. Reuse the same canonicalization helper
        // as extraction; rebuilding guarantees its lookup is one hop.
        crate::extract::find_canonical(self, value, sort)
    }

    /// Evaluate the deliberately closed `let-check` expression subset. This is
    /// intentionally separate from `eval_resolved_expr`: the ordinary evaluator
    /// compiles a global action and gives constructors lookup-or-insert semantics.
    fn eval_checked_expr(&self, alias_name: &str, expr: &ResolvedExpr) -> Result<Value, Error> {
        match expr {
            ResolvedExpr::Lit(_, literal) => {
                Ok(literal_to_value(self.backend.base_values(), literal))
            }
            ResolvedExpr::Var(span, variable) => {
                if variable.is_global_ref {
                    return Err(Self::checked_alias_error(
                        span,
                        alias_name,
                        format!("global `{}` is not a checked alias", variable.name),
                    ));
                }
                let checked = self.checked_aliases.get(&variable.name).ok_or_else(|| {
                    Self::checked_alias_error(
                        span,
                        alias_name,
                        format!("checked alias `{}` is unavailable", variable.name),
                    )
                })?;
                let checked_type =
                    self.checked_alias_types
                        .get(&variable.name)
                        .ok_or_else(|| {
                            Self::checked_alias_error(
                                span,
                                alias_name,
                                format!("checked alias `{}` has no type", variable.name),
                            )
                        })?;
                if checked_type.sort.name() != variable.sort.name() {
                    return Err(Self::checked_alias_error(
                        span,
                        alias_name,
                        format!(
                            "checked alias `{}` has runtime sort `{}` but expression expects `{}`",
                            variable.name,
                            checked_type.sort.name(),
                            variable.sort.name()
                        ),
                    ));
                }
                Ok(self.canonical_checked_value(&checked_type.sort, checked.value))
            }
            ResolvedExpr::Call(span, ResolvedCall::Values(_), _) => Err(Self::checked_alias_error(
                span,
                alias_name,
                "tuple values are not supported",
            )),
            ResolvedExpr::Call(span, ResolvedCall::Func(function), children) => {
                if function.subtype != FunctionSubtype::Constructor
                    || function.outputs.len() != 1
                    || !function.output().is_eq_sort()
                {
                    return Err(Self::checked_alias_error(
                        span,
                        alias_name,
                        format!(
                            "function `{}` is not a single-output EqSort constructor",
                            function.name
                        ),
                    ));
                }
                let mut arguments = children
                    .iter()
                    .map(|child| self.eval_checked_expr(alias_name, child))
                    .collect::<Result<Vec<_>, _>>()?;
                for (argument, sort) in arguments.iter_mut().zip(&function.input) {
                    *argument = self.canonical_checked_value(sort, *argument);
                }

                // Under term/proof encoding (including a serialized desugared
                // program replayed in a plain graph), the original constructor
                // name is the term relation.  Prefer the FD view whose
                // `term_constructor` points back to the source constructor; its
                // lookup is read-only and returns the existing e-class.
                let encoded_term_node = self.functions.get(&function.name).filter(|candidate| {
                    candidate.decl.internal_term_node
                        && candidate.schema.input.len() == function.input.len() + 1
                        && candidate
                            .schema
                            .input
                            .iter()
                            .zip(&function.input)
                            .all(|(left, right)| left.name() == right.name())
                        && candidate.schema.input.last().unwrap().name() == function.output().name()
                        && candidate.schema.outputs.len() == 1
                        && candidate.schema.output().name() == UnitSort.name()
                });
                let mut encoded_views = self.functions.values().filter(|candidate| {
                    encoded_term_node.is_some()
                        && candidate.decl.subtype == FunctionSubtype::Custom
                        && !candidate.decl.internal_let
                        && !candidate.decl.internal_term_node
                        && candidate.decl.identity_vals == Some(1)
                        && candidate.decl.term_constructor.as_deref()
                            == Some(function.name.as_str())
                        && candidate.schema.input.len() == function.input.len()
                        && candidate.schema.outputs.len() == 2
                        && candidate
                            .schema
                            .input
                            .iter()
                            .zip(&function.input)
                            .all(|(left, right)| left.name() == right.name())
                        && candidate.schema.output().name() == function.output().name()
                });
                let encoded_view = encoded_views.next();
                if encoded_views.next().is_some() {
                    return Err(Self::checked_alias_error(
                        span,
                        alias_name,
                        format!(
                            "constructor `{}` has more than one readable FD view",
                            function.name
                        ),
                    ));
                }
                let entry = encoded_view
                    .or_else(|| {
                        encoded_term_node
                            .is_none()
                            .then(|| self.functions.get(&function.name))
                            .flatten()
                    })
                    .ok_or_else(|| {
                        Self::checked_alias_error(
                            span,
                            alias_name,
                            format!("constructor `{}` has no readable table", function.name),
                        )
                    })?;
                let value = self
                    .backend
                    .lookup_id(entry.backend_id, &arguments)
                    .ok_or_else(|| {
                        Self::checked_alias_error(
                            span,
                            alias_name,
                            format!("lookup of constructor `{}` failed", function.name),
                        )
                    })?;
                Ok(self.canonical_checked_value(function.output(), value))
            }
            ResolvedExpr::Call(span, ResolvedCall::Primitive(primitive), children) => {
                if !primitive.is_pure() || primitive.validator().is_none() {
                    return Err(Self::checked_alias_error(
                        span,
                        alias_name,
                        format!(
                            "primitive `{}` is not replay-safe and pure",
                            primitive.name()
                        ),
                    ));
                }
                if primitive.output().is_container_sort()
                    && !self
                        .type_info
                        .checked_alias_container_sorts
                        .contains(primitive.output().name())
                {
                    return Err(Self::checked_alias_error(
                        span,
                        alias_name,
                        format!(
                            "primitive `{}` returns unsupported container sort `{}`",
                            primitive.name(),
                            primitive.output().name()
                        ),
                    ));
                }
                let mut arguments = children
                    .iter()
                    .map(|child| self.eval_checked_expr(alias_name, child))
                    .collect::<Result<Vec<_>, _>>()?;
                for (argument, sort) in arguments.iter_mut().zip(primitive.input()) {
                    *argument = self.canonical_checked_value(sort, *argument);
                }
                let external = primitive.external_id(Context::Pure);
                let (value, mutated) = self.backend.with_execution_state_tracked(|state| {
                    state.call_external_func(external, &arguments)
                });
                if mutated {
                    return Err(Self::checked_alias_error(
                        span,
                        alias_name,
                        format!(
                            "primitive `{}` staged a database mutation",
                            primitive.name()
                        ),
                    ));
                }
                let value = value.ok_or_else(|| {
                    Self::checked_alias_error(
                        span,
                        alias_name,
                        format!("primitive `{}` failed", primitive.name()),
                    )
                })?;
                Ok(self.canonical_checked_value(primitive.output(), value))
            }
        }
    }

    /// Publish only the static half of a checked alias while resolving a
    /// program without executing it (notably the source program retained for
    /// proof checking). Runtime `Value`s are intentionally never synthesized
    /// or copied by this path.
    fn record_checked_alias_type_only(
        &mut self,
        span: &Span,
        name: &ResolvedVar,
        expr: &ResolvedExpr,
    ) -> Result<(), Error> {
        if let Some(previous) = self.checked_alias_types.get(&name.name) {
            return Err(TypeError::CheckedAliasAlreadyBound {
                name: name.name.clone(),
                first: previous.declaration_span.clone(),
                duplicate: span.clone(),
            }
            .into());
        }
        self.names.check_checked_alias_available(&name.name, span)?;
        self.checked_alias_types.insert(
            name.name.clone(),
            CheckedAliasType {
                declaration_span: span.clone(),
                sort: name.sort.clone(),
                closed_expr: typechecking::expand_checked_alias_expr(
                    &expr.clone().make_unresolved(),
                    &self.checked_alias_types,
                ),
            },
        );
        self.names.record_checked_alias(&name.name, span);
        Ok(())
    }

    fn add_combined_ruleset(&mut self, name: String, rulesets: Vec<String>) {
        match self.rulesets.entry(name.clone()) {
            Entry::Occupied(_) => panic!("Ruleset '{name}' was already present"),
            Entry::Vacant(e) => e.insert(Ruleset::Combined(rulesets)),
        };
    }

    fn add_ruleset(&mut self, name: String) {
        match self.rulesets.entry(name.clone()) {
            Entry::Occupied(_) => panic!("Ruleset '{name}' was already present"),
            Entry::Vacant(e) => e.insert(Ruleset::Rules(Default::default())),
        };
    }

    fn check_facts(
        &mut self,
        span: &Span,
        facts: &[ResolvedFact],
        record_criterion: bool,
    ) -> Result<(), Error> {
        let criterion_capture = record_criterion
            .then(|| {
                self.capture_catalog
                    .as_mut()
                    .map(CaptureCatalog::next_check)
            })
            .flatten();
        let mut checked_variables = IndexMap::<String, (Span, ResolvedVar)>::default();
        for fact in facts {
            fact.visit_vars(&mut |variable_span, variable| {
                if !variable.is_global_ref && self.checked_alias_types.contains_key(&variable.name)
                {
                    checked_variables
                        .entry(variable.name.clone())
                        .or_insert_with(|| (variable_span.clone(), variable.clone()));
                }
            });
        }
        let checked_constants = checked_variables
            .into_values()
            .map(|(variable_span, variable)| {
                let checked = self.checked_aliases.get(&variable.name).ok_or_else(|| {
                    Self::checked_alias_error(
                        &variable_span,
                        &variable.name,
                        "checked alias has no published runtime value",
                    )
                })?;
                let value = self.canonical_checked_value(&variable.sort, checked.value);
                Ok((variable, value))
            })
            .collect::<Result<Vec<_>, Error>>()?;
        let checked_variables = checked_constants
            .iter()
            .map(|(variable, _)| variable.clone())
            .collect::<HashSet<_>>();
        let fresh_name = self.parser.symbol_gen.fresh("check_facts");
        let fresh_ruleset = self.parser.symbol_gen.fresh("check_facts_ruleset");
        let rule = ast::ResolvedRule {
            span: span.clone(),
            head: ResolvedActions::default(),
            body: facts.to_vec(),
            name: fresh_name.clone(),
            ruleset: fresh_ruleset.clone(),
            eval_mode: RuleEvalMode::default(),
            no_decomp: false,
            include_subsumed: false,
        };
        let canonicalized = if criterion_capture.is_some() {
            Some(rule.to_canonicalized_check_rule(&self.type_info, &mut self.parser.symbol_gen)?)
        } else {
            None
        };
        let (query, check_equalities) = if let Some(canonicalized) = canonicalized {
            (canonicalized.core.body, canonicalized.equalities)
        } else {
            (
                rule.to_canonicalized_core_rule_with_constants(
                    &self.type_info,
                    &mut self.parser.symbol_gen,
                    self.proof_state.original_typechecking.is_none(),
                    &checked_variables,
                )?
                .core
                .body,
                Vec::new().into_boxed_slice(),
            )
        };
        let criterion_equalities = if criterion_capture.is_some() {
            let catalog = self
                .capture_catalog
                .as_ref()
                .expect("a criterion requires an active capture catalog");
            let premise = |source: &core::CheckPremise| -> Result<CriterionCapturePremise, Error> {
                let atom = query.atoms.get(source.body_atom).ok_or_else(|| {
                    Error::BackendError(format!(
                        "criterion endpoint cites missing body atom {}",
                        source.body_atom
                    ))
                })?;
                let ResolvedCall::Func(function) = &atom.head else {
                    return Err(Error::BackendError(format!(
                        "{}: criterion endpoint producer is not a function",
                        atom.span
                    )));
                };
                let constructor = catalog.constructor_term_spec(function);
                if function.subtype == FunctionSubtype::Constructor && constructor.is_none() {
                    return Err(Error::BackendError(format!(
                        "{}: criterion endpoint constructor has no registered replay identity",
                        atom.span
                    )));
                }
                if source.column + 1 != atom.args.len() {
                    return Err(Error::BackendError(format!(
                        "{}: criterion endpoint does not cite the constructor output column",
                        atom.span
                    )));
                }
                Ok(CriterionCapturePremise {
                    body_atom: source.body_atom,
                    column: source.column,
                    constructor,
                })
            };
            check_equalities
                .iter()
                .map(|(left, right)| Ok((premise(left)?, premise(right)?)))
                .collect::<Result<Vec<_>, Error>>()?
        } else {
            Vec::new()
        };

        let ext_sc = egglog_bridge::SideChannel::default();
        let ext_sc_ref = ext_sc.clone();
        let ext_id = self
            .backend
            .register_external_func(Box::new(make_external_func(move |_, _| {
                *ext_sc_ref.lock().unwrap() = Some(());
                Some(Value::new_const(0))
            })));

        let mut translator = BackendRule::new(
            &mut *self.backend,
            &self.functions,
            &self.type_info,
            self.capture_catalog.as_ref(),
            &mut self.unstable_fn_panic_ids,
            true, // global query: Read context (may read the DB)
        );
        for (variable, value) in &checked_constants {
            translator.bind_constant(variable, *value)?;
        }
        translator.rollback_external_funcs.push(ext_id);
        translator.query(&query, true)?;
        translator.call_external_func(
            span.clone(),
            ext_id,
            "check_facts_match",
            Vec::new(),
            egglog_bridge::ColumnTy::Id,
        );
        if let Some(check) = criterion_capture {
            translator.criterion_capture = Some(CriterionCaptureSpec {
                check,
                equalities: criterion_equalities.into_boxed_slice(),
            });
        }
        let id = translator.try_build("check_facts", false, false, span.clone())?;
        let run_result = self.backend.run_rules(RuleSetRun {
            name: None,
            rules: &[id],
        });
        self.backend.free_rule(id);
        run_result.map_err(|e| Error::BackendError(e.to_string()))?;
        self.finalize_trace_wave()?;

        let ext_sc_val = ext_sc.lock().unwrap().take();
        let matched = matches!(ext_sc_val, Some(()));

        if !matched {
            Err(Error::CheckError(
                facts.iter().map(|f| f.clone().make_unresolved()).collect(),
                span.clone(),
            ))
        } else {
            Ok(())
        }
    }

    fn run_command(&mut self, command: ResolvedNCommand) -> Result<Vec<CommandOutput>, Error> {
        match command {
            // Sorts are already declared during typechecking
            ResolvedNCommand::Sort {
                name,
                uf,
                proof_func,
                proof_constructors,
                ..
            } => {
                // Restore the sort's UF metadata into proof_state.
                if let Some((uf_ctor, _uf_index)) = uf {
                    self.proof_state
                        .uf_parent
                        .insert(name.clone(), uf_ctor.clone());
                }
                // If the sort has a :internal-proof-func field, store the mapping for proof lookup.
                // This annotation is set by proof instrumentation and consumed here.
                if let Some(proof_func_name) = proof_func {
                    self.proof_state
                        .proof_func_parent
                        .insert(name.clone(), proof_func_name);
                }
                // The Proof sort's :internal-proof-names records the global proof
                // constructors; restore them so container rebuild can recover them.
                if let Some(pc) = proof_constructors {
                    let names = &mut self.proof_state.proof_names;
                    names.proof_datatype = name.clone();
                    names.congr_constructor = pc.congr;
                    names.congr_all_constructor = pc.congr_all;
                    names.eq_trans_constructor = pc.trans;
                    names.eq_sym_constructor = pc.sym;
                    names.container_normalize_constructor = pc.normalize;
                    // Recovered so `native_input` can build `(input …)` base-fact
                    // proofs when replaying an encoded program in a fresh e-graph.
                    names.fiat_constructor = pc.fiat;
                }
                log::info!("Declared sort {name}.")
            }
            ResolvedNCommand::Function(fdecl) => {
                self.declare_function(&fdecl)?;
                log::info!("Declared {} {}.", fdecl.subtype, fdecl.name)
            }
            ResolvedNCommand::AddRuleset(_span, name) => {
                self.add_ruleset(name.clone());
                log::info!("Declared ruleset {name}.");
            }
            ResolvedNCommand::UnstableCombinedRuleset(_span, name, others) => {
                self.add_combined_ruleset(name.clone(), others);
                log::info!("Declared ruleset {name}.");
            }
            ResolvedNCommand::NormRule { rule } => {
                let name = rule.name.clone();
                self.add_rule(rule)?;
                log::info!("Declared rule {name}.")
            }
            ResolvedNCommand::RunSchedule(sched) => {
                let report = self.run_schedule(&sched)?;
                if let Some(catalog) = self.capture_catalog.as_mut() {
                    catalog.has_run = true;
                }
                log::info!("Ran schedule {sched}.");
                log::info!("Report: {report}");
                self.overall_run_report.union(report.clone());
                return Ok(vec![CommandOutput::RunSchedule(report)]);
            }
            ResolvedNCommand::PrintOverallStatistics(span, file) => match file {
                None => {
                    log::info!("Printed overall statistics");
                    return Ok(vec![CommandOutput::OverallStatistics(
                        self.overall_run_report.clone(),
                    )]);
                }
                Some(path) => {
                    let mut file = std::fs::File::create(&path)
                        .map_err(|e| Error::IoError(path.clone().into(), e, span.clone()))?;
                    log::info!("Printed overall statistics to json file {path}");

                    serde_json::to_writer(&mut file, &self.overall_run_report)
                        .expect("error serializing to json");
                }
            },
            ResolvedNCommand::Check(span, facts) => {
                self.check_facts(&span, &facts, true)?;
                log::info!("Checked fact {facts:?}.");
            }
            ResolvedNCommand::LetCheck {
                span,
                name,
                expr,
                expected_sort: _,
            } => {
                if self.capture_catalog.is_some() {
                    return Err(Self::checked_alias_error(
                        &span,
                        &name.name,
                        "checked aliases are replay-only and cannot be recorded as trace sources",
                    ));
                }
                if self.checked_aliases.contains_key(&name.name) {
                    let first = self.checked_alias_types[&name.name]
                        .declaration_span
                        .clone();
                    return Err(TypeError::CheckedAliasAlreadyBound {
                        name: name.name,
                        first,
                        duplicate: span,
                    }
                    .into());
                }
                self.names
                    .check_checked_alias_available(&name.name, &span)?;
                let value = self.eval_checked_expr(&name.name, &expr)?;
                let value = self.canonical_checked_value(&name.sort, value);
                let closed_expr = typechecking::expand_checked_alias_expr(
                    &expr.make_unresolved(),
                    &self.checked_alias_types,
                );
                let alias = name.name.clone();
                self.checked_aliases
                    .insert(alias.clone(), CheckedAlias { value });
                self.checked_alias_types.insert(
                    alias.clone(),
                    CheckedAliasType {
                        declaration_span: span.clone(),
                        sort: name.sort,
                        closed_expr,
                    },
                );
                self.names.record_checked_alias(&alias, &span);
                log::info!("Checked replay alias {alias}.");
            }
            ResolvedNCommand::CoreAction(action) => match &action {
                ResolvedAction::Let(_, name, contents) => {
                    panic!("Globals should have been desugared away: {name} = {contents}")
                }
                _ => {
                    self.eval_actions(&ResolvedActions::new(vec![action.clone()]))?;
                }
            },
            // One `eval_actions` call, so the block's `let`s stay local.
            ResolvedNCommand::CoreActions(actions) => {
                self.eval_actions(&actions)?;
            }
            ResolvedNCommand::LetBegin(..) => {
                unreachable!("LetBegin is removed by remove_globals")
            }
            ResolvedNCommand::Extract(span, expr, variants) => {
                let sort = expr.output_type();

                let x = self.eval_resolved_expr(span.clone(), &expr)?;
                let n = self.eval_resolved_expr(span, &variants)?;
                let n: i64 = self.backend.base_values().unwrap(n);

                let mut termdag = TermDag::default();

                let extractor = Extractor::compute_costs_from_rootsorts(
                    Some(vec![sort]),
                    self,
                    TreeAdditiveCostModel::default(),
                );
                return if n == 0 {
                    if let Some((cost, term)) = extractor.extract_best(self, &mut termdag, x) {
                        // dont turn termdag into a string if we have messages disabled for performance reasons
                        if log_enabled!(Level::Info) {
                            log::info!("extracted with cost {cost}: {}", termdag.to_string(term));
                        }
                        Ok(vec![CommandOutput::ExtractBest(termdag, cost, term)])
                    } else {
                        Err(Error::ExtractError(
                            "Unable to find any valid extraction (likely due to subsume or delete)"
                                .to_string(),
                        ))
                    }
                } else {
                    if n < 0 {
                        panic!("Cannot extract negative number of variants");
                    }
                    let terms: Vec<TermId> = extractor
                        .extract_variants(self, &mut termdag, x, n as usize)
                        .iter()
                        .map(|e| e.1)
                        .collect();
                    if log_enabled!(Level::Info) {
                        let expr_str = expr.to_string();
                        log::info!("extracted {} variants for {expr_str}", terms.len());
                    }
                    Ok(vec![CommandOutput::ExtractVariants(termdag, terms)])
                };
            }
            ResolvedNCommand::Push(n) => {
                if self.capture_catalog.is_some() {
                    return Err(Error::BackendError(
                        "trace capture does not support push/pop state".into(),
                    ));
                }
                (0..n).for_each(|_| self.push());
                log::info!("Pushed {n} levels.")
            }
            ResolvedNCommand::Pop(span, n) => {
                if self.capture_catalog.is_some() {
                    return Err(Error::BackendError(
                        "trace capture does not support push/pop state".into(),
                    ));
                }
                for _ in 0..n {
                    self.pop().map_err(|err| {
                        if let Error::Pop(_) = err {
                            Error::Pop(span.clone())
                        } else {
                            err
                        }
                    })?;
                }
                log::info!("Popped {n} levels.")
            }
            ResolvedNCommand::PrintFunction(span, f, n, file, mode) => {
                let file = file
                    .map(|file| {
                        std::fs::File::create(&file)
                            .map_err(|e| Error::IoError(file.into(), e, span.clone()))
                    })
                    .transpose()?;
                return self
                    .print_function(&f, n, file, mode)
                    .map_err(|e| match e {
                        Error::TypeError(TypeError::UnboundFunction(f, _)) => {
                            Error::TypeError(TypeError::UnboundFunction(f, span.clone()))
                        }
                        // This case is currently impossible
                        _ => e,
                    })
                    .map(|opt| opt.into_iter().collect());
            }
            ResolvedNCommand::PrintSize(span, f) => {
                let res = self.print_size(f.as_deref()).map_err(|e| match e {
                    Error::TypeError(TypeError::UnboundFunction(f, _)) => {
                        Error::TypeError(TypeError::UnboundFunction(f, span.clone()))
                    }
                    // This case is currently impossible
                    _ => e,
                })?;
                return Ok(vec![res]);
            }
            ResolvedNCommand::Fail(span, cmds) => {
                if self.capture_catalog.is_some() {
                    return Err(Error::BackendError(
                        "trace capture does not support nested fail commands".into(),
                    ));
                }
                let mut any_failed = false;
                for c in cmds {
                    if let Err(e) = self.run_command(c) {
                        log::info!("Command failed as expected: {e}");
                        any_failed = true;
                        break;
                    }
                }
                if !any_failed {
                    return Err(Error::ExpectFail(span));
                }
            }
            ResolvedNCommand::Input { span, name, file } => {
                // An encoded program (term/proof mode, or a replayed desugared
                // program) keeps `(input …)` targeting the encoded *term relation*,
                // loaded natively into the encoded tables; a plain program targets a
                // user relation/constructor loaded by the relation loader.
                if self
                    .functions
                    .get(&name)
                    .is_some_and(|f| f.is_relation_term())
                {
                    self.native_input(span, &name, file)?;
                } else {
                    self.input_file(span, &name, file)?;
                }
            }
            ResolvedNCommand::Output { span, file, exprs } => {
                let mut filename = self.fact_directory.clone().unwrap_or_default();
                filename.push(file.as_str());
                // append to file
                let mut f = File::options()
                    .append(true)
                    .create(true)
                    .open(&filename)
                    .map_err(|e| Error::IoError(filename.clone(), e, span.clone()))?;

                let extractor = Extractor::compute_costs_from_rootsorts(
                    None,
                    self,
                    TreeAdditiveCostModel::default(),
                );
                let mut termdag: TermDag = Default::default();

                use std::io::Write;
                for expr in exprs {
                    let value = self.eval_resolved_expr(span.clone(), &expr)?;
                    let expr_type = expr.output_type();

                    let term = extractor
                        .extract_best_with_sort(self, &mut termdag, value, expr_type)
                        .unwrap()
                        .1;
                    writeln!(f, "{}", termdag.to_string(term))
                        .map_err(|e| Error::IoError(filename.clone(), e, span.clone()))?;
                }

                log::info!("Output to '{filename:?}'.")
            }
            ResolvedNCommand::UserDefined(_span, name, exprs) => {
                let command = self
                    .commands
                    .get(&name)
                    .ok_or_else(|| {
                        NotFoundError(format!("Unrecognized user-defined command: {name}"))
                    })?
                    .clone();
                if self.capture_catalog.is_some() {
                    let mut context = TraceScheduleContext { egraph: self };
                    return command
                        .update_trace(&mut context, &exprs)
                        .unwrap_or_else(|| {
                            Err(Error::BackendError(format!(
                                "trace capture does not support user-defined command `{name}`"
                            )))
                        });
                }
                return command.update(self, &exprs);
            }

            ResolvedNCommand::ProveExists(span, resolved_call) => {
                let mut instrument = ProofInstrumentor::new(self);
                let (proof_store, proof_id) =
                    instrument
                        .prove_exists(&resolved_call)
                        .map_err(|error| Error::ProofError {
                            span: span.clone(),
                            error,
                        })?;
                return Ok(vec![CommandOutput::ProveExists {
                    proof_store,
                    proof_id,
                }]);
            }
        };

        Ok(vec![])
    }

    fn read_input_file(
        fact_directory: Option<&std::path::Path>,
        function_type: &FuncType,
        span: &Span,
        file: &str,
        capture_digest: bool,
    ) -> Result<ParsedInputFile, Error> {
        let mut filename = fact_directory.map_or_else(PathBuf::new, PathBuf::from);
        filename.push(file);

        let row_schema = Self::input_row_schema(function_type);

        log::info!("Opening file '{filename:?}'...");
        let bytes = std::fs::read(&filename)
            .map_err(|error| Error::IoError(filename.clone(), error, span.clone()))?;
        let digest = capture_digest.then(|| {
            let digest: [u8; 32] = Sha256::digest(&bytes).into();
            digest
        });
        let contents = String::from_utf8(bytes).map_err(|error| {
            Error::IoError(
                filename.clone(),
                std::io::Error::new(std::io::ErrorKind::InvalidData, error),
                span.clone(),
            )
        })?;

        let mut rows = Vec::with_capacity(contents.lines().count());
        for (line_index, line) in contents.lines().enumerate() {
            if let Some(row) = Self::parse_input_line(
                &row_schema,
                file,
                u64::try_from(line_index + 1).expect("input file has too many lines"),
                line,
            )? {
                rows.push(row);
            }
        }
        Ok(ParsedInputFile {
            path: filename,
            digest,
            rows,
        })
    }

    fn input_row_schema(function_type: &FuncType) -> Vec<ArcSort> {
        for sort in &function_type.input {
            match sort.name() {
                "i64" | "f64" | "String" => {}
                name => panic!("Unsupported type {name} for input"),
            }
        }
        if function_type.subtype != FunctionSubtype::Constructor {
            for sort in &function_type.outputs {
                match sort.name() {
                    "i64" | "String" | "Unit" => {}
                    name => panic!("Unsupported type {name} for input"),
                }
            }
        }

        let mut row_schema = function_type.input.clone();
        // Relations desugar to constructors, so their implicit output is not a TSV column.
        if function_type.subtype == FunctionSubtype::Custom {
            row_schema.extend(function_type.outputs.iter().cloned());
        }

        row_schema
    }

    fn parse_input_line(
        row_schema: &[ArcSort],
        file: &str,
        line_number: u64,
        line: &str,
    ) -> Result<Option<ParsedInputRow>, Error> {
        let mut fields = line.split('\t').map(str::trim);
        let mut row = Vec::with_capacity(row_schema.len());
        for sort in row_schema {
            if sort.name() == "Unit" {
                row.push(Literal::Unit);
                continue;
            }
            let Some(raw) = fields.next() else {
                break;
            };
            let literal = match sort.name() {
                "i64" => raw
                    .parse()
                    .map(Literal::Int)
                    .map_err(|_| Error::InputFileFormatError(file.to_owned()))?,
                "f64" => raw
                    .parse::<f64>()
                    .map(ordered_float::OrderedFloat)
                    .map(Literal::Float)
                    .map_err(|_| Error::InputFileFormatError(file.to_owned()))?,
                "String" => Literal::String(raw.to_owned()),
                _ => unreachable!(),
            };
            row.push(literal);
        }
        if row.is_empty() {
            return Ok(None);
        }
        if row.len() != row_schema.len() || fields.next().is_some() {
            return Err(Error::InputFileFormatError(file.to_owned()));
        }
        Ok(Some(ParsedInputRow {
            line: line_number,
            literals: row,
        }))
    }

    /// Read a TSV `file` into literal rows matching `row_schema` (one column per
    /// sort). A `Unit` column contributes `Literal::Unit` without consuming a
    /// field; `i64`/`f64`/`String` columns are parsed from the next field.
    fn read_input_rows(
        fact_directory: Option<&std::path::Path>,
        row_schema: &[ArcSort],
        span: &Span,
        file: &str,
    ) -> Result<Vec<Vec<Literal>>, Error> {
        let mut filename = fact_directory.map_or_else(PathBuf::new, PathBuf::from);
        filename.push(file);

        log::info!("Opening file '{filename:?}'...");
        let contents = std::fs::read_to_string(&filename)
            .map_err(|error| Error::IoError(filename, error, span.clone()))?;

        let mut rows = Vec::with_capacity(contents.lines().count());
        for (line_index, line) in contents.lines().enumerate() {
            if let Some(row) = Self::parse_input_line(
                row_schema,
                file,
                u64::try_from(line_index + 1).expect("input file has too many lines"),
                line,
            )? {
                rows.push(row.literals);
            }
        }
        Ok(rows)
    }

    fn input_file(&mut self, span: Span, func_name: &str, file: String) -> Result<(), Error> {
        let function_type = self
            .type_info
            .get_func_type(func_name)
            .unwrap_or_else(|| panic!("Unrecognized function name {func_name}"))
            .clone();
        let parsed_file = Self::read_input_file(
            self.fact_directory.as_deref(),
            &function_type,
            &span,
            &file,
            self.capture_catalog.is_some(),
        )?;
        let resolved_input_path = if parsed_file.path.is_absolute() {
            parsed_file.path.clone()
        } else {
            std::env::current_dir()
                .map_err(|error| Error::IoError(parsed_file.path.clone(), error, span.clone()))?
                .join(&parsed_file.path)
        };
        let backend_id = self.functions[func_name].backend_id;
        let unit_val = self.backend.base_values().get(());
        let pending_input_catalog = self.capture_catalog.as_mut().map(|catalog| {
            let source_ordinal = catalog.next_source_ordinal();
            let command = catalog
                .active_command
                .expect("input capture requires an active catalog command")
                .command;
            (
                source_ordinal,
                InputCatalogEntry {
                    command,
                    function: func_name.to_owned(),
                    file: file.clone(),
                    resolved_path: resolved_input_path,
                    digest: parsed_file
                        .digest
                        .expect("input capture requires a parsed file digest"),
                    unsupported: catalog
                        .has_run
                        .then(|| "input command executed after a run command".to_owned())
                        .or_else(|| {
                            (function_type.subtype == FunctionSubtype::Custom).then(|| {
                                format!(
                                    "input into value function `{func_name}` requires set/merge replay semantics"
                                )
                            })
                        }),
                },
            )
        });
        let source_command = pending_input_catalog.as_ref().map(|(command, _)| *command);
        let parsed_contents = parsed_file.rows;
        let (values, capture_rows) = if let Some(command) = source_command {
            let mut capture_rows = Vec::with_capacity(parsed_contents.len());
            for parsed in parsed_contents {
                let row_values = parsed
                    .literals
                    .iter()
                    .map(|literal| literal_to_value(self.backend.base_values(), literal))
                    .collect::<Vec<_>>();
                let mut terms = Vec::with_capacity(parsed.literals.len());
                for (literal, value) in parsed.literals.iter().zip(row_values.iter().copied()) {
                    let catalog = self.capture_catalog.as_ref().unwrap();
                    let term = self
                        .backend
                        .intern_replay_literal(
                            catalog.literal_sort(literal),
                            CaptureCatalog::replay_literal(literal),
                            value,
                        )
                        .map_err(|error| Error::BackendError(error.to_string()))?;
                    terms.push(term);
                }
                capture_rows.push(egglog_bridge::SourceInputRow::new(
                    SourceRef::InputRow {
                        command,
                        line: parsed.line,
                    },
                    row_values,
                    terms,
                ));
            }
            (Vec::new(), Some(capture_rows))
        } else {
            let values = parsed_contents
                .into_iter()
                .map(|row| {
                    row.literals
                        .into_iter()
                        .map(|literal| match literal {
                            Literal::Int(value) => self.backend.base_values().get(value),
                            Literal::Float(value) => self
                                .backend
                                .base_values()
                                .get::<F>(core_relations::Boxed::new(value)),
                            Literal::String(value) => {
                                self.backend.base_values().get::<S>(value.into())
                            }
                            Literal::Unit => unit_val,
                            Literal::Bool(_) => unreachable!(),
                        })
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            (values, None)
        };

        log::debug!("Successfully loaded file.");

        let num_facts = capture_rows.as_ref().map_or_else(|| values.len(), Vec::len);

        let bridge = self
            .backend
            .as_any()
            .downcast_ref::<egglog_bridge::EGraph>()
            .ok_or_else(|| {
                Error::BackendError(
                    "loading facts from a file requires the reference bridge backend".into(),
                )
            })?;
        if let Some(capture_rows) = capture_rows {
            bridge
                .stage_source_input_rows(backend_id, &capture_rows)
                .map_err(|error| Error::BackendError(error.to_string()))?;
        } else {
            let table_action = egglog_bridge::TableAction::new(bridge, backend_id);
            if function_type.subtype != FunctionSubtype::Constructor {
                self.backend.with_execution_state(|es| {
                    for row in values.iter() {
                        table_action.insert(es, row.iter().copied());
                    }
                    Some(unit_val)
                });
            } else {
                self.backend.with_execution_state(|es| {
                    for row in values.iter() {
                        // Constructor semantics: mint a fresh eclass id for
                        // each missing key.
                        table_action.lookup_or_insert(es, row);
                    }
                    Some(unit_val)
                });
            }
        }

        self.backend
            .flush_updates()
            .map_err(|error| Error::BackendError(error.to_string()))?;
        if self.capture_catalog.is_some() {
            self.backend
                .finalize_trace_wave()
                .map_err(|error| Error::BackendError(error.to_string()))?;
        }
        if let Some((command, entry)) = pending_input_catalog {
            self.capture_catalog
                .as_mut()
                .expect("input capture lost the capture catalog")
                .input_commands
                .insert(command, entry);
        }

        log::info!("Read {num_facts} facts into {func_name} from '{file}'.");
        Ok(())
    }

    /// Load `(input …)` facts natively into the term/proof encoding's tables. For
    /// each row we mint a term id (and, when the encoding carries proofs, its AST +
    /// fiat-proof ids) and insert the encoded term-relation, view, and proof rows
    /// directly. Rows are plain-inserted (no get-or-insert): a duplicate view key
    /// is left to the view's merge/no-merge handling. The proof checker keeps using
    /// the per-row top-level fiat actions (`desugared_before_proofs`); this just
    /// materializes the same table state.
    ///
    /// Everything is derived from the encoded schema + annotations (never the
    /// pre-encoding `FuncType`), so it also works when a desugared program is
    /// replayed in a fresh e-graph. `func_name` names the encoded *term relation*;
    /// the encoded shape is read off the term and view schemas:
    /// * constructor / relation (`term_inputs == view_inputs + 1`) — term row
    ///   `(F children… term-id) Unit`, FD view `(children…) -> (term-id, proof)`,
    ///   and the term id's `<Sort>Proof` row.
    /// * custom `:merge` / `:no-merge` (`term_inputs == view_inputs + 2`) — term
    ///   row `(f children… output term-id) Unit` and view row `(children… output
    ///   proof)`; the proof lives only in the view (a custom's fresh term sort has
    ///   no `<Sort>Proof`).
    fn native_input(&mut self, span: Span, func_name: &str, file: String) -> Result<(), Error> {
        // The encoded term relation keeps the user's original name. Its last input
        // column is the minted term id; the columns before it are the CSV base
        // columns (children, plus a custom function's output value).
        let term = self
            .functions
            .get(func_name)
            .unwrap_or_else(|| panic!("Unrecognized function name {func_name}"));
        let f_id = term.backend_id;
        let term_input = term.schema.input.clone();
        let n_term_input = term_input.len();
        let term_id_sort = term_input[n_term_input - 1].name().to_string();
        let csv_sorts: Vec<ArcSort> = term_input[..n_term_input - 1].to_vec();

        // Locate the view by its `:internal-term-constructor` back-reference (as
        // extraction / print-size do) and read the encoded shape off it.
        let view = self
            .functions
            .values()
            .find(|g| g.decl.term_constructor.as_deref() == Some(func_name))
            .unwrap_or_else(|| panic!("no encoded view for {func_name}"));
        let view_id = view.backend_id;
        let view_n_inputs = view.schema.input.len();
        // Proofs are on for this relation iff the view's proof column (its last
        // output) is not `Unit`; term-encoding-only mode uses `Unit` there.
        let proofs = view.schema.outputs.last().unwrap().name() != "Unit";
        // Constructor iff the FD view keys on all children and the term relation
        // adds exactly the term id; a custom's (`:merge` or `:no-merge`) term
        // relation also carries the output column.
        let is_constructor = view.is_fd_view() && n_term_input == view_n_inputs + 1;

        let rows = Self::read_input_rows(self.fact_directory.as_deref(), &csv_sorts, &span, &file)?;
        let unit_val = self.backend.base_values().get(());
        // Convert literals to values up front (ends the `&backend` borrow before minting).
        let value_rows: Vec<Vec<Value>> = rows
            .iter()
            .map(|row| {
                row.iter()
                    .map(|lit| match lit {
                        Literal::Int(v) => self.backend.base_values().get(*v),
                        Literal::Float(v) => self
                            .backend
                            .base_values()
                            .get::<F>(core_relations::Boxed::new(*v)),
                        Literal::String(v) => self.backend.base_values().get::<S>(v.clone().into()),
                        Literal::Unit => unit_val,
                        Literal::Bool(_) => unreachable!(),
                    })
                    .collect()
            })
            .collect();

        // Proof tables: `Fiat` from the `Proof` sort's `:internal-proof-names`,
        // the term-id sort's AST constructor by its `(<sort> <Ast>) -> Unit`
        // signature, and (constructors only) `<Sort>Proof` from the term-id
        // sort's `:internal-proof-func`.
        let proof_tables = proofs.then(|| {
            let fiat = self.proof_state.proof_names.fiat_constructor.clone();
            let fiat_fn = &self.functions[&fiat];
            let fiat_id = fiat_fn.backend_id;
            let ast_sort = fiat_fn.schema.input[0].name().to_string();
            let ast_id = self
                .functions
                .values()
                .find(|g| {
                    g.decl.internal_hidden
                        && g.schema.input.len() == 2
                        && g.schema.input[0].name() == term_id_sort
                        && g.schema.input[1].name() == ast_sort
                        && g.schema.output().name() == "Unit"
                })
                .unwrap_or_else(|| panic!("no AST constructor for sort {term_id_sort}"))
                .backend_id;
            let proof_func_id = is_constructor.then(|| {
                let pf = self.proof_state.proof_func_parent[&term_id_sort].clone();
                self.functions[&pf].backend_id
            });
            (ast_id, fiat_id, proof_func_id)
        });

        let num_facts = value_rows.len();
        let mut batch: Vec<(egglog_bridge::FunctionId, Vec<Value>)> = Vec::new();
        for value_row in value_rows {
            let fv = self.backend.fresh_id();
            // Term-relation row: CSV columns (children [+ output]) + term id + Unit.
            let mut frow = value_row.clone();
            frow.push(fv);
            frow.push(unit_val);
            batch.push((f_id, frow));

            let view_proof = if let Some((ast_id, fiat_id, proof_func_id)) = proof_tables {
                // Fiat proof of the base fact: `@Fiat(ast(fv), ast(fv))`.
                let a1 = self.backend.fresh_id();
                batch.push((ast_id, vec![fv, a1, unit_val]));
                let a2 = self.backend.fresh_id();
                batch.push((ast_id, vec![fv, a2, unit_val]));
                let pf = self.backend.fresh_id();
                batch.push((fiat_id, vec![a1, a2, pf, unit_val]));
                if let Some(proof_func_id) = proof_func_id {
                    batch.push((proof_func_id, vec![fv, pf]));
                }
                pf
            } else {
                unit_val
            };

            // View row. A constructor's FD view value-0 is the minted term id; a
            // custom view stores the base output (already in `value_row`). The
            // proof column follows (`Unit` when the encoding carries no proofs).
            let mut vrow = value_row;
            if is_constructor {
                vrow.push(fv);
            }
            vrow.push(view_proof);
            batch.push((view_id, vrow));
        }
        self.backend.add_values(batch);
        log::info!("Natively loaded {num_facts} facts into {func_name} from '{file}'.");
        Ok(())
    }

    /// Returns true if proofs are enabled.
    pub fn are_proofs_enabled(&self) -> bool {
        self.proof_state.proofs_enabled
    }

    fn resolve_command_before_proofs(
        &mut self,
        command: Command,
    ) -> Result<Vec<ResolvedNCommand>, Error> {
        let desugared = desugar_command(command, &mut self.parser, self.proof_state.proof_testing)?;
        let checked_alias_types = &self.checked_alias_types;
        if let Some(original_typechecking) = self.proof_state.original_typechecking.as_mut() {
            // Values are backend-local. Only mirror the successfully published
            // alias types needed to resolve this next source command. Checked
            // aliases are immutable and append-only between push/pop snapshots,
            // so rebuilding and cloning the complete prefix for every alias is
            // quadratic in a replay program. Copy only the newly published
            // suffix, rebinding each sort by name so even the type object comes
            // from the source typechecking graph.
            let synchronized = original_typechecking.checked_alias_types.len();
            if synchronized > checked_alias_types.len()
                || (synchronized > 0
                    && original_typechecking
                        .checked_alias_types
                        .get_index(synchronized - 1)
                        .map(|(name, _)| name)
                        != checked_alias_types
                            .get_index(synchronized - 1)
                            .map(|(name, _)| name))
            {
                return Err(Error::BackendError(
                    "proof typechecker checked-alias prefix diverged from runtime state".into(),
                ));
            }
            for index in synchronized..checked_alias_types.len() {
                let (name, alias) = checked_alias_types
                    .get_index(index)
                    .expect("checked-alias suffix index disappeared");
                let sort_name = alias.sort.name();
                let sort = original_typechecking
                    .type_info
                    .get_sort_by_name(sort_name)
                    .unwrap_or_else(|| {
                        panic!("checked alias sort `{sort_name}` missing from source typechecker")
                    })
                    .clone();
                let previous = original_typechecking.checked_alias_types.insert(
                    name.clone(),
                    CheckedAliasType {
                        declaration_span: alias.declaration_span.clone(),
                        sort,
                        closed_expr: alias.closed_expr.clone(),
                    },
                );
                debug_assert!(previous.is_none(), "checked alias was synchronized twice");
            }
            // Typecheck using the original egraph
            // TODO this is ugly- we don't need an entire e-graph just for type information.
            let typechecked = original_typechecking.typecheck_program(&desugared)?;

            for command in &typechecked {
                if let Err(reason) = command_supports_proof_encoding(
                    &command.to_command(),
                    &original_typechecking.type_info,
                ) {
                    let command_text = format!("{}", command.to_command());
                    return Err(Error::UnsupportedProofCommand {
                        command: command_text,
                        reason,
                    });
                }
            }

            Ok(proof_form(typechecked, &mut self.parser.symbol_gen))
        } else {
            let mut typechecked = self.typecheck_program(&desugared)?;

            typechecked = remove_globals::remove_globals(typechecked, &mut self.parser.symbol_gen);
            for command in &typechecked {
                self.names.check_shadowing(command)?;
            }
            Ok(typechecked)
        }
    }

    /// Desugars, typechecks, and removes globals from a single [`Command`].
    /// Leverages previous type information in the [`EGraph`] to do so, adding new type information.
    /// When will_run is true, adds to `desugared_commands_run_so_far`, which is used for proof checking.
    fn resolve_command(&mut self, command: Command) -> Result<ResolvedNCommands, Error> {
        let resolved_before_proofs = self.resolve_command_before_proofs(command)?;

        // Add term encoding when it is enabled
        if self.proof_state.original_typechecking.is_none() {
            Ok(ResolvedNCommands {
                desugared: resolved_before_proofs,
                desugared_before_proofs: vec![],
            })
        } else {
            // The proof checker consumes the per-row top-level fiat actions.
            let per_row_before_proofs =
                ProofInstrumentor::lower_inputs(self, resolved_before_proofs.clone())?;
            // Execution keeps every `(input …)` as an `Input` command, loaded
            // natively at run time by `EGraph::native_input` straight into the
            // encoded tables. Globals get the same function-style desugaring
            // (`remove_globals`) as the non-encoding path.
            let typechecked_no_globals =
                remove_globals::remove_globals(resolved_before_proofs, &mut self.parser.symbol_gen);
            // The term encoder runs before the encoded program is typechecked, so it
            // can't rely on the later typecheck to populate `global_sorts`. Register
            // the new global functions' sorts eagerly so `is_global` recognizes them
            // while encoding.
            for command in &typechecked_no_globals {
                if let GenericNCommand::Function(fdecl) = command
                    && fdecl.internal_let
                    && let Some(output_sort) = self.type_info.sorts.get(fdecl.schema.output())
                {
                    self.type_info
                        .global_sorts
                        .insert(fdecl.name.clone(), output_sort.clone());
                }
            }
            for command in &typechecked_no_globals {
                self.names.check_shadowing(command)?;
            }

            // Share repeated constructor applications (see `ast::cse`).
            let deduped =
                ast::cse::cse_program(typechecked_no_globals, &mut self.parser.symbol_gen);

            let term_encoding_added = ProofInstrumentor::add_term_encoding(self, deduped)?;
            let mut new_typechecked = vec![];
            for new_cmd in term_encoding_added {
                let desugared =
                    desugar_command(new_cmd, &mut self.parser, self.proof_state.proof_testing)?;
                for cmd in &desugared {
                    log::trace!("Desugared term encoding: {}", cmd.to_command());
                }

                // Now typecheck using self, adding term type information.
                let desugared_typechecked = self.typecheck_program(&desugared)?;
                // Remove the globals the term encoding itself introduced (its minted
                // `let`s), the same way source-level globals were removed above.
                let desugared_typechecked = remove_globals::remove_globals(
                    desugared_typechecked,
                    &mut self.parser.symbol_gen,
                );

                new_typechecked.extend(desugared_typechecked);
            }
            Ok(ResolvedNCommands {
                desugared: new_typechecked,
                desugared_before_proofs: per_row_before_proofs,
            })
        }
    }

    /// Run a program, returning the desugared outputs as well as the CommandOutputs.
    /// Can optionally not run the commands, just adding type information.
    fn process_program_internal(
        &mut self,
        program: Vec<Command>,
        run_commands: bool,
    ) -> Result<ResolvedNCommandsWithOutput, Error> {
        let mut outputs = Vec::new();
        let mut desugared_before_proofs = Vec::new();
        let mut desugared = Vec::new();

        for before_expanded_command in program {
            // First do user-provided macro expansion for this command,
            // which may rely on type information from previous commands.
            let macro_type_info = self
                .proof_state
                .original_typechecking
                .as_ref()
                .map(|egraph| &egraph.type_info)
                .unwrap_or(&self.type_info);
            let macro_expanded = self.command_macros.apply(
                before_expanded_command,
                &mut self.parser.symbol_gen,
                macro_type_info,
            )?;

            for command in macro_expanded {
                // Reject `fail` before resolve/desugar: both desugaring and
                // global lowering may lift mutation prefixes out of the
                // nested command, so guarding only the final normalized
                // `ResolvedNCommand::Fail` is too late.
                if self.capture_catalog.is_some() {
                    let unsupported = match &command {
                        Command::Fail(_, _) => Some("nested fail commands"),
                        Command::Push(_) | Command::Pop(_, _) => Some("push/pop state"),
                        _ => None,
                    };
                    if let Some(unsupported) = unsupported {
                        return Err(Error::BackendError(format!(
                            "trace capture does not support {unsupported}"
                        )));
                    }
                }
                // handle include specially- we keep them as-is for desugaring
                if let Command::Include(span, file) = &command {
                    let s = std::fs::read_to_string(file)
                        .map_err(|e| Error::IoError(file.clone().into(), e, span.clone()))?;
                    let included_program = self
                        .parser
                        .get_program_from_string(Some(file.clone()), &s)?;
                    // run program internal on these include commands
                    let resolved = self.process_program_internal(included_program, run_commands)?;
                    outputs.extend(resolved.outputs);
                    desugared.extend(resolved.resolved);
                    desugared_before_proofs.extend(resolved.resolved_before_proofs);
                } else {
                    // Preserve the macro-expanded source form separately from
                    // the normalized commands used for exact event identity.
                    // The former is parseable artifact syntax; the latter is
                    // what native capture ordinals refer to.
                    let surface_replay_command = self.capture_catalog.as_ref().and_then(|_| {
                        matches!(
                            &command,
                            Command::Sort { .. }
                                | Command::Datatype { .. }
                                | Command::Datatypes { .. }
                                | Command::Constructor { .. }
                                | Command::Relation { .. }
                                | Command::Function { .. }
                                | Command::AddRuleset(..)
                                | Command::UnstableCombinedRuleset(..)
                                | Command::Rewrite(..)
                                | Command::BiRewrite(..)
                                | Command::Action(_)
                                | Command::Check(..)
                        )
                        .then(|| command.clone())
                    });
                    let capture_rule_origins = self
                        .capture_catalog
                        .is_some()
                        .then(|| catalog_rule_origins(&command));
                    let relation_name = match &command {
                        Command::Relation { name, .. } => Some(name.clone()),
                        _ => None,
                    };
                    let inserted_relation = relation_name
                        .as_ref()
                        .is_some_and(|name| self.relation_names.insert(name.clone()));
                    if let Some(catalog) = self.capture_catalog.as_mut() {
                        catalog.begin_resolution()?;
                    }
                    let resolved_result = if self.capture_catalog.is_some() {
                        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            self.resolve_command(command)
                        })) {
                            Ok(result) => result,
                            Err(payload) => {
                                self.capture_catalog
                                    .as_mut()
                                    .expect("trace resolution lost catalog while unwinding")
                                    .finish_resolution(false);
                                std::panic::resume_unwind(payload);
                            }
                        }
                    } else {
                        self.resolve_command(command)
                    };
                    if let Some(catalog) = self.capture_catalog.as_mut() {
                        catalog.finish_resolution(resolved_result.is_ok());
                    }
                    let resolved = match resolved_result {
                        Ok(resolved) => resolved,
                        Err(error) => {
                            if inserted_relation {
                                self.relation_names
                                    .remove(relation_name.as_ref().expect("missing relation name"));
                            }
                            return Err(error);
                        }
                    };
                    let surface_command = self
                        .capture_catalog
                        .as_mut()
                        .map(|catalog| catalog.register_surface_command(surface_replay_command));
                    if let Some(origins) = &capture_rule_origins {
                        let normalized_rules = resolved
                            .desugared
                            .iter()
                            .filter(|command| matches!(command, ResolvedNCommand::NormRule { .. }))
                            .count();
                        if origins.len() != normalized_rules {
                            self.capture_catalog
                                .as_mut()
                                .expect("capture rule origins lost state")
                                .poison(format!(
                                    "surface rule-origin count {} does not match {normalized_rules} normalized rules",
                                    origins.len()
                                ));
                            return Err(Error::BackendError(
                                "capture rule-origin catalog did not match normalized expansion"
                                    .into(),
                            ));
                        }
                    }
                    let mut capture_rule_origins =
                        capture_rule_origins.map(|origins| origins.into_iter());
                    let defer_checked_alias_proof_program = (run_commands
                        && self.are_proofs_enabled()
                        && resolved
                            .desugared_before_proofs
                            .iter()
                            .any(|command| matches!(command, ResolvedNCommand::LetCheck { .. })))
                    .then(|| resolved.desugared_before_proofs.clone());
                    if run_commands
                        && self.are_proofs_enabled()
                        && defer_checked_alias_proof_program.is_none()
                    {
                        self.proof_check_program
                            .extend(resolved.desugared_before_proofs.clone());
                    }

                    desugared_before_proofs.extend(resolved.desugared_before_proofs);
                    desugared.extend(resolved.desugared.clone());

                    for processed in resolved.desugared {
                        let rule_origin = if matches!(processed, ResolvedNCommand::NormRule { .. })
                        {
                            capture_rule_origins.as_mut().and_then(Iterator::next)
                        } else {
                            None
                        };
                        // even in desugar mode we still run push and pop
                        if run_commands
                            || matches!(
                                processed,
                                ResolvedNCommand::Push(_) | ResolvedNCommand::Pop(_, _)
                            )
                        {
                            if let Some(catalog) = self.capture_catalog.as_mut() {
                                catalog.begin_command(
                                    &processed,
                                    rule_origin,
                                    surface_command
                                        .expect("source capture command was not cataloged"),
                                )?;
                            }
                            let result = if self.capture_catalog.is_some() {
                                match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                                    self.run_command(processed)
                                })) {
                                    Ok(result) => result,
                                    Err(payload) => {
                                        self.capture_catalog
                                            .as_mut()
                                            .expect("trace command lost catalog while unwinding")
                                            .finish_command(false);
                                        std::panic::resume_unwind(payload);
                                    }
                                }
                            } else {
                                self.run_command(processed)
                            };
                            if let Some(catalog) = self.capture_catalog.as_mut() {
                                catalog.finish_command(result.is_ok());
                            }
                            match result {
                                Ok(result) => outputs.extend(result),
                                Err(error) => {
                                    if inserted_relation
                                        && relation_name
                                            .as_ref()
                                            .is_some_and(|name| !self.functions.contains_key(name))
                                    {
                                        self.relation_names.remove(
                                            relation_name.as_ref().expect("missing relation name"),
                                        );
                                    }
                                    return Err(error);
                                }
                            }
                        } else if let ResolvedNCommand::LetCheck {
                            span, name, expr, ..
                        } = &processed
                        {
                            self.record_checked_alias_type_only(span, name, expr)?;
                        }
                    }
                    if let Some(commands) = defer_checked_alias_proof_program {
                        // A failed lookup must not make the alias appear in the
                        // retained proof-checking source program.
                        self.proof_check_program.extend(commands);
                    }
                    if capture_rule_origins
                        .as_mut()
                        .is_some_and(|origins| origins.next().is_some())
                    {
                        self.capture_catalog
                            .as_mut()
                            .expect("capture rule origins lost state")
                            .poison("capture rule-origin iterator was not fully consumed");
                        return Err(Error::BackendError(
                            "capture rule-origin catalog did not match normalized expansion".into(),
                        ));
                    }
                }
            }
        }

        Ok(ResolvedNCommandsWithOutput {
            outputs,
            resolved_before_proofs: desugared_before_proofs,
            resolved: desugared,
        })
    }

    /// Run a program, represented as an AST.
    /// Return a list of messages.
    pub fn run_program(&mut self, program: Vec<Command>) -> Result<Vec<CommandOutput>, Error> {
        if let Some(catalog) = self.capture_catalog.as_ref() {
            catalog.ensure_healthy()?;
        }
        if self.backend.requires_term_encoding() && self.proof_state.original_typechecking.is_none()
        {
            return Err(Error::BackendRequiresTermEncoding);
        }
        let res = self.process_program_internal(program, true)?;
        Ok(res.outputs)
    }

    /// Resolves an egglog program by parsing, typechecking, and desugaring each command.
    /// Outputs a new egglog program without any syntactic sugar, either user provided ([`CommandMacro`]) or built-in (e.g., `rewrite` commands).
    /// Also removes globals from the program by replacing with new constructors.
    pub fn resolve_program(
        &mut self,
        filename: Option<String>,
        input: &str,
    ) -> Result<Vec<ResolvedCommand>, Error> {
        if self.capture_catalog.is_some() {
            return Err(Error::BackendError(
                "trace capture does not support resolve_program after capture starts".into(),
            ));
        }
        let parsed = self.parser.get_program_from_string(filename, input)?;
        let res = self.process_program_internal(parsed, false)?;
        Ok(res.resolved.into_iter().map(|c| c.to_command()).collect())
    }

    /// Takes a source program `input` and parses it into a list of [`Command`]s.
    pub fn parse_program(
        &mut self,
        filename: Option<String>,
        input: &str,
    ) -> Result<Vec<Command>, Error> {
        let parsed = self.parser.get_program_from_string(filename, input)?;
        Ok(parsed)
    }

    /// Takes a source program `input`, parses it, runs it, and returns a list of messages.
    ///
    /// `filename` is an optional argument to indicate the source of
    /// the program for error reporting. If `filename` is `None`,
    /// a default name will be used.
    pub fn parse_and_run_program(
        &mut self,
        filename: Option<String>,
        input: &str,
    ) -> Result<Vec<CommandOutput>, Error> {
        let parsed = self.parser.get_program_from_string(filename, input)?;
        self.run_program(parsed)
    }

    /// Get the number of tuples in the database.
    ///
    pub fn num_tuples(&self) -> usize {
        self.functions
            .values()
            .map(|f| self.backend.table_size(f.backend_id))
            .sum()
    }

    /// Returns a sort based on the type.
    pub fn get_sort<S: Sort>(&self) -> Arc<S> {
        self.type_info.get_sort()
    }

    /// Returns a sort that satisfies the type and predicate.
    pub fn get_sort_by<S: Sort>(&self, f: impl Fn(&Arc<S>) -> bool) -> Arc<S> {
        self.type_info.get_sort_by(f)
    }

    /// Returns all sorts based on the type.
    pub fn get_sorts<S: Sort>(&self) -> Vec<Arc<S>> {
        self.type_info.get_sorts()
    }

    /// Returns all sorts that satisfy the type and predicate.
    pub fn get_sorts_by<S: Sort>(&self, f: impl Fn(&Arc<S>) -> bool) -> Vec<Arc<S>> {
        self.type_info.get_sorts_by(f)
    }

    /// Returns a sort based on the predicate.
    pub fn get_arcsort_by(&self, f: impl Fn(&ArcSort) -> bool) -> ArcSort {
        self.type_info.get_arcsort_by(f)
    }

    /// Returns the unique sort whose runtime values have Rust type `T`.
    pub fn get_arcsort_for_value_type<T: 'static>(&self) -> ArcSort {
        self.type_info.get_arcsort_for_value_type::<T>()
    }

    /// Returns all sorts that satisfy the predicate.
    pub fn get_arcsorts_by(&self, f: impl Fn(&ArcSort) -> bool) -> Vec<ArcSort> {
        self.type_info.get_arcsorts_by(f)
    }

    /// Returns the sort with the given name if it exists.
    pub fn get_sort_by_name(&self, sym: &str) -> Option<&ArcSort> {
        self.type_info.get_sort_by_name(sym)
    }

    /// Gets the overall run report and returns it.
    pub fn get_overall_run_report(&self) -> &RunReport {
        &self.overall_run_report
    }

    /// Convert from an egglog value to a Rust type.
    /// This method assumes `x` belongs to sort `T`.
    pub fn value_to_base<T: BaseValue>(&self, x: Value) -> T {
        self.backend.base_values().unwrap::<T>(x)
    }

    /// Convert from a Rust type to an egglog value.
    pub fn base_to_value<T: BaseValue>(&self, x: T) -> Value {
        self.backend.base_values().get::<T>(x)
    }

    /// Convert from an egglog value to a reference of a Rust container type.
    ///
    /// Returns `None` if the value cannot be converted to the requested container type.
    ///
    /// Warning: The return type of this function may contain lock guards.
    /// Attempts to modify the contents of the containers database may deadlock if the given guard has not been dropped.
    pub fn value_to_container<T: ContainerValue>(
        &self,
        x: Value,
    ) -> Option<impl Deref<Target = T>> {
        self.backend.container_values().get_val::<T>(x)
    }

    /// Convert from a Rust container type to an egglog value.
    pub fn container_to_value<T: ContainerValue>(&mut self, x: T) -> Value {
        assert!(
            self.capture_catalog.is_none(),
            "trace capture does not support direct container interning on the recording graph"
        );
        self.backend.with_execution_state(|state| {
            self.backend.container_values().register_val::<T>(x, state)
        })
    }

    /// Get the size of a function in the e-graph.
    ///
    /// `panics` if the function does not exist.
    pub fn get_size(&self, func: &str) -> usize {
        let function_id = self.functions.get(func).unwrap().backend_id;
        self.backend.table_size(function_id)
    }

    /// Get a function by name.
    ///
    /// Returns `None` if the function does not exist.
    pub fn get_function(&self, name: &str) -> Option<&Function> {
        self.functions.get(name)
    }

    /// Whether this e-graph's backend exposes the in-memory action registry
    /// used by registry-backed primitives.
    pub fn supports_action_registry(&self) -> bool {
        self.backend.action_registry().is_some()
    }

    /// Returns `true` if a user-defined command with the given name is
    /// registered in this e-graph.
    pub fn has_command(&self, name: &str) -> bool {
        self.commands.contains_key(name)
    }

    /// Invoke a registered user-defined command by name, passing the given
    /// unresolved expression arguments.
    ///
    /// This is equivalent to writing `(name args...)` at the top level, but
    /// callable directly from Rust.  Returns an error if no command with the given
    /// name is registered.
    pub fn run_user_defined_command(
        &mut self,
        name: &str,
        args: &[Expr],
    ) -> Result<Vec<CommandOutput>, Error> {
        if self.capture_catalog.is_some() {
            return Err(Error::BackendError(
                "trace capture does not support direct user-defined command execution".into(),
            ));
        }
        self.run_command(ResolvedNCommand::UserDefined(
            span!(),
            name.to_string(),
            args.to_vec(),
        ))
    }

    /// Set the report verbosity level for rule execution output.
    pub fn set_report_level(&mut self, level: ReportLevel) {
        self.backend.set_report_level(level);
    }

    /// A basic method for dumping the state of the database to `log::info!`.
    ///
    /// For large tables, this is unlikely to give particularly useful output.
    pub fn dump_debug_info(&self) {
        self.backend.dump_debug_info();
    }

    /// Run `f` with a [`FullState`] handle on this EGraph's database
    /// — the same handle a `:naive` rule's `add_rust_rule_full`
    /// callback receives. Use to drive name-indexed reads / writes
    /// (`fs.set`, `fs.add`, `fs.lookup`, `fs.eclass_of`,
    /// `fs.contains`, `fs.remove`, …) from outside a rule.
    ///
    /// # Flush semantics
    ///
    /// Pending writes flush once, **after** `f` returns. Two
    /// consequences:
    ///
    /// 1. A `set` / `add` / `remove` inside the closure is *not*
    ///    visible to a subsequent `lookup` / `contains` / `eclass_of`
    ///    in the **same** closure. Split write-then-read into separate
    ///    `update` calls.
    /// 2. Conversely, batching multiple writes in one closure is the
    ///    fast path — only one flush + rebuild happens, regardless of
    ///    how many writes occurred.
    /// 3. A closure that only reads (e.g. `lookup`, `constructor_enodes`)
    ///    stages nothing, so the flush is skipped entirely — a read
    ///    costs no more than a direct backend scan.
    ///
    /// # Example
    /// ```
    /// use egglog::prelude::*;
    /// let mut eg = EGraph::default();
    /// eg.parse_and_run_program(None, "(function f (i64) i64 :no-merge)")?;
    /// eg.update(|mut fs| fs.set("f", (1_i64,), 42_i64))?;
    /// let got = eg.update(|fs| fs.lookup("f", 1_i64))?;
    /// let got: Option<i64> = got.map(|v| eg.value_to_base::<i64>(v));
    /// assert_eq!(got, Some(42));
    /// # Ok::<(), egglog::Error>(())
    /// ```
    pub fn update<R>(
        &mut self,
        f: impl FnOnce(FullState<'_, '_>) -> Result<R, Error>,
    ) -> Result<R, Error> {
        if self.capture_catalog.is_some() {
            return Err(Error::BackendError(
                "trace capture does not support EGraph::update".into(),
            ));
        }
        if self.are_proofs_enabled() {
            return Err(Error::ProofsIncompatibleApi {
                api: "EGraph::update",
                reason: "writes inside the closure bypass the proof-encoding pipeline,\n\
                         so any rule derivations resting on them would be unverifiable.",
            });
        }
        self.update_unchecked(f)
    }

    /// Internal version of [`EGraph::update`] without the proofs
    /// check. Used by proof-system internals that need to read the
    /// e-graph while the proof system itself is enabled.
    pub(crate) fn update_unchecked<R>(
        &mut self,
        f: impl FnOnce(FullState<'_, '_>) -> Result<R, Error>,
    ) -> Result<R, Error> {
        if self.capture_catalog.is_some() {
            return Err(Error::BackendError(
                "trace capture does not support EGraph::update".into(),
            ));
        }
        let registry = self.backend.action_registry().cloned().ok_or_else(|| {
            Error::BackendError("EGraph::update requires a backend action registry".into())
        })?;
        let guard = registry.read().unwrap();
        let (result, changed) = self
            .backend
            .with_execution_state_tracked(|es| f(FullState::wrap(es, &guard, Context::Full)));
        drop(guard);
        // A read-only closure stages nothing, so `flush_updates` would only do
        // a no-op merge plus a spurious timestamp bump and rebuild check. Skip
        // it unless the closure actually wrote, keeping reads as cheap as a
        // direct backend scan.
        if changed {
            self.backend
                .flush_updates()
                .map_err(|error| Error::BackendError(error.to_string()))?;
        }
        result
    }

    /// Run a pattern query: bind the variables in `vars` against
    /// `facts` and return one [`HashMap`] per match, keyed by variable
    /// name. Values stay raw — convert via [`EGraph::value_to_base`].
    ///
    /// With zero vars, returns at most one empty map (so `.len()` is 1
    /// if the body matched, 0 if it didn't).
    pub fn query(
        &mut self,
        vars: &[(&str, ArcSort)],
        facts: ast::Facts<String, String>,
    ) -> Result<Vec<HashMap<String, Value>>, Error> {
        if self.capture_catalog.is_some() {
            return Err(Error::BackendError(
                "trace capture does not support EGraph::query".into(),
            ));
        }
        // Fail fast under proofs — otherwise the failure would
        // surface through `rust_rule`'s check below with a misleading
        // api: "rust_rule" in the error message.
        if self.are_proofs_enabled() {
            return Err(Error::ProofsIncompatibleApi {
                api: "EGraph::query",
                reason: "the underlying rust_rule callback has no proof-encoding validator,\n\
                         so query matches cannot be verified.",
            });
        }
        use std::sync::{Arc, Mutex};
        let names: Arc<[String]> = vars.iter().map(|(n, _)| (*n).to_owned()).collect();
        let results: Arc<Mutex<Vec<HashMap<String, Value>>>> = Arc::new(Mutex::new(Vec::new()));
        let results_weak = Arc::downgrade(&results);
        let names_for_cb = names.clone();

        let ruleset = self.parser.symbol_gen.fresh("query_ruleset");
        prelude::add_ruleset(self, &ruleset)?;
        let named_rule_checkpoint = self.type_info.named_rule_checkpoint();
        let original_named_rule_checkpoint = self
            .proof_state
            .original_typechecking
            .as_ref()
            .map(|egraph| egraph.type_info.named_rule_checkpoint());
        // From here on, we OWN the ruleset and the rule and have to
        // clean them up on every exit path. Run the rest in a closure
        // and tear down before propagating.
        let outcome = (|| -> Result<_, Error> {
            prelude::rust_rule(self, "query", &ruleset, vars, facts, move |_, values| {
                let arc = results_weak.upgrade().unwrap();
                let mut results = arc.lock().unwrap();
                let map: HashMap<String, Value> = names_for_cb
                    .iter()
                    .zip(values.iter().copied())
                    .map(|(n, v)| (n.clone(), v))
                    .collect();
                results.push(map);
                Some(())
            })?;
            prelude::run_ruleset(self, &ruleset)?;
            Ok(())
        })();

        // Tear the temporary rule + ruleset down whether the body
        // succeeded or not.
        if let Some(Ruleset::Rules(rules)) = self.rulesets.swap_remove(&ruleset) {
            for (_, rule) in rules {
                self.backend.free_rule(rule.backend_id);
            }
        }
        self.type_info
            .restore_named_rule_checkpoint(named_rule_checkpoint);
        if let (Some(original), Some(checkpoint)) = (
            self.proof_state.original_typechecking.as_mut(),
            original_named_rule_checkpoint,
        ) {
            original.type_info.restore_named_rule_checkpoint(checkpoint);
        }
        outcome?;

        let Some(mutex) = Arc::into_inner(results) else {
            panic!("`results_weak` outlived the callback");
        };
        Ok(mutex.into_inner().unwrap())
    }
}

pub use crate::api::{ApiError, FromValue, FromValues, IntoValue, IntoValues, RawValues};

fn unstable_fn_panic_message(name: &str) -> String {
    format!(
        "unstable-fn over `{name}` was applied in a context where its wrapped \
         function is not valid for this call site, if in a rule, add :naive."
    )
}

/// Return the persistent panic callback for `name`, registering it as pending
/// on the first uncached use. Pending callbacks remain separate until the
/// surrounding compilation or preparation operation commits.
fn get_or_register_unstable_fn_panic(
    backend: &mut dyn Backend,
    committed: &HashMap<String, ExternalFunctionId>,
    pending: &mut HashMap<String, ExternalFunctionId>,
    name: &str,
) -> ExternalFunctionId {
    if let Some(id) = committed.get(name).or_else(|| pending.get(name)) {
        return *id;
    }
    let id = backend.new_panic(unstable_fn_panic_message(name));
    pending.insert(name.to_owned(), id);
    id
}

fn commit_unstable_fn_panics(
    committed: &mut HashMap<String, ExternalFunctionId>,
    pending: &mut HashMap<String, ExternalFunctionId>,
) {
    for (name, id) in pending.drain() {
        let previous = committed.insert(name, id);
        debug_assert!(previous.is_none());
    }
}

fn free_pending_unstable_fn_panics(
    backend: &mut dyn Backend,
    pending: &mut HashMap<String, ExternalFunctionId>,
) {
    for (_, id) in pending.drain() {
        backend.free_external_func(id);
    }
}

/// Build the runtime value backing a resolved `(unstable-fn name)` target.
///
/// For table-backed functions, this captures the table action that
/// `unstable-app` will call later. For primitive targets, this bakes one
/// dispatch id per runtime context so application can choose the entrypoint
/// matching the primitive body's current call-site context.
fn resolve_function_container_target_with_context(
    backend: &egglog_bridge::EGraph,
    functions: &IndexMap<String, Function>,
    type_info: &TypeInfo,
    name: &str,
    primitive: &core::SpecializedPrimitive,
    panic_id: ExternalFunctionId,
) -> Result<ResolvedFunction, Error> {
    let target_function = type_info
        .get_sorts::<FunctionSort>()
        .into_iter()
        .find(|function| function.name() == primitive.output().name())
        .ok_or_else(|| {
            Error::BackendError(format!(
                "`unstable-fn` output sort `{}` is not a function sort",
                primitive.output().name()
            ))
        })?;

    let partial_arcsorts: Vec<_> = primitive.input().iter().skip(1).cloned().collect();
    let remaining_inputs = target_function.inputs();
    let output = target_function.output();

    let id = if let Some(func) = functions.get(name) {
        let func_type = type_info
            .get_func_type(name)
            .ok_or_else(|| Error::BackendError(format!("No resolution for {name:?}")))?;
        let expected_inputs = partial_arcsorts
            .iter()
            .chain(remaining_inputs)
            .collect::<Vec<_>>();
        let inputs_match = func_type.input.len() == expected_inputs.len()
            && func_type
                .input
                .iter()
                .zip(&expected_inputs)
                .all(|(actual, expected)| actual.name() == expected.name());
        if !inputs_match || func_type.output().name() != output.name() {
            let expected_input_names = expected_inputs
                .iter()
                .map(|sort| sort.name())
                .collect::<Vec<_>>()
                .join(", ");
            let actual_input_names = func_type
                .input
                .iter()
                .map(|sort| sort.name())
                .collect::<Vec<_>>()
                .join(", ");
            return Err(Error::BackendError(format!(
                "function container lookup for `{name}` expected ({}) -> {}, found ({}) -> {}",
                expected_input_names,
                output.name(),
                actual_input_names,
                func_type.output().name(),
            )));
        }

        let action = egglog_bridge::TableAction::new(backend, func.backend_id);
        match func_type.subtype {
            ast::FunctionSubtype::Constructor => ResolvedFunctionId::Constructor(action),
            ast::FunctionSubtype::Custom => ResolvedFunctionId::Function(action),
        }
    } else if let Some(primitives) = type_info.get_prims(name) {
        let signature: Vec<_> = partial_arcsorts
            .iter()
            .chain(remaining_inputs)
            .chain(once(&output))
            .cloned()
            .collect();
        let candidates: Vec<_> = primitives
            .iter()
            .filter(|primitive| primitive.accept(&signature, type_info))
            .collect();
        let mut context_ids = enum_map::EnumMap::from_fn(|_| None);
        for runtime_ctx in Context::ALL {
            let mut ids = candidates
                .iter()
                .filter_map(|primitive| primitive.context_ids[runtime_ctx]);
            // The first `next` finds the candidate for this runtime context;
            // the second detects whether there is more than one such candidate.
            match (ids.next(), ids.next()) {
                (None, _) => {}
                (Some(id), None) => context_ids[runtime_ctx] = Some(id),
                (Some(_), Some(_)) => {
                    return Err(Error::BackendError(format!(
                        "Ambiguous primitive resolution for {name:?} in unstable-fn context {runtime_ctx:?}"
                    )));
                }
            }
        }
        if !context_ids.iter().any(|(_, id)| id.is_some()) {
            let (output_sort, input_sorts) = signature
                .split_last()
                .expect("primitive signature should include an output sort");
            let input_names = input_sorts
                .iter()
                .map(|sort| sort.name())
                .collect::<Vec<_>>()
                .join(", ");
            return Err(Error::BackendError(format!(
                "no primitive overload matched expected signature for {name:?}: ({}) -> {}; \
                 context ids: {context_ids:?}",
                input_names,
                output_sort.name(),
            )));
        }
        ResolvedFunctionId::Primitive { context_ids }
    } else {
        return Err(Error::BackendError(format!("No resolution for {name:?}")));
    };

    Ok(ResolvedFunction {
        id,
        partial_arcsorts,
        name: name.to_owned(),
        panic_id,
    })
}

type LoweredPrimitive = (
    ExternalFunctionId,
    Vec<core::GenericAtomTerm<RuleVar, RuleValue>>,
    ColumnTy,
    Option<Arc<ReplayConstructorSpec>>,
);

struct BackendRule<'a> {
    backend: &'a mut dyn Backend,
    unstable_fn_panic_ids: &'a mut HashMap<String, ExternalFunctionId>,
    pending_unstable_fn_panic_ids: HashMap<String, ExternalFunctionId>,
    entries: HashMap<core::ResolvedAtomTerm, core::GenericAtomTerm<RuleVar, RuleValue>>,
    constant_bindings: HashMap<String, RuleValue>,
    next_var: u32,
    body: core::Query<RuleBodyCall, RuleVar, RuleValue>,
    head: core::GenericCoreActions<RuleActionCall, RuleVar, RuleValue>,
    rollback_external_funcs: Vec<ExternalFunctionId>,
    functions: &'a IndexMap<String, Function>,
    type_info: &'a TypeInfo,
    capture_catalog: Option<&'a CaptureCatalog>,
    source_capture: Option<SourceRef>,
    firing_capture: Option<FiringCaptureSpec>,
    criterion_capture: Option<CriterionCaptureSpec>,
    literal_terms: HashMap<Literal, ReplayTermId>,
    capture_union_sorts: Vec<ReplaySortId>,
    /// Whether primitives may read the database. When true the per-phase
    /// [`crate::Context`] widens from `Pure`/`Write` to `Read`/`Full` (query
    /// gains reads, action gains reads on top of writes). True for `:naive` /
    /// `:unsafe-seminaive` rules and a non-seminaive EGraph.
    requires_read_context: bool,
}

impl<'a> BackendRule<'a> {
    fn new(
        backend: &'a mut dyn Backend,
        functions: &'a IndexMap<String, Function>,
        type_info: &'a TypeInfo,
        capture_catalog: Option<&'a CaptureCatalog>,
        unstable_fn_panic_ids: &'a mut HashMap<String, ExternalFunctionId>,
        requires_read_context: bool,
    ) -> BackendRule<'a> {
        BackendRule {
            backend,
            unstable_fn_panic_ids,
            pending_unstable_fn_panic_ids: Default::default(),
            functions,
            type_info,
            capture_catalog,
            source_capture: None,
            firing_capture: None,
            criterion_capture: None,
            literal_terms: HashMap::default(),
            capture_union_sorts: Vec::new(),
            requires_read_context,
            entries: Default::default(),
            constant_bindings: Default::default(),
            next_var: 0,
            body: Default::default(),
            head: Default::default(),
            rollback_external_funcs: Vec::new(),
        }
    }

    /// The [`crate::Context`] that applies when compiling
    /// primitives on the query side (LHS) of this rule. Under
    /// seminaive evaluation, queries are pure (no DB reads or
    /// writes); a `:naive` rule (or `eg.seminaive = false`) widens
    /// this to [`Context::Read`] so reads from primitives are
    /// admissible.
    fn query_context(&self) -> crate::Context {
        if self.requires_read_context {
            crate::Context::Read
        } else {
            crate::Context::Pure
        }
    }

    /// The [`crate::Context`] that applies when compiling
    /// primitives on the action side (RHS) of this rule. Under
    /// seminaive, actions may write but not read; a `:naive` rule
    /// widens to [`Context::Full`] so writes and reads are both
    /// admissible.
    fn action_context(&self) -> crate::Context {
        if self.requires_read_context {
            crate::Context::Full
        } else {
            crate::Context::Write
        }
    }

    fn set_firing_capture(
        &mut self,
        rule: u32,
        inputs: &[ResolvedVar],
        substitutions: &[(ResolvedVar, ResolvedAtomTerm)],
    ) -> Result<(), Error> {
        let catalog = self
            .capture_catalog
            .expect("capture rule metadata requires an active capture catalog");
        let mut bindings = Vec::with_capacity(inputs.len());
        for input in inputs {
            let mut term = ResolvedAtomTerm::Var(Span::Panic, input.clone());
            for _ in 0..=substitutions.len() {
                let ResolvedAtomTerm::Var(_, variable) = &term else {
                    break;
                };
                let Some((_, replacement)) =
                    substitutions.iter().find(|(source, _)| source == variable)
                else {
                    break;
                };
                term = replacement.clone();
            }

            match &term {
                ResolvedAtomTerm::Var(_, variable) => {
                    let current_sort = catalog.sort_ids[variable.sort.name()];
                    let lowered = self.entry(&term)?;
                    let core::GenericAtomTerm::Var(_, variable) = lowered else {
                        return Err(Error::BackendError(format!(
                            "capture binding `{}` did not lower to a native variable",
                            input.name
                        )));
                    };
                    bindings.push(FiringCaptureBinding::Variable {
                        variable,
                        current_sort,
                    });
                }
                ResolvedAtomTerm::Literal(_, literal) => {
                    self.entry(&term)?;
                    let replay = self.literal_terms.get(literal).copied().ok_or_else(|| {
                        Error::BackendError(format!(
                            "capture binding `{}` has no typed literal term",
                            input.name
                        ))
                    })?;
                    bindings.push(FiringCaptureBinding::Constant {
                        term: replay,
                        sort: catalog.literal_sort(literal),
                    });
                }
                ResolvedAtomTerm::Global(_, variable) => {
                    return Err(Error::BackendError(format!(
                        "capture binding `{}` still references global `{}`",
                        input.name, variable.name
                    )));
                }
            }
        }
        self.firing_capture = Some(FiringCaptureSpec {
            rule,
            bindings: bindings.into_boxed_slice(),
            union_sorts: self.capture_union_sorts.clone().into_boxed_slice(),
        });
        Ok(())
    }

    fn fresh_var(&mut self, variable: &ResolvedVar) -> RuleVar {
        let id = self.next_var;
        self.next_var += 1;
        RuleVar {
            id,
            name: variable.name.clone().into_boxed_str(),
            ty: variable.sort.column_ty(self.backend.base_values()),
        }
    }

    fn bind_constant(&mut self, variable: &ResolvedVar, value: Value) -> Result<(), Error> {
        let bound = RuleValue {
            value,
            ty: variable.sort.column_ty(self.backend.base_values()),
        };
        if let Some(previous) = self.constant_bindings.insert(variable.name.clone(), bound)
            && previous != bound
        {
            return Err(Error::BackendError(format!(
                "checked alias `{}` has conflicting runtime values",
                variable.name
            )));
        }
        Ok(())
    }

    fn entry(
        &mut self,
        term: &core::ResolvedAtomTerm,
    ) -> Result<core::GenericAtomTerm<RuleVar, RuleValue>, Error> {
        if let Some(entry) = self.entries.get(term) {
            return Ok(entry.clone());
        }
        let entry = match term {
            core::GenericAtomTerm::Var(span, variable) => self
                .constant_bindings
                .get(&variable.name)
                .copied()
                .map(|value| core::GenericAtomTerm::Literal(span.clone(), value))
                .unwrap_or_else(|| {
                    core::GenericAtomTerm::Var(span.clone(), self.fresh_var(variable))
                }),
            core::GenericAtomTerm::Literal(span, literal) => {
                let value = literal_to_rule_value(self.backend.base_values(), literal);
                if let Some(catalog) = self.capture_catalog {
                    let term = self
                        .backend
                        .intern_replay_literal(
                            catalog.literal_sort(literal),
                            CaptureCatalog::replay_literal(literal),
                            value.value,
                        )
                        .map_err(|error| Error::BackendError(error.to_string()))?;
                    self.literal_terms.insert(literal.clone(), term);
                }
                core::GenericAtomTerm::Literal(span.clone(), value)
            }
            core::GenericAtomTerm::Global(span, variable) => self
                .constant_bindings
                .get(&variable.name)
                .copied()
                .map(|value| core::GenericAtomTerm::Literal(span.clone(), value))
                .ok_or_else(|| {
                    Error::BackendError(format!(
                        "{span}: global `{}` was not desugared before backend lowering",
                        variable.name
                    ))
                })?,
        };
        self.entries.insert(term.clone(), entry.clone());
        Ok(entry)
    }

    fn func(&self, f: &typechecking::FuncType) -> egglog_bridge::FunctionId {
        self.functions[&f.name].backend_id
    }

    fn prim(
        &mut self,
        prim: &core::SpecializedPrimitive,
        args: &[core::ResolvedAtomTerm],
        ctx: crate::Context,
    ) -> Result<LoweredPrimitive, Error> {
        // The typechecker has already checked that this primitive is
        // valid in `ctx`; pick the runtime id that stamps the same ctx
        // onto the state wrapper when invoked.
        let resolved_id = prim.external_id(ctx);

        let mut rule_args = self.args(args)?;

        if prim.name() == "unstable-fn" {
            let Some(core::ResolvedAtomTerm::Literal(_, Literal::String(name))) = args.first()
            else {
                return Err(Error::BackendError(
                    "expected string literal after `unstable-fn`".into(),
                ));
            };
            if self
                .backend
                .as_any()
                .downcast_ref::<egglog_bridge::EGraph>()
                .is_none()
            {
                return Err(Error::BackendError(
                    "`unstable-fn` is only supported on the reference bridge backend".into(),
                ));
            }
            // Obtain the EGraph-lifetime panic id used by
            // `FunctionContainer::apply` when the wrapped function is applied
            // in a context that doesn't admit it. A new id remains pending
            // until this rule is registered successfully.
            let panic_id = get_or_register_unstable_fn_panic(
                self.backend,
                self.unstable_fn_panic_ids,
                &mut self.pending_unstable_fn_panic_ids,
                name,
            );
            let bridge = self
                .backend
                .as_any()
                .downcast_ref::<egglog_bridge::EGraph>()
                .ok_or_else(|| {
                    Error::BackendError(
                        "`unstable-fn` is only supported on the reference bridge backend".into(),
                    )
                })?;
            let resolved = resolve_function_container_target_with_context(
                bridge,
                self.functions,
                self.type_info,
                name,
                prim,
                panic_id,
            );
            let resolved = resolved?;
            rule_args[0] = core::GenericAtomTerm::Literal(
                args[0].span().clone(),
                base_rule_value(self.backend.base_values(), resolved),
            );
        }

        let output_ty = prim.output().column_ty(self.backend.base_values());
        let replay = self
            .capture_catalog
            .and_then(|catalog| catalog.primitive_spec(prim));
        Ok((resolved_id, rule_args, output_ty, replay))
    }

    fn args<'b>(
        &mut self,
        args: impl IntoIterator<Item = &'b core::ResolvedAtomTerm>,
    ) -> Result<Vec<core::GenericAtomTerm<RuleVar, RuleValue>>, Error> {
        args.into_iter().map(|term| self.entry(term)).collect()
    }

    fn query(
        &mut self,
        query: &core::Query<ResolvedCall, ResolvedVar>,
        include_subsumed: bool,
    ) -> Result<(), Error> {
        for atom in &query.atoms {
            let (head, args) = match &atom.head {
                ResolvedCall::Func(f) => (
                    RuleBodyCall::Table {
                        id: self.func(f),
                        read: if include_subsumed {
                            ReadMode::All
                        } else {
                            ReadMode::Live
                        },
                    },
                    self.args(&atom.args)?,
                ),
                ResolvedCall::Primitive(p) => {
                    let ctx = self.query_context();
                    let (id, args, output, replay) = self.prim(p, &atom.args, ctx)?;
                    (
                        RuleBodyCall::Primitive {
                            id,
                            name: p.name().into(),
                            output,
                            replay,
                        },
                        args,
                    )
                }
                ResolvedCall::Values(_) => {
                    unreachable!("`values` is lowered to the underlying function atom before query")
                }
            };
            self.body.atoms.push(core::GenericAtom {
                span: atom.span.clone(),
                head,
                args,
            });
        }
        Ok(())
    }

    fn actions(&mut self, actions: &core::ResolvedCoreActions) -> Result<(), Error> {
        for action in &actions.0 {
            match action {
                core::GenericCoreAction::Let(span, v, f, args) => {
                    let (call, args) = match f {
                        ResolvedCall::Func(f) => (
                            RuleActionCall::Table {
                                id: self.func(f),
                                name: f.name.clone().into_boxed_str(),
                            },
                            self.args(args)?,
                        ),
                        ResolvedCall::Primitive(p) => {
                            let ctx = self.action_context();
                            let (id, args, output, replay) = self.prim(p, args, ctx)?;
                            (
                                RuleActionCall::Primitive {
                                    id,
                                    name: p.name().into(),
                                    output,
                                    replay,
                                },
                                args,
                            )
                        }
                        ResolvedCall::Values(_) => {
                            panic!("`values` cannot be bound as a single value")
                        }
                    };
                    let variable = self.fresh_var(v);
                    self.head.0.push(core::GenericCoreAction::Let(
                        span.clone(),
                        variable.clone(),
                        call,
                        args,
                    ));
                    self.entries.insert(
                        core::GenericAtomTerm::Var(span.clone(), v.clone()),
                        core::GenericAtomTerm::Var(span.clone(), variable),
                    );
                }
                core::GenericCoreAction::LetAtomTerm(span, v, x) => {
                    let value = self.entry(x)?;
                    let variable = self.fresh_var(v);
                    self.head.0.push(core::GenericCoreAction::LetAtomTerm(
                        span.clone(),
                        variable.clone(),
                        value,
                    ));
                    self.entries.insert(
                        core::GenericAtomTerm::Var(span.clone(), v.clone()),
                        core::GenericAtomTerm::Var(span.clone(), variable),
                    );
                }
                core::GenericCoreAction::Set(span, f, xs, ys) => match f {
                    ResolvedCall::Primitive(..) => {
                        return Err(Error::BackendError("cannot set a primitive".into()));
                    }
                    ResolvedCall::Values(..) => {
                        return Err(Error::BackendError(
                            "`values` is not a settable function".into(),
                        ));
                    }
                    ResolvedCall::Func(f) => {
                        let arguments = self.args(xs)?;
                        let values = self.args(ys)?;
                        self.head.0.push(core::GenericCoreAction::Set(
                            span.clone(),
                            RuleActionCall::Table {
                                id: self.func(f),
                                name: f.name.clone().into_boxed_str(),
                            },
                            arguments,
                            values,
                        ));
                    }
                },
                core::GenericCoreAction::Change(span, change, f, args) => match f {
                    ResolvedCall::Primitive(..) => {
                        return Err(Error::BackendError(
                            "cannot delete or subsume a primitive".into(),
                        ));
                    }
                    ResolvedCall::Values(..) => {
                        return Err(Error::BackendError(
                            "`values` is not a changeable function".into(),
                        ));
                    }
                    ResolvedCall::Func(f) => {
                        let name = f.name.clone();
                        let can_subsume = self.functions[&f.name].can_subsume;
                        if matches!(change, Change::Subsume) && !can_subsume {
                            return Err(Error::SubsumeMergeError(name, span.clone()));
                        }
                        let arguments = self.args(args)?;
                        self.head.0.push(core::GenericCoreAction::Change(
                            span.clone(),
                            *change,
                            RuleActionCall::Table {
                                id: self.func(f),
                                name: f.name.clone().into_boxed_str(),
                            },
                            arguments,
                        ));
                    }
                },
                core::GenericCoreAction::Union(span, x, y) => {
                    if let Some(catalog) = self.capture_catalog {
                        let x_sort = core::atom_term_sort(x);
                        let y_sort = core::atom_term_sort(y);
                        if x_sort.name() != y_sort.name() {
                            return Err(Error::BackendError(format!(
                                "capture union joins different logical sorts `{}` and `{}`",
                                x_sort.name(),
                                y_sort.name()
                            )));
                        }
                        self.capture_union_sorts
                            .push(catalog.sort_ids[x_sort.name()]);
                    }
                    let x = self.entry(x)?;
                    let y = self.entry(y)?;
                    self.head
                        .0
                        .push(core::GenericCoreAction::Union(span.clone(), x, y));
                }
                core::GenericCoreAction::Panic(span, message) => {
                    self.head.0.push(core::GenericCoreAction::Panic(
                        span.clone(),
                        message.clone(),
                    ));
                }
            }
        }
        Ok(())
    }

    fn query_table(
        &mut self,
        span: Span,
        table: egglog_bridge::FunctionId,
        entries: Vec<core::GenericAtomTerm<RuleVar, RuleValue>>,
        read: ReadMode,
    ) {
        self.body.atoms.push(core::GenericAtom {
            span,
            head: RuleBodyCall::Table { id: table, read },
            args: entries,
        });
    }

    fn call_external_func(
        &mut self,
        span: Span,
        id: ExternalFunctionId,
        name: &str,
        arguments: Vec<core::GenericAtomTerm<RuleVar, RuleValue>>,
        output: ColumnTy,
    ) -> core::GenericAtomTerm<RuleVar, RuleValue> {
        let variable = RuleVar {
            id: self.next_var,
            name: format!("@{name}").into_boxed_str(),
            ty: output,
        };
        self.next_var += 1;
        self.head.0.push(core::GenericCoreAction::Let(
            span.clone(),
            variable.clone(),
            RuleActionCall::Primitive {
                id,
                name: name.into(),
                output,
                replay: None,
            },
            arguments,
        ));
        core::GenericAtomTerm::Var(span, variable)
    }

    fn remove(
        &mut self,
        span: Span,
        table: egglog_bridge::FunctionId,
        name: &str,
        arguments: Vec<core::GenericAtomTerm<RuleVar, RuleValue>>,
    ) {
        self.head.0.push(core::GenericCoreAction::Change(
            span,
            Change::Delete,
            RuleActionCall::Table {
                id: table,
                name: name.into(),
            },
            arguments,
        ));
    }

    fn try_build(
        mut self,
        name: &str,
        seminaive: bool,
        no_decomp: bool,
        span: Span,
    ) -> Result<egglog_bridge::RuleId, Error> {
        let spec = RuleSpec {
            name: name.to_owned(),
            seminaive,
            no_decomp,
            core: core::GenericCoreRule {
                span,
                body: std::mem::take(&mut self.body),
                head: std::mem::take(&mut self.head),
            },
            firing_capture: self.firing_capture.take(),
            criterion_capture: self.criterion_capture.take(),
            source_capture: self.source_capture.take().map(|source| SourceCaptureSpec {
                source,
                union_sorts: self.capture_union_sorts.clone().into_boxed_slice(),
            }),
            owned_external_funcs: std::mem::take(&mut self.rollback_external_funcs),
        };
        let result = self
            .backend
            .add_rule(spec)
            .map_err(|error| Error::BackendError(error.to_string()));
        if result.is_ok() {
            commit_unstable_fn_panics(
                self.unstable_fn_panic_ids,
                &mut self.pending_unstable_fn_panic_ids,
            );
        }
        result
    }
}

impl Drop for BackendRule<'_> {
    fn drop(&mut self) {
        free_pending_unstable_fn_panics(self.backend, &mut self.pending_unstable_fn_panic_ids);
        for id in self.rollback_external_funcs.drain(..) {
            self.backend.free_external_func(id);
        }
    }
}

fn base_rule_value<T: core_relations::BaseValue>(base_values: &BaseValues, x: T) -> RuleValue {
    RuleValue {
        value: base_values.get(x),
        ty: ColumnTy::Base(base_values.get_ty::<T>()),
    }
}

fn literal_to_rule_value(base_values: &BaseValues, l: &Literal) -> RuleValue {
    match l {
        Literal::Int(x) => base_rule_value::<i64>(base_values, *x),
        Literal::Float(x) => base_rule_value::<sort::F>(base_values, x.into()),
        Literal::String(x) => base_rule_value::<sort::S>(base_values, sort::S::new(x.clone())),
        Literal::Bool(x) => base_rule_value::<bool>(base_values, *x),
        Literal::Unit => base_rule_value::<()>(base_values, ()),
    }
}

fn literal_to_value(base_values: &BaseValues, l: &Literal) -> Value {
    match l {
        Literal::Int(x) => base_values.get::<i64>(*x),
        Literal::Float(x) => base_values.get::<sort::F>(x.into()),
        Literal::String(x) => base_values.get::<sort::S>(sort::S::new(x.clone())),
        Literal::Bool(x) => base_values.get::<bool>(*x),
        Literal::Unit => base_values.get::<()>(()),
    }
}

#[derive(Debug, Error)]
pub enum Error {
    #[error(transparent)]
    ParseError(#[from] ParseError),
    #[error(transparent)]
    NotFoundError(#[from] NotFoundError),
    #[error(transparent)]
    TypeError(#[from] TypeError),
    #[error(transparent)]
    ApiError(#[from] crate::api::ApiError),
    #[error("Errors:\n{}", ListDisplay(.0, "\n"))]
    TypeErrors(Vec<TypeError>),
    #[error("{}\nCheck failed: \n{}", .1, ListDisplay(.0, "\n"))]
    CheckError(Vec<Fact>, Span),
    #[error("{1}\nNo such ruleset: {0}")]
    NoSuchRuleset(String, Span),
    #[error("{1}\nNo such rule: {0:?}")]
    NoSuchRule(String, Span),
    #[error("{span}\nlet-check {alias}: {reason}")]
    CheckedAlias {
        alias: String,
        reason: String,
        span: Span,
    },
    #[error(
        "{1}\nAttempted to add a rule to combined ruleset {0}. Combined rulesets may only depend on other rulesets."
    )]
    CombinedRulesetError(String, Span),
    #[error("{0}")]
    BackendError(String),
    #[error(
        "This backend requires term encoding. Build the e-graph with `EGraph::with_backend(..).with_term_encoding()`."
    )]
    BackendRequiresTermEncoding,
    #[error("{0}\nTried to pop too much")]
    Pop(Span),
    #[error("{0}\nCommand should have failed.")]
    ExpectFail(Span),
    #[error("{2}\nIO error: {0}: {1}")]
    IoError(PathBuf, std::io::Error, Span),
    #[error("{1}\nCannot subsume function with merge: {0}")]
    SubsumeMergeError(String, Span),
    #[error("extraction failure: {:?}", .0)]
    ExtractError(String),
    #[error("{span}\n{error}")]
    ProofError {
        span: Span,
        #[source]
        error: ProveExistsError,
    },
    #[error("{1}\n{2}\nShadowing is not allowed, but found {0}")]
    Shadowing(String, Span, Span),
    #[error("{1}\nCommand already exists: {0}")]
    CommandAlreadyExists(String, Span),
    #[error("Incorrect format in file '{0}'.")]
    InputFileFormatError(String),
    #[error(
        "Command is not supported by the current proof term encoding implementation.\n\
         Reason: {reason}\n\
         This typically means the command uses constructs that cannot yet be represented as proof terms.\n\
         Consider disabling proof term encoding for this run or rewriting the command to avoid unsupported features.\n\
         Offending command: {command}"
    )]
    UnsupportedProofCommand {
        command: String,
        reason: ProofEncodingUnsupportedReason,
    },
    #[error(
        "`{api}` is incompatible with proof mode: {reason} \
         Disable proofs or make the operation a command in the syntax of the egglog language and use `EGraph::parse_and_run`."
    )]
    ProofsIncompatibleApi {
        api: &'static str,
        reason: &'static str,
    },
}

#[cfg(test)]
mod tests {
    use std::sync::OnceLock;

    use crate::constraint::SimpleTypeConstraint;
    use crate::core_relations::EqualityReason;
    use crate::*;

    use crate::PureState;

    fn serial_trace_pool() -> &'static rayon::ThreadPool {
        static SERIAL_POOL: OnceLock<rayon::ThreadPool> = OnceLock::new();
        SERIAL_POOL.get_or_init(|| {
            rayon::ThreadPoolBuilder::new()
                .num_threads(1)
                .build()
                .unwrap()
        })
    }

    fn enable_serial_trace(egraph: &mut EGraph) -> Result<(), Error> {
        serial_trace_pool().install(|| egraph.enable_trace())
    }

    fn find_container_canonicalization(
        view: &core_relations::TraceView<'_>,
        root: core_relations::CauseId,
    ) -> Result<
        Option<(
            core_relations::Wave,
            core_relations::EdgeHorizon,
            core_relations::HistoryPosition,
            Vec<core_relations::TypedCellEquality>,
        )>,
        core_relations::TraceViewError,
    > {
        let mut pending = vec![core_relations::CauseRef::Cause(root)];
        while let Some(cause) = pending.pop() {
            let core_relations::CauseRef::Cause(cause) = cause else {
                continue;
            };
            match view.cause(cause)? {
                core_relations::RawCause::ContainerCanonicalize {
                    wave,
                    as_of_edges,
                    position,
                    equalities,
                } => return Ok(Some((wave, as_of_edges, position, equalities.to_vec()))),
                core_relations::RawCause::Merge { incoming, .. } => {
                    pending.push(incoming);
                }
                _ => {}
            }
        }
        Ok(None)
    }

    #[test]
    fn trace_merge_input_choice_opt_in_is_explicit() {
        for name in [
            "min",
            "max",
            "pair-min-by-second-i64",
            "maybe-either-i64-bool-min",
            "maybe-either-i64-bool-max",
        ] {
            assert!(primitive_merge_returns_one_input(name), "{name}");
        }
        for name in ["+", "pair", "unstable-fn", "clamp"] {
            assert!(!primitive_merge_returns_one_input(name), "{name}");
        }
    }

    #[test]
    fn trace_attribute_pair_registry_congruence() {
        serial_trace_pool().install(|| {
            let mut egraph = EGraph::default();
            egraph.enable_trace().unwrap();
            let mut program = String::new();
            // Base literals and container ids share raw Value bits. Crowd the
            // literal and computed-Call sorts so collision selection must use
            // the changed children's typed equality metadata.
            for value in 0..200 {
                program.push_str(&format!("(let $literal-{value} {value})"));
                program.push_str(&format!(
                    "(let $computed-{value} (+ 1000 {}))",
                    value - 1000
                ));
            }
            program.push_str(
                "(datatype Expr (A i64) (B i64))\
                 (sort ExprPair (Pair Expr i64))\
                 (datatype Root (Hold ExprPair))\
                 (relation Go (Unit))\
                 (relation Done (Unit))\
                 (Go ())\
                 (rule ((Go u))\
                   ((Hold (pair (A 1) 7))\
                    (Hold (pair (B 2) 7))\
                    (Done ())\
                    (union (A 1) (B 2))) :name \"merge-child\")\
                 (run 1)\
                 (check (Done ()))",
            );
            egraph.parse_and_run_program(None, &program).unwrap();

            egraph
                .with_trace_view(|view| {
                    let (cause, wave, as_of_edges, position) = (1..=view
                        .totals()
                        .applied_equalities)
                        .find_map(|raw| {
                            match view
                                .applied_equality(core_relations::AppliedEqualityId::new(raw))
                                .ok()?
                                .reason
                            {
                                EqualityReason::Congruence {
                                    cause,
                                    wave,
                                    as_of_edges,
                                    position,
                                } => Some((cause, wave, as_of_edges, position)),
                                _ => None,
                            }
                        })
                        .expect("Pair collision should retain one exact container-congruence edge");
                    let dependency = find_container_canonicalization(view, cause)?
                        .expect("Pair congruence should unfold to its container collision");
                    assert_eq!(
                        (dependency.0, dependency.1, dependency.2),
                        (wave, as_of_edges, position)
                    );
                    assert!(!dependency.3.is_empty());
                    for pair in dependency.3 {
                        assert!(
                            !view
                                .explain_equality_support_at(
                                    pair.left,
                                    pair.right,
                                    as_of_edges,
                                    position
                                )?
                                .applied
                                .is_empty()
                        );
                    }
                    Ok(())
                })
                .unwrap();
        });
    }

    #[test]
    fn trace_ignore_raw_colliding_unrelated_set_ancestor() {
        serial_trace_pool().install(|| {
            let mut egraph = EGraph::default();
            egraph.enable_trace().unwrap();
            let mut program = String::from(
                "(datatype Expr (A i64) (B i64))\
                 (sort Exprs (Vec Expr))\
                 (sort Ints (Set i64))\
                 (function Hold (Unit) Exprs :no-merge)\
                 (relation Go (Unit))\
                 (relation Done (Unit))\
                 (let $a (A 1))",
            );
            // Crowd the unsupported Set registry with every likely raw child
            // id. Its i64 elements are not typed Vec children, even when their
            // Value bits collide with the dirty Vec id.
            for value in 0..256 {
                program.push_str(&format!("(let $ints-{value} (set-of {value}))"));
            }
            program.push_str(
                "(Go ())\
                 (rule ((Go u))\
                   ((set (Hold ()) (vec-of (B 2)))\
                    (union (A 1) (B 2))) :name \"merge-child\")\
                 (run 1)\
                 (rule ((= v (Hold ()))\
                        (= v (vec-of (A 1))))\
                   ((Done ())) :name \"observe-refresh\")\
                 (run 1)\
                 (check (Done ()))",
            );
            egraph.parse_and_run_program(None, &program).unwrap();

            egraph
                .with_trace_view(|view| {
                    let mut refreshed = false;
                    for raw in 1..=view.totals().facts {
                        let fact = view.fact(core_relations::FactId::new(raw))?;
                        let core_relations::CauseRef::Cause(cause) = fact.cause else {
                            continue;
                        };
                        refreshed |= matches!(
                            view.cause(cause)?,
                            core_relations::RawCause::ContainerRefresh { .. }
                        );
                    }
                    assert!(refreshed);
                    Ok(())
                })
                .unwrap();
        });
    }

    #[test]
    #[should_panic(expected = "multiple exact logical replay sorts")]
    fn trace_reject_ambiguous_nominal_container_aliases() {
        serial_trace_pool().install(|| {
            let mut egraph = EGraph::default();
            egraph.enable_trace().unwrap();
            egraph
                .parse_and_run_program(
                    None,
                    "(datatype Expr (A i64) (B i64))\
                     (sort P1 (Pair Expr i64))\
                     (sort P2 (Pair Expr i64))\
                     (datatype R1 (H1 P1))\
                     (datatype R2 (H2 P2))\
                     (relation Go (Unit))\
                     (relation Done (Unit))\
                     (Go ())\
                     (rule ((Go u))\
                       ((H1 (pair (A 1) 7))\
                        (H1 (pair (B 2) 7))\
                        (H2 (pair (A 1) 7))\
                        (H2 (pair (B 2) 7))\
                        (Done ())\
                        (union (A 1) (B 2))) :name \"merge-child\")\
                     (run 1)\
                     (check (Done ()))",
                )
                .unwrap();
        });
    }

    #[test]
    fn trace_defer_body_primitive_terms_until_all_guards_pass() {
        let mut egraph = EGraph::default();
        enable_serial_trace(&mut egraph).unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(relation Input (i64))\
                 (relation Done (i64))\
                 (Input 1)\
                 (rule ((Input x) (= y (+ x 1)) (< y 0)) ((Done y)) :name \"dead\")\
                 (run 1)",
            )
            .unwrap();

        let state = egraph.capture_catalog.as_ref().unwrap();
        let add = state.op_ids[&ReplayOpKey {
            name: "+".to_owned(),
            inputs: vec!["i64".to_owned(), "i64".to_owned()],
            output: "i64".to_owned(),
        }];
        let mut ordinal = 1;
        while let Some(term) = egraph.replay_term(ReplayTermId::new(ordinal)).unwrap() {
            assert!(!matches!(term, ReplayTerm::Call { op, .. } if op == add));
            ordinal += 1;
        }
    }

    #[test]
    fn trace_fail_closed_when_a_pure_call_depends_on_an_unsupported_primitive() {
        let mut egraph = EGraph::default();
        enable_serial_trace(&mut egraph).unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(sort Fn (UnstableFn (i64 i64) i64))\
                 (relation Input (i64))\
                 (relation Done (i64))\
                 (Input 1)\
                 (rule ((Input l))\
                   ((Done (+ (unstable-app (unstable-fn \"+\") l 1) 1)))\
                   :name \"unsupported-child\")\
                 (run 1)",
            )
            .unwrap();
        let failure = egraph
            .with_trace_view(|view| {
                for raw in 1..=view.totals().facts {
                    view.fact_terms(core_relations::FactId::new(raw))?;
                }
                Ok(())
            })
            .unwrap_err();
        assert!(
            failure
                .to_string()
                .contains("unsupported causal row origin"),
            "unexpected trace failure: {failure}"
        );
    }

    #[test]
    fn failed_relation_declaration_does_not_poison_origin_catalog() {
        let mut egraph = EGraph::default();
        let error = egraph
            .parse_and_run_program(None, "(relation Broken (MissingSort))")
            .unwrap_err();

        assert!(error.to_string().contains("MissingSort"));
        assert!(!egraph.relation_names.contains("Broken"));
    }

    #[test]
    fn trace_subsume_mark_only_transition_records_no_specialized_capture() {
        let mut egraph = EGraph::default();
        enable_serial_trace(&mut egraph).unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(datatype Expr (A))\
                 (relation Go ())\
                 (let $a (A))\
                 (Go)",
            )
            .unwrap();
        let before = egraph
            .with_trace_view(|view| Ok((view.totals().facts, view.totals().removals)))
            .unwrap();

        egraph
            .parse_and_run_program(
                None,
                "(rule ((Go)) ((subsume (A))) :name \"subsume-existing\")\
                 (run 1)",
            )
            .unwrap();

        let after = egraph
            .with_trace_view(|view| Ok((view.totals().facts, view.totals().removals)))
            .unwrap();
        assert_eq!(after, before);
    }

    #[test]
    fn trace_refresh_parent_fact_after_stable_vec_rebuild() {
        serial_trace_pool().install(|| {
            let mut egraph = EGraph::default();
            egraph.enable_trace().unwrap();
            egraph
                .parse_and_run_program(
                    None,
                    "(datatype Expr (A i64) (B i64))\
                     (sort Exprs (Vec Expr))\
                     (function Hold (Unit) Exprs :no-merge)\
                     (relation Go (Unit))\
                     (relation Done (Unit))\
                     (let $a (A 1))\
                     (Go ())\
                     (rule ((Go u))\
                       ((set (Hold ()) (vec-of (B 2)))\
                        (union (A 1) (B 2))) :name \"merge-child\")\
                     (run 1)",
                )
                .unwrap();
            egraph
                .parse_and_run_program(
                    None,
                    "(rule ((= v (Hold ()))\
                            (= v (vec-of (A 1))))\
                       ((Done ())) :name \"observe-refresh\")\
                     (run 1)\
                     (check (Done ()))",
                )
                .unwrap();

            egraph
                .with_trace_view(|view| {
                    let observed = (1..=view.totals().firings)
                        .find_map(|raw| {
                            view.firing(core_relations::FiringId::new(raw))
                                .ok()
                                .filter(|firing| firing.rule == 1)
                        })
                        .expect("the post-refresh observer should fire");
                    let (fact, prior_fact, as_of_edges, position, equalities) = observed
                        .premises
                        .iter()
                        .find_map(|fact| {
                            let record = view.fact(*fact).ok()?;
                            let core_relations::CauseRef::Cause(cause) = record.cause else {
                                return None;
                            };
                            match view.cause(cause).ok()? {
                                core_relations::RawCause::ContainerRefresh {
                                    prior_fact,
                                    as_of_edges,
                                    position,
                                    equalities,
                                    ..
                                } => Some((
                                    *fact,
                                    prior_fact,
                                    as_of_edges,
                                    position,
                                    equalities.to_vec(),
                                )),
                                _ => None,
                            }
                        })
                        .expect(
                            "the successful check should cite a refreshed immutable parent fact",
                        );
                    assert_ne!(fact, prior_fact);
                    assert_eq!(view.fact(prior_fact)?.table, view.fact(fact)?.table);
                    assert!(!equalities.is_empty());
                    for pair in &equalities {
                        assert!(
                            !view
                                .explain_raw_equality_support_at(
                                    core_relations::RawEqualityEndpoint {
                                        sort: pair.left.sort,
                                        raw: pair.left.raw
                                    },
                                    core_relations::RawEqualityEndpoint {
                                        sort: pair.right.sort,
                                        raw: pair.right.raw
                                    },
                                    as_of_edges,
                                    position
                                )?
                                .applied
                                .is_empty()
                        );
                    }
                    Ok(())
                })
                .unwrap();
        });
    }

    #[test]
    fn trace_chain_two_stable_vec_refreshes() {
        serial_trace_pool().install(|| {
            let mut egraph = EGraph::default();
            egraph.enable_trace().unwrap();
            egraph
                .parse_and_run_program(
                    None,
                    "(datatype Expr (A i64) (B i64) (C i64))\
                     (sort Exprs (Vec Expr))\
                     (function Hold (Unit) Exprs :no-merge)\
                     (relation First (Unit))\
                     (let $a (A 1))\
                     (let $b (B 2))\
                     (First ())\
                     (rule ((First u))\
                       ((set (Hold ()) (vec-of (C 3)))\
                        (union (B 2) (C 3))) :name \"first-refresh\")\
                     (run 1)",
                )
                .unwrap();
            egraph
                .parse_and_run_program(
                    None,
                    "(relation Second (Unit))\
                     (Second ())\
                     (rule ((Second u))\
                       ((union (A 1) (B 2))) :name \"second-refresh\")\
                     (run 1)",
                )
                .unwrap();
            egraph
                .parse_and_run_program(
                    None,
                    "(relation Done (Unit))\
                     (rule ((= v (Hold ()))\
                            (= v (vec-of (A 1))))\
                       ((Done ())) :name \"observe-refresh-chain\")\
                     (run 1)\
                     (check (Done ()))",
                )
                .unwrap();

            egraph
                .with_trace_view(|view| {
                    let mut chain = None;
                    for raw in 1..=view.totals().facts {
                        let latest = view.fact(core_relations::FactId::new(raw))?;
                        let core_relations::CauseRef::Cause(latest_cause) = latest.cause else {
                            continue;
                        };
                        let core_relations::RawCause::ContainerRefresh {
                            wave: latest_wave,
                            prior_fact: middle,
                            as_of_edges: latest_edges,
                            position: latest_position,
                            equalities: latest_pairs,
                        } = view.cause(latest_cause)?
                        else {
                            continue;
                        };
                        let middle_record = view.fact(middle)?;
                        let core_relations::CauseRef::Cause(middle_cause) = middle_record.cause
                        else {
                            continue;
                        };
                        let core_relations::RawCause::ContainerRefresh {
                            wave: middle_wave,
                            prior_fact: original,
                            as_of_edges: middle_edges,
                            position: middle_position,
                            equalities: middle_pairs,
                        } = view.cause(middle_cause)?
                        else {
                            continue;
                        };
                        chain = Some((
                            latest.id,
                            middle,
                            original,
                            latest_wave,
                            middle_wave,
                            (latest_edges, latest_position, latest_pairs.to_vec()),
                            (middle_edges, middle_position, middle_pairs.to_vec()),
                        ));
                        break;
                    }
                    let (
                        latest,
                        middle,
                        original,
                        latest_wave,
                        middle_wave,
                        latest_landmark,
                        middle_landmark,
                    ) = chain.expect("latest Vec fact should point to a prior refreshed fact");
                    assert_ne!(latest, middle);
                    assert_ne!(middle, original);
                    assert!(middle_wave < latest_wave);
                    assert_ne!(middle_landmark.0, latest_landmark.0);
                    for landmark in [middle_landmark, latest_landmark] {
                        for pair in &landmark.2 {
                            assert!(
                                !view
                                    .explain_raw_equality_support_at(
                                        core_relations::RawEqualityEndpoint {
                                            sort: pair.left.sort,
                                            raw: pair.left.raw
                                        },
                                        core_relations::RawEqualityEndpoint {
                                            sort: pair.right.sort,
                                            raw: pair.right.raw
                                        },
                                        landmark.0,
                                        landmark.1
                                    )?
                                    .applied
                                    .is_empty()
                            );
                        }
                    }
                    Ok(())
                })
                .unwrap();
        });
    }

    #[test]
    fn trace_refresh_nested_vec_parent_fact() {
        serial_trace_pool().install(|| {
            let mut egraph = EGraph::default();
            egraph.enable_trace().unwrap();
            egraph
                .parse_and_run_program(
                    None,
                    "(sort E)\
                     (sort VE (Vec E))\
                     (sort VVE (Vec VE))\
                     (constructor b () E)\
                     (constructor w (E) E)\
                     (constructor p (VVE) E)\
                     (rewrite (w x) x)\
                     (rewrite (p (vec-of (vec-of (b)))) (b))\
                     (let $nested (p (vec-of (vec-of (w (b))))))\
                     (run-schedule (saturate (run)))\
                     (check (= $nested (b)))",
                )
                .unwrap();

            let p = egraph.capture_catalog.as_ref().unwrap().op_ids[&ReplayOpKey {
                name: "p".into(),
                inputs: vec!["VVE".into()],
                output: "E".into(),
            }];
            egraph.with_trace_view(|view| {
            let mut parent = None;
            for raw in 1..=view.totals().facts {
                let fact = view.fact(core_relations::FactId::new(raw))?;
                let core_relations::CauseRef::Cause(cause) = fact.cause else { continue };
                let core_relations::RawCause::ContainerRefresh { as_of_edges, position, equalities, .. } = view.cause(cause)? else { continue };
                let terms = view.fact_terms(fact.id)?;
                if terms.iter().any(|term| matches!(egraph.replay_term(*term).unwrap(), Some(ReplayTerm::Call { op, .. }) if op == p)) {
                    parent = Some((as_of_edges, position, equalities.to_vec()));
                    break;
                }
            }
            let (as_of_edges, position, equalities) = parent.expect("the outer p fact should receive an exact nested-container refresh");
            assert!(!equalities.is_empty());
            for pair in &equalities {
                assert!(
                    !view.explain_raw_equality_support_at(
                        core_relations::RawEqualityEndpoint { sort: pair.left.sort, raw: pair.left.raw },
                        core_relations::RawEqualityEndpoint { sort: pair.right.sort, raw: pair.right.raw },
                        as_of_edges, position)?.applied.is_empty()
                );
            }
            Ok(())
            }).unwrap();
        });
    }

    #[test]
    fn trace_fail_closed_on_unsupported_container_rebuild() {
        serial_trace_pool().install(|| {
            let mut egraph = EGraph::default();
            egraph.enable_trace().unwrap();
            let error = egraph
                .parse_and_run_program(
                    None,
                    "(datatype Expr (A i64) (B i64))\
                     (sort Exprs (Set Expr))\
                     (datatype Root (Hold Exprs))\
                     (relation Go (Unit))\
                     (Go ())\
                     (rule ((Go u))\
                       ((Hold (set-of (A 1)))\
                        (Hold (set-of (B 2)))\
                        (union (A 1) (B 2))) :name \"merge-child\")\
                     (run 1)",
                )
                .expect_err("unsupported Set rebuild unexpectedly succeeded");
            assert!(
                error.to_string().contains("SetContainer"),
                "unexpected container-rebuild error: {error}"
            );
        });
    }

    #[test]
    fn trace_container_rebuild_restores_registry_on_error() {
        serial_trace_pool().install(|| {
            let mut egraph = EGraph::default();
            egraph.enable_trace().unwrap();
            egraph
                .parse_and_run_program(
                    None,
                    "(datatype Expr (A i64) (Wrap Expr))\
                     (sort ExprVec (Vec Expr))\
                     (sort ExprSet (Set Expr))\
                     (relation Go (Unit))\
                     (let $low-vec (vec-of (Wrap (A 1))))\
                     (let $high-vec (vec-of (A 1)))\
                     (let $bad-set (set-of (Wrap (A 1))))\
                     (Go ())",
                )
                .unwrap();
            let low_vec = get_value(&egraph, "$low-vec");
            let high_vec = get_value(&egraph, "$high-vec");
            let bad_set = get_value(&egraph, "$bad-set");
            let low_before = egraph
                .value_to_container::<VecContainer>(low_vec)
                .expect("low Vec must exist before the rejected rebuild")
                .clone();
            let high_before = egraph
                .value_to_container::<VecContainer>(high_vec)
                .expect("high Vec must exist before the rejected rebuild")
                .clone();
            let set_before = egraph
                .value_to_container::<SetContainer>(bad_set)
                .expect("Set must exist before the rejected rebuild")
                .clone();
            let term_state_before = egraph.replay_term_counters().unwrap();

            let failed = egraph
                .parse_and_run_program(
                    None,
                    "(rule ((Go u))\
                       ((union (Wrap (A 1)) (A 1))) :name \"merge-child\")\
                     (run 1)",
                )
                .expect_err("unsupported Set rebuild unexpectedly succeeded");
            let message = failed.to_string();
            assert!(
                message.contains("SetContainer"),
                "unexpected container-rebuild error: {message}"
            );

            let low_after = egraph
                .value_to_container::<VecContainer>(low_vec)
                .expect("caught rebuild panic dropped the low Vec")
                .clone();
            let high_after = egraph
                .value_to_container::<VecContainer>(high_vec)
                .expect("caught rebuild panic dropped the high Vec")
                .clone();
            let set_after = egraph
                .value_to_container::<SetContainer>(bad_set)
                .expect("caught rebuild panic dropped the Set")
                .clone();
            assert_eq!(low_after, low_before);
            assert_eq!(high_after, high_before);
            assert_eq!(set_after, set_before);
            assert_eq!(
                egraph.replay_term_counters().unwrap(),
                term_state_before,
                "rejected rebuild published anchors, first-wins mappings, or term nodes"
            );
            assert!(
                egraph
                    .with_trace_view(|_| Ok(()))
                    .unwrap_err()
                    .to_string()
                    .contains("poisoned"),
                "an unwound native command cannot be retried against the same trace capture"
            );
        });
    }

    #[test]
    fn trace_fail_closed_on_unsupported_container_ancestor() {
        serial_trace_pool().install(|| {
            let mut egraph = EGraph::default();
            egraph.enable_trace().unwrap();
            let error = egraph
                .parse_and_run_program(
                    None,
                    "(datatype Expr (A i64) (B i64))\
                     (sort Exprs (Vec Expr))\
                     (sort ExprSets (Set Exprs))\
                     (function Hold (Unit) ExprSets :no-merge)\
                     (relation Go (Unit))\
                     (let $a (A 1))\
                     (Go ())\
                     (rule ((Go u))\
                       ((set (Hold ()) (set-of (vec-of (B 2))))\
                        (union (A 1) (B 2))) :name \"merge-child\")\
                     (run 1)",
                )
                .expect_err("unsupported Set ancestor unexpectedly succeeded");
            assert!(
                error.to_string().contains("SetContainer"),
                "unexpected container-ancestor error: {error}"
            );
        });
    }

    #[test]
    fn trace_capture_exact_rule_premise_and_wave() {
        let mut egraph = EGraph::default();
        enable_serial_trace(&mut egraph).unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(datatype Node (N i64 i64))\
                 (relation Input (i64 i64))\
                 (relation Seen (Node))\
                 (Input 3 7)\
                 (rule ((Input y x) (= x 7)) ((Seen (N y x))) :name \"derive\")\
                 (run 1)\
                 (check (Seen (N 3 7)))",
            )
            .unwrap();

        egraph
            .with_trace_view(|view| {
                let firing = view.firing(core_relations::FiringId::new(1))?;
                assert_eq!(firing.rule, 0);
                assert_eq!(firing.wave.get(), 1);
                assert_eq!(firing.premises.len(), 1);
                let terms = view.firing_terms(firing.id)?;
                assert_eq!(terms.len(), 2);
                assert_eq!(
                    egraph.replay_term(terms[0]).unwrap(),
                    Some(ReplayTerm::Literal {
                        sort: egraph.capture_catalog.as_ref().unwrap().sort_ids["i64"],
                        literal: ReplayLiteral::I64(3),
                    })
                );
                assert_eq!(
                    egraph.replay_term(terms[1]).unwrap(),
                    Some(ReplayTerm::Literal {
                        sort: egraph.capture_catalog.as_ref().unwrap().sort_ids["i64"],
                        literal: ReplayLiteral::I64(7),
                    })
                );
                let cataloged_rule = &egraph.capture_catalog.as_ref().unwrap().rule_catalog[0];
                assert_eq!(cataloged_rule.ruleset, "");
                assert_eq!(cataloged_rule.replay_name, "derive");
                assert_eq!(
                    cataloged_rule
                        .variables
                        .iter()
                        .map(|variable| (
                            variable.name.as_str(),
                            variable.sort.as_str(),
                            variable.role.clone()
                        ))
                        .collect::<Vec<_>>(),
                    vec![
                        ("y", "i64", RuleBindingRole::SurfaceVar),
                        ("x", "i64", RuleBindingRole::SurfaceVar),
                    ]
                );
                let premise = view.fact(firing.premises[0])?;
                let core_relations::CauseRef::Cause(source) = premise.cause else {
                    panic!("premise lost source cause")
                };
                assert!(matches!(
                    view.cause(source)?,
                    core_relations::RawCause::Source(_)
                ));
                for raw in 1..=view.totals().facts {
                    if let core_relations::CauseRef::Rule(id) =
                        view.fact(core_relations::FactId::new(raw))?.cause
                    {
                        assert_eq!(id, firing.id);
                    }
                }
                let root = view.check_root(0)?;
                assert_eq!(root.check, 0);
                assert_eq!(root.wave.get(), 1);
                assert!(!root.premises.is_empty());
                assert!(root.equalities.is_empty());
                Ok(())
            })
            .unwrap();
    }

    #[test]
    fn trace_preserve_distinct_check_equality_terms() {
        let mut egraph = EGraph::default();
        enable_serial_trace(&mut egraph).unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(datatype Expr (A i64) (B i64))\
                 (relation Go (Unit))\
                 (let $lhs (A 1))\
                 (Go ())\
                 (rule ((Go u)) ((union (A 1) (B 2))) :name \"merge\")\
                 (run 1)\
                 (check (= $lhs (B 2)))",
            )
            .unwrap();

        egraph
            .with_trace_view(|view| {
                let root = view.check_root(0)?;
                assert_eq!(root.premises.len(), 2);
                assert_eq!(root.equalities.len(), 1);
                let (left, right) = root.equalities[0];
                assert_eq!(left.sort, right.sort);
                assert_ne!(
                    left.raw, right.raw,
                    "the check root preserves each premise's immutable creation occurrence"
                );
                assert_ne!(left.term, right.term);

                let state = egraph.capture_catalog.as_ref().unwrap();
                let a = state.op_ids[&ReplayOpKey {
                    name: "A".into(),
                    inputs: vec!["i64".into()],
                    output: "Expr".into(),
                }];
                let b = state.op_ids[&ReplayOpKey {
                    name: "B".into(),
                    inputs: vec!["i64".into()],
                    output: "Expr".into(),
                }];
                assert!(matches!(
                    egraph.replay_term(left.term).unwrap(),
                    Some(ReplayTerm::Call { op, .. }) if op == a
                ));
                assert!(matches!(
                    egraph.replay_term(right.term).unwrap(),
                    Some(ReplayTerm::Call { op, .. }) if op == b
                ));
                let explanation =
                    view.explain_equality_support_at(left, right, root.as_of_edges, root.position)?;
                assert_eq!(
                    explanation.applied.as_ref(),
                    [core_relations::AppliedEqualityId::new(1)]
                );
                assert!(matches!(
                    view.applied_equality(core_relations::AppliedEqualityId::new(1))?.reason,
                    core_relations::EqualityReason::RuleUnion(rule) if view.firing(rule)?.rule == 0
                ));
                Ok(())
            })
            .unwrap();
    }

    #[test]
    fn trace_waves_are_cumulative_across_run_commands() {
        let mut egraph = EGraph::default();
        enable_serial_trace(&mut egraph).unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(datatype Node (N i64))\
                 (relation Seed (i64))\
                 (relation Seen (Node))\
                 (rule ((Seed x)) ((Seen (N x))) :name \"derive\")\
                 (Seed 7)\
                 (run 1)\
                 (Seed 8)\
                 (run 1)",
            )
            .unwrap();

        egraph
            .with_trace_view(|view| {
                let waves = (1..=view.totals().firings)
                    .filter_map(|raw| view.firing(core_relations::FiringId::new(raw)).ok())
                    .filter(|firing| firing.rule == 0)
                    .map(|firing| firing.wave.get())
                    .collect::<Vec<_>>();
                assert_eq!(waves, [1, 2]);
                Ok(())
            })
            .unwrap();
    }

    #[test]
    fn parsed_input_digest_is_optional() {
        let directory = std::env::temp_dir().join(format!(
            "egglog-input-digest-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir_all(&directory).unwrap();
        std::fs::write(directory.join("rows.tsv"), "first\nsecond\n").unwrap();

        let mut egraph = EGraph {
            fact_directory: Some(directory.clone()),
            ..Default::default()
        };
        egraph
            .parse_and_run_program(None, "(relation R (String))")
            .unwrap();
        let function_type = egraph.type_info.get_func_type("R").unwrap();
        let uncaptured = EGraph::read_input_file(
            egraph.fact_directory.as_deref(),
            function_type,
            &Span::Panic,
            "rows.tsv",
            false,
        )
        .unwrap();
        assert_eq!(uncaptured.digest, None);

        let captured = EGraph::read_input_file(
            egraph.fact_directory.as_deref(),
            function_type,
            &Span::Panic,
            "rows.tsv",
            true,
        )
        .unwrap();
        let expected: [u8; 32] = Sha256::digest(b"first\nsecond\n").into();
        assert_eq!(captured.digest, Some(expected));
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn trace_batch_tsv_rows_with_exact_physical_sources() {
        let directory = std::env::temp_dir().join(format!(
            "egglog-trace-input-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir_all(&directory).unwrap();
        std::fs::write(directory.join("leaf.tsv"), "7\n7\n9\n").unwrap();
        std::fs::write(directory.join("edge.tsv"), "1\t2\n").unwrap();
        std::fs::write(directory.join("score.tsv"), "1\t10\n").unwrap();

        let mut egraph = EGraph {
            fact_directory: Some(directory.clone()),
            ..Default::default()
        };
        enable_serial_trace(&mut egraph).unwrap();
        let result = egraph.parse_and_run_program(
            None,
            r#"
                (datatype Node (Leaf i64))
                (relation Edge (i64 i64))
                (function Score (i64) i64 :merge old)
                (relation SeenScore (i64))
                (input Leaf "leaf.tsv")
                (input Edge "edge.tsv")
                (input Score "score.tsv")
                (rule ((= value (Score 1))) ((SeenScore value)))
                (run 1)
                (check (Edge 1 2))
                (check (SeenScore 10))
            "#,
        );
        result.unwrap();

        std::fs::write(directory.join("bad.tsv"), "1\nnot-an-integer\n").unwrap();
        let mut rejected = EGraph {
            fact_directory: Some(directory.clone()),
            ..Default::default()
        };
        enable_serial_trace(&mut rejected).unwrap();
        let error = rejected
            .parse_and_run_program(
                None,
                "(datatype BadNode (BadLeaf i64)) (input BadLeaf \"bad.tsv\")",
            )
            .unwrap_err();
        assert!(matches!(error, Error::InputFileFormatError(_)));
        assert!(
            rejected
                .with_trace_view(|_| Ok(()))
                .unwrap_err()
                .to_string()
                .contains("poisoned"),
            "a command that fails after entering trace execution must make the capture unusable instead of reusing reserved identities"
        );
        std::fs::remove_dir_all(&directory).ok();

        egraph
            .with_trace_view(|view| {
                let mut source_facts = Vec::new();
                for raw in 1..=view.totals().facts {
                    let fact = view.fact(core_relations::FactId::new(raw))?;
                    let core_relations::CauseRef::Cause(cause) = fact.cause else {
                        continue;
                    };
                    if let core_relations::RawCause::Source(source) = view.cause(cause)? {
                        source_facts.push((source.clone(), fact.id));
                    }
                }
                assert_eq!(source_facts.len(), 4);
                for expected in [
                    SourceRef::InputRow {
                        command: 0,
                        line: 1,
                    },
                    SourceRef::InputRow {
                        command: 0,
                        line: 3,
                    },
                    SourceRef::InputRow {
                        command: 1,
                        line: 1,
                    },
                    SourceRef::InputRow {
                        command: 2,
                        line: 1,
                    },
                ] {
                    assert!(source_facts.iter().any(|(source, _)| *source == expected));
                }
                assert!(!source_facts.iter().any(|(source, _)| {
                    *source
                        == SourceRef::InputRow {
                            command: 0,
                            line: 2,
                        }
                }));
                for (_, fact) in source_facts
                    .iter()
                    .filter(|(source, _)| matches!(source, SourceRef::InputRow { command: 0, .. }))
                {
                    assert!(view.fact_terms(*fact)?.iter().copied().any(|term| {
                        !term.is_missing()
                            && matches!(
                                egraph.replay_term(term).unwrap(),
                                Some(ReplayTerm::Call { .. })
                            )
                    }));
                }
                Ok(())
            })
            .unwrap();
    }

    #[test]
    fn capture_catalog_tracks_expanded_order_and_anonymous_rule_identity() {
        let mut egraph = EGraph::default();
        enable_serial_trace(&mut egraph).unwrap();
        egraph
            .parse_and_run_program(
                None,
                r#"
                    (datatype Expr (Num i64))
                    (let $seed (Num 1))
                    (relation Seen (i64))
                    (Seen 1)
                    (rule ((Seen x)) ((Seen x)))
                    (run 1)
                    (check (Seen 1))
                "#,
            )
            .unwrap();

        let catalog = egraph.capture_catalog.as_ref().unwrap();
        let commands = catalog
            .command_catalog
            .iter()
            .map(|entry| entry.command.to_string())
            .collect::<Vec<_>>();
        assert!(
            commands
                .windows(2)
                .any(|pair| pair[0].starts_with("(sort Expr")
                    && pair[1].starts_with("(constructor Num")),
            "datatype expansion must be cataloged in execution order: {commands:#?}"
        );
        let datatype_surface = catalog
            .command_catalog
            .iter()
            .filter(|entry| {
                matches!(
                    &entry.command,
                    Command::Sort { name, .. } if name == "Expr"
                ) || matches!(
                    &entry.command,
                    Command::Constructor { name, .. } if name == "Num"
                )
            })
            .map(|entry| entry.surface_command)
            .collect::<HashSet<_>>();
        assert_eq!(datatype_surface.len(), 1);
        let datatype_surface = *datatype_surface.iter().next().unwrap();
        assert!(matches!(
            catalog.surface_command_catalog[datatype_surface],
            Some(Command::Datatype { .. })
        ));
        let global_entries = catalog
            .command_catalog
            .iter()
            .filter(|entry| {
                matches!(
                    &entry.command,
                    Command::Function { name, .. } if name == "$seed"
                ) || entry.command.to_string().starts_with("(set ($seed)")
            })
            .collect::<Vec<_>>();
        assert_eq!(global_entries.len(), 2);
        assert_eq!(
            global_entries[0].surface_command,
            global_entries[1].surface_command
        );
        assert!(matches!(
            catalog.surface_command_catalog[global_entries[0].surface_command],
            Some(Command::Action(Action::Let(..)))
        ));
        assert_eq!(catalog.rule_catalog.len(), 1);
        let generated_name = format!(
            "__slice_replay_rule_s{}",
            catalog.command_catalog[catalog.rule_catalog[0].command].surface_command
        );
        assert_eq!(catalog.rule_catalog[0].replay_name, generated_name);
        let rule_command = &catalog.command_catalog[catalog.rule_catalog[0].command].command;
        let Command::Rule { rule } = rule_command else {
            panic!("cataloged captured rule is not a normalized rule: {rule_command}")
        };
        assert_eq!(rule.name, generated_name);
        assert!(
            catalog
                .source_commands
                .contains_key(&SourceRef::Synthetic(0))
        );
        assert!(
            catalog
                .source_commands
                .contains_key(&SourceRef::Synthetic(1))
        );
        assert!(catalog.check_commands.contains_key(&0));
    }

    #[test]
    fn capture_catalog_detects_generated_rule_name_collision() {
        let mut egraph = EGraph::default();
        enable_serial_trace(&mut egraph).unwrap();
        egraph
            .parse_and_run_program(
                None,
                r#"
                    (relation R (i64))
                    (rule ((R x)) ((R x)))
                "#,
            )
            .unwrap();
        let generated_name = egraph.capture_catalog.as_ref().unwrap().rule_catalog[0]
            .replay_name
            .clone();
        egraph
            .parse_and_run_program(
                None,
                &format!(r#"(rule ((R x)) ((R x)) :name "{generated_name}")"#),
            )
            .unwrap();
        let error = egraph
            .capture_catalog
            .as_ref()
            .unwrap()
            .validate_replay_rule_names()
            .unwrap_err();
        assert!(error.contains("collides between rule ordinals 0 and 1"));
    }

    #[test]
    fn capture_catalog_rejects_stateful_command_boundaries_before_mutation() {
        let mut egraph = EGraph::default();
        enable_serial_trace(&mut egraph).unwrap();
        let push = egraph.parse_and_run_program(None, "(push)").unwrap_err();
        assert!(push.to_string().contains("does not support push/pop"));
        assert!(egraph.pushed_egraph.is_none());

        let catalog_len = egraph
            .capture_catalog
            .as_ref()
            .unwrap()
            .command_catalog
            .len();
        let nested = egraph
            .parse_and_run_program(None, "(fail (let $causal_leak 1))")
            .unwrap_err();
        assert!(nested.to_string().contains("nested fail commands"));
        assert_eq!(
            egraph
                .capture_catalog
                .as_ref()
                .unwrap()
                .command_catalog
                .len(),
            catalog_len,
            "fail must be rejected before global lowering can lift a declaration"
        );
        assert!(
            egraph
                .get_function_names()
                .iter()
                .all(|name| !name.contains("causal_leak"))
        );
        let datatype = egraph
            .parse_and_run_program(None, "(fail (datatype CausalLeaked (CausalLeak)))")
            .unwrap_err();
        assert!(datatype.to_string().contains("nested fail commands"));
        assert!(egraph.get_sort_by_name("CausalLeaked").is_none());
        assert!(
            !egraph
                .get_function_names()
                .iter()
                .any(|name| name == "CausalLeak")
        );
        let resolve = egraph
            .resolve_program(None, "(relation CausalHidden (i64))")
            .unwrap_err();
        assert!(resolve.to_string().contains("resolve_program"));
        assert!(egraph.get_function("CausalHidden").is_none());
        let sort = egraph
            .declare_sort("CausalDirectSort", &None, span!())
            .unwrap_err();
        assert!(sort.to_string().contains("registration after capture"));
        assert!(egraph.get_sort_by_name("CausalDirectSort").is_none());
        assert!(egraph.with_trace_view(|_| Ok(())).is_ok());

        let mut proof = EGraph::new_with_proofs();
        let proof_error = enable_serial_trace(&mut proof).unwrap_err();
        assert!(
            proof_error
                .to_string()
                .contains("ordinary, non-proof graph")
        );
    }

    #[test]
    fn trace_user_command_authority_is_not_granted_by_name() {
        struct Impostor(std::sync::Arc<std::sync::atomic::AtomicBool>);

        impl UserDefinedCommand for Impostor {
            fn update(
                &self,
                _egraph: &mut EGraph,
                _args: &[Expr],
            ) -> Result<Vec<CommandOutput>, Error> {
                self.0.store(true, std::sync::atomic::Ordering::SeqCst);
                Ok(Vec::new())
            }
        }

        let called = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
        let mut egraph = EGraph::default();
        egraph
            .add_command(
                "run-schedule".into(),
                std::sync::Arc::new(Impostor(called.clone())),
            )
            .unwrap();
        enable_serial_trace(&mut egraph).unwrap();
        let error = egraph
            .parse_and_run_program(None, "(run-schedule safe-looking-ruleset)")
            .unwrap_err();
        assert!(error.to_string().contains("does not support user-defined"));
        assert!(!called.load(std::sync::atomic::Ordering::SeqCst));
        assert!(
            egraph
                .with_trace_view(|_| Ok(()))
                .unwrap_err()
                .to_string()
                .contains("poisoned")
        );
    }

    #[test]
    fn trace_direct_mutation_apis_fail_before_effects() {
        struct Noop(std::sync::Arc<std::sync::atomic::AtomicBool>);

        impl UserDefinedCommand for Noop {
            fn update(
                &self,
                _egraph: &mut EGraph,
                _args: &[Expr],
            ) -> Result<Vec<CommandOutput>, Error> {
                self.0.store(true, std::sync::atomic::Ordering::SeqCst);
                Ok(Vec::new())
            }
        }

        let command_called = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
        let update_called = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
        let mut egraph = EGraph::default();
        egraph
            .add_command(
                "causal-noop".into(),
                std::sync::Arc::new(Noop(command_called.clone())),
            )
            .unwrap();
        enable_serial_trace(&mut egraph).unwrap();
        egraph
            .parse_and_run_program(None, "(relation R (i64)) (ruleset rs)")
            .unwrap();

        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| egraph.push())).is_err());
        assert!(egraph.pushed_egraph.is_none());
        assert!(
            egraph
                .pop()
                .unwrap_err()
                .to_string()
                .contains("EGraph::pop")
        );
        assert!(
            egraph
                .step_rules("rs")
                .unwrap_err()
                .to_string()
                .contains("cataloged schedule")
        );
        assert!(
            egraph
                .clear_function("R")
                .unwrap_err()
                .to_string()
                .contains("clear_function")
        );
        assert!(
            egraph
                .eval_expr(&Expr::Lit(span!(), Literal::Int(1)))
                .unwrap_err()
                .to_string()
                .contains("eval_expr")
        );
        assert!(
            egraph
                .run_user_defined_command("causal-noop", &[])
                .unwrap_err()
                .to_string()
                .contains("direct user-defined")
        );
        assert!(!command_called.load(std::sync::atomic::Ordering::SeqCst));
        let update_called_in_closure = update_called.clone();
        assert!(
            egraph
                .update(move |_state| {
                    update_called_in_closure.store(true, std::sync::atomic::Ordering::SeqCst);
                    Ok(())
                })
                .unwrap_err()
                .to_string()
                .contains("EGraph::update")
        );
        assert!(!update_called.load(std::sync::atomic::Ordering::SeqCst));
        assert!(
            egraph
                .query(&[], ast::Facts(Vec::new()))
                .unwrap_err()
                .to_string()
                .contains("EGraph::query")
        );
        assert_eq!(egraph.get_size("R"), 0);
        assert!(egraph.with_trace_view(|_| Ok(())).is_ok());
    }

    #[test]
    fn trace_wave_spans_multiple_native_rebuild_timestamps() {
        let mut egraph = EGraph::default();
        enable_serial_trace(&mut egraph).unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(datatype Expr (A) (B) (F Expr) (G Expr))\
                 (relation Go (Unit))\
                 (let $ga (G (F (A))))\
                 (let $gb (G (F (B))))\
                 (Go ())\
                 (rule ((Go u)) ((union (A) (B))) :name \"merge-leaves\")\
                 (run 1)\
                 (check (= $ga $gb))",
            )
            .unwrap();

        egraph
            .with_trace_view(|view| {
                assert!(view.totals().applied_equalities >= 3);
                for raw in 1..=view.totals().applied_equalities {
                    assert_eq!(
                        view.applied_equality(core_relations::AppliedEqualityId::new(raw))?
                            .wave
                            .get(),
                        1,
                        "direct and multi-pass congruence edges belong to one replay wave"
                    );
                }
                Ok(())
            })
            .unwrap();
    }

    #[test]
    fn trace_reject_late_rule_activation_without_switching_modes() {
        let mut egraph = EGraph::default();
        egraph
            .parse_and_run_program(
                None,
                "(relation A (i64)) (relation B (i64))\
                 (rule ((A x)) ((B x)))",
            )
            .unwrap();

        let error = enable_serial_trace(&mut egraph).unwrap_err();
        assert!(error.to_string().contains("replay catalog is complete"));
        egraph
            .parse_and_run_program(None, "(A 1) (run 1) (check (B 1))")
            .unwrap();
    }

    #[test]
    fn query_error_restores_named_rule_metadata() {
        let mut egraph = EGraph::new_with_term_encoding();
        egraph
            .parse_and_run_program(None, "(relation R (i64)) (R 1)")
            .unwrap();
        let main_checkpoint = egraph.type_info.named_rule_checkpoint();
        let original_checkpoint = egraph
            .proof_state
            .original_typechecking
            .as_ref()
            .unwrap()
            .type_info
            .named_rule_checkpoint();

        egraph
            .query(crate::vars![x: i64], crate::facts![(R x)])
            .unwrap_err();

        assert_eq!(egraph.type_info.named_rule_checkpoint(), main_checkpoint);
        assert_eq!(
            egraph
                .proof_state
                .original_typechecking
                .as_ref()
                .unwrap()
                .type_info
                .named_rule_checkpoint(),
            original_checkpoint
        );
    }

    #[derive(Clone)]
    struct InnerProduct {
        vec: ArcSort,
    }

    // `InnerProduct` is pure, so it declares
    // `State = PureState` and is usable in all
    // contexts. The Rust type checker enforces that the body only uses
    // methods available on `PureState`.
    impl Primitive for InnerProduct {
        fn name(&self) -> &str {
            "inner-product"
        }

        fn get_type_constraints(&self, span: &Span) -> Box<dyn crate::constraint::TypeConstraint> {
            SimpleTypeConstraint::new(
                self.name(),
                vec![self.vec.clone(), self.vec.clone(), I64Sort.to_arcsort()],
                span.clone(),
            )
            .into_box()
        }
    }

    impl PurePrim for InnerProduct {
        fn apply<'a, 'db>(&self, state: PureState<'a, 'db>, args: &[Value]) -> Option<Value> {
            let mut sum = 0;
            let vec1 = state
                .container_values()
                .get_val::<VecContainer>(args[0])
                .unwrap();
            let vec2 = state
                .container_values()
                .get_val::<VecContainer>(args[1])
                .unwrap();
            assert_eq!(vec1.data.len(), vec2.data.len());
            for (a, b) in vec1.data.iter().zip(vec2.data.iter()) {
                let a = state.base_values().unwrap::<i64>(*a);
                let b = state.base_values().unwrap::<i64>(*b);
                sum += a * b;
            }
            Some(state.base_values().get::<i64>(sum))
        }
    }

    #[derive(Clone)]
    struct FullOnly;

    impl Primitive for FullOnly {
        fn name(&self) -> &str {
            "full-only"
        }

        fn get_type_constraints(&self, span: &Span) -> Box<dyn crate::constraint::TypeConstraint> {
            SimpleTypeConstraint::new(self.name(), vec![I64Sort.to_arcsort()], span.clone())
                .into_box()
        }
    }

    impl FullPrim for FullOnly {
        fn apply<'a, 'db>(&self, state: FullState<'a, 'db>, _args: &[Value]) -> Option<Value> {
            Some(state.base_values().get::<i64>(1))
        }
    }

    #[test]
    fn unstable_fn_resolution_error_releases_panic_registration() {
        let mut egraph = EGraph::default();
        egraph
            .parse_and_run_program(None, "(sort Fn (UnstableFn (i64) i64))")
            .unwrap();
        let register_probe = |egraph: &mut EGraph| {
            egraph
                .backend
                .register_external_func(Box::new(core_relations::make_external_func(
                    |_state: &mut core_relations::ExecutionState<'_>, _args: &[Value]| None,
                )))
        };
        let error = egraph
            .parse_and_run_program(None, "(let $first (unstable-fn \"missing\"))")
            .expect_err("missing unstable-fn target should return an error");
        assert!(error.to_string().contains("No resolution for \"missing\""));
        let reused = register_probe(&mut egraph);
        egraph.backend.free_external_func(reused);

        let message = "unstable-fn over `missing` was applied in a context where its wrapped \
                       function is not valid for this call site, if in a rule, add :naive."
            .to_string();
        let shared = egraph.backend.new_panic(message);
        assert_eq!(shared, reused);
        let error = egraph
            .parse_and_run_program(None, "(let $second (unstable-fn \"missing\"))")
            .expect_err("missing unstable-fn target should return an error");
        assert!(error.to_string().contains("No resolution for \"missing\""));
        let occupied = register_probe(&mut egraph);
        assert_ne!(occupied, shared);
        egraph.backend.free_external_func(shared);
        assert_eq!(register_probe(&mut egraph), shared);
    }

    #[test]
    fn unstable_fn_panic_cache_is_persistent_and_bounded_across_rule_specialization() {
        let mut egraph = EGraph::default();
        egraph
            .parse_and_run_program(
                None,
                r#"
                (ruleset owned)
                (sort Fn (UnstableFn (i64) i64))
                (function id (i64) i64 :merge old)
                (function slot () Fn :merge old)
                (rule ()
                    ((set (slot) (unstable-fn "id")))
                    :ruleset owned
                    :name "owns-panic")
                "#,
            )
            .unwrap();

        let panic_id = egraph.unstable_fn_panic_ids["id"];
        assert_eq!(egraph.unstable_fn_panic_ids.len(), 1);

        // Temporary naive specializations reuse the EGraph-lifetime callback;
        // they neither grow the cache nor take rule-owned references.
        for _ in 0..3 {
            egraph
                .parse_and_run_program(None, r#"(run-schedule (run-rule ("owns-panic" ())))"#)
                .unwrap();
            assert_eq!(egraph.unstable_fn_panic_ids.len(), 1);
            assert_eq!(egraph.unstable_fn_panic_ids["id"], panic_id);
        }

        // Freeing the source rule must not invalidate FunctionContainer values
        // already stored in the e-graph.
        let permanent_rule = match &egraph.rulesets["owned"] {
            Ruleset::Rules(rules) => rules["owns-panic"].backend_id,
            Ruleset::Combined(_) => unreachable!(),
        };
        egraph.backend.free_rule(permanent_rule);
        assert_eq!(egraph.unstable_fn_panic_ids.len(), 1);
        assert_eq!(egraph.unstable_fn_panic_ids["id"], panic_id);

        let shared = egraph.backend.new_panic(unstable_fn_panic_message("id"));
        assert_eq!(
            shared, panic_id,
            "the persistent cache must keep the embedded callback registered"
        );
        egraph.backend.free_external_func(shared);
    }

    #[test]
    fn direct_unstable_fn_preparation_uses_the_persistent_cache() {
        let mut egraph = EGraph::default();
        egraph
            .parse_and_run_program(
                None,
                r#"
                (sort Fn (UnstableFn (i64) i64))
                (function id (i64) i64 :merge old)
                "#,
            )
            .unwrap();
        let output = egraph.get_sort_by_name("Fn").unwrap().clone();
        let mut parser = crate::ast::Parser::default();

        for _ in 0..2 {
            let expr = parser
                .get_expr_from_string(None, r#"(unstable-fn "id")"#)
                .unwrap();
            let resolved = egraph
                .typecheck_expr_with_bindings_and_output(&expr, &[], output.clone(), Context::Pure)
                .unwrap();
            let (_, bindings) = egraph
                .prepare_unstable_fn_targets_for_eval(&resolved)
                .unwrap();
            assert_eq!(bindings.len(), 1);
            assert_eq!(egraph.unstable_fn_panic_ids.len(), 1);
        }

        let expr = parser
            .get_expr_from_string(None, r#"(unstable-fn "missing")"#)
            .unwrap();
        let resolved = egraph
            .typecheck_expr_with_bindings_and_output(&expr, &[], output, Context::Pure)
            .unwrap();
        let error = egraph
            .prepare_unstable_fn_targets_for_eval(&resolved)
            .unwrap_err();
        assert!(error.to_string().contains("No resolution for \"missing\""));
        assert_eq!(
            egraph.unstable_fn_panic_ids.len(),
            1,
            "failed direct preparation must not commit its pending panic"
        );
    }

    #[test]
    fn orient_proof_primitives_have_working_validators() {
        let egraph = EGraph::default();
        let validator = |name: &str| {
            egraph.type_info.get_prims(name).unwrap()[0]
                .validator
                .clone()
                .unwrap_or_else(|| panic!("primitive `{name}` has no validator"))
        };
        let mut term_dag = TermDag::default();
        let a = term_dag.var("a".to_string());
        let a_proof = term_dag.var("a-proof".to_string());
        let b = term_dag.var("b".to_string());
        let b_proof = term_dag.var("b-proof".to_string());
        let args = [a, a_proof, b, b_proof];

        assert_eq!(
            validator("proof-of-min")(&mut term_dag, &args),
            Some(a_proof)
        );
        assert_eq!(
            validator("proof-of-max")(&mut term_dag, &args),
            Some(b_proof)
        );
    }

    #[test]
    fn test_user_defined_primitive() {
        let mut egraph = EGraph::default();
        egraph
            .parse_and_run_program(None, "(sort IntVec (Vec i64))")
            .unwrap();

        let int_vec_sort = egraph.get_arcsort_by(|s| {
            s.value_type() == Some(std::any::TypeId::of::<VecContainer>())
                && s.inner_sorts()[0].name() == I64Sort.name()
        });

        egraph.add_pure_primitive(InnerProduct { vec: int_vec_sort }, None);

        egraph
            .parse_and_run_program(
                None,
                "
                (let a (vec-of 1 2 3 4 5 6))
                (let b (vec-of 6 5 4 3 2 1))
                (check (= (inner-product a b) 56))
            ",
            )
            .unwrap();
    }

    #[test]
    fn proof_support_accepts_container_sort_declarations() {
        let mut egraph = EGraph::default();
        let resolved = egraph
            .resolve_program(None, "(datatype X (x))\n(sort XPair (Pair X i64))")
            .unwrap();
        assert!(program_supports_proofs(&resolved, &egraph.type_info));

        let mut egraph = EGraph::default();
        let resolved = egraph
            .resolve_program(None, "(datatype X (x))\n(sort XFn (UnstableFn (X) X))")
            .unwrap();
        assert!(program_supports_proofs(&resolved, &egraph.type_info));
    }

    #[test]
    fn proof_support_rejects_unstable_fn_primitives_without_validators() {
        let mut egraph = EGraph::default();
        let resolved = egraph
            .resolve_program(
                None,
                r#"
                (datatype X (x))
                (sort XFn (UnstableFn (X) X))
                (function id (X) X :merge old)
                (let f (unstable-fn "id"))
                "#,
            )
            .unwrap();
        assert!(!program_supports_proofs(&resolved, &egraph.type_info));
    }

    #[test]
    fn proof_support_accepts_set_primitive_validators() {
        let mut egraph = EGraph::default();
        let resolved = egraph
            .resolve_program(
                None,
                r#"
                (sort ISet (Set i64))
                (function Shared () ISet :merge (set-intersect old new))

                (check (= (set-insert (set-empty) 1) (set-of 1)))
                (check (= (set-remove (set-of 1 2) 2) (set-of 1)))
                (check (= (set-length (set-of 1 2)) 2))
                (check (set-contains (set-of 1 2) 1))
                (check (set-not-contains (set-of 1 2) 3))
                (check (= (set-union (set-of 1) (set-of 2)) (set-of 1 2)))
                (check (= (set-diff (set-of 1 2) (set-of 2)) (set-of 1)))
                (check (= (set-intersect (set-of 1 2) (set-of 2 3)) (set-of 2)))
                "#,
            )
            .unwrap();

        assert!(program_supports_proofs(&resolved, &egraph.type_info));
    }

    /// `set-get` indexes the runtime value order, which the proof checker
    /// cannot reproduce from terms, so it has no validator.
    #[test]
    fn proof_support_rejects_set_get() {
        let mut egraph = EGraph::default();
        let resolved = egraph
            .resolve_program(
                None,
                r#"
                (sort ISet (Set i64))
                (check (= (set-get (set-of 1 2) 0) 1))
                "#,
            )
            .unwrap();

        assert!(!program_supports_proofs(&resolved, &egraph.type_info));
    }

    #[test]
    fn let_check_alias_is_a_constant_in_checks() {
        let mut egraph = EGraph::default();
        egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype E (A i64))
                (A 1)
                (A 2)
                (let-check $a (A 1))
                "#,
            )
            .unwrap();

        egraph
            .parse_and_run_program(None, "(check (= $a (A 1)))")
            .unwrap();
        let error = egraph
            .parse_and_run_program(None, "(check (= $a (A 2)))")
            .expect_err("the checked alias must not act as a free query variable");
        assert!(matches!(error, Error::CheckError(..)));
    }

    #[test]
    fn let_check_constructor_miss_is_atomic() {
        let mut egraph = EGraph::default();
        egraph
            .parse_and_run_program(None, "(datatype E (A i64))")
            .unwrap();
        let before = egraph.num_tuples();

        let error = egraph
            .parse_and_run_program(None, "(let-check $missing (A 1))")
            .unwrap_err();

        assert!(error.to_string().contains("lookup"));
        assert_eq!(egraph.num_tuples(), before);
        assert!(!egraph.checked_aliases.contains_key("$missing"));
        assert!(!egraph.checked_alias_types.contains_key("$missing"));
        assert!(!egraph.names.contains_canonical("missing"));

        // Neither the alias table nor the namespace may retain a ghost name.
        egraph.parse_and_run_program(None, "(A 1)").unwrap();
        egraph
            .parse_and_run_program(None, "(let-check $missing (A 1))")
            .unwrap();
    }

    #[test]
    fn let_check_runs_through_proof_encoding_without_fiat_rows() {
        let mut egraph = EGraph::new_with_proofs();
        egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype E (A i64))
                (A 1)
                "#,
            )
            .unwrap();
        let tuples_before = egraph.num_tuples();
        egraph
            .parse_and_run_program(None, "(let-check $a (A 1))")
            .unwrap();
        assert_eq!(egraph.num_tuples(), tuples_before);
        egraph
            .parse_and_run_program(None, "(check (= $a (A 1)))")
            .unwrap();
    }

    #[test]
    fn let_check_proof_lookup_miss_does_not_publish_proof_or_alias_state() {
        let mut egraph = EGraph::new_with_proofs();
        egraph
            .parse_and_run_program(None, "(datatype E (A i64))")
            .unwrap();
        let tuples_before = egraph.num_tuples();
        let proof_program_before = egraph.proof_check_program.len();

        let error = egraph
            .parse_and_run_program(None, "(let-check $missing (A 1))")
            .unwrap_err();

        assert!(error.to_string().contains("lookup"));
        assert_eq!(egraph.num_tuples(), tuples_before);
        assert_eq!(egraph.proof_check_program.len(), proof_program_before);
        assert!(!egraph.checked_aliases.contains_key("$missing"));
        assert!(!egraph.checked_alias_types.contains_key("$missing"));
        assert!(!egraph.names.contains_canonical("missing"));
    }

    #[test]
    fn let_check_rejects_non_pure_primitives_and_unprefixed_names() {
        let mut egraph = EGraph::default();
        egraph.add_full_primitive(FullOnly, None);
        let error = egraph
            .parse_and_run_program(None, "(let-check $effect (full-only))")
            .unwrap_err();
        assert!(error.to_string().contains("Unbound function full-only"));
        assert!(!egraph.checked_aliases.contains_key("$effect"));

        let error = egraph
            .parse_and_run_program(None, "(let-check plain 1)")
            .unwrap_err();
        assert!(matches!(
            error,
            Error::TypeError(TypeError::CheckedAliasMissingPrefix { .. })
        ));
    }

    #[test]
    fn test_typecheck_expr_with_bindings_and_output_rejects_mismatch() {
        let mut egraph = EGraph::default();
        let mut parser = crate::ast::Parser::default();
        let expr = parser.get_expr_from_string(None, "(+ 1 2)").unwrap();

        let resolved = egraph
            .typecheck_expr_with_bindings_and_output(
                &expr,
                &[],
                I64Sort.to_arcsort(),
                Context::Pure,
            )
            .unwrap();
        assert_eq!(resolved.output_type().name(), I64Sort.name());

        let err = egraph
            .typecheck_expr_with_bindings_and_output(
                &expr,
                &[],
                BoolSort.to_arcsort(),
                Context::Pure,
            )
            .unwrap_err();
        match err {
            TypeError::Mismatch {
                expected, actual, ..
            } => {
                assert_eq!(expected.name(), BoolSort.name());
                assert_eq!(actual.name(), I64Sort.name());
            }
            other => panic!("expected mismatch, got {other:?}"),
        }

        let literal = parser.get_expr_from_string(None, "1").unwrap();
        let err = egraph
            .typecheck_expr_with_bindings_and_output(
                &literal,
                &[],
                BoolSort.to_arcsort(),
                Context::Pure,
            )
            .unwrap_err();
        match err {
            TypeError::Mismatch {
                expected, actual, ..
            } => {
                assert_eq!(expected.name(), BoolSort.name());
                assert_eq!(actual.name(), I64Sort.name());
            }
            other => panic!("expected literal mismatch, got {other:?}"),
        }
    }

    #[test]
    fn test_typecheck_expr_with_bindings_and_output_uses_explicit_bindings() {
        let mut egraph = EGraph::default();
        let mut parser = crate::ast::Parser::default();
        let expr = parser.get_expr_from_string(None, "(+ x 2)").unwrap();
        let bindings = vec![("x".to_string(), span!(), I64Sort.to_arcsort())];

        let resolved = egraph
            .typecheck_expr_with_bindings_and_output(
                &expr,
                &bindings,
                I64Sort.to_arcsort(),
                Context::Pure,
            )
            .unwrap();

        assert_eq!(resolved.output_type().name(), I64Sort.name());
    }

    #[test]
    fn test_typecheck_expr_with_bindings_and_output_uses_context() {
        let mut egraph = EGraph::default();
        egraph.add_full_primitive(FullOnly, None);
        let mut parser = crate::ast::Parser::default();
        let expr = parser.get_expr_from_string(None, "(full-only)").unwrap();

        let resolved = egraph
            .typecheck_expr_with_bindings_and_output(
                &expr,
                &[],
                I64Sort.to_arcsort(),
                Context::Full,
            )
            .unwrap();
        assert_eq!(resolved.output_type().name(), I64Sort.name());

        let err = egraph
            .typecheck_expr_with_bindings_and_output(
                &expr,
                &[],
                I64Sort.to_arcsort(),
                Context::Pure,
            )
            .unwrap_err();
        match err {
            TypeError::UnboundFunction(name, _) => assert_eq!(name, "full-only"),
            other => panic!("expected unbound function, got {other:?}"),
        }
    }

    #[test]
    fn test_typecheck_expr_with_bindings_and_output_rejects_duplicate_bindings() {
        let mut egraph = EGraph::default();
        let mut parser = crate::ast::Parser::default();
        let expr = parser.get_expr_from_string(None, "x").unwrap();
        let bindings = vec![
            ("x".to_string(), span!(), I64Sort.to_arcsort()),
            ("x".to_string(), span!(), BoolSort.to_arcsort()),
        ];

        let err = egraph
            .typecheck_expr_with_bindings_and_output(
                &expr,
                &bindings,
                I64Sort.to_arcsort(),
                Context::Pure,
            )
            .unwrap_err();

        match err {
            TypeError::AlreadyDefined(name, _) => assert_eq!(name, "x"),
            other => panic!("expected duplicate binding, got {other:?}"),
        }
    }

    #[test]
    fn test_typecheck_expr_with_bindings_and_output_rewrites_globals() {
        let mut egraph = EGraph::default();
        egraph.parse_and_run_program(None, "(let $x 1)").unwrap();
        let mut parser = crate::ast::Parser::default();
        let expr = parser.get_expr_from_string(None, "$x").unwrap();

        let resolved = egraph
            .typecheck_expr_with_bindings_and_output(
                &expr,
                &[],
                I64Sort.to_arcsort(),
                Context::Read,
            )
            .unwrap();

        match resolved {
            ResolvedExpr::Call(_, ResolvedCall::Func(func), children) => {
                assert_eq!(func.name, "$x");
                assert!(children.is_empty());
                assert_eq!(func.output().name(), I64Sort.name());
            }
            other => panic!("expected global function call rewrite, got {other:?}"),
        }
    }

    // Test that an `EGraph` is `Send` & `Sync`
    #[test]
    fn test_egraph_send_sync() {
        fn is_send<T: Send>(_t: &T) -> bool {
            true
        }
        fn is_sync<T: Sync>(_t: &T) -> bool {
            true
        }
        let egraph = EGraph::default();
        assert!(is_send(&egraph) && is_sync(&egraph));
    }

    #[test]
    fn test_extension_state_clones_and_restores_with_egraph() {
        let mut egraph = EGraph::default();
        assert_eq!(egraph.extension_state::<usize>(), None);
        assert_eq!(egraph.clone().extension_state::<usize>(), None);

        *egraph.extension_state_or_default::<usize>() = 1;

        let mut cloned = egraph.clone();
        assert_eq!(cloned.extension_state::<usize>(), Some(&1));
        *cloned.extension_state_or_default::<usize>() = 2;
        assert_eq!(egraph.extension_state::<usize>(), Some(&1));

        egraph.push();
        *egraph.extension_state_or_default::<usize>() = 3;
        egraph.pop().unwrap();

        assert_eq!(egraph.extension_state::<usize>(), Some(&1));
    }

    fn get_function(egraph: &EGraph, name: &str) -> Function {
        egraph.functions.get(name).unwrap().clone()
    }

    fn get_value(egraph: &EGraph, name: &str) -> Value {
        let mut out = None;
        let id = get_function(egraph, name).backend_id;
        egraph.backend.for_each(id, |row| out = Some(row.vals[0]));
        out.unwrap()
    }

    #[test]
    fn test_subsumed_unextractable_rebuild_arg() {
        // Tests that a term stays unextractable even after a rebuild after a union would change the value of one of its args
        let mut egraph = EGraph::default();

        egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype Math)
                (constructor container (Math) Math)
                (constructor expensive () Math :cost 100)
                (constructor cheap () Math)
                (constructor cheap-1 () Math)
                ; we make the container cheap so that it will be extracted if possible, but then we mark it as subsumed
                ; so the (expensive) expr should be extracted instead
                (let res (container (cheap)))
                (union res (expensive))
                (cheap)
                (cheap-1)
                (subsume (container (cheap)))
                "#,
            ).unwrap();
        // At this point (cheap) and (cheap-1) should have different values, because they aren't unioned
        let orig_cheap_value = get_value(&egraph, "cheap");
        let orig_cheap_1_value = get_value(&egraph, "cheap-1");
        assert_ne!(orig_cheap_value, orig_cheap_1_value);
        // Then we can union them
        egraph
            .parse_and_run_program(
                None,
                r#"
                (union (cheap-1) (cheap))
                "#,
            )
            .unwrap();
        // And verify that their values are now the same and different from the original (cheap) value.
        let new_cheap_value = get_value(&egraph, "cheap");
        let new_cheap_1_value = get_value(&egraph, "cheap-1");
        assert_eq!(new_cheap_value, new_cheap_1_value);
        assert!(new_cheap_value != orig_cheap_value || new_cheap_1_value != orig_cheap_1_value);
        // Now verify that if we extract, it still respects the unextractable, even though it's a different values now
        let outputs = egraph
            .parse_and_run_program(
                None,
                r#"
                (extract res)
                "#,
            )
            .unwrap();
        assert_eq!(outputs[0].to_string(), "(expensive)\n");
    }

    #[test]
    fn test_subsumed_unextractable_rebuild_self() {
        // Tests that a term stays unextractable even after a rebuild after a union change its output value.
        let mut egraph = EGraph::default();

        egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype Math)
                (constructor container (Math) Math)
                (constructor expensive () Math :cost 100)
                (constructor cheap () Math)
                (expensive)
                (let x (cheap))
                (subsume (cheap))
                "#,
            )
            .unwrap();

        let orig_cheap_value = get_value(&egraph, "cheap");
        // Then we can union them
        egraph
            .parse_and_run_program(
                None,
                r#"
                (union (expensive) x)
                "#,
            )
            .unwrap();
        // And verify that the cheap value is now different
        let new_cheap_value = get_value(&egraph, "cheap");
        assert_ne!(new_cheap_value, orig_cheap_value);

        // Now verify that if we extract, it still respects the subsumption, even though it's a different values now
        let res = egraph
            .parse_and_run_program(
                None,
                r#"
                (extract x)
                "#,
            )
            .unwrap();
        assert_eq!(res[0].to_string(), "(expensive)\n");
    }

    #[test]
    fn test_run_undefined_ruleset_errors() {
        let mut egraph = EGraph::default();
        let err = egraph
            .parse_and_run_program(None, "(ruleset test)\n(run test2 1)")
            .unwrap_err();
        assert!(matches!(err, Error::NoSuchRuleset(name, _) if name == "test2"));
    }

    #[test]
    fn let_check_allows_only_bounded_container_interning() {
        for mut egraph in [EGraph::default(), EGraph::new_with_proofs()] {
            egraph
                .parse_and_run_program(
                    None,
                    r#"
                    (sort P (Pair i64 i64))
                    (sort V (Vec i64))
                    (let-check $p (pair 1 2))
                    (let-check $v (vec-of (pair-first $p) 3))
                    (let-check $n (vec-length $v))
                    "#,
                )
                .unwrap();
        }

        let mut egraph = EGraph::default();
        let error = egraph
            .parse_and_run_program(
                None,
                r#"
                (sort S (Set i64))
                (let-check $set (set-of 1))
                "#,
            )
            .unwrap_err();
        assert!(error.to_string().contains("unsupported container"));
        assert!(!egraph.checked_aliases.contains_key("$set"));
    }

    #[test]
    fn let_check_expected_sort_is_enforced_without_ghost_aliases() {
        let mut egraph = EGraph::default();
        let expr = egraph.parser.get_expr_from_string(None, "(+ 1 2)").unwrap();
        let command = Command::LetCheck {
            span: expr.span(),
            name: "$n".to_owned(),
            expr: expr.clone(),
            expected_sort: Some("bool".to_owned()),
        };
        let error = egraph.run_program(vec![command]).unwrap_err();
        assert!(matches!(
            error,
            Error::TypeError(TypeError::Mismatch { .. })
        ));
        assert!(!egraph.checked_alias_types.contains_key("$n"));
        assert!(!egraph.names.contains_canonical("n"));

        egraph
            .run_program(vec![Command::LetCheck {
                span: expr.span(),
                name: "$n".to_owned(),
                expr,
                expected_sort: Some("i64".to_owned()),
            }])
            .unwrap();
    }
}

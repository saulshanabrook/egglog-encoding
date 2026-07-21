#![doc = include_str!("lib.md")]
pub mod api;
pub mod ast;
pub mod causal_slice;
#[cfg(feature = "bin")]
mod cli;
mod command_macro;
pub mod constraint;
mod core;
mod exec_state;
pub mod extract;
pub mod prelude;
mod proofs;

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
use core::{CoreActionContext, ResolvedAtomTerm, specialize_core_rule};
pub use core::{ResolvedCall, SpecializedPrimitive};
pub use core_relations::{BaseValue, ContainerValue, Value};
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
    GuardedRuleBatchEntry, GuardedRuleBatchOutcome, GuardedRuleRun, GuardedRuleRunOutcome,
    ReadMode, RuleActionCall, RuleBodyCall, RuleSetRun, RuleSpec, RuleValue, RuleVar,
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

#[derive(Clone)]
pub struct EGraph {
    backend: Box<dyn egglog_backend_trait::Backend>,
    pub parser: Parser,
    names: check_shadowing::Names,
    /// pushed_egraph forms a linked list of pushed egraphs.
    /// Pop reverts the egraph to the last pushed egraph.
    pushed_egraph: Option<Box<Self>>,
    functions: IndexMap<String, Function>,
    rulesets: IndexMap<String, Ruleset>,
    /// Panic callbacks embedded in `FunctionContainer` values must remain live
    /// for as long as the e-graph can retain those values. Cache one callback
    /// per unstable-function target for the lifetime of this `EGraph`.
    unstable_fn_panic_ids: HashMap<String, ExternalFunctionId>,
    pub fact_directory: Option<PathBuf>,
    pub seminaive: bool,
    pub no_decomp: bool,
    /// Whether constructor-variable unions may be lowered to constructor-table
    /// sets. Causal tracing disables this semantics-preserving optimization so
    /// the native action path retains both constructor and union causes.
    union_to_set_optimization: bool,
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
}

/// A user-defined command allows users to inject custom command that can be called
/// in an egglog program.
///
/// Compared to an external function, a user-defined command is more powerful because
/// it has an exclusive access to the e-graph.
pub trait UserDefinedCommand: Send + Sync {
    /// Run the command with the given arguments.
    fn update(&self, egraph: &mut EGraph, args: &[Expr]) -> Result<Vec<CommandOutput>, Error>;
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
            rulesets: Default::default(),
            unstable_fn_panic_ids: Default::default(),
            fact_directory: None,
            seminaive: true,
            no_decomp: false,
            union_to_set_optimization: true,
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

        eg.rulesets
            .insert("".into(), Ruleset::Rules(Default::default()));

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

#[derive(Clone)]
enum PreparedSchedule {
    Saturate(Span, Box<PreparedSchedule>),
    Repeat(Span, usize, Box<PreparedSchedule>),
    Run(Span, ResolvedRunConfig),
    RunRule(PreparedRunRule),
    RunRuleBatch(Span, Vec<PreparedRunRule>),
    Sequence(Span, Vec<PreparedSchedule>),
}

#[derive(Clone)]
struct PreparedRunRule {
    span: Span,
    config: ResolvedRunRuleConfig,
    rule_id: egglog_bridge::RuleId,
    ruleset: String,
}

impl Display for PreparedSchedule {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            PreparedSchedule::Saturate(_, schedule) => write!(f, "(saturate {schedule})"),
            PreparedSchedule::Repeat(_, limit, schedule) => {
                write!(f, "(repeat {limit} {schedule})")
            }
            PreparedSchedule::Run(_, config) => write!(f, "{config}"),
            PreparedSchedule::RunRule(prepared) => write!(f, "{}", prepared.config),
            PreparedSchedule::RunRuleBatch(_, prepared) => write!(
                f,
                "(run-rule-batch {})",
                ListDisplay(
                    &prepared
                        .iter()
                        .map(|entry| &entry.config)
                        .collect::<Vec<_>>(),
                    " "
                )
            ),
            PreparedSchedule::Sequence(_, schedules) => {
                write!(f, "(seq {})", ListDisplay(schedules, " "))
            }
        }
    }
}

#[derive(Debug, Error)]
#[error("Not found: {0}")]
pub struct NotFoundError(String);

impl EGraph {
    pub(crate) fn with_union_to_set_optimization(mut self, enabled: bool) -> Self {
        self.union_to_set_optimization = enabled;
        self
    }

    fn use_union_to_set_optimization(&self) -> bool {
        self.union_to_set_optimization && self.proof_state.original_typechecking.is_none()
    }

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
        egraph.proof_state.original_typechecking = Some(Box::new(egraph.clone()));
        egraph
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
        self.proof_state.original_typechecking = Some(Box::new(self.clone()));
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
        self.proof_state.original_typechecking = Some(Box::new(EGraph::default()));
        self
    }

    /// Enable the term-encoding pipeline for a custom backend, using the given
    /// bridge-backed e-graph for parsing/typechecking before instrumentation.
    #[doc(hidden)]
    pub fn with_term_encoding_typechecker(mut self, typechecker: EGraph) -> Self {
        self.proof_state.original_typechecking = Some(Box::new(typechecker));
        self
    }

    /// Enable proof generation on this e-graph.
    /// TODO proofs should be turned on during creation of the e-graph, not afterwards.
    /// This method is to support the current CLI implementation with egglog-experimental (https://github.com/egraphs-good/egglog/issues/768)
    #[doc(hidden)]
    pub fn with_proofs_enabled(mut self) -> Self {
        if self.proof_state.original_typechecking.is_none() {
            self = self.with_term_encoding_enabled();
        }
        self.proof_state.proofs_enabled = true;
        self
    }

    /// Enable testing of getting proofs for all `check` commands.
    pub fn with_proof_testing(mut self) -> Self {
        self.proof_state.proof_testing = true;
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
        &mut self.type_info
    }

    /// Get read-only access to the command macro registry
    pub fn command_macros(&self) -> &CommandMacroRegistry {
        &self.command_macros
    }

    /// Get mutable access to the command macro registry
    pub fn command_macros_mut(&mut self) -> &mut CommandMacroRegistry {
        &mut self.command_macros
    }

    pub fn add_command(
        &mut self,
        name: String,
        command: Arc<dyn UserDefinedCommand>,
    ) -> Result<(), Error> {
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
                Ok(egglog_bridge::MergeFn::Primitive(
                    p.external_id(crate::Context::Write),
                    translated_args,
                ))
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
        let backend_id = self.backend.add_table(egglog_bridge::FunctionConfig {
            schema: input
                .iter()
                .chain(outputs.iter())
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
        });
        assert_eq!(backend_id, own_id);

        let function = Function {
            decl: decl.clone(),
            schema: ResolvedSchema { input, outputs },
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

    // Prepare each static run-rule leaf once, then reuse its temporary naive
    // specialization throughout repeat/saturate. Always release temporary rules,
    // including when preparation or execution fails.
    fn run_schedule(&mut self, sched: &ResolvedSchedule) -> Result<RunReport, Error> {
        let mut temporary_rules = Vec::new();
        let prepared = match self.prepare_schedule(sched, &mut temporary_rules) {
            Ok(prepared) => prepared,
            Err(error) => {
                for rule in temporary_rules {
                    self.backend.free_rule(rule);
                }
                return Err(error);
            }
        };
        let result = self.run_prepared_schedule(&prepared);
        for rule in temporary_rules {
            self.backend.free_rule(rule);
        }
        result
    }

    fn prepare_schedule(
        &mut self,
        sched: &ResolvedSchedule,
        temporary_rules: &mut Vec<egglog_bridge::RuleId>,
    ) -> Result<PreparedSchedule, Error> {
        match sched {
            ResolvedSchedule::Run(span, config) => {
                Ok(PreparedSchedule::Run(span.clone(), config.clone()))
            }
            ResolvedSchedule::RunRule(span, config) => {
                let prepared = self.prepare_run_rule(span, config)?;
                temporary_rules.push(prepared.rule_id);
                Ok(PreparedSchedule::RunRule(prepared))
            }
            ResolvedSchedule::RunRuleBatch(span, configs) => {
                let mut prepared = Vec::with_capacity(configs.len());
                for config in configs {
                    let entry = self.prepare_run_rule(span, config)?;
                    temporary_rules.push(entry.rule_id);
                    prepared.push(entry);
                }
                Ok(PreparedSchedule::RunRuleBatch(span.clone(), prepared))
            }
            ResolvedSchedule::Repeat(span, limit, sched) => Ok(PreparedSchedule::Repeat(
                span.clone(),
                *limit,
                Box::new(self.prepare_schedule(sched, temporary_rules)?),
            )),
            ResolvedSchedule::Saturate(span, sched) => Ok(PreparedSchedule::Saturate(
                span.clone(),
                Box::new(self.prepare_schedule(sched, temporary_rules)?),
            )),
            ResolvedSchedule::Sequence(span, scheds) => {
                let scheds = scheds
                    .iter()
                    .map(|sched| self.prepare_schedule(sched, temporary_rules))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(PreparedSchedule::Sequence(span.clone(), scheds))
            }
        }
    }

    fn run_prepared_schedule(&mut self, sched: &PreparedSchedule) -> Result<RunReport, Error> {
        match sched {
            PreparedSchedule::Run(span, config) => self.run_rules(span, config),
            PreparedSchedule::RunRule(prepared) => self.run_prepared_rule(prepared),
            PreparedSchedule::RunRuleBatch(span, prepared) => {
                self.run_prepared_rule_batch(span, prepared)
            }
            PreparedSchedule::Repeat(_span, limit, sched) => {
                let mut report = RunReport::default();
                for _i in 0..*limit {
                    let rec = self.run_prepared_schedule(sched)?;
                    let can_stop = rec.can_stop;
                    report.union(rec);
                    if can_stop {
                        break;
                    }
                }
                Ok(report)
            }
            PreparedSchedule::Saturate(_span, sched) => {
                let mut report = RunReport::default();
                let mut i = 0usize;
                loop {
                    i += 1;
                    log::debug!(
                        "Saturate iteration {i} start: {}",
                        Self::schedule_for_log(sched)
                    );
                    let rec = self.run_prepared_schedule(sched)?;
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
            PreparedSchedule::Sequence(_span, scheds) => {
                let mut report = RunReport::default();
                for sched in scheds {
                    report.union(self.run_prepared_schedule(sched)?);
                }
                Ok(report)
            }
        }
    }

    fn prepare_run_rule(
        &mut self,
        span: &Span,
        config: &ResolvedRunRuleConfig,
    ) -> Result<PreparedRunRule, Error> {
        let (ruleset, core_rule, substitutions, include_subsumed, no_decomp) = self
            .rulesets
            .iter()
            .find_map(|(ruleset_name, ruleset)| match ruleset {
                Ruleset::Rules(rules) => rules.get(&config.rule).map(|registered| {
                    (
                        ruleset_name.clone(),
                        registered.core.clone(),
                        registered.substitutions.clone(),
                        registered.include_subsumed,
                        registered.no_decomp,
                    )
                }),
                Ruleset::Combined(_) => None,
            })
            .ok_or_else(|| Error::NoSuchRule(config.rule.clone(), span.clone()))?;
        let core_rule = specialize_core_rule(
            &core_rule,
            &config.selectors,
            &substitutions,
            &self.type_info,
            &mut self.parser.symbol_gen,
        )?;
        let mut translator = BackendRule::new(
            &mut *self.backend,
            &self.functions,
            &self.type_info,
            &mut self.unstable_fn_panic_ids,
            true,
        );
        translator.query(&core_rule.body, include_subsumed)?;
        translator.actions(&core_rule.head)?;
        let rule_id = translator.try_build(
            &config.rule,
            false,
            self.no_decomp || no_decomp,
            core_rule.span,
        )?;

        Ok(PreparedRunRule {
            span: span.clone(),
            config: config.clone(),
            rule_id,
            ruleset,
        })
    }

    fn run_prepared_rule(&mut self, prepared: &PreparedRunRule) -> Result<RunReport, Error> {
        let outcome = self.backend.run_rule_guarded(GuardedRuleRun {
            rule: prepared.rule_id,
            expected_matches: prepared.config.expect,
        });

        match outcome.map_err(|error| Error::BackendError(error.to_string()))? {
            GuardedRuleRunOutcome::Applied { report, .. } => {
                Ok(RunReport::singleton(&prepared.ruleset, report))
            }
            GuardedRuleRunOutcome::MatchCountMismatch {
                expected_matches,
                observed_matches,
            } => Err(Error::RunRuleMatchCountMismatch {
                rule: prepared.config.rule.clone(),
                expected: expected_matches,
                observed: observed_matches,
                span: prepared.span.clone(),
            }),
        }
    }

    fn run_prepared_rule_batch(
        &mut self,
        span: &Span,
        prepared: &[PreparedRunRule],
    ) -> Result<RunReport, Error> {
        let runs = prepared
            .iter()
            .map(|entry| GuardedRuleBatchEntry {
                rule: entry.rule_id,
                expected_matches: entry.config.expect,
            })
            .collect::<Vec<_>>();
        let outcome = self
            .backend
            .run_rule_batch_guarded(&runs)
            .map_err(|error| Error::BackendError(error.to_string()))?;
        match outcome {
            GuardedRuleBatchOutcome::Applied { report, .. } => {
                let ruleset = prepared
                    .first()
                    .map(|first| first.ruleset.as_str())
                    .filter(|ruleset| prepared.iter().all(|entry| entry.ruleset == *ruleset))
                    .unwrap_or("<run-rule-batch>");
                Ok(RunReport::singleton(ruleset, report))
            }
            GuardedRuleBatchOutcome::MatchCountMismatch {
                run_index,
                expected_matches,
                observed_matches,
            } => {
                let failed = prepared.get(run_index).ok_or_else(|| {
                    Error::BackendError(format!(
                        "run-rule-batch returned invalid failed entry index {run_index}"
                    ))
                })?;
                Err(Error::RunRuleMatchCountMismatch {
                    rule: failed.config.rule.clone(),
                    expected: expected_matches,
                    observed: observed_matches,
                    span: span.clone(),
                })
            }
        }
    }

    fn run_rules(&mut self, span: &Span, config: &ResolvedRunConfig) -> Result<RunReport, Error> {
        log::debug!("Running ruleset: {}", config.ruleset);
        let mut report: RunReport = Default::default();

        let GenericRunConfig { ruleset, until } = config;

        if !self.rulesets.contains_key(ruleset) {
            return Err(Error::NoSuchRuleset(ruleset.clone(), span.clone()));
        }

        if let Some(facts) = until
            && self.check_facts(span, facts).is_ok()
        {
            log::info!(
                "Breaking early because of facts:\n {}!",
                ListDisplay(facts, "\n")
            );
            return Ok(report);
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

        let iteration_report = self
            .backend
            .run_rules(RuleSetRun {
                name: Some(ruleset),
                rules: &rule_ids,
            })
            .map_err(|e| Error::BackendError(e.to_string()))?;

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
        let union_to_set = self.use_union_to_set_optimization();

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

        let canonicalized = rule.to_canonicalized_core_rule_with_substitutions(
            &self.type_info,
            &mut self.parser.symbol_gen,
            union_to_set,
        )?;
        let core_rule = canonicalized.core;
        let (query, actions) = (&core_rule.body, &core_rule.head);
        let rule_id = {
            let mut translator = BackendRule::new(
                &mut *self.backend,
                &self.functions,
                &self.type_info,
                &mut self.unstable_fn_panic_ids,
                requires_read_context,
            );
            translator.query(query, rule.include_subsumed)?;
            translator.actions(actions)?;
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
                include_subsumed: rule.include_subsumed,
                no_decomp: rule.no_decomp,
            }),
        };
        Ok(rule_name)
    }

    fn eval_actions(&mut self, actions: &ResolvedActions) -> Result<(), Error> {
        let union_to_set = self.use_union_to_set_optimization();
        let mut binding = IndexSet::default();
        let mut ctx = CoreActionContext::new(
            &self.type_info,
            &mut binding,
            &mut self.parser.symbol_gen,
            union_to_set,
        );
        let (actions, _) = actions.to_core_actions(&mut ctx)?;

        let mut translator = BackendRule::new(
            &mut *self.backend,
            &self.functions,
            &self.type_info,
            &mut self.unstable_fn_panic_ids,
            true, // global action: Read/Full contexts (may read the DB)
        );
        translator.actions(&actions)?;
        let id = translator.try_build("eval_actions", false, false, Span::Panic)?;
        let result = self.backend.run_rules(RuleSetRun {
            name: None,
            rules: &[id],
        });
        self.backend.free_rule(id);

        match result {
            Ok(_) => Ok(()),
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
        if function.subtype() != FunctionSubtype::Custom {
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
        if function.subtype() != FunctionSubtype::Constructor {
            return Err(crate::api::ApiError::WrongSubtype {
                name: name.to_owned(),
                expected: "constructor",
                actual: "function",
            }
            .into());
        }
        self.backend.for_each_while(function.backend_id, |row| {
            let (eclass, children) = row
                .vals
                .split_last()
                .expect("constructor row has at least an eclass column");
            f(Enode {
                children,
                eclass: *eclass,
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
        let union_to_set = self.use_union_to_set_optimization();
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
            union_to_set,
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

    fn check_facts(&mut self, span: &Span, facts: &[ResolvedFact]) -> Result<(), Error> {
        let union_to_set = self.use_union_to_set_optimization();
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
        let core_rule = rule.to_canonicalized_core_rule(
            &self.type_info,
            &mut self.parser.symbol_gen,
            union_to_set,
        )?;
        let query = core_rule.body;

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
            &mut self.unstable_fn_panic_ids,
            true, // global query: Read context (may read the DB)
        );
        translator.rollback_external_funcs.push(ext_id);
        translator.query(&query, true)?;
        translator.call_external_func(
            span.clone(),
            ext_id,
            "check_facts_match",
            Vec::new(),
            egglog_bridge::ColumnTy::Id,
        );
        let id = translator.try_build("check_facts", false, false, span.clone())?;
        let run_result = self.backend.run_rules(RuleSetRun {
            name: None,
            rules: &[id],
        });
        self.backend.free_rule(id);
        run_result.map_err(|e| Error::BackendError(e.to_string()))?;

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
                    names.eq_trans_constructor = pc.trans;
                    names.eq_sym_constructor = pc.sym;
                    names.container_normalize_constructor = pc.normalize;
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
                self.check_facts(&span, &facts)?;
                log::info!("Checked fact {facts:?}.");
            }
            ResolvedNCommand::CoreAction(action) => match &action {
                ResolvedAction::Let(_, name, contents) => {
                    panic!("Globals should have been desugared away: {name} = {contents}")
                }
                _ => {
                    self.eval_actions(&ResolvedActions::new(vec![action.clone()]))?;
                }
            },
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
                (0..n).for_each(|_| self.push());
                log::info!("Pushed {n} levels.")
            }
            ResolvedNCommand::Pop(span, n) => {
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
            ResolvedNCommand::Fail(span, c) => {
                let result = self.run_command(*c);
                if let Err(e) = result {
                    log::info!("Command failed as expected: {e}");
                } else {
                    return Err(Error::ExpectFail(span));
                }
            }
            ResolvedNCommand::Input { span, name, file } => {
                self.input_file(span, &name, file)?;
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
                return command.update(self, &exprs);
            }

            ResolvedNCommand::ProveExists(span, resolved_call) => {
                let mut instrument = ProofInstrumentor { egraph: self };
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

    pub(crate) fn read_input_rows(
        fact_directory: Option<&std::path::Path>,
        row_schema: &[String],
        span: &Span,
        file: &str,
    ) -> Result<Vec<Vec<Literal>>, Error> {
        let mut filename = fact_directory.map_or_else(PathBuf::new, PathBuf::from);
        filename.push(file);

        log::info!("Opening file '{filename:?}'...");
        let contents = std::fs::read_to_string(&filename)
            .map_err(|error| Error::IoError(filename, error, span.clone()))?;

        let mut rows = Vec::with_capacity(contents.lines().count());
        for line in contents.lines() {
            let mut fields = line.split('\t').map(str::trim);
            let mut row = Vec::with_capacity(row_schema.len());
            for sort in row_schema {
                if sort == "Unit" {
                    row.push(Literal::Unit);
                    continue;
                }
                let Some(raw) = fields.next() else {
                    break;
                };
                let literal = match sort.as_str() {
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
                continue;
            }
            if row.len() != row_schema.len() || fields.next().is_some() {
                return Err(Error::InputFileFormatError(file.to_owned()));
            }
            rows.push(row);
        }
        Ok(rows)
    }

    fn read_input_file(
        fact_directory: Option<&std::path::Path>,
        function_type: &FuncType,
        span: &Span,
        file: &str,
    ) -> Result<Vec<Vec<Literal>>, Error> {
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

        let mut row_schema = function_type
            .input
            .iter()
            .map(|sort| sort.name().to_owned())
            .collect::<Vec<_>>();
        // Relations desugar to constructors, so their implicit output is not a TSV column.
        if function_type.subtype == FunctionSubtype::Custom {
            row_schema.extend(
                function_type
                    .outputs
                    .iter()
                    .map(|sort| sort.name().to_owned()),
            );
        }
        Self::read_input_rows(fact_directory, &row_schema, span, file)
    }

    fn input_file(&mut self, span: Span, func_name: &str, file: String) -> Result<(), Error> {
        let function_type = self
            .type_info
            .get_func_type(func_name)
            .unwrap_or_else(|| panic!("Unrecognized function name {func_name}"))
            .clone();
        let parsed_contents =
            Self::read_input_file(self.fact_directory.as_deref(), &function_type, &span, &file)?;
        let func = self.functions.get_mut(func_name).unwrap();
        let unit_val = self.backend.base_values().get(());
        let parsed_contents = parsed_contents
            .into_iter()
            .map(|row| {
                row.into_iter()
                    .map(|literal| match literal {
                        Literal::Int(value) => self.backend.base_values().get(value),
                        Literal::Float(value) => self
                            .backend
                            .base_values()
                            .get::<F>(core_relations::Boxed::new(value)),
                        Literal::String(value) => self.backend.base_values().get::<S>(value.into()),
                        Literal::Unit => unit_val,
                        Literal::Bool(_) => unreachable!(),
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        log::debug!("Successfully loaded file.");

        let num_facts = parsed_contents.len();

        let bridge = self
            .backend
            .as_any()
            .downcast_ref::<egglog_bridge::EGraph>()
            .ok_or_else(|| {
                Error::BackendError(
                    "loading facts from a file requires the reference bridge backend".into(),
                )
            })?;
        let table_action = egglog_bridge::TableAction::new(bridge, func.backend_id);

        if function_type.subtype != FunctionSubtype::Constructor {
            self.backend.with_execution_state(|es| {
                for row in parsed_contents.iter() {
                    table_action.insert(es, row.iter().copied());
                }
                Some(unit_val)
            });
        } else {
            self.backend.with_execution_state(|es| {
                for row in parsed_contents.iter() {
                    // Constructor semantics: mint a fresh eclass id for
                    // each missing key.
                    table_action.lookup_or_insert(es, row);
                }
                Some(unit_val)
            });
        }

        self.backend.flush_updates();

        log::info!("Read {num_facts} facts into {func_name} from '{file}'.");
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
        if let Some(original_typechecking) = self.proof_state.original_typechecking.as_mut() {
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
            // Input expansion needs resolved schemas. Lower it once here so the
            // encoded execution and proof checker consume the same fiat actions.
            let resolved_before_proofs =
                ProofInstrumentor::lower_inputs(self, resolved_before_proofs)?;
            // Now remove globals for actual execution (but NOT from desugared_commands)
            let typechecked_no_globals = proof_global_remover::remove_globals(
                resolved_before_proofs.clone(),
                &mut self.parser.symbol_gen,
            );
            for command in &typechecked_no_globals {
                self.names.check_shadowing(command)?;
            }

            let term_encoding_added =
                ProofInstrumentor::add_term_encoding(self, typechecked_no_globals)?;
            let mut new_typechecked = vec![];
            for new_cmd in term_encoding_added {
                let desugared =
                    desugar_command(new_cmd, &mut self.parser, self.proof_state.proof_testing)?;
                for cmd in &desugared {
                    log::trace!("Desugared term encoding: {}", cmd.to_command());
                }

                // Now typecheck using self, adding term type information.
                let desugared_typechecked = self.typecheck_program(&desugared)?;
                // remove globals again, but this time allow primitive globals
                let desugared_typechecked = remove_globals::remove_globals(
                    desugared_typechecked,
                    &mut self.parser.symbol_gen,
                );

                new_typechecked.extend(desugared_typechecked);
            }
            Ok(ResolvedNCommands {
                desugared: new_typechecked,
                desugared_before_proofs: resolved_before_proofs,
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
                    let resolved = self.resolve_command(command)?;
                    if run_commands && self.are_proofs_enabled() {
                        self.proof_check_program
                            .extend(resolved.desugared_before_proofs.clone());
                    }

                    desugared_before_proofs.extend(resolved.desugared_before_proofs);
                    desugared.extend(resolved.desugared.clone());

                    for processed in resolved.desugared {
                        // even in desugar mode we still run push and pop
                        if run_commands
                            || matches!(
                                processed,
                                ResolvedNCommand::Push(_) | ResolvedNCommand::Pop(_, _)
                            )
                        {
                            let result = self.run_command(processed)?;
                            outputs.extend(result);
                        }
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
            self.backend.flush_updates();
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

struct BackendRule<'a> {
    backend: &'a mut dyn Backend,
    unstable_fn_panic_ids: &'a mut HashMap<String, ExternalFunctionId>,
    pending_unstable_fn_panic_ids: HashMap<String, ExternalFunctionId>,
    entries: HashMap<core::ResolvedAtomTerm, core::GenericAtomTerm<RuleVar, RuleValue>>,
    next_var: u32,
    body: core::Query<RuleBodyCall, RuleVar, RuleValue>,
    head: core::GenericCoreActions<RuleActionCall, RuleVar, RuleValue>,
    rollback_external_funcs: Vec<ExternalFunctionId>,
    functions: &'a IndexMap<String, Function>,
    type_info: &'a TypeInfo,
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
        unstable_fn_panic_ids: &'a mut HashMap<String, ExternalFunctionId>,
        requires_read_context: bool,
    ) -> BackendRule<'a> {
        BackendRule {
            backend,
            unstable_fn_panic_ids,
            pending_unstable_fn_panic_ids: Default::default(),
            functions,
            type_info,
            requires_read_context,
            entries: Default::default(),
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

    fn fresh_var(&mut self, variable: &ResolvedVar) -> RuleVar {
        let id = self.next_var;
        self.next_var += 1;
        RuleVar {
            id,
            name: variable.name.clone().into_boxed_str(),
            ty: variable.sort.column_ty(self.backend.base_values()),
        }
    }

    fn entry(
        &mut self,
        term: &core::ResolvedAtomTerm,
    ) -> Result<core::GenericAtomTerm<RuleVar, RuleValue>, Error> {
        if let Some(entry) = self.entries.get(term) {
            return Ok(entry.clone());
        }
        let entry = match term {
            core::GenericAtomTerm::Var(span, variable) => {
                core::GenericAtomTerm::Var(span.clone(), self.fresh_var(variable))
            }
            core::GenericAtomTerm::Literal(span, literal) => core::GenericAtomTerm::Literal(
                span.clone(),
                literal_to_rule_value(self.backend.base_values(), literal),
            ),
            core::GenericAtomTerm::Global(span, variable) => {
                return Err(Error::BackendError(format!(
                    "{span}: global `{}` was not desugared before backend lowering",
                    variable.name
                )));
            }
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
    ) -> Result<
        (
            ExternalFunctionId,
            Vec<core::GenericAtomTerm<RuleVar, RuleValue>>,
            ColumnTy,
        ),
        Error,
    > {
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
        Ok((resolved_id, rule_args, output_ty))
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
                    let (id, args, output) = self.prim(p, &atom.args, ctx)?;
                    (
                        RuleBodyCall::Primitive {
                            id,
                            name: p.name().into(),
                            output,
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
                            let (id, args, output) = self.prim(p, args, ctx)?;
                            (
                                RuleActionCall::Primitive {
                                    id,
                                    name: p.name().into(),
                                    output,
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
    #[error(
        "{span}\nrun-rule {rule:?} expected {expected} match(es), but found {observed}; no rule actions were applied"
    )]
    RunRuleMatchCountMismatch {
        rule: String,
        expected: usize,
        observed: usize,
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
    use crate::constraint::SimpleTypeConstraint;
    use crate::*;

    use crate::PureState;

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
                .parse_and_run_program(None, r#"(run-schedule (run-rule "owns-panic" :expect 1))"#)
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
}

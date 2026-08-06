#![doc = include_str!("lib.md")]
pub mod api;
pub mod ast;
#[cfg(feature = "bin")]
mod cli;
mod command_macro;
mod command_origin;
pub mod constraint;
mod core;
mod exec_state;
pub mod extract;
mod frontend_capture;
pub mod frontend_program;
pub mod frontend_snapshot;
pub mod prelude;
mod proofs;

mod schedule_origin;
pub mod scheduler;
mod serialize;
pub mod sort;
mod termdag;
mod typechecking;
pub mod typed_input;
pub mod util;
pub use command_macro::{CommandMacro, CommandMacroRegistry};

// This is used to allow the `add_primitive` macro to work in
// both this crate and other crates by referring to `::egglog`.
extern crate self as egglog;
pub use ast::{ResolvedExpr, ResolvedFact, ResolvedVar};
#[cfg(feature = "bin")]
pub use cli::*;
use constraint::{
    AllEqualTypeConstraint, Constraint, Problem, SimpleTypeConstraint, TypeConstraint,
};
use core::CoreActionContext;
use core::ResolvedAtomTerm;
pub use core::{Atom, AtomTerm};
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
pub use egglog_backend_trait::{
    Backend, BackendExt, MatchObserver, NativePrimitive, NativeScalarPrimitive,
};
use egglog_backend_trait::{
    NativeInputValue, ReadMode, RuleActionCall, RuleBodyCall, RuleSetRun, RuleSpec, RuleValue,
    RuleVar,
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
use numeric_id::{DenseIdMap, NumericId};
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
use std::ops::{Deref, DerefMut};
use std::path::PathBuf;
use std::sync::Arc;
pub use termdag::{OrdTerm, Term, TermDag, TermId};
use thiserror::Error;
use typechecking::FuncType;
pub use typechecking::PrimitiveValidator;
pub use typechecking::SortRegistrationId;
pub use typechecking::TypeError;
pub use typechecking::TypeInfo;
use util::*;

use crate::ast::desugar::desugar_command;
use crate::ast::*;
use crate::core::{GenericActionsExt, ResolvedRuleExt};
use crate::proofs::proof_encoding::{EncodingState, ProofInstrumentor, SortLineage};
#[cfg(test)]
use crate::proofs::proof_encoding_helpers::finalized_program_supports_proofs;
use crate::proofs::proof_encoding_helpers::{
    ProofEncodingUnsupportedReason, command_supports_proof_encoding_with_sort_authorities,
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

/// Typechecking-only definition for a native binary value primitive. Runtime
/// behavior is supplied by [`NativePrimitive`], while this retains the exact
/// type constraints previously generated by `add_primitive!`.
#[derive(Clone)]
struct NativeBinaryValuePrimitive {
    name: &'static str,
    output: Option<ArcSort>,
}

impl NativeBinaryValuePrimitive {
    fn all_equal(name: &'static str) -> Self {
        Self { name, output: None }
    }

    fn with_output(name: &'static str, output: ArcSort) -> Self {
        Self {
            name,
            output: Some(output),
        }
    }
}

impl Primitive for NativeBinaryValuePrimitive {
    fn name(&self) -> &str {
        self.name
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        let mut constraint =
            AllEqualTypeConstraint::new(self.name(), span.clone()).with_exact_length(3);
        if let Some(output) = &self.output {
            constraint = constraint.with_output_sort(output.clone());
        }
        constraint.into_box()
    }
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

/// The execution engine attached to an [`EGraph`].
///
/// `CompileOnly` deliberately contains no [`Backend`]. Frontend registration
/// still needs stable ids while resolving primitive calls, so that mode owns a
/// deterministic, frontend-only token allocator instead. Any accidental use of
/// an execution API goes through [`Deref`] and panics at the point of access.
#[derive(Clone)]
enum BackendSlot {
    Runtime(Box<dyn Backend>),
    // Consumed by the standalone compiler snapshot in the next integration
    // slice; retained here as the backend-free frontend substrate.
    #[allow(dead_code)]
    CompileOnly(CompileOnlyBackendState),
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct CompileOnlyBackendState {
    next_external_function_id: usize,
    /// Nominal sort registrations in deterministic declaration order. These
    /// are typechecking tokens, not backend [`ColumnTy`] ids.
    sort_tokens: IndexMap<SortRegistrationId, usize>,
}

impl BackendSlot {
    fn runtime(backend: Box<dyn Backend>) -> Self {
        Self::Runtime(backend)
    }

    #[allow(dead_code)]
    fn compile_only() -> Self {
        Self::CompileOnly(CompileOnlyBackendState::default())
    }

    #[allow(dead_code)]
    fn is_compile_only(&self) -> bool {
        matches!(self, Self::CompileOnly(_))
    }

    /// Register a sort for typechecking without asking a compile-only frontend
    /// to manufacture backend-specific storage types.
    fn register_sort(&mut self, identity: SortRegistrationId, sort: &ArcSort) {
        match self {
            Self::Runtime(backend) => sort.register_type(backend.as_mut()),
            Self::CompileOnly(state) => {
                let next = state.sort_tokens.len();
                state.sort_tokens.entry(identity).or_insert(next);
            }
        }
    }

    /// Allocate the runtime or synthetic token used to resolve one primitive
    /// in one context. The callback is never evaluated in compile-only mode.
    fn register_primitive<T>(
        &mut self,
        value: T,
        context: Context,
        build_runtime: &mut impl FnMut(&mut dyn Backend, T, Context) -> ExternalFunctionId,
    ) -> ExternalFunctionId {
        match self {
            Self::Runtime(backend) => build_runtime(backend.as_mut(), value, context),
            Self::CompileOnly(state) => {
                let token = ExternalFunctionId::from_usize(state.next_external_function_id);
                state.next_external_function_id += 1;
                token
            }
        }
    }

    /// Fresh ids are a required typed operation in proof-instrumented source.
    /// The compile-only frontend admits and types that operation without
    /// claiming an execution capability.
    fn supports_fresh_ids_for_typechecking(&self) -> bool {
        match self {
            Self::Runtime(backend) => backend.supports_fresh_ids(),
            Self::CompileOnly(_) => true,
        }
    }
}

impl Deref for BackendSlot {
    type Target = dyn Backend;

    fn deref(&self) -> &Self::Target {
        match self {
            Self::Runtime(backend) => backend.as_ref(),
            Self::CompileOnly(_) => {
                panic!("compile-only frontend attempted to access an execution backend")
            }
        }
    }
}

impl DerefMut for BackendSlot {
    fn deref_mut(&mut self) -> &mut Self::Target {
        match self {
            Self::Runtime(backend) => backend.as_mut(),
            Self::CompileOnly(_) => {
                panic!("compile-only frontend attempted to access an execution backend")
            }
        }
    }
}

#[derive(Clone)]
pub struct EGraph {
    backend: BackendSlot,
    pub parser: Parser,
    names: check_shadowing::Names,
    /// pushed_egraph forms a linked list of pushed egraphs.
    /// Pop reverts the egraph to the last pushed egraph.
    pushed_egraph: Option<Box<Self>>,
    functions: IndexMap<String, Function>,
    rulesets: IndexMap<String, Ruleset>,
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
        Self::with_backend_slot(BackendSlot::runtime(backend))
    }

    /// Construct a frontend whose typechecking state is completely detached
    /// from execution. This is an internal compiler substrate, not an alternate
    /// runtime backend.
    #[allow(dead_code)]
    pub(crate) fn new_compile_only(proofs_enabled: bool) -> Self {
        let mut egraph = Self::with_backend_slot(BackendSlot::compile_only());
        if proofs_enabled {
            let typechecker = egraph.clone();
            egraph.enable_term_encoding(typechecker);
            egraph.proof_state.proofs_enabled = true;
        }
        egraph
    }

    fn with_backend_slot(backend: BackendSlot) -> Self {
        let mut parser = Parser::default();
        let proof_state = EncodingState::new(&mut parser.symbol_gen);
        let mut eg = Self {
            backend,
            parser,
            names: Default::default(),
            pushed_egraph: Default::default(),
            functions: Default::default(),
            rulesets: Default::default(),
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
        eg.add_native_primitive(
            NativeBinaryValuePrimitive::with_output("!=", UnitSort.to_arcsort()),
            Some(Arc::new(neq_validator)),
            NativePrimitive::ValueNeq,
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

        eg.add_value_eq_primitive();
        eg.add_native_primitive(
            NativeBinaryValuePrimitive::all_equal("ordering-min"),
            None,
            NativePrimitive::OrderingMin,
        );
        eg.add_native_primitive(
            NativeBinaryValuePrimitive::all_equal("ordering-max"),
            None,
            NativePrimitive::OrderingMax,
        );

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
        eg.add_native_primitive(
            proofs::proof_encoding_helpers::OrientProof::min(),
            Some(orient_proof_validator(true)),
            NativePrimitive::SelectMinPayload,
        );
        eg.add_native_primitive(
            proofs::proof_encoding_helpers::OrientProof::max(),
            Some(orient_proof_validator(false)),
            NativePrimitive::SelectMaxPayload,
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
        eg.add_native_primitive(
            proofs::proof_encoding_helpers::SelectEqProof,
            Some(select_eq_validator),
            NativePrimitive::SelectEqPayload,
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
    desugared: typechecking::FinalizedProgram,
    /// In proof mode, populated with the desugared program before instrumented with proofs
    desugared_before_proofs: typechecking::FinalizedProgram,
}

struct ResolvedNCommandsWithOutput {
    outputs: Vec<CommandOutput>,
    resolved: typechecking::FinalizedProgram,
    /// Exact parsed source trigger for each entry in `resolved`. Populated only
    /// in compile-only mode.
    resolved_source_triggers: Vec<frontend_program::SourceSubcommandRef>,
    /// In proof mode, populated with the desugared program before instrumented with proofs
    resolved_before_proofs: typechecking::FinalizedProgram,
    /// Exact parsed source trigger for each entry in
    /// `resolved_before_proofs`. Populated only in compile-only mode.
    resolved_before_proofs_source_triggers: Vec<frontend_program::SourceSubcommandRef>,
}

/// One finalized command and the exact parsed source subcommand that triggered
/// it. Instrumentation can emit many finalized commands for one source
/// subcommand, so execution/proof streams cannot be positionally zipped. This
/// association deliberately does not claim a final public
/// [`frontend_program::CommandOrigin`] role for commands generated by later
/// frontend passes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CompileOnlyResolvedCommand {
    pub(crate) source_trigger: frontend_program::SourceSubcommandRef,
    pub(crate) command: ResolvedNCommand,
}

/// The two finalized command streams produced by the backend-free frontend.
/// This is crate-private compiler plumbing; it is intentionally not the public
/// standalone-program snapshot API.
#[allow(dead_code)]
#[derive(Debug)]
pub(crate) struct CompileOnlyResolvedProgram {
    /// Proof-instrumented, typechecked, global-eliminated execution commands.
    pub(crate) execution: Vec<CompileOnlyResolvedCommand>,
    /// Exact recursive command-path authority for execution-view Sorts.
    pub(crate) execution_sort_authorities: Vec<typechecking::SortAuthorityAt>,
    /// The corresponding pre-instrumentation commands used for proof checking.
    pub(crate) proof_check: Vec<CompileOnlyResolvedCommand>,
    /// Exact recursive command-path authority for proof-check-view Sorts.
    pub(crate) proof_check_sort_authorities: Vec<typechecking::SortAuthorityAt>,
    /// Exact source bytes and physical transaction/subcommand partition.
    pub(crate) source: frontend_program::SourceDocument,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ProgramProcessingMode {
    Run,
    ResolvePublic,
    #[allow(dead_code)]
    CompileOnly,
}

/// One input group for the command processor. Compile-only source groups keep
/// their physical identity and group-local parsed subcommands all the way to
/// the processing loop; ordinary API callers have no source provenance.
enum ProgramInputGroup {
    Detached(Vec<Command>),
    Source(frontend_capture::FrontendSourceSeedGroup),
}

impl ProgramProcessingMode {
    fn runs_commands(self) -> bool {
        matches!(self, Self::Run)
    }

    fn executes_push_pop(self) -> bool {
        matches!(self, Self::Run | Self::ResolvePublic)
    }

    fn builds_standalone_snapshot(self) -> bool {
        matches!(self, Self::CompileOnly)
    }
}

/// Why a source command cannot enter the standalone SQL compilation pipeline.
///
/// This is intentionally separate from proof-encoding support: these forms can
/// be meaningful to the normal runtime while still preventing a self-contained,
/// atomically published SQL artifact.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StandalonePreflightReason {
    /// Included files are not yet represented in the artifact's source/hash
    /// manifest, so following the path would make admission non-self-contained.
    Include,
    /// Snapshot/restore changes frontend name and type visibility. The
    /// standalone compiler does not currently expose scoped catalog state.
    Push,
    /// See [`StandalonePreflightReason::Push`].
    Pop,
    /// Presort-backed values include the built-in containers and dynamic
    /// function handles that are outside this milestone's typed SQL surface.
    Presort,
    /// Generic extraction requires runtime term reconstruction and is not an
    /// observable supported by the standalone artifact.
    Extract,
    /// Proof extraction/testing output is a separate follow-up from proof-mode
    /// relational/check parity.
    ProofExtraction,
    /// Function-row printing and its optional filesystem target are outside the
    /// admitted source-output event vocabulary.
    PrintFunction,
    /// Statistics may be printed as an event, but the artifact cannot write a
    /// source-selected file.
    FileStatistics,
    /// Generic expression output writes a source-selected file.
    Output,
    /// User-defined commands are host callbacks with no portable SQL authority.
    UserDefined,
    /// A command that should have been eliminated by the finalized frontend
    /// pipeline survived into capture.
    ResidualFrontendForm,
}

impl Display for StandalonePreflightReason {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(match self {
            Self::Include => "include commands are not part of a self-contained source artifact",
            Self::Push => "push commands require scoped frontend state",
            Self::Pop => "pop commands require scoped frontend state",
            Self::Presort => "presort-backed sorts do not have standalone SQL authority",
            Self::Extract => "extraction commands are outside standalone relational parity",
            Self::ProofExtraction => {
                "proof extraction commands are outside standalone relational parity"
            }
            Self::PrintFunction => "print-function commands are not standalone output events",
            Self::FileStatistics => {
                "file-targeted print-stats commands cannot write from the SQL artifact"
            }
            Self::Output => "output commands cannot write from the SQL artifact",
            Self::UserDefined => "user-defined commands require a host callback",
            Self::ResidualFrontendForm => {
                "an unlowered frontend-only command survived final resolution"
            }
        })
    }
}

/// Reject source forms that must not mutate compile-only frontend state before
/// whole-program admission has succeeded.
///
/// `Fail` is recursive: wrapping a stateful command does not make its type and
/// catalog effects safe to capture. This pass runs both on the parsed program
/// and on each macro expansion, before includes are opened or commands are
/// desugared/typechecked.
fn preflight_standalone_source_commands(commands: &[Command]) -> Result<(), Error> {
    for command in commands {
        let reason = match command {
            Command::Include(..) => Some(StandalonePreflightReason::Include),
            Command::Push(..) => Some(StandalonePreflightReason::Push),
            Command::Pop(..) => Some(StandalonePreflightReason::Pop),
            Command::Sort {
                presort_and_args: Some(_),
                ..
            } => Some(StandalonePreflightReason::Presort),
            Command::Extract(..) => Some(StandalonePreflightReason::Extract),
            Command::Prove(..) | Command::ProveExists(..) => {
                Some(StandalonePreflightReason::ProofExtraction)
            }
            Command::PrintFunction(..) => Some(StandalonePreflightReason::PrintFunction),
            Command::PrintOverallStatistics(_, Some(_)) => {
                Some(StandalonePreflightReason::FileStatistics)
            }
            Command::Output { .. } => Some(StandalonePreflightReason::Output),
            Command::UserDefined(..) => Some(StandalonePreflightReason::UserDefined),
            Command::Fail(_, nested) => {
                preflight_standalone_source_commands(nested)?;
                None
            }
            _ => None,
        };
        if let Some(reason) = reason {
            return Err(Error::UnsupportedStandaloneCommand {
                command: command.to_string(),
                reason,
            });
        }
    }
    Ok(())
}

/// Recheck both finalized streams before any nominal catalog or command arena
/// is published. This catches unsupported forms manufactured by desugaring or
/// proof instrumentation and treats a surviving `LetBegin` as an internal
/// frontend invariant failure.
fn preflight_standalone_resolved_commands(commands: &[ResolvedNCommand]) -> Result<(), Error> {
    for command in commands {
        let reason = match command {
            ResolvedNCommand::Sort {
                presort_and_args: Some(_),
                ..
            } => Some(StandalonePreflightReason::Presort),
            ResolvedNCommand::LetBegin(..) => Some(StandalonePreflightReason::ResidualFrontendForm),
            ResolvedNCommand::Extract(..) => Some(StandalonePreflightReason::Extract),
            ResolvedNCommand::PrintFunction(..) => Some(StandalonePreflightReason::PrintFunction),
            ResolvedNCommand::PrintOverallStatistics(_, Some(_)) => {
                Some(StandalonePreflightReason::FileStatistics)
            }
            ResolvedNCommand::ProveExists(..) => Some(StandalonePreflightReason::ProofExtraction),
            ResolvedNCommand::Output { .. } => Some(StandalonePreflightReason::Output),
            ResolvedNCommand::Push(..) => Some(StandalonePreflightReason::Push),
            ResolvedNCommand::Pop(..) => Some(StandalonePreflightReason::Pop),
            ResolvedNCommand::UserDefined(..) => Some(StandalonePreflightReason::UserDefined),
            ResolvedNCommand::Fail(_, nested) => {
                preflight_standalone_resolved_commands(nested)?;
                None
            }
            _ => None,
        };
        if let Some(reason) = reason {
            return Err(Error::UnsupportedStandaloneCommand {
                command: command.to_command().to_string(),
                reason,
            });
        }
    }
    Ok(())
}

/// Desugar one proof-generated command while attaching exact source-view sort
/// authority at the producer-stamped command path. Paths follow raw `Command`
/// nesting through `fail`; they are never recovered from a sort name or from
/// the generated command's shape.
fn desugar_term_encoded_command(
    command: Command,
    parser: &mut Parser,
    proof_testing: bool,
    lineages: Vec<SortLineage>,
) -> Result<(Vec<NCommand>, Vec<typechecking::SourceSortAuthorityAt>), Error> {
    if lineages.is_empty() {
        return Ok((desugar_command(command, parser, proof_testing)?, Vec::new()));
    }

    if lineages
        .iter()
        .any(|lineage| lineage.command_path.is_empty())
    {
        let [lineage] = lineages.as_slice() else {
            panic!("one generated command received overlapping sort lineage stamps");
        };
        assert!(
            lineage.command_path.is_empty(),
            "one generated command mixed self and descendant sort lineage stamps"
        );
        let desugared = desugar_command(command, parser, proof_testing)?;
        let [NCommand::Sort { .. }] = desugared.as_slice() else {
            panic!("proof instrumentation attached sort lineage to a non-sort command");
        };
        return Ok((
            desugared,
            vec![typechecking::SourceSortAuthorityAt {
                command_path: vec![0],
                source: lineage.source,
            }],
        ));
    }

    let Command::Fail(span, commands) = command else {
        panic!("proof instrumentation attached descendant lineage outside a fail command");
    };
    let mut lineages_by_child = (0..commands.len())
        .map(|_| Vec::new())
        .collect::<Vec<Vec<SortLineage>>>();
    for mut lineage in lineages {
        let child = lineage.command_path.remove(0);
        let Some(child_lineages) = lineages_by_child.get_mut(child) else {
            panic!("proof instrumentation emitted an out-of-range nested sort lineage stamp");
        };
        child_lineages.push(lineage);
    }

    let mut nested = Vec::new();
    let mut source_authorities = Vec::new();
    for (command, child_lineages) in commands.into_iter().zip(lineages_by_child) {
        let (child_commands, mut child_authorities) =
            desugar_term_encoded_command(command, parser, proof_testing, child_lineages)?;
        let offset = nested.len();
        for authority in &mut child_authorities {
            let first = authority
                .command_path
                .first_mut()
                .expect("source sort authority paths are never empty");
            *first += offset;
            authority.command_path.insert(0, 0);
        }
        source_authorities.extend(child_authorities);
        nested.extend(child_commands);
    }
    Ok((vec![NCommand::Fail(span, nested)], source_authorities))
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
    fn enable_term_encoding(&mut self, mut typechecker: EGraph) {
        self.type_info
            .set_view_domain(typechecking::FrontendViewDomain::Execution);
        typechecker
            .type_info
            .set_view_domain(typechecking::FrontendViewDomain::ProofCheck);
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
        self.enable_term_encoding(EGraph::default());
        self
    }

    /// Enable the term-encoding pipeline for a custom backend, using the given
    /// bridge-backed e-graph for parsing/typechecking before instrumentation.
    #[doc(hidden)]
    pub fn with_term_encoding_typechecker(mut self, typechecker: EGraph) -> Self {
        self.enable_term_encoding(typechecker);
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

    fn preserve_frontend_identity_history_from(&mut self, newer: &Self) {
        self.type_info
            .preserve_global_function_identity_history_from(&newer.type_info);
        self.type_info
            .preserve_primitive_registration_high_water_from(&newer.type_info);
        self.type_info
            .preserve_sort_registration_high_water_from(&newer.type_info);
        if let (Some(previous), Some(current)) = (
            self.proof_state.original_typechecking.as_deref_mut(),
            newer.proof_state.original_typechecking.as_deref(),
        ) {
            previous.preserve_frontend_identity_history_from(current);
        }
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
                // Resolved commands inside the popped scope retain exact global
                // registrations even though their diagnostic names leave the
                // active catalog. Keep that authority census monotone alongside
                // the registration generator's high-water mark.
                e.preserve_frontend_identity_history_from(self);
                *self = *e;
                Ok(())
            }
            None => Err(Error::Pop(span!())),
        }
    }

    fn translate_expr_to_mergefn(
        &self,
        expr: &ResolvedExpr,
    ) -> Result<egglog_bridge::MergeFn, Error> {
        match expr {
            GenericExpr::Lit(_, literal) => {
                let val = literal_to_value(self.backend.base_values(), literal);
                let ty = sort::literal_sort(literal).column_ty(self.backend.base_values());
                Ok(egglog_bridge::MergeFn::Const { value: val, ty })
            }
            GenericExpr::Var(_, resolved_var) => match resolved_var.binding {
                ResolvedVarBinding::MergeOld { column } => {
                    Ok(egglog_bridge::MergeFn::OldCol(column))
                }
                ResolvedVarBinding::MergeNew { column } => {
                    Ok(egglog_bridge::MergeFn::NewCol(column))
                }
                ResolvedVarBinding::MergeLet { slot } => Ok(egglog_bridge::MergeFn::LetVar(slot)),
                ResolvedVarBinding::Lexical { .. } | ResolvedVarBinding::Global { .. } => {
                    Err(Error::BackendError(format!(
                        "resolved merge variable {:?} lacks merge binding authority",
                        resolved_var.name
                    )))
                }
            },
            GenericExpr::Call(_, ResolvedCall::Func(f), args) => {
                let translated_args = args
                    .iter()
                    .map(|arg| self.translate_expr_to_mergefn(arg))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(egglog_bridge::MergeFn::Function(
                    self.functions[&f.name].backend_id,
                    translated_args,
                ))
            }
            GenericExpr::Call(_, ResolvedCall::Primitive(p), args) => {
                let mut translated_args = args
                    .iter()
                    .map(|arg| self.translate_expr_to_mergefn(arg))
                    .collect::<Result<Vec<_>, _>>()?;
                let mut input = p
                    .input()
                    .iter()
                    .map(|sort| sort.column_ty(self.backend.base_values()))
                    .collect::<Vec<_>>();
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
                    translated_args[0] = egglog_bridge::MergeFn::Const {
                        value: self.backend.base_values().get(resolved),
                        ty: ColumnTy::Base(self.backend.base_values().get_ty::<ResolvedFunction>()),
                    };
                    // `unstable-fn` is source-typed with a leading String name,
                    // but merge lowering resolves that name to the runtime
                    // `ResolvedFunction` handle consumed by its registered
                    // callback. Describe the actual lowered call boundary.
                    input[0] =
                        ColumnTy::Base(self.backend.base_values().get_ty::<ResolvedFunction>());
                }
                Ok(egglog_bridge::MergeFn::Primitive {
                    id: p.external_id(crate::Context::Write),
                    name: p.name().to_owned(),
                    input,
                    output: p.output().column_ty(self.backend.base_values()),
                    args: translated_args,
                })
            }
            // `(values ...)` never legitimately reaches here: a top-level tuple merge is
            // destructured per column in `declare_function`, and any other `(values ...)` is
            // rejected during type-checking. This arm only keeps the match exhaustive.
            GenericExpr::Call(span, ResolvedCall::Values(_), _) => Err(Error::TypeError(
                TypeError::TupleMergeNotValues("<merge>".to_owned(), span.clone()),
            )),
        }
    }

    /// Lower a resolved `:merge` (a value-producing action block) to a backend [`egglog_bridge::MergeFn`], keeping
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
        // Lower the result value (a `(values ...)` result becomes one column per element).
        let result = match &merge.result {
            GenericExpr::Call(_, ResolvedCall::Values(_), cols) => MergeFn::Columns(
                cols.iter()
                    .map(|e| self.translate_expr_to_mergefn(e))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            expr => self.translate_expr_to_mergefn(expr)?,
        };
        if merge.actions.is_empty() {
            return Ok(result);
        }
        // A value-producing action block: run the effects, then evaluate the result value(s).
        let actions = merge
            .actions
            .iter()
            .map(|a| self.translate_merge_action(a, self_ref))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(MergeFn::Block {
            actions,
            result: Box::new(result),
        })
    }

    /// Lower a single resolved merge action to a backend [`egglog_bridge::MergeAction`]. Supports `set`, `let`, and
    /// `union`; other actions (`delete`/`panic`/`extract`/...) are not meaningful during a merge.
    fn translate_merge_action(
        &self,
        action: &ResolvedAction,
        self_ref: (&str, egglog_bridge::FunctionId),
    ) -> Result<egglog_bridge::MergeAction, Error> {
        use egglog_bridge::MergeAction;
        match action {
            GenericAction::Let(_, var, expr) => {
                let ResolvedVarBinding::MergeLet { slot } = var.binding else {
                    return Err(Error::BackendError(format!(
                        "resolved merge let {:?} lacks slot authority",
                        var.name
                    )));
                };
                Ok(MergeAction::Let {
                    slot,
                    value: self.translate_expr_to_mergefn(expr)?,
                })
            }
            GenericAction::Union(_, a, b) => Ok(MergeAction::Union(
                self.translate_expr_to_mergefn(a)?,
                self.translate_expr_to_mergefn(b)?,
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
                    .map(|k| self.translate_expr_to_mergefn(k))
                    .collect::<Result<Vec<_>, _>>()?;
                // A tuple-output target is set with `(values ...)`; expand it into value columns.
                match val {
                    GenericExpr::Call(_, ResolvedCall::Values(_), cols) => {
                        for c in cols {
                            args.push(self.translate_expr_to_mergefn(c)?);
                        }
                    }
                    _ => args.push(self.translate_expr_to_mergefn(val)?),
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
        let schema = input
            .iter()
            .chain(outputs.iter())
            .map(|sort| sort.column_ty(self.backend.base_values()))
            .collect();
        let config = egglog_bridge::FunctionConfig {
            schema,
            n_vals: num_outputs,
            n_identity_vals: decl.identity_vals,
            default: match decl.subtype {
                FunctionSubtype::Constructor => DefaultVal::FreshId,
                FunctionSubtype::Custom => DefaultVal::Fail,
            },
            merge,
            name: decl.name.to_string(),
            can_subsume,
        };
        let backend_id = self.backend.add_table(config);
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
        let resolved =
            proof_check_eg.process_program_internal(prog, ProgramProcessingMode::ResolvePublic)?;

        self.proof_check_program = resolved.resolved_before_proofs.commands;
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

    // returns whether the egraph was updated
    fn run_schedule(&mut self, sched: &ResolvedSchedule) -> Result<RunReport, Error> {
        match sched {
            ResolvedSchedule::Run(span, config) => self.run_rules(span, config),
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

    fn schedule_for_log(sched: &ResolvedSchedule) -> String {
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
                    for (_, id) in rules.values() {
                        ids.push(*id);
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

        let core_rule = rule.to_canonicalized_core_rule(
            &self.type_info,
            &mut self.parser.symbol_gen,
            union_to_set,
        )?;
        let (query, actions) = (&core_rule.body, &core_rule.head);
        let rule_id = {
            let mut translator = BackendRule::new(
                &mut *self.backend,
                &self.functions,
                &self.type_info,
                requires_read_context,
            );
            translator.query(query, rule.include_subsumed)?;
            translator.actions(actions)?;
            translator.try_build(&rule.name, seminaive, no_decomp, core_rule.span.clone())?
        };

        let Some(Ruleset::Rules(rules)) = self.rulesets.get_mut(&rule.ruleset) else {
            unreachable!("ruleset was validated before compiling the rule")
        };
        match rules.entry(rule.name.clone()) {
            indexmap::map::Entry::Occupied(_) => {
                panic!("Rule '{}' was already present", rule.name)
            }
            indexmap::map::Entry::Vacant(e) => e.insert((core_rule, rule_id)),
        };
        Ok(rule.name)
    }

    fn eval_actions(&mut self, actions: &ResolvedActions) -> Result<(), Error> {
        let mut binding = IndexSet::default();
        let mut ctx = CoreActionContext::new(
            &self.type_info,
            &mut binding,
            &mut self.parser.symbol_gen,
            self.proof_state.original_typechecking.is_none(),
        );
        let (actions, _) = actions.to_core_actions(&mut ctx)?;

        let mut translator = BackendRule::new(
            &mut *self.backend,
            &self.functions,
            &self.type_info,
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
                .extend(resolved.desugared_before_proofs.commands);
        }
        let resolved_commands = resolved.desugared.commands;

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
        let expr = self.prepare_unstable_fn_targets_for_eval_inner(expr, &mut bindings)?;
        Ok((expr, bindings))
    }

    fn prepare_unstable_fn_targets_for_eval_inner(
        &mut self,
        expr: &ResolvedExpr,
        bindings: &mut Vec<(String, Value)>,
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
                    let panic_id = self.backend.new_panic(format!(
                        "unstable-fn over `{name}` was applied in a context where its wrapped \
                         function is not valid for this call site, if in a rule, add :naive."
                    ));
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
                    let resolved_function = match resolved_function {
                        Ok(resolved) => resolved,
                        Err(error) => {
                            self.backend.free_external_func(panic_id);
                            return Err(error);
                        }
                    };
                    let fn_value = self.backend.base_values().get(resolved_function);
                    let binding_name = self.parser.symbol_gen.fresh("unstable_fn_target");
                    bindings.push((binding_name.clone(), fn_value));
                    let mut prepared_children = Vec::with_capacity(children.len());
                    prepared_children.push(ResolvedExpr::Var(
                        target_span.clone(),
                        ResolvedVar {
                            name: binding_name,
                            sort: children[0].output_type(),
                            binding: ResolvedVarBinding::Lexical {
                                id: self.parser.symbol_gen.fresh_resolved_binding_id(),
                            },
                            is_global_ref: false,
                        },
                    ));
                    for child in &children[1..] {
                        prepared_children.push(
                            self.prepare_unstable_fn_targets_for_eval_inner(child, bindings)?,
                        );
                    }
                    return Ok(ResolvedExpr::Call(
                        span.clone(),
                        resolved_call.clone(),
                        prepared_children,
                    ));
                }

                let prepared_children = children
                    .iter()
                    .map(|child| self.prepare_unstable_fn_targets_for_eval_inner(child, bindings))
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
            true, // global action: Read/Full contexts (may read the DB)
        );
        translator.rollback_external_funcs.push(ext_id);

        let result_var = ResolvedVar {
            name: self.parser.symbol_gen.fresh("eval_resolved_expr"),
            sort: expr.output_type(),
            binding: ResolvedVarBinding::Lexical {
                id: self.parser.symbol_gen.fresh_resolved_binding_id(),
            },
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
        self.backend.free_external_func(ext_id);
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
            self.proof_state.original_typechecking.is_none(),
        )?;
        let query = core_rule.body;

        let observer = MatchObserver::new();
        let ext_id = self.backend.register_match_observer(observer.clone());

        let mut translator = BackendRule::new(
            &mut *self.backend,
            &self.functions,
            &self.type_info,
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
        self.backend.free_external_func(ext_id);
        run_result.map_err(|e| Error::BackendError(e.to_string()))?;

        if !observer.matched() {
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
            ResolvedNCommand::Index { name, function, .. } => {
                // Nothing to build: the backend creates the occurrence index the
                // first time a rule probes it. Typechecking already registered
                // the relation the atoms resolve against.
                log::info!("Declared index {name} over {function}.");
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
            ResolvedNCommand::Fail(span, cmds) => {
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

        let mut row_schema = function_type.input.clone();
        // Relations desugar to constructors, so their implicit output is not a TSV column.
        if function_type.subtype == FunctionSubtype::Custom {
            row_schema.extend(function_type.outputs.iter().cloned());
        }
        Self::read_input_rows(fact_directory, &row_schema, span, file)
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
        for line in contents.lines() {
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
                    name => panic!("Unsupported type {name} for input"),
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

    fn input_file(&mut self, span: Span, func_name: &str, file: String) -> Result<(), Error> {
        // A declared index has a function type but no table of its own to load
        // rows into.
        if self.type_info.indexes.contains_key(func_name) {
            return Err(TypeError::IndexIsReadOnly(func_name.to_owned(), span).into());
        }
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
        let mut batch: Vec<(egglog_bridge::FunctionId, Vec<NativeInputValue>)> = Vec::new();
        let mut next_fresh_slot = 0u32;
        let mut fresh = || -> Result<NativeInputValue, Error> {
            if next_fresh_slot == u32::MAX {
                return Err(Error::BackendError(
                    "native input fresh-slot count exceeds the usable Value domain".to_string(),
                ));
            }
            let slot = next_fresh_slot;
            next_fresh_slot += 1;
            Ok(NativeInputValue::FreshSlot(slot))
        };
        for value_row in value_rows {
            let fv = fresh()?;
            // Term-relation row: CSV columns (children [+ output]) + term id + Unit.
            let mut frow = value_row
                .iter()
                .copied()
                .map(NativeInputValue::Existing)
                .collect::<Vec<_>>();
            frow.push(fv);
            frow.push(NativeInputValue::Existing(unit_val));
            batch.push((f_id, frow));

            let view_proof = if let Some((ast_id, fiat_id, proof_func_id)) = proof_tables {
                // Fiat proof of the base fact: `@Fiat(ast(fv), ast(fv))`.
                let a1 = fresh()?;
                batch.push((ast_id, vec![fv, a1, NativeInputValue::Existing(unit_val)]));
                let a2 = fresh()?;
                batch.push((ast_id, vec![fv, a2, NativeInputValue::Existing(unit_val)]));
                let pf = fresh()?;
                batch.push((
                    fiat_id,
                    vec![a1, a2, pf, NativeInputValue::Existing(unit_val)],
                ));
                if let Some(proof_func_id) = proof_func_id {
                    batch.push((proof_func_id, vec![fv, pf]));
                }
                pf
            } else {
                NativeInputValue::Existing(unit_val)
            };

            // View row. A constructor's FD view value-0 is the minted term id; a
            // custom view stores the base output (already in `value_row`). The
            // proof column follows (`Unit` when the encoding carries no proofs).
            let mut vrow = value_row
                .into_iter()
                .map(NativeInputValue::Existing)
                .collect::<Vec<_>>();
            if is_constructor {
                vrow.push(fv);
            }
            vrow.push(view_proof);
            batch.push((view_id, vrow));
        }
        self.backend
            .add_values_with_fresh(batch)
            .map_err(|error| Error::BackendError(error.to_string()))?;
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
    ) -> Result<typechecking::FinalizedProgram, Error> {
        let desugared = desugar_command(command, &mut self.parser, self.proof_state.proof_testing)?;
        if let Some(original_typechecking) = self.proof_state.original_typechecking.as_mut() {
            // Typecheck using the original egraph
            // TODO this is ugly- we don't need an entire e-graph just for type information.
            let typechecked = original_typechecking
                .typecheck_program_with_sort_authority(&desugared, Vec::new())?;

            let mut authorities_by_command = (0..typechecked.commands.len())
                .map(|_| Vec::new())
                .collect::<Vec<Vec<typechecking::SortAuthorityAt>>>();
            for mut authority in typechecked.sort_authorities.iter().cloned() {
                let top = authority.command_path.remove(0);
                authorities_by_command
                    .get_mut(top)
                    .expect("validated proof-admission sort path was out of range")
                    .push(authority);
            }
            for (command, sort_authorities) in
                typechecked.commands.iter().zip(authorities_by_command)
            {
                if let Err(reason) = command_supports_proof_encoding_with_sort_authorities(
                    command,
                    &original_typechecking.type_info,
                    &sort_authorities,
                ) {
                    // Proof checking needs each input expanded into top-level
                    // fiat actions, which cannot preserve a surrounding
                    // `fail`. Term-encoding-only backends do not build that
                    // proof-check program: keep the input nested so the
                    // backend's fallible native-input boundary is observed by
                    // `fail` itself.
                    let term_only_single_fail_input = !self.proof_state.proofs_enabled
                        && matches!(&reason, ProofEncodingUnsupportedReason::FailInputCommand)
                        && matches!(
                            command,
                            ResolvedNCommand::Fail(_, commands)
                                if matches!(commands.as_slice(), [ResolvedNCommand::Input { .. }])
                        );
                    if !term_only_single_fail_input {
                        let command_text = format!("{}", command.to_command());
                        return Err(Error::UnsupportedProofCommand {
                            command: command_text,
                            reason,
                        });
                    }
                }
            }

            let commands = proof_form(typechecked.commands, &mut self.parser.symbol_gen);
            Ok(typechecking::FinalizedProgram::new(
                commands,
                typechecked.sort_authorities,
            ))
        } else {
            let typechecked = self.typecheck_program_with_sort_authority(&desugared, Vec::new())?;
            let typechecked = remove_globals::remove_globals_with_sort_authority(
                typechecked,
                &mut self.parser.symbol_gen,
            );
            for command in &typechecked.commands {
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
                desugared_before_proofs: typechecking::FinalizedProgram::empty(),
            })
        } else {
            // The proof checker consumes the per-row top-level fiat actions.
            let per_row_before_proofs =
                ProofInstrumentor::lower_inputs(self, resolved_before_proofs.clone())?;
            // Execution keeps every `(input …)` as an `Input` command, loaded
            // natively at run time by `EGraph::native_input` straight into the
            // encoded tables. Globals get the same function-style desugaring
            // (`remove_globals`) as the non-encoding path.
            let typechecked_no_globals = remove_globals::remove_globals_with_sort_authority(
                resolved_before_proofs,
                &mut self.parser.symbol_gen,
            );
            // The term encoder runs before the encoded program is typechecked, so it
            // can't rely on the later typecheck to populate `global_sorts`. Register
            // the new global functions' sorts eagerly so `is_global` recognizes them
            // while encoding.
            for command in &typechecked_no_globals.commands {
                if let GenericNCommand::Function(fdecl) = command
                    && fdecl.internal_let
                    && let Some(output_sort) = self.type_info.sorts.get(fdecl.schema.output())
                {
                    self.type_info
                        .global_sorts
                        .insert(fdecl.name.clone(), output_sort.clone());
                }
            }
            for command in &typechecked_no_globals.commands {
                self.names.check_shadowing(command)?;
            }

            let term_encoding_added =
                ProofInstrumentor::add_term_encoding(self, typechecked_no_globals)?;
            let mut new_typechecked = Vec::new();
            let mut new_sort_authorities = Vec::new();
            let mut sort_lineages = term_encoding_added.sort_lineages.into_iter().peekable();
            for (generated_index, new_cmd) in term_encoding_added.commands.into_iter().enumerate() {
                let mut command_lineages = Vec::new();
                loop {
                    let Some(next_index) = sort_lineages.peek().map(|lineage| {
                        *lineage
                            .command_path
                            .first()
                            .expect("sort lineage paths are never empty")
                    }) else {
                        break;
                    };
                    assert!(
                        next_index >= generated_index,
                        "proof instrumentation emitted unordered sort lineage stamps"
                    );
                    if next_index != generated_index {
                        break;
                    }
                    let mut lineage = sort_lineages.next().unwrap();
                    lineage.command_path.remove(0);
                    command_lineages.push(lineage);
                }
                let (desugared, source_authorities) = desugar_term_encoded_command(
                    new_cmd,
                    &mut self.parser,
                    self.proof_state.proof_testing,
                    command_lineages,
                )?;
                for cmd in &desugared {
                    log::trace!("Desugared term encoding: {}", cmd.to_command());
                }

                // Now typecheck using self, adding term type information.
                let desugared_typechecked =
                    self.typecheck_program_with_sort_authority(&desugared, source_authorities)?;
                // Remove the globals the term encoding itself introduced (its minted
                // `let`s), the same way source-level globals were removed above.
                let desugared_typechecked = remove_globals::remove_globals_with_sort_authority(
                    desugared_typechecked,
                    &mut self.parser.symbol_gen,
                );
                let offset = new_typechecked.len();
                for mut authority in desugared_typechecked.sort_authorities {
                    let top = authority
                        .command_path
                        .first_mut()
                        .expect("finalized sort authority paths are never empty");
                    *top += offset;
                    new_sort_authorities.push(authority);
                }
                new_typechecked.extend(desugared_typechecked.commands);
            }
            assert!(
                sort_lineages.next().is_none(),
                "proof instrumentation emitted an out-of-range sort lineage stamp"
            );
            Ok(ResolvedNCommands {
                desugared: typechecking::FinalizedProgram::new(
                    new_typechecked,
                    new_sort_authorities,
                ),
                desugared_before_proofs: per_row_before_proofs,
            })
        }
    }

    /// Process a program for execution, public resolution, or backend-free
    /// compiler resolution.
    fn process_program_internal(
        &mut self,
        program: Vec<Command>,
        mode: ProgramProcessingMode,
    ) -> Result<ResolvedNCommandsWithOutput, Error> {
        self.process_program_internal_groups(vec![ProgramInputGroup::Detached(program)], mode)
    }

    fn process_program_internal_groups(
        &mut self,
        groups: Vec<ProgramInputGroup>,
        mode: ProgramProcessingMode,
    ) -> Result<ResolvedNCommandsWithOutput, Error> {
        let mut outputs = Vec::new();
        let mut desugared_before_proofs = typechecking::FinalizedProgram::empty();
        let mut desugared_before_proofs_source_triggers = Vec::new();
        let mut desugared = typechecking::FinalizedProgram::empty();
        let mut desugared_source_triggers = Vec::new();

        for group in groups {
            let commands = match group {
                ProgramInputGroup::Detached(commands) => commands
                    .into_iter()
                    .map(|command| (None, command))
                    .collect::<Vec<_>>(),
                ProgramInputGroup::Source(group) => group
                    .subcommands
                    .into_iter()
                    .map(|command| {
                        debug_assert_eq!(command.source.group, group.id);
                        (Some(command.source), command.command)
                    })
                    .collect(),
            };

            for (source_trigger, before_expanded_command) in commands {
                if mode.builds_standalone_snapshot() && source_trigger.is_none() {
                    return Err(Error::StandaloneSnapshotInvariant {
                        message: "compile-only command is missing its physical source trigger",
                    });
                }

                // First do user-provided macro expansion for this command,
                // which may rely on type information from previous commands.
                let macro_type_info = self
                    .proof_state
                    .original_typechecking
                    .as_ref()
                    .map(|egraph| &egraph.type_info)
                    .unwrap_or(&self.type_info);
                let macro_expanded = if mode.builds_standalone_snapshot() {
                    // Post-parse command macros do not yet return provenance
                    // stamps. A one-to-one transformation can inherit the
                    // exact parsed trigger, but every individual macro stage
                    // must remain one-to-one: a later macro must not hide an
                    // earlier unstamped deletion or fan-out.
                    vec![self.command_macros.apply_one_to_one_for_standalone(
                        before_expanded_command,
                        &mut self.parser.symbol_gen,
                        macro_type_info,
                    )?]
                } else {
                    self.command_macros.apply(
                        before_expanded_command,
                        &mut self.parser.symbol_gen,
                        macro_type_info,
                    )?
                };

                // A macro can manufacture an unsupported stateful command even
                // when the parsed source itself was admissible. Check the complete
                // expansion before following an include or typechecking any sibling
                // command from that expansion.
                if mode.builds_standalone_snapshot() {
                    preflight_standalone_source_commands(&macro_expanded)?;
                }

                for command in macro_expanded {
                    // handle include specially- we keep them as-is for desugaring
                    if let Command::Include(span, file) = &command {
                        let s = std::fs::read_to_string(file)
                            .map_err(|e| Error::IoError(file.clone().into(), e, span.clone()))?;
                        let included_program = self
                            .parser
                            .get_program_from_string(Some(file.clone()), &s)?;
                        // run program internal on these include commands
                        let resolved = self.process_program_internal(included_program, mode)?;
                        outputs.extend(resolved.outputs);
                        desugared.append(resolved.resolved);
                        desugared_before_proofs.append(resolved.resolved_before_proofs);
                    } else {
                        let resolved = self.resolve_command(command)?;
                        if mode.runs_commands() && self.are_proofs_enabled() {
                            self.proof_check_program
                                .extend(resolved.desugared_before_proofs.commands.clone());
                        }

                        if let Some(source_trigger) = source_trigger {
                            desugared_before_proofs_source_triggers.extend(std::iter::repeat_n(
                                source_trigger,
                                resolved.desugared_before_proofs.commands.len(),
                            ));
                            desugared_source_triggers.extend(std::iter::repeat_n(
                                source_trigger,
                                resolved.desugared.commands.len(),
                            ));
                        }
                        desugared_before_proofs.append(resolved.desugared_before_proofs);
                        desugared.append(resolved.desugared.clone());

                        for processed in resolved.desugared.commands {
                            // Public desugaring retains its historical scoped-state
                            // behavior. Compiler resolution retains Push/Pop in the
                            // stream without executing either command.
                            if mode.runs_commands()
                                || mode.executes_push_pop()
                                    && matches!(
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
        }

        Ok(ResolvedNCommandsWithOutput {
            outputs,
            resolved_before_proofs: desugared_before_proofs,
            resolved_before_proofs_source_triggers: desugared_before_proofs_source_triggers,
            resolved: desugared,
            resolved_source_triggers: desugared_source_triggers,
        })
    }

    /// Run a program, represented as an AST.
    /// Return a list of messages.
    pub fn run_program(&mut self, program: Vec<Command>) -> Result<Vec<CommandOutput>, Error> {
        if self.backend.requires_term_encoding() && self.proof_state.original_typechecking.is_none()
        {
            return Err(Error::BackendRequiresTermEncoding);
        }
        let res = self.process_program_internal(program, ProgramProcessingMode::Run)?;
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
        Ok(self
            .resolve_program_with_sort_authority(filename, input)?
            .commands
            .into_iter()
            .map(|command| command.to_command())
            .collect())
    }

    pub(crate) fn resolve_program_with_sort_authority(
        &mut self,
        filename: Option<String>,
        input: &str,
    ) -> Result<typechecking::FinalizedProgram, Error> {
        let parsed = self.parser.get_program_from_string(filename, input)?;
        let res = self.process_program_internal(parsed, ProgramProcessingMode::ResolvePublic)?;
        Ok(res.resolved)
    }

    /// Resolve source through the complete frontend pipeline without attaching
    /// or invoking an execution backend.
    ///
    /// Stateful raw source forms are rejected for the whole program before any
    /// command is typechecked. Macro expansions receive the same check before
    /// processing, with the complete frontend transaction restored on failure.
    #[allow(dead_code)]
    pub(crate) fn resolve_program_compile_only(
        &mut self,
        filename: Option<String>,
        input: &str,
    ) -> Result<CompileOnlyResolvedProgram, Error> {
        assert!(
            self.backend.is_compile_only(),
            "resolve_program_compile_only requires EGraph::new_compile_only"
        );
        // Macro expansion is type-dependent, so a command late in the source
        // cannot always be admitted before earlier declarations are resolved.
        // Resolve against this clone-backed transaction and restore every
        // frontend-owned allocator/catalog/parser field if any later phase
        // rejects. Successful resolution commits the accumulated typed state.
        let checkpoint = self.clone();
        let resolved = (|| {
            let parsed = self
                .parser
                .get_program_from_string_grouped(filename, input)?;
            let frontend_capture::FrontendSourceSeed { document, groups } =
                frontend_capture::capture_source_seed(parsed).map_err(|_| {
                    Error::StandaloneSnapshotInvariant {
                        message: "physical source identity exceeds the standalone ID domain",
                    }
                })?;

            // Parser-level command macros have already produced authoritative
            // group-local subcommand identities. Preflight every such command
            // before resolving any sibling, while retaining empty physical
            // groups in `document`.
            for group in &groups {
                for command in &group.subcommands {
                    preflight_standalone_source_commands(std::slice::from_ref(&command.command))?;
                }
            }
            let resolved = self.process_program_internal_groups(
                groups.into_iter().map(ProgramInputGroup::Source).collect(),
                ProgramProcessingMode::CompileOnly,
            )?;
            preflight_standalone_resolved_commands(&resolved.resolved.commands)?;
            preflight_standalone_resolved_commands(&resolved.resolved_before_proofs.commands)?;
            if resolved.resolved.commands.len() != resolved.resolved_source_triggers.len() {
                return Err(Error::StandaloneSnapshotInvariant {
                    message: "execution command/source-origin cardinality mismatch",
                });
            }
            if resolved.resolved_before_proofs.commands.len()
                != resolved.resolved_before_proofs_source_triggers.len()
            {
                return Err(Error::StandaloneSnapshotInvariant {
                    message: "proof-check command/source-origin cardinality mismatch",
                });
            }
            Ok((document, resolved))
        })();
        let (source, resolved) = match resolved {
            Ok(resolved) => resolved,
            Err(error) => {
                *self = checkpoint;
                return Err(error);
            }
        };
        let typechecking::FinalizedProgram {
            commands: execution_commands,
            sort_authorities: execution_sort_authorities,
        } = resolved.resolved;
        let typechecking::FinalizedProgram {
            commands: proof_check_commands,
            sort_authorities: proof_check_sort_authorities,
        } = resolved.resolved_before_proofs;
        Ok(CompileOnlyResolvedProgram {
            execution: resolved
                .resolved_source_triggers
                .into_iter()
                .zip(execution_commands)
                .map(|(source_trigger, command)| CompileOnlyResolvedCommand {
                    source_trigger,
                    command,
                })
                .collect(),
            execution_sort_authorities,
            proof_check: resolved
                .resolved_before_proofs_source_triggers
                .into_iter()
                .zip(proof_check_commands)
                .map(|(source_trigger, command)| CompileOnlyResolvedCommand {
                    source_trigger,
                    command,
                })
                .collect(),
            proof_check_sort_authorities,
            source,
        })
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

    /// Whether two sort carriers resolve to the same exact authority in this
    /// e-graph's frontend view.
    pub fn same_sort(&self, left: &ArcSort, right: &ArcSort) -> bool {
        self.type_info.same_sort(left, right)
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
    /// `facts` and return one `HashMap` per match, keyed by variable
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
                self.backend.free_rule(rule.1);
            }
        }
        outcome?;

        let Some(mutex) = Arc::into_inner(results) else {
            panic!("`results_weak` outlived the callback");
        };
        Ok(mutex.into_inner().unwrap())
    }
}

pub use crate::api::{ApiError, FromValue, FromValues, IntoValue, IntoValues, RawValues};

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
        requires_read_context: bool,
    ) -> BackendRule<'a> {
        BackendRule {
            backend,
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
            // Pre-register a panic id used by `FunctionContainer::apply`
            // when the wrapped function is applied in a context that
            // doesn't admit it. Triggered at runtime via the egglog
            // panic side channel so misuse surfaces as an `Err` from
            // `run_rules` rather than a thread unwind.
            let panic_id = self.backend.new_panic(format!(
                "unstable-fn over `{name}` was applied in a context where its wrapped \
                 function is not valid for this call site, if in a rule, add :naive."
            ));
            self.rollback_external_funcs.push(panic_id);
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

    /// Establish which occurrence probes are reachable without scanning a
    /// multi-column index. Ordinary function rows seed bindings, then reachable
    /// index rows extend them to a fixed point independently of source order.
    fn check_index_values_are_reachable(
        &self,
        query: &core::Query<ResolvedCall, ResolvedVar>,
    ) -> Result<(), Error> {
        let mut reachable = HashSet::<ResolvedVar>::default();
        for atom in &query.atoms {
            let ResolvedCall::Func(function) = &atom.head else {
                continue;
            };
            if self.type_info.indexes.contains_key(&function.name) {
                // Every synthetic index result is canonical Unit, so it is
                // known before any row is joined and may probe another index.
                if let Some(core::GenericAtomTerm::Var(_, variable)) = atom.args.last() {
                    reachable.insert(variable.clone());
                }
                continue;
            }
            for argument in &atom.args {
                if let core::GenericAtomTerm::Var(_, variable) = argument {
                    reachable.insert(variable.clone());
                }
            }
        }

        let mut admitted_indices = HashSet::<usize>::default();
        loop {
            let mut changed = false;
            for (atom_index, atom) in query.atoms.iter().enumerate() {
                let ResolvedCall::Func(function) = &atom.head else {
                    continue;
                };
                let Some(index) = self.type_info.indexes.get(&function.name) else {
                    continue;
                };
                if admitted_indices.contains(&atom_index) {
                    continue;
                }
                let Some((probe, rest)) = atom.args.split_first() else {
                    continue;
                };
                let Some((_unit, row)) = rest.split_last() else {
                    continue;
                };
                let any_of = index.any_of.iter().copied().collect::<HashSet<_>>();
                let ready = match probe {
                    core::GenericAtomTerm::Literal(..) => true,
                    core::GenericAtomTerm::Var(_, variable) => {
                        reachable.contains(variable)
                            || row.iter().enumerate().any(|(column, term)| {
                                any_of.contains(&column)
                                    && matches!(term, core::GenericAtomTerm::Var(_, row) if row == variable)
                            })
                            || any_of.len() == 1
                    }
                    core::GenericAtomTerm::Global(..) => false,
                };
                if !ready {
                    continue;
                }
                if let core::GenericAtomTerm::Var(_, variable) = probe {
                    reachable.insert(variable.clone());
                }
                for term in row {
                    if let core::GenericAtomTerm::Var(_, variable) = term {
                        reachable.insert(variable.clone());
                    }
                }
                admitted_indices.insert(atom_index);
                changed = true;
            }
            if !changed {
                break;
            }
        }

        for (atom_index, atom) in query.atoms.iter().enumerate() {
            let ResolvedCall::Func(index) = &atom.head else {
                continue;
            };
            if !self.type_info.indexes.contains_key(&index.name)
                || admitted_indices.contains(&atom_index)
            {
                continue;
            }
            let Some(
                core::GenericAtomTerm::Var(span, value)
                | core::GenericAtomTerm::Global(span, value),
            ) = atom.args.first()
            else {
                continue;
            };
            return Err(TypeError::IndexValueUnbound(
                index.name.clone(),
                value.name.clone(),
                span.clone(),
            )
            .into());
        }
        Ok(())
    }

    fn query(
        &mut self,
        query: &core::Query<ResolvedCall, ResolvedVar>,
        include_subsumed: bool,
    ) -> Result<(), Error> {
        // IndexTable is a synthetic occurrence view whose result is always
        // canonical Unit. Seed every such result before lowering any body atom
        // or checking probe reachability, so every consumer observes the same
        // source-order-independent constant.
        for atom in &query.atoms {
            let ResolvedCall::Func(function) = &atom.head else {
                continue;
            };
            if !self.type_info.indexes.contains_key(&function.name) {
                continue;
            }
            let output = atom
                .args
                .last()
                .expect("typed index atom includes its Unit output");
            self.entries.insert(
                output.clone(),
                core::GenericAtomTerm::Literal(
                    output.span().clone(),
                    RuleValue {
                        value: self.backend.base_values().get(()),
                        ty: ColumnTy::Base(self.backend.base_values().get_ty::<()>()),
                    },
                ),
            );
        }
        self.check_index_values_are_reachable(query)?;
        for atom in &query.atoms {
            let read = if include_subsumed {
                ReadMode::All
            } else {
                ReadMode::Live
            };
            let (head, args) = match &atom.head {
                // An atom on a declared index reads the rows of the indexed
                // function, reached through the value its first argument binds.
                ResolvedCall::Func(f) if self.type_info.indexes.contains_key(&f.name) => {
                    let index = self.type_info.indexes[&f.name].clone();
                    let indexed = self
                        .type_info
                        .get_func_type(&index.function)
                        .expect("index target checked at declaration")
                        .clone();
                    (
                        RuleBodyCall::IndexTable {
                            id: self.func(&indexed),
                            any_of: index.any_of,
                            read,
                        },
                        self.args(&atom.args)?,
                    )
                }
                ResolvedCall::Func(f) => (
                    RuleBodyCall::Table {
                        id: self.func(f),
                        read,
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

    /// A declared index is a view the database maintains, so an action writing
    /// to one is rejected.
    fn reject_index_write(&self, call: &ResolvedCall, span: &Span) -> Result<(), Error> {
        if let ResolvedCall::Func(f) = call
            && self.type_info.indexes.contains_key(&f.name)
        {
            return Err(TypeError::IndexIsReadOnly(f.name.clone(), span.clone()).into());
        }
        Ok(())
    }

    fn actions(&mut self, actions: &core::ResolvedCoreActions) -> Result<(), Error> {
        for action in &actions.0 {
            match action {
                core::GenericCoreAction::Let(span, _, f, _)
                | core::GenericCoreAction::Set(span, f, _, _)
                | core::GenericCoreAction::Change(span, _, f, _) => {
                    self.reject_index_write(f, span)?;
                }
                _ => {}
            }
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
        };
        let result = self
            .backend
            .add_rule(spec)
            .map_err(|error| Error::BackendError(error.to_string()));
        if result.is_ok() {
            self.rollback_external_funcs.clear();
        }
        result
    }
}

impl Drop for BackendRule<'_> {
    fn drop(&mut self) {
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
        "Command is not supported by standalone SQL compilation.\n\
         Reason: {reason}\n\
         Offending command: {command}"
    )]
    UnsupportedStandaloneCommand {
        command: String,
        reason: StandalonePreflightReason,
    },
    #[error("standalone snapshot {arena} exceed the u64 ordinal domain")]
    StandaloneOrdinalOverflow { arena: &'static str },
    #[error("standalone frontend invariant failed: {message}")]
    StandaloneSnapshotInvariant { message: &'static str },
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
    use egglog_bridge::MergeFn;

    use crate::PureState;

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
    struct AuthorityDecoy;

    impl Primitive for AuthorityDecoy {
        fn name(&self) -> &str {
            "authority-decoy"
        }

        fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
            SimpleTypeConstraint::new(
                self.name(),
                vec![
                    I64Sort.to_arcsort(),
                    I64Sort.to_arcsort(),
                    I64Sort.to_arcsort(),
                ],
                span.clone(),
            )
            .into_box()
        }
    }

    impl PurePrim for AuthorityDecoy {
        fn apply<'a, 'db>(&self, state: PureState<'a, 'db>, args: &[Value]) -> Option<Value> {
            let [left, right] = args else {
                return None;
            };
            let left = state.base_values().unwrap::<i64>(*left);
            let right = state.base_values().unwrap::<i64>(*right);
            Some(state.base_values().get::<i64>(left + right))
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

    fn compile_only_state(egraph: &EGraph) -> &CompileOnlyBackendState {
        match &egraph.backend {
            BackendSlot::CompileOnly(state) => state,
            BackendSlot::Runtime(_) => panic!("expected a compile-only frontend"),
        }
    }

    fn type_info_sort_registration_fingerprint(
        type_info: &TypeInfo,
    ) -> Vec<(
        SortRegistrationId,
        String,
        typechecking::RegisteredSortKind,
        bool,
    )> {
        type_info
            .sort_registrations_in_order()
            .map(|registration| {
                (
                    registration.identity,
                    registration.sort.name().to_owned(),
                    registration.kind,
                    registration.unionable,
                )
            })
            .collect()
    }

    fn sort_registration_fingerprint(
        egraph: &EGraph,
    ) -> Vec<(
        SortRegistrationId,
        String,
        typechecking::RegisteredSortKind,
        bool,
    )> {
        type_info_sort_registration_fingerprint(&egraph.type_info)
    }

    #[test]
    #[should_panic(expected = "compile-only frontend attempted to access an execution backend")]
    fn compile_only_backend_slot_panics_on_execution_access() {
        let egraph = EGraph::new_compile_only(false);
        let _ = egraph.backend.base_values();
    }

    #[test]
    fn compile_only_resolution_rejects_push_pop_before_frontend_mutation() {
        let source = "(relation Edge (i64 i64))\n(push)\n(pop)";
        let mut first = EGraph::new_compile_only(false);
        let first_error = first
            .resolve_program_compile_only(None, source)
            .unwrap_err();
        let mut second = EGraph::new_compile_only(false);
        let second_error = second
            .resolve_program_compile_only(None, source)
            .unwrap_err();

        assert!(matches!(
            first_error,
            Error::UnsupportedStandaloneCommand {
                reason: StandalonePreflightReason::Push,
                ..
            }
        ));
        assert_eq!(first_error.to_string(), second_error.to_string());

        // Whole-program preflight runs before the preceding declaration can
        // leak into the compile-only type or execution state.
        assert!(first.type_info.get_func_type("Edge").is_none());
        assert!(first.functions.is_empty());
        assert!(first.pushed_egraph.is_none());
        assert_eq!(compile_only_state(&first), compile_only_state(&second));
    }

    #[test]
    fn compile_only_resolution_rejects_nested_pop_before_frontend_mutation() {
        let source = "(relation Edge (i64 i64))\n(fail (pop))";
        let mut egraph = EGraph::new_compile_only(false);
        let error = egraph
            .resolve_program_compile_only(None, source)
            .unwrap_err();

        assert!(matches!(
            error,
            Error::UnsupportedStandaloneCommand {
                reason: StandalonePreflightReason::Pop,
                ..
            }
        ));
        assert!(egraph.type_info.get_func_type("Edge").is_none());
        assert!(egraph.functions.is_empty());
        assert!(egraph.pushed_egraph.is_none());
    }

    #[test]
    fn compile_only_late_failure_rolls_back_sort_ledger_and_allocator() {
        let mut attempted = EGraph::new_compile_only(false);
        let before_sorts = sort_registration_fingerprint(&attempted);
        let before_backend = compile_only_state(&attempted).clone();
        let error = attempted
            .resolve_program_compile_only(
                None,
                "(sort MustRollback)\n(function broken (MissingSort) i64 :no-merge)",
            )
            .unwrap_err();
        assert!(matches!(
            error,
            Error::TypeError(TypeError::UndefinedSort(name, _)) if name == "MissingSort"
        ));
        assert_eq!(sort_registration_fingerprint(&attempted), before_sorts);
        assert_eq!(compile_only_state(&attempted), &before_backend);
        assert!(attempted.get_sort_by_name("MustRollback").is_none());

        let mut fresh = EGraph::new_compile_only(false);
        let attempted_result = attempted
            .resolve_program_compile_only(None, "(sort Stable)")
            .unwrap();
        let fresh_result = fresh
            .resolve_program_compile_only(None, "(sort Stable)")
            .unwrap();
        assert_eq!(attempted_result.execution, fresh_result.execution);
        assert_eq!(
            sort_registration_fingerprint(&attempted),
            sort_registration_fingerprint(&fresh)
        );
        assert_eq!(compile_only_state(&attempted), compile_only_state(&fresh));
    }

    #[test]
    fn compile_only_proof_late_failure_rolls_back_cross_view_sort_links() {
        let mut attempted = EGraph::new_compile_only(true);
        let before_execution_sorts = sort_registration_fingerprint(&attempted);
        let before_execution_links = attempted.type_info.linked_sort_arc_count();
        let before_backend = compile_only_state(&attempted).clone();
        let before_source_sorts = type_info_sort_registration_fingerprint(
            &attempted
                .proof_state
                .original_typechecking
                .as_ref()
                .expect("proof mode retains its source-program typechecking view")
                .type_info,
        );
        let before_source_links = attempted
            .proof_state
            .original_typechecking
            .as_ref()
            .unwrap()
            .type_info
            .linked_sort_arc_count();

        let error = attempted
            .resolve_program_compile_only(
                None,
                "(sort MustRollback)\n(function broken (MissingSort) i64 :no-merge)",
            )
            .unwrap_err();
        assert!(matches!(
            error,
            Error::TypeError(TypeError::UndefinedSort(name, _)) if name == "MissingSort"
        ));
        assert_eq!(
            sort_registration_fingerprint(&attempted),
            before_execution_sorts
        );
        assert_eq!(
            attempted.type_info.linked_sort_arc_count(),
            before_execution_links
        );
        assert_eq!(compile_only_state(&attempted), &before_backend);
        let attempted_source = &attempted
            .proof_state
            .original_typechecking
            .as_ref()
            .unwrap()
            .type_info;
        assert_eq!(
            type_info_sort_registration_fingerprint(attempted_source),
            before_source_sorts
        );
        assert_eq!(
            attempted_source.linked_sort_arc_count(),
            before_source_links
        );
        assert!(attempted.get_sort_by_name("MustRollback").is_none());
        assert!(
            attempted
                .proof_state
                .original_typechecking
                .as_ref()
                .unwrap()
                .get_sort_by_name("MustRollback")
                .is_none()
        );

        let mut fresh = EGraph::new_compile_only(true);
        let attempted_result = attempted
            .resolve_program_compile_only(None, "(sort Stable)")
            .unwrap();
        let fresh_result = fresh
            .resolve_program_compile_only(None, "(sort Stable)")
            .unwrap();
        let stable_rendering = |commands: &[CompileOnlyResolvedCommand]| {
            commands
                .iter()
                .map(|command| {
                    (
                        command.source_trigger,
                        command.command.to_command().to_string(),
                    )
                })
                .collect::<Vec<_>>()
        };
        assert_eq!(
            stable_rendering(&attempted_result.execution),
            stable_rendering(&fresh_result.execution)
        );
        assert_eq!(
            stable_rendering(&attempted_result.proof_check),
            stable_rendering(&fresh_result.proof_check)
        );
        assert_eq!(
            attempted_result.execution_sort_authorities,
            fresh_result.execution_sort_authorities
        );
        assert_eq!(
            attempted_result.proof_check_sort_authorities,
            fresh_result.proof_check_sort_authorities
        );
        assert_eq!(
            sort_registration_fingerprint(&attempted),
            sort_registration_fingerprint(&fresh)
        );
        assert_eq!(
            attempted.type_info.linked_sort_arc_count(),
            fresh.type_info.linked_sort_arc_count()
        );
        let attempted_source = &attempted
            .proof_state
            .original_typechecking
            .as_ref()
            .unwrap()
            .type_info;
        let fresh_source = &fresh
            .proof_state
            .original_typechecking
            .as_ref()
            .unwrap()
            .type_info;
        assert_eq!(
            type_info_sort_registration_fingerprint(attempted_source),
            type_info_sort_registration_fingerprint(fresh_source)
        );
        assert_eq!(
            attempted_source.linked_sort_arc_count(),
            fresh_source.linked_sort_arc_count()
        );
        assert_eq!(compile_only_state(&attempted), compile_only_state(&fresh));
    }

    #[test]
    fn compile_only_proof_nested_fail_sorts_keep_exact_cross_view_lineage() {
        let mut egraph = EGraph::new_compile_only(true);
        egraph
            .resolve_program_compile_only(
                None,
                r#"
                (fail
                  (sort BeforeFailure)
                  (fail
                    (sort DeeplyNested)
                    (check (= 1 2)))
                  (check (= 1 2))
                  (sort AfterFailure))
                "#,
            )
            .unwrap();

        let source_type_info = &egraph
            .proof_state
            .original_typechecking
            .as_ref()
            .expect("proof mode retains its source-program typechecking view")
            .type_info;
        for name in ["BeforeFailure", "DeeplyNested", "AfterFailure"] {
            let execution_arc = egraph
                .type_info
                .sorts
                .get(name)
                .unwrap_or_else(|| panic!("execution view lost nested sort {name}"));
            let source_arc = source_type_info
                .sorts
                .get(name)
                .unwrap_or_else(|| panic!("source view lost nested sort {name}"));
            assert!(
                egraph.type_info.same_sort(execution_arc, source_arc),
                "execution view did not retain producer lineage for {name}"
            );
            assert!(
                source_type_info.same_sort(execution_arc, source_arc),
                "source view did not retain producer lineage for {name}"
            );
        }
    }

    #[test]
    fn compile_only_sort_sidecar_remaps_through_nested_global_expansion() {
        let mut egraph = EGraph::new_compile_only(false);
        let resolved = egraph
            .resolve_program_compile_only(
                None,
                r#"
                (fail
                  (let $global 1)
                  (sort NestedAfterGlobal)
                  (check (= 1 2)))
                "#,
            )
            .unwrap();

        let [authority] = resolved.execution_sort_authorities.as_slice() else {
            panic!("expected exactly one finalized sort authority")
        };
        assert_eq!(authority.command_path, [0, 2]);
        assert!(authority.source.is_none());
        let ResolvedNCommand::Fail(_, nested) = &resolved.execution[0].command else {
            panic!("source fail did not remain one transaction command")
        };
        assert!(matches!(
            &nested[2],
            ResolvedNCommand::Sort { name, .. } if name == "NestedAfterGlobal"
        ));
        assert_eq!(
            egraph
                .type_info
                .sort_registration(authority.local)
                .unwrap()
                .sort
                .name(),
            "NestedAfterGlobal"
        );
    }

    #[test]
    fn compile_only_resolution_rejects_include_before_opening_it() {
        let mut egraph = EGraph::new_compile_only(false);
        let error = egraph
            .resolve_program_compile_only(None, "(include \"certainly-missing.egg\")")
            .unwrap_err();

        assert!(matches!(
            error,
            Error::UnsupportedStandaloneCommand {
                reason: StandalonePreflightReason::Include,
                ..
            }
        ));
    }

    #[test]
    fn compile_only_resolution_preflights_macro_expansions() {
        struct ExpandToPush;

        impl CommandMacro for ExpandToPush {
            fn transform(
                &self,
                command: Command,
                _symbol_gen: &mut crate::util::SymbolGen,
                _type_info: &TypeInfo,
            ) -> Result<Vec<Command>, Error> {
                Ok(if matches!(command, Command::AddRuleset(..)) {
                    vec![Command::Push(1)]
                } else {
                    vec![command]
                })
            }
        }

        let mut egraph = EGraph::new_compile_only(false);
        egraph.command_macros_mut().register(Arc::new(ExpandToPush));
        let error = egraph
            .resolve_program_compile_only(None, "(relation Edge (i64 i64))\n(ruleset trigger)")
            .unwrap_err();

        assert!(matches!(
            error,
            Error::UnsupportedStandaloneCommand {
                reason: StandalonePreflightReason::Push,
                ..
            }
        ));
        assert!(egraph.type_info.get_func_type("Edge").is_none());
        assert!(!egraph.rulesets.contains_key("trigger"));
        assert!(egraph.pushed_egraph.is_none());
    }

    #[test]
    fn compile_only_resolution_rejects_unstamped_command_macro_fanout() {
        struct AppendPrintSize;

        impl CommandMacro for AppendPrintSize {
            fn transform(
                &self,
                command: Command,
                _symbol_gen: &mut crate::util::SymbolGen,
                _type_info: &TypeInfo,
            ) -> Result<Vec<Command>, Error> {
                Ok(match command {
                    Command::AddRuleset(span, name) => vec![
                        Command::AddRuleset(span.clone(), name),
                        Command::PrintSize(span, None),
                    ],
                    command => vec![command],
                })
            }
        }

        let mut egraph = EGraph::new_compile_only(false);
        egraph
            .command_macros_mut()
            .register(Arc::new(AppendPrintSize));
        let error = egraph
            .resolve_program_compile_only(None, "(ruleset trigger)\n(print-size)")
            .unwrap_err();

        assert!(matches!(
            error,
            Error::StandaloneSnapshotInvariant {
                message: "multi-output command-macro expansion lacks standalone provenance"
            }
        ));
        assert!(!egraph.rulesets.contains_key("trigger"));
    }

    #[test]
    fn compile_only_resolution_rejects_unstamped_command_macro_deletion() {
        struct DeleteRuleset;

        impl CommandMacro for DeleteRuleset {
            fn transform(
                &self,
                command: Command,
                _symbol_gen: &mut crate::util::SymbolGen,
                _type_info: &TypeInfo,
            ) -> Result<Vec<Command>, Error> {
                Ok(if matches!(command, Command::AddRuleset(..)) {
                    Vec::new()
                } else {
                    vec![command]
                })
            }
        }

        let mut egraph = EGraph::new_compile_only(false);
        egraph
            .command_macros_mut()
            .register(Arc::new(DeleteRuleset));
        let error = egraph
            .resolve_program_compile_only(None, "(ruleset erased)")
            .unwrap_err();

        assert!(matches!(
            error,
            Error::StandaloneSnapshotInvariant {
                message: "zero-output command-macro expansion lacks standalone provenance"
            }
        ));
        assert!(!egraph.rulesets.contains_key("erased"));
    }

    #[test]
    fn compile_only_rejects_intermediate_macro_fanout_hidden_by_later_deletion() {
        struct FanOut;
        struct DeleteGeneratedPrint;

        impl CommandMacro for FanOut {
            fn transform(
                &self,
                command: Command,
                symbol_gen: &mut crate::util::SymbolGen,
                _type_info: &TypeInfo,
            ) -> Result<Vec<Command>, Error> {
                Ok(match command {
                    Command::AddRuleset(span, name) => {
                        let _ = symbol_gen.fresh("hidden-fanout");
                        vec![
                            Command::AddRuleset(span.clone(), name),
                            Command::PrintSize(span, None),
                        ]
                    }
                    command => vec![command],
                })
            }
        }

        impl CommandMacro for DeleteGeneratedPrint {
            fn transform(
                &self,
                command: Command,
                _symbol_gen: &mut crate::util::SymbolGen,
                _type_info: &TypeInfo,
            ) -> Result<Vec<Command>, Error> {
                Ok(if matches!(command, Command::PrintSize(..)) {
                    Vec::new()
                } else {
                    vec![command]
                })
            }
        }

        let mut egraph = EGraph::new_compile_only(false);
        egraph.command_macros_mut().register(Arc::new(FanOut));
        egraph
            .command_macros_mut()
            .register(Arc::new(DeleteGeneratedPrint));
        let before_symbols = egraph.parser.symbol_gen.clone();
        let before_backend = compile_only_state(&egraph).clone();

        let error = egraph
            .resolve_program_compile_only(None, "(ruleset trigger)")
            .unwrap_err();

        assert!(matches!(
            error,
            Error::StandaloneSnapshotInvariant {
                message: "multi-output command-macro expansion lacks standalone provenance"
            }
        ));
        assert_eq!(egraph.parser.symbol_gen, before_symbols);
        assert_eq!(compile_only_state(&egraph), &before_backend);
        assert!(!egraph.rulesets.contains_key("trigger"));
    }

    #[test]
    fn compile_only_frontend_capture_retains_parser_macro_groups_and_exact_bytes() {
        let mut egraph = EGraph::new_compile_only(false);
        egraph
            .parser
            .add_command_macro(Arc::new(crate::ast::SimpleMacro::new(
                "emit-none",
                |_tail, _span, _parser| Ok(Vec::new()),
            )));
        egraph
            .parser
            .add_command_macro(Arc::new(crate::ast::SimpleMacro::new(
                "emit-two",
                |_tail, span, _parser| {
                    Ok(vec![
                        Command::PrintSize(span.clone(), None),
                        Command::PrintSize(span, Some("second".to_owned())),
                    ])
                },
            )));
        let input = " \t; λ lead\n(emit-none)\n; between\n(emit-two)\n; Ω trailer";
        let resolved = egraph
            .resolve_program_compile_only(Some("physical.egg".to_owned()), input)
            .unwrap();

        assert_eq!(
            resolved.source.logical_name.as_deref(),
            Some("physical.egg")
        );
        assert_eq!(resolved.source.contents, input);
        assert_eq!(resolved.source.groups.len(), 2);
        assert!(resolved.source.groups[0].subcommands.is_empty());
        assert_eq!(resolved.source.groups[1].subcommands.len(), 2);
        assert_eq!(
            resolved
                .execution
                .iter()
                .map(|command| command.source_trigger)
                .collect::<Vec<_>>(),
            vec![
                frontend_program::SourceSubcommandRef::new(
                    frontend_program::SourceGroupId::new(1),
                    frontend_program::SourceSubcommandId::new(0),
                ),
                frontend_program::SourceSubcommandRef::new(
                    frontend_program::SourceGroupId::new(1),
                    frontend_program::SourceSubcommandId::new(1),
                ),
            ]
        );
        let mut reconstructed = String::new();
        for group in &resolved.source.groups {
            reconstructed.push_str(&resolved.source.contents[group.leading_trivia.clone()]);
            reconstructed.push_str(&resolved.source.contents[group.command.clone()]);
        }
        reconstructed.push_str(&resolved.source.contents[resolved.source.eof_trailer.clone()]);
        assert_eq!(reconstructed, input);
    }

    #[test]
    fn compile_only_frontend_capture_inherits_one_to_one_command_macro_trigger() {
        struct RulesetToPrintSize;

        impl CommandMacro for RulesetToPrintSize {
            fn transform(
                &self,
                command: Command,
                _symbol_gen: &mut crate::util::SymbolGen,
                _type_info: &TypeInfo,
            ) -> Result<Vec<Command>, Error> {
                Ok(match command {
                    Command::AddRuleset(span, _) => vec![Command::PrintSize(span, None)],
                    command => vec![command],
                })
            }
        }

        let mut egraph = EGraph::new_compile_only(false);
        egraph
            .command_macros_mut()
            .register(Arc::new(RulesetToPrintSize));
        let input = "(ruleset replaced)\n; between\n(print-size)";
        let resolved = egraph.resolve_program_compile_only(None, input).unwrap();

        assert_eq!(resolved.source.contents, input);
        assert_eq!(resolved.execution.len(), 2);
        assert!(
            resolved
                .execution
                .iter()
                .all(|command| matches!(command.command, ResolvedNCommand::PrintSize(..)))
        );
        assert_eq!(
            resolved
                .execution
                .iter()
                .map(|command| command.source_trigger)
                .collect::<Vec<_>>(),
            vec![
                frontend_program::SourceSubcommandRef::new(
                    frontend_program::SourceGroupId::new(0),
                    frontend_program::SourceSubcommandId::new(0),
                ),
                frontend_program::SourceSubcommandRef::new(
                    frontend_program::SourceGroupId::new(1),
                    frontend_program::SourceSubcommandId::new(0),
                ),
            ]
        );
    }

    #[test]
    fn compile_only_resolution_rejects_unsupported_source_output_and_container_forms() {
        let cases = [
            (
                "(sort Numbers (Vec i64))",
                StandalonePreflightReason::Presort,
            ),
            ("(extract 1 1)", StandalonePreflightReason::Extract),
            (
                "(print-function Missing)",
                StandalonePreflightReason::PrintFunction,
            ),
            (
                "(print-stats :file \"must-not-exist.json\")",
                StandalonePreflightReason::FileStatistics,
            ),
            (
                "(output \"must-not-exist.json\" 1)",
                StandalonePreflightReason::Output,
            ),
        ];

        for (source, expected) in cases {
            let mut egraph = EGraph::new_compile_only(false);
            let error = egraph
                .resolve_program_compile_only(None, source)
                .unwrap_err();
            assert!(
                matches!(
                    error,
                    Error::UnsupportedStandaloneCommand { reason, .. } if reason == expected
                ),
                "unexpected preflight result for {source:?}: {error}"
            );
            assert!(egraph.functions.is_empty());
        }
    }

    #[test]
    fn compile_only_proof_resolution_registers_fresh_and_view_ops() {
        let source = r#"
                (datatype X (Leaf i64))
                (let $x (Leaf 1))
                (run 1)
                (check (= $x $x))
                "#;
        let mut egraph = EGraph::new_compile_only(true);
        let resolved = egraph.resolve_program_compile_only(None, source).unwrap();
        let mut again = EGraph::new_compile_only(true);
        let resolved_again = again.resolve_program_compile_only(None, source).unwrap();

        assert!(!resolved.execution.is_empty());
        assert!(!resolved.proof_check.is_empty());
        let stable_rendering = |commands: &[CompileOnlyResolvedCommand]| {
            commands
                .iter()
                .map(|command| {
                    (
                        command.source_trigger,
                        command.command.to_command().to_string(),
                    )
                })
                .collect::<Vec<_>>()
        };
        assert_eq!(
            stable_rendering(&resolved.execution),
            stable_rendering(&resolved_again.execution)
        );
        assert_eq!(
            stable_rendering(&resolved.proof_check),
            stable_rendering(&resolved_again.proof_check)
        );
        assert_eq!(
            resolved.execution_sort_authorities,
            resolved_again.execution_sort_authorities
        );
        assert_eq!(
            resolved.proof_check_sort_authorities,
            resolved_again.proof_check_sort_authorities
        );
        assert_eq!(resolved.source, resolved_again.source);
        assert_eq!(resolved.source.groups.len(), 4);
        for stream in [&resolved.execution, &resolved.proof_check] {
            assert!(
                stream
                    .windows(2)
                    .all(|commands| { commands[0].source_trigger <= commands[1].source_trigger })
            );
            assert!(stream.iter().all(|command| {
                resolved.source.groups.iter().any(|group| {
                    group.id == command.source_trigger.group
                        && group
                            .subcommands
                            .iter()
                            .any(|source| source.id == command.source_trigger.subcommand)
                })
            }));
        }
        assert_eq!(compile_only_state(&egraph), compile_only_state(&again));

        fn sort_name_at_path<'a>(
            commands: &'a [CompileOnlyResolvedCommand],
            path: &[usize],
        ) -> &'a str {
            let (top, rest) = path.split_first().unwrap();
            let mut command = &commands[*top].command;
            for child in rest {
                let ResolvedNCommand::Fail(_, nested) = command else {
                    panic!("sort authority path traversed a non-Fail command")
                };
                command = &nested[*child];
            }
            let ResolvedNCommand::Sort { name, .. } = command else {
                panic!("sort authority path targeted a non-Sort command")
            };
            name
        }

        let execution_sorts = resolved
            .execution_sort_authorities
            .iter()
            .map(|authority| {
                (
                    sort_name_at_path(&resolved.execution, &authority.command_path),
                    authority.local,
                )
            })
            .collect::<Vec<_>>();
        let proof_sorts = resolved
            .proof_check_sort_authorities
            .iter()
            .map(|authority| {
                (
                    sort_name_at_path(&resolved.proof_check, &authority.command_path),
                    authority.local,
                )
            })
            .collect::<Vec<_>>();
        let (execution_name, proof_name, colliding_identity) = execution_sorts
            .iter()
            .find_map(|(execution_name, execution_identity)| {
                proof_sorts.iter().find_map(|(proof_name, proof_identity)| {
                    (*execution_identity == *proof_identity && execution_name != proof_name)
                        .then_some((*execution_name, *proof_name, *execution_identity))
                })
            })
            .expect("proof and execution views should exhibit a raw-ID collision canary");
        assert_eq!(
            egraph
                .type_info
                .sort_registration(colliding_identity)
                .unwrap()
                .sort
                .name(),
            execution_name
        );
        let proof_type_info = &egraph
            .proof_state
            .original_typechecking
            .as_ref()
            .expect("proof mode retains its source-program typechecking view")
            .type_info;
        assert_eq!(
            proof_type_info
                .sort_registration(colliding_identity)
                .unwrap()
                .sort
                .name(),
            proof_name
        );
        assert_ne!(execution_name, proof_name);

        let execution_x_identity = execution_sorts
            .iter()
            .find_map(|(name, identity)| (*name == "X").then_some(*identity))
            .expect("execution view should retain the source X sort");
        let proof_x_identity = proof_sorts
            .iter()
            .find_map(|(name, identity)| (*name == "X").then_some(*identity))
            .expect("proof-check view should retain the source X sort");
        let execution_x_arc = egraph
            .type_info
            .sort_registration(execution_x_identity)
            .unwrap()
            .sort
            .clone();
        let proof_x_arc = proof_type_info
            .sort_registration(proof_x_identity)
            .unwrap()
            .sort
            .clone();
        assert_eq!(
            proof_type_info
                .sort_registration_for_arc(&execution_x_arc)
                .unwrap()
                .identity,
            proof_x_identity,
            "the execution producer arc should resolve through its explicit source-view link"
        );
        assert_eq!(
            egraph
                .type_info
                .sort_registration_for_arc(&proof_x_arc)
                .unwrap()
                .identity,
            execution_x_identity,
            "the source producer arc should resolve through its explicit execution-view link"
        );
        assert!(
            egraph.type_info.same_sort(&execution_x_arc, &proof_x_arc),
            "the execution view should equate its canonical arc with the stamped source arc"
        );
        assert!(
            proof_type_info.same_sort(&execution_x_arc, &proof_x_arc),
            "the source view should equate its canonical arc with the stamped execution arc"
        );
        let same_shaped_decoy: ArcSort = Arc::new(EqSort {
            name: "X".to_owned(),
        });
        assert!(
            egraph
                .type_info
                .sort_registration_for_arc(&same_shaped_decoy)
                .is_none(),
            "same-shaped execution decoys must not inherit explicit lineage"
        );
        assert!(
            proof_type_info
                .sort_registration_for_arc(&same_shaped_decoy)
                .is_none(),
            "same-shaped source decoys must not inherit explicit lineage"
        );
        assert!(
            !egraph
                .type_info
                .same_sort(&execution_x_arc, &same_shaped_decoy)
        );
        assert!(!proof_type_info.same_sort(&proof_x_arc, &same_shaped_decoy));

        let write_only_contexts = |primitive: &typechecking::PrimitiveWithId| {
            assert_eq!(
                Context::ALL.map(|context| primitive.is_valid_in_context(context)),
                [false, true, false, true]
            );
        };
        let assert_registration_is_deterministic = |name: &str| {
            let first = egraph.type_info.get_prims(name).unwrap();
            let second = again.type_info.get_prims(name).unwrap();
            assert_eq!(first.len(), second.len());
            for (first, second) in first.iter().zip(second) {
                assert_eq!(first.registration_id(), second.registration_id());
                assert_eq!(
                    first.registration_id().ordinal(),
                    second.registration_id().ordinal()
                );
                assert_eq!(first.authority(), second.authority());
                assert_eq!(first.context_ids, second.context_ids);
            }
        };

        let fresh = egraph
            .type_info
            .get_prims(crate::proofs::proof_fresh::GET_FRESH_PRIM_NAME)
            .unwrap();
        assert!(fresh.iter().all(|primitive| matches!(
            primitive.authority(),
            typechecking::PrimitiveAuthority::GetFresh
        )));
        fresh.iter().for_each(&write_only_contexts);
        assert_registration_is_deterministic(crate::proofs::proof_fresh::GET_FRESH_PRIM_NAME);

        let view_name = resolved
            .execution
            .iter()
            .find_map(|command| match &command.command {
                ResolvedNCommand::Function(decl)
                    if decl.term_constructor.as_deref() == Some("Leaf") =>
                {
                    Some(decl.name.as_str())
                }
                _ => None,
            })
            .expect("proof instrumentation should declare Leaf's logical view");
        let set_if_empty_name = crate::proofs::proof_fresh::set_if_empty_prim_name(view_name);
        let set_if_empty = egraph.type_info.get_prims(&set_if_empty_name).unwrap();
        assert!(set_if_empty.iter().all(|primitive| matches!(
            primitive.authority(),
            typechecking::PrimitiveAuthority::SetIfEmpty { target_view }
                if target_view == view_name
        )));
        set_if_empty.iter().for_each(&write_only_contexts);
        assert_registration_is_deterministic(&set_if_empty_name);

        let view_proof_name = crate::proofs::proof_fresh::view_proof_prim_name(view_name);
        let view_proof = egraph.type_info.get_prims(&view_proof_name).unwrap();
        assert!(view_proof.iter().all(|primitive| matches!(
            primitive.authority(),
            typechecking::PrimitiveAuthority::ViewColumn {
                target_view,
                value_column: 1,
            } if target_view == view_name
        )));
        view_proof.iter().for_each(&write_only_contexts);
        assert_registration_is_deterministic(&view_proof_name);

        let uf_name = egraph
            .proof_state
            .uf_parent
            .get("X")
            .expect("proof instrumentation should register X's UF relation");
        for (primitive_name, expected_column) in [
            (
                crate::proofs::proof_container_rebuild::uf_canon_prim_name(uf_name),
                0,
            ),
            (
                crate::proofs::proof_container_rebuild::uf_canon_proof_prim_name(uf_name),
                1,
            ),
        ] {
            let primitives = egraph.type_info.get_prims(&primitive_name).unwrap();
            assert!(primitives.iter().all(|primitive| matches!(
                primitive.authority(),
                typechecking::PrimitiveAuthority::ViewColumn {
                    target_view,
                    value_column,
                } if target_view == uf_name && *value_column == expected_column
            )));
            primitives.iter().for_each(&write_only_contexts);
            assert_registration_is_deterministic(&primitive_name);
        }
    }

    #[test]
    fn primitive_authority_is_registration_site_data_not_name_or_signature() {
        let mut egraph = EGraph::default();
        egraph.add_pure_primitive(AuthorityDecoy, None);
        egraph.add_native_scalar_primitive(AuthorityDecoy, None, NativeScalarPrimitive::I64Add);

        let registrations = egraph.type_info.get_prims("authority-decoy").unwrap();
        assert_eq!(registrations.len(), 2);
        assert_ne!(
            registrations[0].registration_id(),
            registrations[1].registration_id()
        );
        assert!(matches!(
            registrations[0].authority(),
            typechecking::PrimitiveAuthority::Opaque
        ));
        assert!(matches!(
            registrations[1].authority(),
            typechecking::PrimitiveAuthority::NativeScalar(NativeScalarPrimitive::I64Add)
        ));
        assert!(registrations.iter().all(|primitive| {
            Context::ALL
                .into_iter()
                .all(|context| primitive.is_valid_in_context(context))
        }));
        assert_ne!(registrations[0].context_ids, registrations[1].context_ids);

        let ordering_min = &egraph.type_info.get_prims("ordering-min").unwrap()[0];
        assert!(matches!(
            ordering_min.authority(),
            typechecking::PrimitiveAuthority::Native(NativePrimitive::OrderingMin)
        ));

        egraph.add_pure_primitive(proofs::proof_encoding_helpers::SelectEqProof, None);
        let select_eq = egraph.type_info.get_prims("select-eq").unwrap();
        assert_eq!(select_eq.len(), 2);
        assert!(matches!(
            select_eq[0].authority(),
            typechecking::PrimitiveAuthority::Native(NativePrimitive::SelectEqPayload)
        ));
        assert!(matches!(
            select_eq[1].authority(),
            typechecking::PrimitiveAuthority::Opaque
        ));
        assert_ne!(
            select_eq[0].registration_id(),
            select_eq[1].registration_id()
        );

        for (name, expected) in [
            (">", NativeScalarPrimitive::I64Gt),
            ("<=", NativeScalarPrimitive::I64Le),
            ("bool-<", NativeScalarPrimitive::I64BoolLt),
        ] {
            let registrations = egraph.type_info.get_prims(name).unwrap();
            assert!(registrations.iter().any(|primitive| {
                primitive.authority() == &typechecking::PrimitiveAuthority::NativeScalar(expected)
            }));
        }
        assert!(
            egraph
                .type_info
                .get_prims("bool-<")
                .unwrap()
                .iter()
                .any(|primitive| matches!(
                    primitive.authority(),
                    typechecking::PrimitiveAuthority::Opaque
                ))
        );
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
        let tied = [a, a_proof, a, b_proof];
        assert_eq!(
            validator("proof-of-min")(&mut term_dag, &tied),
            Some(b_proof)
        );
        assert_eq!(
            validator("proof-of-max")(&mut term_dag, &tied),
            Some(b_proof)
        );
        assert_eq!(validator("proof-of-min")(&mut term_dag, &args[..3]), None);
        assert_eq!(validator("proof-of-max")(&mut term_dag, &args[..3]), None);
    }

    #[test]
    fn merge_lowering_retains_specialized_primitive_and_constant_types() {
        let mut egraph = EGraph::default();
        let mut parser = crate::ast::Parser::default();

        let ordering = parser
            .get_expr_from_string(None, "(ordering-min 1 2)")
            .unwrap();
        let ordering = egraph
            .typecheck_expr_with_bindings_and_output(
                &ordering,
                &[],
                I64Sort.to_arcsort(),
                Context::Write,
            )
            .unwrap();
        let ordering = egraph.translate_expr_to_mergefn(&ordering).unwrap();
        let MergeFn::Primitive {
            name,
            input,
            output,
            args,
            ..
        } = ordering
        else {
            panic!("ordering-min did not lower to a primitive merge call");
        };
        let i64_ty = I64Sort.to_arcsort().column_ty(egraph.backend.base_values());
        assert_eq!(name, "ordering-min");
        assert_eq!(input, [i64_ty, i64_ty]);
        assert_eq!(output, i64_ty);
        assert!(
            args.iter()
                .all(|arg| matches!(arg, MergeFn::Const { ty, .. } if *ty == i64_ty))
        );

        let orient = parser
            .get_expr_from_string(None, "(proof-of-min 1 true 2 false)")
            .unwrap();
        let orient = egraph
            .typecheck_expr_with_bindings_and_output(
                &orient,
                &[],
                BoolSort.to_arcsort(),
                Context::Write,
            )
            .unwrap();
        let orient = egraph.translate_expr_to_mergefn(&orient).unwrap();
        let MergeFn::Primitive {
            name,
            input,
            output,
            ..
        } = orient
        else {
            panic!("proof-of-min did not lower to a primitive merge call");
        };
        let bool_ty = BoolSort
            .to_arcsort()
            .column_ty(egraph.backend.base_values());
        assert_eq!(name, "proof-of-min");
        assert_eq!(input, [i64_ty, bool_ty, i64_ty, bool_ty]);
        assert_eq!(output, bool_ty);

        egraph.parse_and_run_program(None, "(sort Proof)").unwrap();
        let proof_sort = egraph.get_sort_by_name("Proof").unwrap().clone();
        let get_fresh = parser
            .get_expr_from_string(None, "(get-fresh! \"Proof\")")
            .unwrap();
        let get_fresh = egraph
            .typecheck_expr_with_bindings_and_output(&get_fresh, &[], proof_sort, Context::Write)
            .unwrap();
        let get_fresh = egraph.translate_expr_to_mergefn(&get_fresh).unwrap();
        let MergeFn::Primitive {
            name,
            input,
            output,
            args,
            ..
        } = get_fresh
        else {
            panic!("get-fresh! did not lower to a primitive merge call");
        };
        let string_ty = StringSort
            .to_arcsort()
            .column_ty(egraph.backend.base_values());
        assert_eq!(name, "get-fresh!");
        assert_eq!(input, [string_ty]);
        assert_eq!(output, ColumnTy::Id);
        assert!(matches!(
            args.as_slice(),
            [MergeFn::Const { ty, .. }] if *ty == string_ty
        ));
    }

    #[test]
    fn merge_lowering_uses_binding_authority_not_variable_spelling() {
        let mut egraph = EGraph::default();
        let command = egraph
            .parser
            .get_program_from_string(
                None,
                "(function choose (i64) (i64 i64) :merge (values new1 old0))",
            )
            .unwrap()
            .pop()
            .unwrap();
        let mut resolved = egraph.resolve_command_before_proofs(command).unwrap();
        let ResolvedNCommand::Function(declaration) = resolved.commands.pop().unwrap() else {
            panic!("function declaration did not remain a resolved function");
        };
        let mut merge = declaration.merge.unwrap();
        let GenericExpr::Call(_, ResolvedCall::Values(_), columns) = &mut merge.result else {
            panic!("tuple merge did not retain its values roots");
        };
        let (first_column, remaining_columns) = columns.split_at_mut(1);
        let GenericExpr::Var(_, first) = &mut first_column[0] else {
            panic!("first tuple merge root is not a variable");
        };
        let GenericExpr::Var(_, second) = &mut remaining_columns[0] else {
            panic!("second tuple merge root is not a variable");
        };
        assert_eq!(first.binding, ResolvedVarBinding::MergeNew { column: 1 });
        assert_eq!(second.binding, ResolvedVarBinding::MergeOld { column: 0 });

        // Swap the diagnostic spellings without changing either resolved
        // authority. Name-parsing lowering would now produce the opposite
        // columns; nominal lowering must remain unchanged.
        first.name = "old0".to_owned();
        second.name = "new1".to_owned();
        let lowered = egraph
            .translate_merge_to_mergefn(&merge, ("choose", egraph.backend.peek_next_function_id()))
            .unwrap();
        assert!(matches!(
            lowered,
            MergeFn::Columns(ref roots)
                if matches!(roots.as_slice(), [MergeFn::NewCol(1), MergeFn::OldCol(0)])
        ));
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
        let registration = &egraph.type_info.get_prims("inner-product").unwrap()[0];
        assert!(matches!(
            registration.authority(),
            typechecking::PrimitiveAuthority::Opaque
        ));
        assert!(
            Context::ALL
                .into_iter()
                .all(|context| registration.is_valid_in_context(context))
        );

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
            .resolve_program_with_sort_authority(
                None,
                "(datatype X (x))\n(sort XPair (Pair X i64))",
            )
            .unwrap();
        assert!(finalized_program_supports_proofs(
            &resolved,
            &egraph.type_info
        ));

        let mut egraph = EGraph::default();
        let resolved = egraph
            .resolve_program_with_sort_authority(
                None,
                "(datatype X (x))\n(sort XFn (UnstableFn (X) X))",
            )
            .unwrap();
        assert!(finalized_program_supports_proofs(
            &resolved,
            &egraph.type_info
        ));
    }

    #[test]
    fn proof_support_uses_exact_function_output_not_diagnostic_schema() {
        let mut egraph = EGraph::default();
        let mut resolved = egraph
            .resolve_program_with_sort_authority(
                None,
                r#"
                (datatype E (Mk))
                (function scalar () i64 :no-merge)
                (function eclass () E :no-merge)
                "#,
            )
            .unwrap();

        let scalar = resolved
            .commands
            .iter_mut()
            .find(|command| {
                matches!(command, ResolvedNCommand::Function(function) if function.name == "scalar")
            })
            .expect("resolved scalar function");
        let ResolvedNCommand::Function(function) = scalar else {
            unreachable!()
        };
        function.schema.outputs[0] = "E".to_owned();
        assert!(
            command_supports_proof_encoding_with_sort_authorities(scalar, &egraph.type_info, &[])
                .is_ok(),
            "a diagnostic eq-sort spelling must not override the exact i64 output"
        );

        let eclass = resolved
            .commands
            .iter_mut()
            .find(|command| {
                matches!(command, ResolvedNCommand::Function(function) if function.name == "eclass")
            })
            .expect("resolved eclass function");
        let ResolvedNCommand::Function(function) = eclass else {
            unreachable!()
        };
        function.schema.outputs[0] = "i64".to_owned();
        assert!(matches!(
            command_supports_proof_encoding_with_sort_authorities(eclass, &egraph.type_info, &[]),
            Err(ProofEncodingUnsupportedReason::NoMergeEqSortFunction)
        ));
    }

    #[test]
    fn proof_support_rejects_unstable_fn_primitives_without_validators() {
        let mut egraph = EGraph::default();
        let resolved = egraph
            .resolve_program_with_sort_authority(
                None,
                r#"
                (datatype X (x))
                (sort XFn (UnstableFn (X) X))
                (function id (X) X :merge old)
                (let f (unstable-fn "id"))
                "#,
            )
            .unwrap();
        assert!(!finalized_program_supports_proofs(
            &resolved,
            &egraph.type_info
        ));
    }

    #[test]
    fn proof_support_accepts_set_primitive_validators() {
        let mut egraph = EGraph::default();
        let resolved = egraph
            .resolve_program_with_sort_authority(
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

        assert!(finalized_program_supports_proofs(
            &resolved,
            &egraph.type_info
        ));
    }

    /// `set-get` indexes the runtime value order, which the proof checker
    /// cannot reproduce from terms, so it has no validator.
    #[test]
    fn proof_support_rejects_set_get() {
        let mut egraph = EGraph::default();
        let resolved = egraph
            .resolve_program_with_sort_authority(
                None,
                r#"
                (sort ISet (Set i64))
                (check (= (set-get (set-of 1 2) 0) 1))
                "#,
            )
            .unwrap();

        assert!(!finalized_program_supports_proofs(
            &resolved,
            &egraph.type_info
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
}

#[cfg(test)]
mod index_binding_tests {
    use crate::*;

    /// The header every case below shares: one function and an index over all
    /// three of its columns.
    const INDEXED: &str = "
        (datatype Math (Num i64))
        (function edge (Math Math) Math :merge old)
        (index EdgeOcc edge (any 0 1 2))
        (relation dirty (Math))
        (relation touched (Math Math Math))
    ";

    fn run(rule: &str) -> Result<(), Error> {
        EGraph::default().parse_and_run_program(None, &format!("{INDEXED}{rule}"))?;
        Ok(())
    }

    /// An index is probed, so its value has to be bound — but a *row column* of
    /// another index atom binds like any other atom's column.
    #[test]
    fn an_index_value_may_come_from_another_indexs_row() {
        run("(rule ((dirty x) (EdgeOcc x p q r) (EdgeOcc q s t u)) ((touched s t u)))")
            .expect("the second index is probed by a column the first one bound");
    }

    /// The value an index is probed by does not bind: two atoms naming each
    /// other there would each look bound with neither reachable.
    #[test]
    fn an_index_value_bound_only_by_another_probe_is_rejected() {
        let err = run("(rule ((EdgeOcc x p q r) (EdgeOcc y s t u)) ((touched p q r)))")
            .expect_err("neither index's value is bound by anything");
        assert!(
            format!("{err}").contains("must be bound"),
            "expected an unbound-index-value error, got {err}"
        );
    }

    #[test]
    fn mutually_cyclic_index_rows_do_not_anchor_either_probe() {
        let err = run("(rule ((EdgeOcc x y p q) (EdgeOcc y x s t)) ((dirty p)))")
            .expect_err("neither side of an index cycle has a reachable probe");
        assert!(
            format!("{err}").contains("must be bound"),
            "expected an unbound-index-value error, got {err}"
        );
    }

    #[test]
    fn a_multi_column_index_does_not_bind_a_probe_repeated_only_elsewhere() {
        let err = EGraph::default()
            .parse_and_run_program(
                None,
                "
                (function f (i64 i64) i64 :merge old)
                (index FOcc f (any 0 1))
                (relation touched (i64))
                (rule ((FOcc x p q x)) ((touched x)))
                ",
            )
            .expect_err("an unindexed row column cannot anchor a multi-column probe");
        assert!(
            format!("{err}").contains("must be bound"),
            "expected an unbound-index-value error, got {err}"
        );
    }

    #[test]
    fn one_deduplicated_occurrence_column_can_supply_an_unbound_probe() {
        EGraph::default()
            .parse_and_run_program(
                None,
                "
                (function f (i64) i64 :merge old)
                (index FOcc f (any 0 0))
                (relation seen (i64 i64 i64))
                (set (f 7) 8)
                (rule ((FOcc probe key value)) ((seen probe key value)))
                (run 1)
                (check (seen 7 7 8))
                ",
            )
            .expect("one unique occurrence column supplies the probe value");
    }

    /// A body primitive runs once per match, after the join, so the value it
    /// computes cannot key a probe.
    #[test]
    fn an_index_value_bound_only_by_a_primitive_is_rejected() {
        let err = EGraph::default()
            .parse_and_run_program(
                None,
                "
                (function f (i64 i64) i64 :merge old)
                (index FOcc f (any 0 1 2))
                (relation touched (i64 i64 i64))
                (rule ((= v (+ 0 1)) (FOcc v p q r)) ((touched p q r)))
                ",
            )
            .expect_err("a primitive does not bind a value the join can probe by");
        assert!(
            format!("{err}").contains("must be bound"),
            "expected an unbound-index-value error, got {err}"
        );
    }

    /// A literal is already known, so it needs no binder at all.
    #[test]
    fn an_index_may_be_probed_by_a_literal() {
        EGraph::default()
            .parse_and_run_program(
                None,
                "
                (function f (i64 i64) i64 :merge old)
                (index FOcc f (any 0 1 2))
                (relation touched (i64 i64 i64))
                (set (f 1 2) 3)
                (rule ((FOcc 1 p q r)) ((touched p q r)))
                (run 1)
                (check (touched 1 2 3))
                ",
            )
            .expect("a literal probe needs no binder");
    }

    #[test]
    fn an_index_unit_result_is_available_to_primitives_in_either_atom_order() {
        for body in [
            "(= ok (value-eq u ())) (= u (FOcc 1 x y))",
            "(= u (FOcc 1 x y)) (= ok (value-eq u ()))",
        ] {
            EGraph::default()
                .parse_and_run_program(
                    None,
                    &format!(
                        "
                        (function f (i64) i64 :merge old)
                        (index FOcc f (any 0 1))
                        (relation seen (i64))
                        (rule ({body}) ((seen x)))
                        (set (f 1) 2)
                        (run 1)
                        (check (seen 1))
                        "
                    ),
                )
                .unwrap_or_else(|error| panic!("index/primitive order `{body}` failed: {error}"));
        }
    }

    #[test]
    fn an_index_unit_result_can_probe_a_multi_column_unit_index_in_either_atom_order() {
        for body in [
            "(= u (FOcc 1 x y)) (= v (UOcc u key value))",
            "(= v (UOcc u key value)) (= u (FOcc 1 x y))",
        ] {
            EGraph::default()
                .parse_and_run_program(
                    None,
                    &format!(
                        "
                        (function f (i64) i64 :merge old)
                        (index FOcc f (any 0 1))
                        (function unit-row (Unit) Unit :merge old)
                        (index UOcc unit-row (any 0 1))
                        (relation seen (i64))
                        (set (f 1) 2)
                        (set (unit-row ()) ())
                        (rule ({body}) ((seen x)))
                        (run 1)
                        (check (seen 1))
                        "
                    ),
                )
                .unwrap_or_else(|error| panic!("index/Unit-index order `{body}` failed: {error}"));
        }
    }
}

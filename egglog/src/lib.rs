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
use egglog_bridge::{ColumnTy, QueryEntry, TableKind};
use egglog_core_relations as core_relations;
use egglog_numeric_id as numeric_id;
use egglog_reports::{
    OverallReport, ReportLevel, RulesetTimingRole, RunReport, TimingSummary, TimingSummaryError,
};
pub use exec_state::{
    Context, Core, Enode, FullState, FunctionEntry, PureState, Read, ReadState, Write, WriteState,
};
use extract::DefaultCost;
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
use smallvec::SmallVec;
use sort::*;
use std::any::{Any, TypeId};
use std::fmt::{Debug, Display, Formatter};
use std::fs::File;
use std::hash::Hash;
use std::io::Write as _;
use std::iter::once;
use std::ops::Deref;
use std::path::PathBuf;
use std::rc::Rc;
use std::sync::Arc;
use std::time::Instant;
pub use termdag::{OrdTerm, Term, TermDag, TermId};
use thiserror::Error;
pub use typechecking::FuncType;
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

/// A type-erased output from a user-defined command.
pub trait UserDefinedCommandOutput: Debug + std::fmt::Display + Send + Sync {
    /// Views a stored output as [`Any`] so consumers can safely downcast it.
    ///
    /// Call this on a `&dyn UserDefinedCommandOutput`; smart pointers that
    /// themselves satisfy this trait should first be dereferenced with
    /// `as_ref()`.
    ///
    /// [`CommandOutput::UserDefined`] owns its output, so values stored there
    /// satisfy the required `'static` bound. Keeping the bound on this method
    /// lets borrowed values continue to implement `UserDefinedCommandOutput`.
    fn as_any(&self) -> &dyn Any
    where
        Self: 'static;
}
impl<T> UserDefinedCommandOutput for T
where
    T: Debug + std::fmt::Display + Send + Sync,
{
    fn as_any(&self) -> &dyn Any
    where
        Self: 'static,
    {
        self
    }
}

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
                let out_is_unit = function.func_type.output().name() == UnitSort.name();
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
    backend: egglog_bridge::EGraph,
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
    /// Cumulative run and process reporting state.
    overall_report: OverallReport,
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
/// the table id of the function in the e-graph.
#[derive(Clone)]
pub struct Function {
    decl: ResolvedFunctionDecl,
    func_type: Arc<FuncType>,
    can_subsume: bool,
    backend_id: egglog_bridge::FunctionId,
}

enum ProgramSource<'a> {
    Commands(std::vec::IntoIter<Command>),
    Text {
        parser: SexpParser<'a>,
        expanded: std::vec::IntoIter<Command>,
    },
}

// Owned metadata survives bounded flushes, but is discarded before any command
// that can change types or table identities. Declined heads are cached too.
type GroundActionCache = HashMap<String, Option<(Arc<FuncType>, Rc<egglog_bridge::TableAction>)>>;

struct GroundActions {
    lookups: Vec<(Rc<egglog_bridge::TableAction>, SmallVec<[usize; 4]>)>,
    union: Option<(usize, usize)>,
}

impl Function {
    /// Get the name of the function.
    pub fn name(&self) -> &str {
        &self.decl.name
    }

    /// The function's resolved signature.
    pub fn func_type(&self) -> &FuncType {
        &self.func_type
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

    /// Whether this table is a view created by the term/proof encoding: the
    /// function's own rows, keyed on canonicalized children.
    pub fn is_view(&self) -> bool {
        self.decl.internal_view.is_some()
    }

    /// The source-level row layout exposed by the Rust APIs. Encoded views use
    /// physical function tables with an internal row layout, but retain their
    /// source constructor/function kind and select only the source output.
    fn table_read_projection(&self) -> (TableKind, usize, usize) {
        let rows_are_enodes = self.rows_are_enodes();
        let input_arity = if rows_are_enodes {
            self.extraction_layout().1
        } else {
            self.func_type.input.len()
        };
        (
            if rows_are_enodes {
                TableKind::Constructor
            } else {
                TableKind::Function
            },
            input_arity,
            if rows_are_enodes {
                1
            } else {
                self.func_type.outputs.len() - usize::from(self.is_fd_view())
            },
        )
    }

    /// Whether this constructor is excluded from ordinary extraction.
    pub fn is_unextractable(&self) -> bool {
        self.decl.unextractable
    }
}

impl Debug for Function {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Function")
            .field("decl", &self.decl)
            .field("func_type", &self.func_type)
            .finish()
    }
}

impl Default for EGraph {
    fn default() -> Self {
        Self::new_inner(1)
    }
}

impl EGraph {
    fn new_inner(num_threads: usize) -> Self {
        let mut parser = Parser::default();
        let proof_state = EncodingState::new(&mut parser.symbol_gen);
        let mut eg = Self {
            backend: egglog_bridge::EGraph::new(num_threads),
            parser,
            names: Default::default(),
            pushed_egraph: Default::default(),
            functions: Default::default(),
            rulesets: Default::default(),
            fact_directory: None,
            seminaive: true,
            no_decomp: false,
            overall_report: Default::default(),
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

        add_primitive_with_validator!(
            &mut eg,
            "bool=" = |a: #, b: #| -> bool {
                (a == b)
            },
            |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
                if args.len() == 2 {
                    Some(termdag.lit(Literal::Bool(args[0] == args[1])))
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
        // Whether `ordering-min`/`ordering-max` swap their arguments: 0 when `a`
        // is the max, 1 when `b` is. A top-level `union`'s fiat records this so
        // proof conversion can orient the action's two operands the way the
        // encoding did, without the row naming either of them.
        add_primitive!(&mut eg, "ordering-swapped" = |a: #, b: #| -> i64 {
            if a > b { 0 } else { 1 }
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
        // `drop-reflexive-step` narrows a view rebuild's packed-row spelling to
        // the steps that moved; see
        // [`crate::proofs::proof_encoding_helpers::DropReflexiveStep`].
        eg.add_pure_primitive(
            proofs::proof_encoding_helpers::DropReflexiveStep::default(),
            None,
        );

        eg.rulesets.insert(
            "".into(),
            Ruleset {
                kind: RulesetKind::Rules(Default::default()),
                timing_role: RulesetTimingRole::Program,
            },
        );

        // The generic `get-fresh!` mint primitive is registered on every e-graph.
        // Doing it here — rather than per-eq-sort — means it is present whenever
        // the *encoded* program is run,
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
    /// Create a new e-graph configured with `num_threads`.
    ///
    /// Passing `1` keeps execution serial. Passing `0` uses available
    /// parallelism.
    pub fn new(num_threads: usize) -> Self {
        Self::new_inner(num_threads)
    }

    /// Create a new e-graph with the term-encoding pipeline enabled.
    ///
    /// In term-encoding mode the e-graph eagerly instruments every constructor
    /// and function with source-named views and per-sort
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
        let typechecker = self.clone();
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

    /// Enable testing of getting proofs for every `check` outside `fail`.
    /// Checks inside `fail` remain negative assertions.
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

    /// Return a copy of this e-graph configured with `num_threads`.
    pub fn with_num_threads(mut self, num_threads: usize) -> Self {
        self.set_num_threads(num_threads);
        self
    }

    /// Set the number of threads used by this e-graph.
    ///
    /// Passing `1` keeps execution serial. Passing `0` uses available
    /// parallelism.
    pub fn set_num_threads(&mut self, num_threads: usize) {
        self.backend.set_num_threads(num_threads);
        if let Some(original) = &mut self.proof_state.original_typechecking {
            original.set_num_threads(num_threads);
        }
    }

    /// Return the number of threads configured for this e-graph.
    pub fn num_threads(&self) -> usize {
        self.backend.num_threads()
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
                // Work performed in the popped scope still belongs to this run.
                std::mem::swap(&mut self.overall_report, &mut e.overall_report);
                // Preserve the symbol generator so that fresh symbols
                // generated after pop don't collide with ones generated before pop.
                std::mem::swap(&mut self.parser.symbol_gen, &mut e.parser.symbol_gen);
                // Likewise the global-action numbering a fiat names: the program
                // proof checking reads keeps what the popped scope contributed,
                // so the count it is an index into must not go back either.
                std::mem::swap(
                    &mut self.proof_state.global_actions_numbered,
                    &mut e.proof_state.global_actions_numbered,
                );
                // And the program itself, for the same reason: a command that
                // ran is one proof checking has to know about, and dropping it
                // would renumber everything a later fiat names.
                std::mem::swap(&mut self.proof_check_program, &mut e.proof_check_program);
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
                let val = literal_to_value(&self.backend, literal);
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
                    let Some(GenericExpr::Lit(span, Literal::String(name))) = args.first() else {
                        return Err(Error::BackendError(
                            "expected string literal after `unstable-fn`".into(),
                        ));
                    };
                    let panic_id = self.backend.action_registry().read().default_panic_id();
                    let resolved = resolve_function_container_target_with_context(
                        &self.backend,
                        &self.functions,
                        &self.type_info,
                        name,
                        p,
                        panic_id,
                        // Merge expressions evaluate in the `Write` context.
                        crate::Context::Write,
                        span,
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

    /// Lower a resolved `:merge` (a value-producing action block) to an [`egglog_bridge::MergeFn`], keeping
    /// the existing merge interpreter. The `result` produces the merged value(s); any `actions` run
    /// first as effects.
    /// `self_ref` names the function this merge belongs to and its (peeked) table id,
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

    /// Lower a single resolved merge action to an [`egglog_bridge::MergeAction`]. Supports `set`, `let`, and
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
        // Typechecking records the signatures it resolves, so reuse that.
        // Desugaring also generates declarations (the functions global bindings
        // lower to, proof tables) without typechecking them; resolving those
        // here is what keeps every declared function reachable by name.
        let func_type = match self.type_info.get_func_type(&decl.name) {
            Some(func_type) => {
                debug_assert!(
                    func_type.subtype == decl.subtype
                        && func_type.input.len() == decl.schema.input.len()
                        && func_type
                            .input
                            .iter()
                            .zip(&decl.schema.input)
                            .all(|(sort, name)| sort.name() == name)
                        && func_type.outputs.len() == decl.schema.outputs.len()
                        && func_type
                            .outputs
                            .iter()
                            .zip(&decl.schema.outputs)
                            .all(|(sort, name)| sort.name() == name),
                    "recorded signature for {} disagrees with its declaration",
                    decl.name
                );
                func_type.clone()
            }
            None => {
                let get_sort = |name: &String| match self.type_info.get_sort_by_name(name) {
                    Some(sort) => Ok(sort.clone()),
                    None => Err(Error::TypeError(TypeError::UndefinedSort(
                        name.to_owned(),
                        decl.span.clone(),
                    ))),
                };
                let func_type = Arc::new(FuncType {
                    name: decl.name.clone(),
                    subtype: decl.subtype,
                    input: decl
                        .schema
                        .input
                        .iter()
                        .map(get_sort)
                        .collect::<Result<Vec<_>, _>>()?,
                    outputs: decl
                        .schema
                        .outputs
                        .iter()
                        .map(get_sort)
                        .collect::<Result<Vec<_>, _>>()?,
                });
                self.type_info.declare_func_type(func_type.clone());
                func_type
            }
        };

        let input = &func_type.input;
        let outputs = &func_type.outputs;
        let num_outputs = outputs.len();
        let can_subsume = match decl.subtype {
            FunctionSubtype::Constructor => true,
            // View tables need subsumption support
            FunctionSubtype::Custom => decl.internal_view.is_some(),
        };

        use egglog_bridge::{DefaultVal, MergeFn};
        // This function's table id (the id `add_table` below will assign, peeked
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
        // Proof-node relations are write-once records identified by a freshly
        // minted final id; extraction only scans them.
        let is_proof_node = decl.internal_term_node
            && input
                .last()
                .is_some_and(|sort| sort.name() == self.proof_state.proof_names.proof_datatype);
        if is_proof_node {
            assert_eq!(
                decl.subtype,
                FunctionSubtype::Custom,
                "proof-node relation `{}` must be a custom function",
                decl.name
            );
            assert!(
                decl.merge.is_none(),
                "proof-node relation `{}` cannot declare merge behavior",
                decl.name
            );
            assert!(
                decl.internal_view.is_none(),
                "proof-node relation `{}` cannot be an FD view",
                decl.name
            );
            assert!(
                matches!(outputs.as_slice(), [output] if output.name() == "Unit"),
                "proof-node relation `{}` must have exactly one Unit output",
                decl.name
            );
            assert!(
                input.last().is_some_and(|sort| sort.is_eq_sort()),
                "proof-node relation `{}` must end in an eq-sort id",
                decl.name
            );
        }
        let config = egglog_bridge::FunctionConfig {
            schema: input
                .iter()
                .chain(outputs.iter())
                .map(|sort| sort.column_ty(&self.backend))
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
        };
        let function = Function {
            decl: decl.clone(),
            func_type,
            can_subsume,
            backend_id: own_id,
        };
        let (kind, input_arity, output_arity) = function.table_read_projection();
        let backend_id = if is_proof_node {
            self.backend.add_internal_flat_table(config)
        } else {
            self.backend
                .add_table_with_read_projection(config, kind, input_arity, output_arity)
        };
        assert_eq!(backend_id, function.backend_id);
        if function.is_hidden() {
            self.type_info
                .hidden_functions
                .insert(function.name().to_owned());
        }

        let old = self.functions.insert(decl.name.clone(), function);
        if old.is_some() {
            panic!(
                "Typechecking should have caught function already bound: {}",
                decl.name
            );
        }

        Ok(())
    }

    /// Print up to `n` of a function's tuples, or all of them when `n` is
    /// `None`.
    pub fn print_function(
        &mut self,
        sym: &str,
        n: Option<usize>,
        file: Option<(File, PathBuf)>,
        span: Span,
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
            // function_to_dag resolved the same name, so this cannot miss
            .unwrap();
        let terms_and_outputs: Vec<_> = terms.into_iter().zip(outputs.unwrap()).collect();
        let output = CommandOutput::PrintFunction(f.clone(), termdag, terms_and_outputs, mode);
        match file {
            Some((mut file, path)) => {
                log::info!("Writing output to file");
                file.write_all(output.to_string().as_bytes())
                    .map_err(|e| Error::IoError(path, e, span.clone()))?;
                Ok(None)
            }
            None => Ok(Some(output)),
        }
    }

    /// Provide source for use in proof checking.
    /// This enables testing of a desugared egglog proof program outside of proof mode.
    /// When proof_testing is true, turns every `check` outside `fail` into a `prove` command.
    /// Parse and resolve the source in one fresh proof graph, just as
    /// [`Self::resolve_program`] does: anonymous variables allocated during parsing
    /// share the generator that names proof rules during lowering. Passing an AST
    /// parsed by another graph loses that state and can produce different rule names.
    /// This helper uses the default parser and proof configuration, plus this graph's
    /// fact directory; it does not replay custom parser or command extensions.
    /// Checks inside `fail` remain negative assertions.
    /// Not intended for general use but needed in files.rs, so public but hidden.
    #[doc(hidden)]
    pub fn set_proof_checking_program(
        &mut self,
        filename: Option<String>,
        source: &str,
        proof_testing: bool,
    ) -> Result<(), Error> {
        // make a new e-graph, desugar the program in proof mode
        let mut proof_check_eg = EGraph::new_with_proofs();
        proof_check_eg
            .fact_directory
            .clone_from(&self.fact_directory);
        if proof_testing {
            proof_check_eg = proof_check_eg.with_proof_testing();
        }
        let prog = proof_check_eg.parse_program_timed(filename, source)?;
        let resolved = proof_check_eg
            .process_program_internal(ProgramSource::Commands(prog.into_iter()), false)?;

        self.proof_check_program = resolved.resolved_before_proofs;
        Ok(())
    }

    /// Print the size of a function. If no function name is provided,
    /// print the size of all non-hidden functions as an s-expression list of
    /// `(name size)` pairs, e.g. `((name size) ...)`.
    pub fn print_size(&self, sym: Option<&str>) -> Result<CommandOutput, Error> {
        if let Some(sym) = sym {
            let f = self
                .functions
                .get(sym)
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
            let mut lens = self
                .functions
                .iter()
                .filter(|(_, f)| !f.decl.internal_hidden && !f.decl.internal_let)
                .map(|(sym, f)| (sym.clone(), self.backend.table_size(f.backend_id)))
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
    /// The iteration is recorded in the overall run report, whatever ran it.
    ///
    /// This will return an error if an egglog primitive returns None in an action.
    pub fn step_rules(&mut self, ruleset: &str) -> Result<RunReport, Error> {
        fn collect_rule_ids(
            ruleset: &str,
            rulesets: &IndexMap<String, Ruleset>,
            ids: &mut Vec<egglog_bridge::RuleId>,
        ) {
            match &rulesets[ruleset].kind {
                RulesetKind::Rules(rules) => {
                    for rule in rules.values() {
                        ids.push(rule.backend_id);
                    }
                }
                RulesetKind::Combined(sub_rulesets) => {
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
            .run_rules(&rule_ids, Some(&self.type_info))
            .map_err(|e| Error::BackendError(e.to_string()))?;

        let report = RunReport::singleton(
            ruleset,
            self.rulesets[ruleset].timing_role,
            iteration_report,
        );
        self.overall_report.run.union(report.clone());
        Ok(report)
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

        match self
            .rulesets
            .get(&rule.ruleset)
            .map(|ruleset| &ruleset.kind)
        {
            Some(RulesetKind::Rules(_)) => {}
            Some(RulesetKind::Combined(_)) => {
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
            let builder = self.backend.new_rule(&rule.name, seminaive);
            let mut translator = RuleTranslator::new(
                builder,
                &self.functions,
                &self.type_info,
                requires_read_context,
            );
            translator.query(query, rule.include_subsumed)?;
            translator.actions(actions)?;
            translator.build(no_decomp)
        };

        let Some(Ruleset {
            kind: RulesetKind::Rules(rules),
            ..
        }) = self.rulesets.get_mut(&rule.ruleset)
        else {
            unreachable!("ruleset was validated before compiling the rule")
        };
        match rules.entry(rule.name.clone()) {
            indexmap::map::Entry::Occupied(_) => {
                return Err(Error::RuleAlreadyExists(rule.name, rule.span));
            }
            indexmap::map::Entry::Vacant(e) => e.insert(CompiledRule {
                core: core_rule,
                backend_id: rule_id,
                seminaive,
                requires_read_context,
                no_decomp,
                include_subsumed: rule.include_subsumed,
            }),
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

        let builder = self.backend.new_rule("eval_actions", false);
        let mut translator = RuleTranslator::new(
            builder,
            &self.functions,
            &self.type_info,
            true, // global action: Read/Full contexts (may read the DB)
        );
        translator.actions(&actions)?;
        let id = translator.build(false);
        let result = self.backend.run_rules(&[id], Some(&self.type_info));
        self.backend.free_rule(id);

        match result {
            Ok(_) => Ok(()),
            Err(e) => Err(Error::BackendError(e.to_string())),
        }
    }

    /// Commit a bounded sequence of validated constructor actions together.
    /// Their command-local indexes are independent, while pending table values
    /// are shared until the final merge/rebuild restores congruence.
    fn flush_ground_actions(&mut self, pending: &mut Vec<GroundActions>) -> Result<(), Error> {
        if pending.is_empty() {
            return Ok(());
        }
        let timer = Instant::now();
        let union = egglog_bridge::UnionAction::new(&self.backend);
        let result = self.backend.run_actions(|state| {
            let mut values = Vec::new();
            let mut arguments = Vec::new();
            // Table handles are interned for this action run. Nullary results
            // stay fixed until this transaction's final merge/rebuild.
            let mut constants = HashMap::default();
            for prepared in pending.drain(..) {
                values.clear();
                for (table, args) in prepared.lookups {
                    let value = if args.is_empty() {
                        *constants
                            .entry(Rc::as_ptr(&table))
                            .or_insert_with(|| table.lookup_or_insert(state, &[]).unwrap())
                    } else {
                        arguments.clear();
                        arguments.extend(args.iter().map(|index| values[*index]));
                        table.lookup_or_insert(state, &arguments).unwrap()
                    };
                    values.push(value);
                }
                if let Some((left, right)) = prepared.union {
                    union.union(state, values[left], values[right]);
                }
            }
        });
        self.overall_report.commands_actions += timer.elapsed();
        result.map_err(|e| Error::BackendError(e.to_string()))
    }

    /// Apply the same memory and backend-callback boundaries to source and AST
    /// plans. Metadata stays valid across bounded flushes within an action run.
    fn queue_ground_action(
        &mut self,
        prepared: GroundActions,
        pending: &mut Vec<GroundActions>,
        pending_lookups: &mut usize,
        batchable: &mut Option<bool>,
    ) -> Result<(), Error> {
        *pending_lookups += prepared.lookups.len();
        pending.push(prepared);
        let can_batch = *batchable.get_or_insert_with(|| self.backend.can_batch_actions());
        if !can_batch || pending.len() >= 2_048 || *pending_lookups >= 131_072 {
            self.flush_ground_actions(pending)?;
            *pending_lookups = 0;
        }
        Ok(())
    }

    fn ground_table(&self, func: &FuncType) -> Option<egglog_bridge::TableAction> {
        let function = self.functions.get(&func.name)?;
        if func.subtype != FunctionSubtype::Constructor
            || function.subtype() != FunctionSubtype::Constructor
            || func.num_outputs() != 1
            || function.decl.internal_view.is_some()
            || function.is_let_binding()
            || self.type_info.is_global(&func.name)
            || self.type_info.indexes.contains_key(&func.name)
        {
            return None;
        }
        let table = egglog_bridge::TableAction::new(&self.backend, function.backend_id);
        if table.kind() != TableKind::Constructor
            || table.output_arity() != 1
            || table.input_arity() != func.input.len()
        {
            return None;
        }
        Some(table)
    }

    /// Typecheck closed source actions directly into an execution plan. No IDs or
    /// writes are allocated until every call and the optional union have passed.
    fn prepare_source_action<S>(
        &self,
        form: &Sexp<'_, S>,
        calls: &mut GroundActionCache,
    ) -> Option<GroundActions> {
        let (head, action) = self.parser.closed_action(form)?;
        if !self
            .command_macros
            .preserves_closed_constructor_action(head)
        {
            return None;
        }
        self.prepare_ground_action(Some(action), calls, |head| {
            self.parser.can_parse_constructor_call(head)
        })
    }

    /// The source and AST paths use the same semantic checks and plan emitter.
    fn prepare_ground_action<Node: typechecking::CallView>(
        &self,
        action: Option<typechecking::ClosedAction<&Node>>,
        calls: &mut GroundActionCache,
        mut permit_call: impl FnMut(&str) -> bool,
    ) -> Option<GroundActions> {
        if self.proof_state.original_typechecking.is_some() {
            return None;
        }
        let mut prepared = GroundActions {
            lookups: Vec::new(),
            union: None,
        };
        let checked = self.type_info.check_closed_action(
            action?,
            &mut |head| {
                // Source admission is checked even on metadata cache hits: AST
                // calls did not pass parser dispatch, and parser macros may add
                // overrides while expanding a form to zero ordinary commands.
                if !permit_call(head) {
                    return None;
                }
                if let Some(cached) = calls.get(head) {
                    return cached.clone();
                }
                let call = self.type_info.closed_call_type(head).and_then(|func| {
                    // Custom sorts and encoded views retain ordinary compiled execution.
                    if !(func.output().as_ref() as &dyn Any).is::<EqSort>() {
                        return None;
                    }
                    self.ground_table(func)
                        .map(|table| (func.clone(), Rc::new(table)))
                });
                calls.insert(head.into(), call.clone());
                call
            },
            &mut |_, _, table, args: SmallVec<[usize; 4]>| {
                let index = prepared.lookups.len();
                prepared.lookups.push((table, args));
                Some(index)
            },
        )?;
        if let typechecking::ClosedAction::Union(left, right) = checked {
            prepared.union = Some((left, right));
        }
        Some(prepared)
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

    /// Run `f` against a raw execution state, with this e-graph's declarations
    /// visible to any primitive it reaches.
    ///
    /// Every execution egglog starts goes through here or its `_tracked` twin,
    /// so no call site has to decide whether a primitive it cannot see might
    /// want to resolve a signature.
    fn with_execution_state<R>(&self, f: impl FnOnce(&mut ExecutionState<'_>) -> R) -> R {
        self.backend.with_execution_state(Some(&self.type_info), f)
    }

    /// [`EGraph::with_execution_state`], also reporting whether `f` staged a
    /// mutation.
    fn with_execution_state_tracked<R>(
        &self,
        f: impl FnOnce(&mut ExecutionState<'_>) -> R,
    ) -> (R, bool) {
        self.backend
            .with_execution_state_tracked(Some(&self.type_info), f)
    }

    /// Run a read-only closure against the e-graph. The closure receives
    /// a [`ReadState`], so it can read but not write. Because this
    /// borrows `&self`, the closure and its callbacks may also call other
    /// `&self` methods such as [`EGraph::value_to_base`].
    ///
    pub fn read<R>(&self, f: impl FnOnce(ReadState<'_, '_>) -> R) -> R {
        let registry = self.backend.action_registry().clone();
        let guard = registry.read();
        self.with_execution_state_tracked(|es| f(ReadState::wrap(es, &guard, Context::Read)))
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
        let (kind, input_arity, output_arity) = function.table_read_projection();
        if kind == TableKind::Constructor {
            return Err(crate::api::ApiError::WrongSubtype {
                name: name.to_owned(),
                expected: "function",
                actual: "constructor",
            }
            .into());
        }
        if output_arity != 1 {
            return Err(crate::api::ApiError::TupleOutputUnsupported {
                name: name.to_owned(),
                method: "function_entries",
            }
            .into());
        }
        self.backend.for_each_while(function.backend_id, |row| {
            f(FunctionEntry {
                inputs: &row.vals[..input_arity],
                output: row.vals[input_arity],
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
        let (kind, input_arity, _) = function.table_read_projection();
        if kind != TableKind::Constructor {
            return Err(crate::api::ApiError::WrongSubtype {
                name: name.to_owned(),
                expected: "constructor",
                actual: "function",
            }
            .into());
        }
        self.backend.for_each_while(function.backend_id, |row| {
            f(Enode {
                name,
                children: &row.vals[..input_arity],
                eclass: row.vals[input_arity],
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

        if resolved_commands.len() != 1 {
            return Err(Error::BackendError(
                "eval_expr expects a single resolved command".to_string(),
            ));
        }
        let Some(resolved_command) = resolved_commands.into_iter().next() else {
            return Err(Error::BackendError(
                "eval_expr expects a single resolved command".to_string(),
            ));
        };
        let resolved_expr = match resolved_command {
            ResolvedNCommand::CoreAction(ResolvedAction::Expr(_, resolved_expr)) => resolved_expr,
            cmd => {
                return Err(Error::BackendError(format!(
                    "eval_expr: unexpected resolved command: {cmd:?}"
                )));
            }
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
    /// that rule lowering injects for `unstable-fn`.
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
                    let panic_id = self.backend.new_panic(format!(
                        "unstable-fn over `{name}` was applied in a context where its wrapped \
                         function is not valid for this call site, if in a rule, add :naive."
                    ));
                    let resolved_function = resolve_function_container_target_with_context(
                        &self.backend,
                        &self.functions,
                        &self.type_info,
                        name,
                        prim,
                        panic_id,
                        // Top-level action evaluation runs in the `Full` context.
                        crate::Context::Full,
                        target_span,
                    )?;
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

        let builder = self.backend.new_rule("eval_resolved_expr", false);
        let mut translator = RuleTranslator::new(
            builder,
            &self.functions,
            &self.type_info,
            true, // global action: Read/Full contexts (may read the DB)
        );
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
            ext_id,
            "eval_resolved_expr_result",
            &[arg],
            egglog_bridge::ColumnTy::Base(unit_id),
        );

        let id = translator.build(false);
        let rule_result = self.backend.run_rules(&[id], Some(&self.type_info));
        self.backend.free_rule(id);
        self.backend.free_external_func(ext_id);
        let _ = rule_result.map_err(|e| {
            Error::BackendError(format!("Failed to evaluate expression '{expr}': {e}"))
        })?;

        let result = result.lock().unwrap().unwrap();
        Ok(result)
    }

    fn add_combined_ruleset(
        &mut self,
        span: &Span,
        name: String,
        rulesets: Vec<String>,
    ) -> Result<(), Error> {
        let mut timing_role = None;
        for ruleset in &rulesets {
            let role = self
                .rulesets
                .get(ruleset)
                .map(|ruleset| ruleset.timing_role)
                .ok_or_else(|| Error::NoSuchRuleset(ruleset.clone(), span.clone()))?;
            if timing_role.is_some_and(|expected| expected != role) {
                return Err(Error::MixedRulesetResponsibilities(name, span.clone()));
            }
            timing_role = Some(role);
        }
        match self.rulesets.entry(name.clone()) {
            Entry::Occupied(_) => panic!("Ruleset '{name}' was already present"),
            Entry::Vacant(e) => e.insert(Ruleset {
                kind: RulesetKind::Combined(rulesets),
                timing_role: timing_role.unwrap_or(RulesetTimingRole::Program),
            }),
        };
        Ok(())
    }

    fn add_ruleset(&mut self, name: String) {
        let proof_names = &self.proof_state.proof_names;
        let timing_role = if [
            &proof_names.path_compress_ruleset_name,
            &proof_names.rebuilding_ruleset_name,
            &proof_names.rebuilding_cleanup_ruleset_name,
            &proof_names.subsume_ruleset_name,
        ]
        .iter()
        .any(|generated| generated.as_str() == name)
        {
            RulesetTimingRole::Equality
        } else {
            RulesetTimingRole::Program
        };
        match self.rulesets.entry(name.clone()) {
            Entry::Occupied(_) => panic!("Ruleset '{name}' was already present"),
            Entry::Vacant(e) => e.insert(Ruleset {
                kind: RulesetKind::Rules(Default::default()),
                timing_role,
            }),
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

        let ext_sc = egglog_bridge::SideChannel::default();
        let ext_sc_ref = ext_sc.clone();
        let ext_id = self
            .backend
            .register_external_func(Box::new(make_external_func(move |exec_state, _| {
                *ext_sc_ref.lock().unwrap() = Some(());
                exec_state.trigger_early_stop();
                Some(Value::new_const(0))
            })));

        let builder = self.backend.new_rule("check_facts", false);
        let mut translator = RuleTranslator::new(
            builder,
            &self.functions,
            &self.type_info,
            true, // global query: Read context (may read the DB)
        );
        translator.query(&query, true)?;
        translator.call_external_func(
            ext_id,
            "check_facts_match",
            &[],
            egglog_bridge::ColumnTy::Id,
        );
        let id = translator.build(false);
        let run_result = self.backend.run_rules(&[id], Some(&self.type_info));
        self.backend.free_rule(id);
        self.backend.free_external_func(ext_id);
        let iteration_report = run_result.map_err(|e| Error::BackendError(e.to_string()))?;
        self.overall_report.commands_check += iteration_report.total_time();

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
        enum CommandPhase {
            Install,
            Actions,
            Check,
            Other,
        }

        let phase = match &command {
            ResolvedNCommand::Sort { .. }
            | ResolvedNCommand::Function(_)
            | ResolvedNCommand::Index { .. }
            | ResolvedNCommand::AddRuleset(..)
            | ResolvedNCommand::UnstableCombinedRuleset(..)
            | ResolvedNCommand::NormRule { .. } => CommandPhase::Install,
            ResolvedNCommand::CoreAction(_)
            | ResolvedNCommand::CoreActions(_)
            | ResolvedNCommand::Input { .. } => CommandPhase::Actions,
            ResolvedNCommand::Check(..) => CommandPhase::Check,
            _ => CommandPhase::Other,
        };
        let command_timer = Instant::now();
        let process_before = self.overall_report.process_time();
        let iteration_before = self.overall_report.run.iterations.len();
        let result = self.run_command_inner(command);
        let nested_process = self
            .overall_report
            .process_time()
            .saturating_sub(process_before);
        let nested_rulesets = self.overall_report.run.iterations[iteration_before..]
            .iter()
            .map(|iteration| iteration.report.total_time())
            .sum();
        let own_time = command_timer
            .elapsed()
            .saturating_sub(nested_process + nested_rulesets);
        match phase {
            CommandPhase::Install => self.overall_report.frontend_install += own_time,
            CommandPhase::Actions => self.overall_report.commands_actions += own_time,
            CommandPhase::Check => self.overall_report.commands_check += own_time,
            CommandPhase::Other => self.overall_report.commands_other += own_time,
        }
        result
    }

    fn run_command_inner(
        &mut self,
        command: ResolvedNCommand,
    ) -> Result<Vec<CommandOutput>, Error> {
        match command {
            // Sorts are already declared during typechecking
            ResolvedNCommand::Sort {
                name,
                uf,
                proof_constructors,
                ..
            } => {
                // Restore the sort's UF metadata into proof_state.
                if let Some((uf_ctor, _uf_index)) = uf {
                    self.proof_state
                        .uf_parent
                        .insert(name.clone(), uf_ctor.clone());
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
                    names.fiat_prefix = pc.fiat;
                    names.proj_constructor = pc.proj;
                    names.proj_prim_prefix = pc.proj_prim;
                }
                log::info!("Declared sort {name}.")
            }
            ResolvedNCommand::Function(fdecl) => {
                self.declare_function(&fdecl)?;
                log::info!("Declared {} {}.", fdecl.subtype, fdecl.name)
            }
            ResolvedNCommand::Index { name, function, .. } => {
                // Nothing to build: storage creates the occurrence index the
                // first time a rule probes it. Typechecking already registered
                // the relation the atoms resolve against.
                log::info!("Declared index {name} over {function}.");
            }
            ResolvedNCommand::AddRuleset(_span, name) => {
                self.add_ruleset(name.clone());
                log::info!("Declared ruleset {name}.");
            }
            ResolvedNCommand::UnstableCombinedRuleset(span, name, others) => {
                self.add_combined_ruleset(&span, name.clone(), others)?;
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
                // Already recorded by `step_rules`, per iteration.
                return Ok(vec![CommandOutput::RunSchedule(report)]);
            }
            ResolvedNCommand::PrintOverallStatistics(span, file) => match file {
                None => {
                    log::info!("Printed overall statistics");
                    return Ok(vec![CommandOutput::OverallStatistics(
                        self.overall_report.run.clone(),
                    )]);
                }
                Some(path) => {
                    let mut file = std::fs::File::create(&path)
                        .map_err(|e| Error::IoError(path.clone().into(), e, span.clone()))?;
                    log::info!("Printed overall statistics to json file {path}");

                    serde_json::to_writer(&mut file, &self.overall_report.run).map_err(|e| {
                        Error::BackendError(format!("failed writing statistics: {e}"))
                    })?;
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
                    self.eval_actions(&ResolvedActions::new(vec![action]))?;
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

                return if n == 0 {
                    let (termdag, term, cost) = self.extract_value(&sort, x)?;
                    // dont turn termdag into a string if we have messages disabled for performance reasons
                    if log_enabled!(Level::Info) {
                        log::info!("extracted with cost {cost}: {}", termdag.to_string(term));
                    }
                    Ok(vec![CommandOutput::ExtractBest(termdag, cost, term)])
                } else {
                    if n < 0 {
                        return Err(Error::ExtractError(
                            "cannot extract a negative number of variants".to_string(),
                        ));
                    }
                    let extracted = self.extract_variants(vec![(sort, x)], n as usize)?;
                    let terms: Vec<TermId> = extracted
                        .variants
                        .into_iter()
                        .next()
                        .expect("extract_variants returns one result for one root")
                        .into_iter()
                        .map(|extracted| extracted.term)
                        .collect();
                    if log_enabled!(Level::Info) {
                        let expr_str = expr.to_string();
                        log::info!("extracted {} variants for {expr_str}", terms.len());
                    }
                    Ok(vec![CommandOutput::ExtractVariants(
                        extracted.termdag,
                        terms,
                    )])
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
                        let path: PathBuf = file.into();
                        match std::fs::File::create(&path) {
                            Ok(f) => Ok((f, path)),
                            Err(e) => Err(Error::IoError(path, e, span.clone())),
                        }
                    })
                    .transpose()?;
                return self
                    .print_function(&f, n, file, span.clone(), mode)
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
                // A single check is read-only, so avoid cloning the e-graph for
                // the overwhelmingly common negative-assertion form.
                if matches!(cmds.as_slice(), [ResolvedNCommand::Check(..)]) {
                    let check = cmds.into_iter().next().unwrap();
                    return match self.run_command(check) {
                        Err(error) => {
                            log::info!("Command failed as expected: {error}");
                            Ok(vec![])
                        }
                        Ok(_) => Err(Error::ExpectFail(span)),
                    };
                }

                self.push();
                let failure = cmds
                    .into_iter()
                    .find_map(|command| self.run_command(command).err());
                self.pop()
                    .expect("the snapshot pushed for `fail` must still be present");
                return match failure {
                    Some(error) => {
                        log::info!("Command failed as expected: {error}");
                        Ok(vec![])
                    }
                    None => Err(Error::ExpectFail(span)),
                };
            }
            ResolvedNCommand::Input {
                span,
                name,
                file,
                proof_base,
            } => {
                // An encoded program (term/proof mode, or a replayed desugared
                // program) declares nothing under the function's own name, so the
                // name resolving to a view is what says the rows go into the
                // encoded tables; a plain program targets a user
                // relation/constructor loaded by the relation loader.
                if self.functions.get(&name).is_some_and(|f| f.is_fd_view()) {
                    self.native_input(span, &name, file, proof_base)?;
                } else {
                    self.input_file(span, &name, file)?;
                }
            }
            ResolvedNCommand::Output { span, file, exprs } => {
                let mut filename = self.fact_directory.clone().unwrap_or_default();
                filename.push(file.as_str());

                // Preserve the command's file-error ordering: reject an invalid
                // output path before evaluating expressions.
                use std::io::Write;
                let mut f = File::options()
                    .append(true)
                    .create(true)
                    .open(&filename)
                    .map_err(|e| Error::IoError(filename.clone(), e, span.clone()))?;

                // Evaluation may mutate the e-graph, so finish it before
                // extraction takes a shared borrow for its prepared costs.
                let roots = exprs
                    .iter()
                    .map(|expr| {
                        let value = self.eval_resolved_expr(span.clone(), expr)?;
                        Ok((expr.output_type(), value))
                    })
                    .collect::<Result<Vec<_>, Error>>()?;
                let extracted = self.extract_best(roots)?;
                for root in extracted.terms {
                    let root = root.ok_or_else(|| {
                        Error::ExtractError(
                            "Unable to find any valid extraction (likely due to subsume or delete)"
                                .to_string(),
                        )
                    })?;
                    writeln!(f, "{}", extracted.termdag.to_string(root.term))
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
                name => return Err(Error::UnsupportedInputType(name.to_owned(), span.clone())),
            }
        }
        if function_type.subtype != FunctionSubtype::Constructor {
            for sort in &function_type.outputs {
                match sort.name() {
                    "i64" | "String" | "Unit" => {}
                    name => {
                        return Err(Error::UnsupportedInputType(name.to_owned(), span.clone()));
                    }
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
            .ok_or_else(|| {
                Error::TypeError(TypeError::UnboundFunction(
                    func_name.to_owned(),
                    span.clone(),
                ))
            })?
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

        let table_action = egglog_bridge::TableAction::new(&self.backend, func.backend_id);

        if function_type.subtype != FunctionSubtype::Constructor {
            self.with_execution_state(|es| {
                for row in parsed_contents.iter() {
                    table_action.insert(es, row.iter().copied());
                }
                Some(unit_val)
            });
        } else {
            self.with_execution_state(|es| {
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

    /// Load `(input …)` facts natively into the encoding's tables. Each row gets
    /// a fresh e-class and goes straight into the function's view, with the fiat
    /// justifying it when the encoding carries proofs. Rows are plain-inserted
    /// (no get-or-insert): a duplicate view key is left to the view's
    /// merge/no-merge handling.
    ///
    /// The row shape is read off the view, so this also works when a desugared
    /// program is replayed in a fresh e-graph. `proof_base` is where
    /// `lower_inputs` put this input's per-row actions in the program proof
    /// checking reads: row `i` is justified by naming the action at
    /// `proof_base + i`.
    fn native_input(
        &mut self,
        span: Span,
        func_name: &str,
        file: String,
        proof_base: Option<usize>,
    ) -> Result<(), Error> {
        let view = self
            .functions
            .get(func_name)
            .unwrap_or_else(|| panic!("Unrecognized function name {func_name}"));
        let view_id = view.backend_id;
        // Proofs are on for this relation iff the view's proof column (its last
        // output) is not `Unit`; term-encoding-only mode uses `Unit` there.
        let proofs = view.func_type.outputs.last().unwrap().name() != "Unit";
        // A constructor's and a relation's output is the e-class the load mints;
        // a function's is a value the rows carry. That is the split the view
        // records, and it has to agree with the one `input_actions` made when it
        // built the per-row actions a fiat now names.
        let output_is_minted = view.rows_are_enodes();
        // The CSV columns: the view's children, plus any output they carry.
        let mut csv_sorts: Vec<ArcSort> = view.func_type.input.clone();
        if !output_is_minted {
            csv_sorts.push(view.func_type.outputs[0].clone());
        }

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

        // Each row's existence is justified by the per-row action `lower_inputs`
        // put in the program proof checking reads, named by position like every
        // other fiat, so nothing here names the term the row built. The encoder
        // stamped where those actions start onto the command.
        let fiat_term = proofs.then(|| {
            let relation = self.proof_state.proof_names.fiat_term_constructor.clone();
            let table = self
                .functions
                .get(&relation)
                .unwrap_or_else(|| panic!("no fiat-term relation"))
                .backend_id;
            let base = proof_base.expect("an encoded input carries where its rows start");
            // A constructor row is the whole per-row action; a custom row is the
            // `set`'s row node, which follows its argument and value nodes — one
            // literal each, so one per CSV column.
            let node = if output_is_minted { 0 } else { csv_sorts.len() };
            (table, base, node)
        });

        let num_facts = value_rows.len();
        let mut batch: Vec<(egglog_bridge::FunctionId, Vec<Value>)> = Vec::new();
        for (row_index, value_row) in value_rows.into_iter().enumerate() {
            let fv = self.backend.fresh_id();

            let view_proof = if let Some((fiat_id, base, node)) = fiat_term {
                // `(FiatTerm <this row's action> <node> pf)`.
                let pf = self.backend.fresh_id();
                let at = self.backend.base_values().get((base + row_index) as i64);
                let node = self.backend.base_values().get(node as i64);
                batch.push((fiat_id, vec![at, node, pf, unit_val]));
                pf
            } else {
                unit_val
            };

            // View row. A constructor's FD view value-0 is the minted term id; a
            // custom view stores the base output (already in `value_row`). The
            // proof column follows (`Unit` when the encoding carries no proofs).
            let mut vrow = value_row;
            if output_is_minted {
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
        let proofs_enabled = self.proof_state.proofs_enabled;
        if let Some(original_typechecking) = self.proof_state.original_typechecking.as_mut() {
            // Typecheck using the original egraph
            // TODO this is ugly- we don't need an entire e-graph just for type information.
            let typecheck_timer = Instant::now();
            let typechecked = original_typechecking.typecheck_program(&desugared)?;
            self.overall_report.typecheck += typecheck_timer.elapsed();

            for command in &typechecked {
                if let Err(reason) = command_supports_proof_encoding(
                    &command.to_command(),
                    &original_typechecking.type_info,
                    proofs_enabled,
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
            let typecheck_timer = Instant::now();
            let mut typechecked = self.typecheck_program(&desugared)?;
            self.overall_report.typecheck += typecheck_timer.elapsed();

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
        let lowering_timer = Instant::now();
        let nested_before = self.overall_report.process_time();
        let resolved = self.resolve_command_inner(command);
        let nested = self
            .overall_report
            .process_time()
            .saturating_sub(nested_before);
        self.overall_report.frontend_other += lowering_timer.elapsed().saturating_sub(nested);
        resolved
    }

    fn resolve_command_inner(&mut self, command: Command) -> Result<ResolvedNCommands, Error> {
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

            let numbered_before = self.proof_state.global_actions_numbered;
            let term_encoding_added =
                ProofInstrumentor::add_term_encoding(self, typechecked_no_globals)?;
            // A fiat names a global action by index, so the encoder's numbering
            // has to be the one `gather_global_actions` will walk. It counts the
            // encoded program's commands while the checker walks the lowered
            // one; the two agree only because neither lowering changes how many
            // global actions a command contributes.
            debug_assert_eq!(
                self.proof_state.global_actions_numbered - numbered_before,
                crate::proofs::proof_checker::gather_global_actions(&per_row_before_proofs).count(),
                "the encoder numbered a different number of global actions than this command \
                 contributes to the program proof checking reads"
            );
            let mut new_typechecked = vec![];
            for new_cmd in term_encoding_added {
                let desugared =
                    desugar_command(new_cmd, &mut self.parser, self.proof_state.proof_testing)?;
                for cmd in &desugared {
                    log::trace!("Desugared term encoding: {}", cmd.to_command());
                }

                // Now typecheck using self, adding term type information.
                let typecheck_timer = Instant::now();
                let desugared_typechecked = self.typecheck_program(&desugared)?;
                self.overall_report.typecheck += typecheck_timer.elapsed();
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

    /// Run a program and return its outputs, or resolve it without execution.
    /// Only resolution retains the lowered commands in the returned value.
    fn process_program_internal(
        &mut self,
        mut program: ProgramSource<'_>,
        run_commands: bool,
    ) -> Result<ResolvedNCommandsWithOutput, Error> {
        let mut outputs = Vec::new();
        let mut desugared_before_proofs = Vec::new();
        let mut desugared = Vec::new();
        let mut pending = Vec::new();
        let mut pending_lookups = 0;
        // Tables and callback capabilities cannot change inside an admitted run.
        let mut batchable = None;
        let mut ground_calls = GroundActionCache::default();

        'program: loop {
            let next = match &mut program {
                ProgramSource::Commands(commands) => commands.next(),
                ProgramSource::Text { parser, expanded } => loop {
                    if let Some(command) = expanded.next() {
                        break Some(command);
                    }
                    // Proof/resolution paths already require the full AST, so
                    // construct owned spans directly instead of converting later.
                    if !run_commands || self.proof_state.original_typechecking.is_some() {
                        let timer = Instant::now();
                        let parsed = self.parser.parse_next_command(parser);
                        self.overall_report.frontend_parse += timer.elapsed();
                        match parsed {
                            Ok(Some(commands)) => *expanded = commands.into_iter(),
                            Ok(None) => break None,
                            Err(error) => {
                                self.flush_ground_actions(&mut pending)?;
                                return Err(error.into());
                            }
                        }
                        continue;
                    }
                    let timer = Instant::now();
                    let parsed = parser.next_sexp(|_, range| range);
                    self.overall_report.frontend_parse += timer.elapsed();
                    let form = match parsed {
                        Ok(Some(form)) => form,
                        Ok(None) => break None,
                        Err(error) => {
                            self.flush_ground_actions(&mut pending)?;
                            return Err(error.into());
                        }
                    };
                    let timer = Instant::now();
                    let prepared = self.prepare_source_action(&form, &mut ground_calls);
                    self.overall_report.typecheck += timer.elapsed();
                    if let Some(prepared) = prepared {
                        self.queue_ground_action(
                            prepared,
                            &mut pending,
                            &mut pending_lookups,
                            &mut batchable,
                        )?;
                        continue 'program;
                    }
                    let timer = Instant::now();
                    let form = form.with_spans(parser);
                    let parsed = self.parser.parse_command(&form);
                    self.overall_report.frontend_parse += timer.elapsed();
                    *expanded = match parsed {
                        Ok(commands) => commands.into_iter(),
                        Err(error) => {
                            self.flush_ground_actions(&mut pending)?;
                            return Err(error.into());
                        }
                    };
                },
            };
            let Some(before_expanded_command) = next else {
                break;
            };
            // First do user-provided macro expansion for this command,
            // which may rely on type information from previous commands.
            let macro_type_info = self
                .proof_state
                .original_typechecking
                .as_ref()
                .map(|egraph| &egraph.type_info)
                .unwrap_or(&self.type_info);
            let macro_timer = Instant::now();
            let macro_expanded = self.command_macros.apply(
                before_expanded_command,
                &mut self.parser.symbol_gen,
                macro_type_info,
            );
            self.overall_report.frontend_other += macro_timer.elapsed();
            let macro_expanded = match macro_expanded {
                Ok(commands) => commands,
                Err(error) => {
                    self.flush_ground_actions(&mut pending)?;
                    return Err(error);
                }
            };

            for command in macro_expanded {
                if run_commands && let Command::Action(action) = &command {
                    let timer = Instant::now();
                    let prepared = self.prepare_ground_action(
                        typechecking::ClosedAction::from_action(action),
                        &mut ground_calls,
                        |_| true,
                    );
                    self.overall_report.typecheck += timer.elapsed();
                    if let Some(prepared) = prepared {
                        self.queue_ground_action(
                            prepared,
                            &mut pending,
                            &mut pending_lookups,
                            &mut batchable,
                        )?;
                        continue;
                    }
                }

                // Reads, schedules, declarations, unsupported actions and includes
                // observe the complete preceding prefix, even if they later fail.
                self.flush_ground_actions(&mut pending)?;
                pending_lookups = 0;
                batchable = None;
                ground_calls.clear();

                // handle include specially- we keep them as-is for desugaring
                if let Command::Include(span, file) = &command {
                    let include_timer = Instant::now();
                    let s = std::fs::read_to_string(file)
                        .map_err(|e| Error::IoError(file.clone().into(), e, span.clone()));
                    self.overall_report.frontend_other += include_timer.elapsed();
                    let s = s?;
                    let included_program = if run_commands {
                        ProgramSource::Text {
                            parser: SexpParser::new(Some(file.clone()), &s),
                            expanded: Vec::new().into_iter(),
                        }
                    } else {
                        ProgramSource::Commands(
                            self.parse_program_timed(Some(file.clone()), &s)?
                                .into_iter(),
                        )
                    };
                    let resolved = self.process_program_internal(included_program, run_commands)?;
                    outputs.extend(resolved.outputs);
                    desugared.extend(resolved.resolved);
                    desugared_before_proofs.extend(resolved.resolved_before_proofs);
                } else {
                    let resolved = self.resolve_command(command)?;
                    // Execution callers discard resolved trees; retaining them here
                    // duplicates large proof programs. Keep only the checker's history.
                    if run_commands {
                        if self.are_proofs_enabled() {
                            self.proof_check_program
                                .extend(resolved.desugared_before_proofs);
                        }
                    } else {
                        desugared_before_proofs.extend(resolved.desugared_before_proofs);
                        desugared.extend(resolved.desugared.clone());
                    }

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

        self.flush_ground_actions(&mut pending)?;

        Ok(ResolvedNCommandsWithOutput {
            outputs,
            resolved_before_proofs: desugared_before_proofs,
            resolved: desugared,
        })
    }

    /// Run a program, represented as an AST.
    /// Return a list of messages.
    ///
    /// Egglog errors, including `(panic ...)`, are not transactional: effects
    /// completed before an error remain. After a rule-action error, a successful
    /// recovery rebuild leaves the database canonical and reusable. Rust panics
    /// in extension code unwind normally instead of becoming [`enum@Error`] values.
    pub fn run_program(&mut self, program: Vec<Command>) -> Result<Vec<CommandOutput>, Error> {
        let res =
            self.process_program_internal(ProgramSource::Commands(program.into_iter()), true)?;
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
        let parsed = self.parse_program_timed(filename, input)?;
        let res =
            self.process_program_internal(ProgramSource::Commands(parsed.into_iter()), false)?;
        Ok(res.resolved.into_iter().map(|c| c.to_command()).collect())
    }

    /// Takes a source program `input` and parses it into a list of [`Command`]s.
    pub fn parse_program(
        &mut self,
        filename: Option<String>,
        input: &str,
    ) -> Result<Vec<Command>, Error> {
        self.parse_program_timed(filename, input)
    }

    /// Parse and execute source commands, returning their messages.
    ///
    /// With proofs disabled, commands execute incrementally: earlier commands remain
    /// executed if a later command fails to parse, and parser extensions installed by
    /// a command are available to subsequent source forms.
    /// With proofs enabled, this input is parsed in full before execution.
    /// Call [`Self::parse_program`] followed by [`Self::run_program`] to request
    /// eager parsing regardless of proof mode.
    ///
    /// `filename` is an optional argument to indicate the source of
    /// the program for error reporting. If `filename` is `None`,
    /// a default name will be used.
    pub fn parse_and_run_program(
        &mut self,
        filename: Option<String>,
        input: &str,
    ) -> Result<Vec<CommandOutput>, Error> {
        if self.are_proofs_enabled() {
            let program = self.parse_program_timed(filename, input)?;
            return self.run_program(program);
        }
        let source = ProgramSource::Text {
            parser: SexpParser::new(filename, input),
            expanded: Vec::new().into_iter(),
        };
        Ok(self.process_program_internal(source, true)?.outputs)
    }

    /// Parse through the single accounting boundary shared by source, include,
    /// and generated term-encoding text.
    pub(crate) fn parse_program_timed(
        &mut self,
        filename: Option<String>,
        input: &str,
    ) -> Result<Vec<Command>, Error> {
        let parse_timer = Instant::now();
        let parsed = self.parser.get_program_from_string(filename, input);
        self.overall_report.frontend_parse += parse_timer.elapsed();
        Ok(parsed?)
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
        &self.overall_report.run
    }

    pub(crate) fn timing_summary(&self) -> Result<TimingSummary, TimingSummaryError> {
        TimingSummary::from_report(&self.overall_report)
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
        self.with_execution_state(|state| {
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

    /// The total number of rows across all non-hidden functions, including
    /// global `let` bindings.
    pub fn total_size(&self) -> usize {
        self.functions
            .values()
            .filter(|f| !f.is_hidden())
            .map(|f| self.backend.table_size(f.backend_id))
            .sum()
    }

    /// The number of e-nodes in the e-graph: the total number of rows across
    /// visible constructor tables for unionable eq-sorts, including their
    /// term/proof-encoding views. Analysis functions, global lets, hidden
    /// helpers, and `relation`s are excluded.
    pub fn num_nodes(&self) -> usize {
        self.functions
            .values()
            .filter(|f| {
                !f.is_hidden()
                    && !f.is_let_binding()
                    && f.rows_are_enodes()
                    && self.type_info.is_sort_unionable(f.extraction_layout().0)
            })
            .map(|f| self.backend.table_size(f.backend_id))
            .sum()
    }

    /// Get a function by name.
    ///
    /// Returns `None` if the function does not exist.
    pub fn get_function(&self, name: &str) -> Option<&Function> {
        self.functions.get(name)
    }

    /// Returns the typed child values stored inside a container-sort value.
    ///
    /// `sort` must be a container sort and `value` must belong to that sort.
    pub fn container_inner_values(&self, sort: &ArcSort, value: Value) -> Vec<(ArcSort, Value)> {
        sort.inner_values(self.backend.container_values(), value)
    }

    /// Reconstructs a base-sort value into a [`TermDag`].
    ///
    /// `sort` must be a base sort and `value` must belong to that sort in this
    /// e-graph.
    pub fn reconstruct_base_value(
        &self,
        sort: &ArcSort,
        value: Value,
        termdag: &mut TermDag,
    ) -> TermId {
        sort.reconstruct_termdag_base(self.backend.base_values(), value, termdag)
    }

    /// Reconstructs a container-sort value from its extracted element terms.
    ///
    /// `sort` and `value` must identify a container in this e-graph, and
    /// `element_terms` must correspond to [`EGraph::container_inner_values`] in
    /// the same order.
    pub fn reconstruct_container_value(
        &self,
        sort: &ArcSort,
        value: Value,
        termdag: &mut TermDag,
        element_terms: Vec<TermId>,
    ) -> TermId {
        sort.reconstruct_termdag_container(
            self.backend.container_values(),
            value,
            termdag,
            element_terms,
        )
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
    ///    costs no more than a direct table scan.
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
        let registry = self.backend.action_registry().clone();
        let guard = registry.read();
        let (result, changed) =
            self.with_execution_state_tracked(|es| f(FullState::wrap(es, &guard, Context::Full)));
        drop(guard);
        // A read-only closure stages nothing, so `flush_updates` would only do
        // a no-op merge plus a spurious timestamp bump and rebuild check. Skip
        // it unless the closure actually wrote, keeping reads as cheap as a
        // direct table scan.
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
            let rule_ids = match &self.rulesets[&ruleset].kind {
                RulesetKind::Rules(rules) => rules
                    .values()
                    .map(|rule| rule.backend_id)
                    .collect::<Vec<_>>(),
                RulesetKind::Combined(_) => unreachable!("the query ruleset was created directly"),
            };
            let iteration_report = self
                .backend
                .run_rules(&rule_ids, Some(&self.type_info))
                .map_err(|e| Error::BackendError(e.to_string()))?;
            self.overall_report.commands_check += iteration_report.total_time();
            Ok(())
        })();

        // Tear the temporary rule + ruleset down whether the body
        // succeeded or not.
        if let Some(Ruleset {
            kind: RulesetKind::Rules(rules),
            ..
        }) = self.rulesets.swap_remove(&ruleset)
        {
            for (_, rule) in rules {
                self.backend.free_rule(rule.backend_id);
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
#[allow(clippy::too_many_arguments)]
fn resolve_function_container_target_with_context(
    backend: &egglog_bridge::EGraph,
    functions: &IndexMap<String, Function>,
    type_info: &TypeInfo,
    name: &str,
    primitive: &core::SpecializedPrimitive,
    panic_id: ExternalFunctionId,
    ctx: crate::Context,
    span: &Span,
) -> Result<ResolvedFunction, Error> {
    let Some(target_function) = type_info
        .get_sorts::<FunctionSort>()
        .into_iter()
        .find(|function| function.name() == primitive.output().name())
    else {
        return Err(Error::BackendError(format!(
            "`unstable-fn` output sort `{}` is not a function sort",
            primitive.output().name()
        )));
    };

    let partial_arcsorts: Vec<_> = primitive.input().iter().skip(1).cloned().collect();
    let remaining_inputs = target_function.inputs();
    let output = target_function.output();

    let id = if let Some(func) = functions.get(name) {
        let func_type = type_info.get_func_type(name).ok_or_else(|| {
            Error::BackendError(format!(
                "`unstable-fn` references `{name}`, which has no resolved type"
            ))
        })?;
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
                "`unstable-fn` reference `{name}` expected ({}) -> {}, found ({}) -> {}",
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
        let mut ambiguous_ctx = None;
        let context_ids = enum_map::EnumMap::from_fn(|runtime_ctx| {
            let mut ids = candidates
                .iter()
                .filter_map(|primitive| primitive.context_ids[runtime_ctx]);
            // The first `next` finds the candidate for this runtime context;
            // the second detects whether there is more than one such candidate.
            match (ids.next(), ids.next()) {
                (None, _) => None,
                (Some(id), None) => Some(id),
                (Some(_), Some(_)) => {
                    ambiguous_ctx = Some(runtime_ctx);
                    None
                }
            }
        });
        if let Some(runtime_ctx) = ambiguous_ctx {
            return Err(TypeError::AmbiguousPrimitive {
                name: name.to_owned(),
                ctx: runtime_ctx,
                span: span.clone(),
            }
            .into());
        }
        if !context_ids.iter().any(|(_, id)| id.is_some()) {
            return Err(TypeError::UnresolvedPrimitive {
                name: name.to_owned(),
                ctx,
                span: span.clone(),
            }
            .into());
        }
        ResolvedFunctionId::Primitive { context_ids }
    } else {
        return Err(TypeError::UnresolvedPrimitive {
            name: name.to_owned(),
            ctx,
            span: span.clone(),
        }
        .into());
    };

    Ok(ResolvedFunction {
        id,
        partial_arcsorts,
        name: name.to_owned(),
        panic_id,
    })
}

struct RuleTranslator<'a> {
    builder: egglog_bridge::RuleBuilder<'a>,
    entries: HashMap<core::ResolvedAtomTerm, QueryEntry>,
    functions: &'a IndexMap<String, Function>,
    type_info: &'a TypeInfo,
    /// Whether primitives may read the database. When true the per-phase
    /// [`crate::Context`] widens from `Pure`/`Write` to `Read`/`Full` (query
    /// gains reads, action gains reads on top of writes). True for `:naive` /
    /// `:unsafe-seminaive` rules and a non-seminaive EGraph.
    requires_read_context: bool,
}

impl<'a> RuleTranslator<'a> {
    fn new(
        builder: egglog_bridge::RuleBuilder<'a>,
        functions: &'a IndexMap<String, Function>,
        type_info: &'a TypeInfo,
        requires_read_context: bool,
    ) -> RuleTranslator<'a> {
        RuleTranslator {
            builder,
            functions,
            type_info,
            requires_read_context,
            entries: Default::default(),
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

    fn entry(&mut self, term: &core::ResolvedAtomTerm) -> Result<QueryEntry, Error> {
        if let Some(entry) = self.entries.get(term) {
            return Ok(entry.clone());
        }
        let entry = match term {
            core::GenericAtomTerm::Var(_, variable) => self.builder.new_var_named(
                variable.sort.column_ty(self.builder.egraph()),
                &variable.name,
            ),
            core::GenericAtomTerm::Literal(_, literal) => {
                literal_to_entry(self.builder.egraph(), literal)
            }
            core::GenericAtomTerm::Global(span, variable) => {
                return Err(Error::BackendError(format!(
                    "{span}: global `{}` was not desugared before rule lowering",
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
    ) -> Result<(ExternalFunctionId, Vec<QueryEntry>, ColumnTy), Error> {
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
            // Pre-register a panic id used by `FunctionContainer::apply`
            // when the wrapped function is applied in a context that
            // doesn't admit it. Triggered at runtime via the egglog
            // panic side channel so misuse surfaces as an `Err` from
            // `run_rules` rather than a thread unwind.
            let panic_id = self.builder.new_panic(format!(
                "unstable-fn over `{name}` was applied in a context where its wrapped \
                 function is not valid for this call site, if in a rule, add :naive."
            ));
            let resolved = resolve_function_container_target_with_context(
                self.builder.egraph(),
                self.functions,
                self.type_info,
                name,
                prim,
                panic_id,
                ctx,
                args[0].span(),
            )?;
            rule_args[0] = self.builder.egraph().base_value_constant(resolved);
        }

        let output_ty = prim.output().column_ty(self.builder.egraph());
        Ok((resolved_id, rule_args, output_ty))
    }

    fn args<'b>(
        &mut self,
        args: impl IntoIterator<Item = &'b core::ResolvedAtomTerm>,
    ) -> Result<Vec<QueryEntry>, Error> {
        args.into_iter().map(|term| self.entry(term)).collect()
    }

    /// An index atom is probed, never scanned, so the value it is looked up by
    /// must be bound elsewhere in the query. A literal needs no binder.
    fn check_index_value_is_bound(
        &self,
        index: &crate::typechecking::FuncType,
        atom: &core::GenericAtom<ResolvedCall, ResolvedVar>,
        query: &core::Query<ResolvedCall, ResolvedVar>,
    ) -> Result<(), Error> {
        let Some(core::GenericAtomTerm::Var(span, value)) = atom.args.first() else {
            return Ok(());
        };
        // The value may sit at a column of this very atom, which both binds it and
        // makes the occurrence redundant — the atom is then an ordinary one.
        if atom
            .args
            .iter()
            .skip(1)
            .any(|arg| matches!(arg, core::GenericAtomTerm::Var(_, v) if v.name == value.name))
        {
            return Ok(());
        }
        let bound_elsewhere =
            query.atoms.iter().any(|other| {
                if std::ptr::eq(other, atom) {
                    return false;
                }
                // Only a function's rows bind a value the join can probe by. A body
                // primitive runs once per match, after the join, so the value it
                // computes is not available as a lookup key.
                let ResolvedCall::Func(f) = &other.head else {
                    return false;
                };
                // Another index atom binds through its row columns like any other
                // atom, but not through the value it is itself probed by: two index
                // atoms naming each other there would each look bound with neither
                // reachable.
                let probed = self.type_info.indexes.contains_key(&f.name);
                other.args.iter().skip(usize::from(probed)).any(
                    |arg| matches!(arg, core::GenericAtomTerm::Var(_, v) if v.name == value.name),
                )
            });
        if bound_elsewhere {
            return Ok(());
        }
        Err(
            TypeError::IndexValueUnbound(index.name.clone(), value.name.clone(), span.clone())
                .into(),
        )
    }

    fn query(
        &mut self,
        query: &core::Query<ResolvedCall, ResolvedVar>,
        include_subsumed: bool,
    ) -> Result<(), Error> {
        for atom in &query.atoms {
            let is_subsumed = if include_subsumed { None } else { Some(false) };
            match &atom.head {
                // An atom on a declared index reads the rows of the indexed
                // function, reached through the value its first argument binds.
                ResolvedCall::Func(f) if self.type_info.indexes.contains_key(&f.name) => {
                    self.check_index_value_is_bound(f, atom, query)?;
                    let index = self.type_info.indexes[&f.name].clone();
                    let indexed = self
                        .type_info
                        .get_func_type(&index.function)
                        .expect("index target checked at declaration")
                        .clone();
                    let entries = self.args(&atom.args)?;
                    let (indexed_value, rest) = entries
                        .split_first()
                        .expect("an index atom binds a value and a row");
                    let (_unit, row) = rest
                        .split_last()
                        .expect("an index atom carries the relation's unit output");
                    self.builder
                        .query_table_by_occurrence(
                            self.func(&indexed),
                            row,
                            indexed_value.clone(),
                            &index.any_of,
                            is_subsumed,
                        )
                        .map_err(|error| Error::BackendError(error.to_string()))?;
                }
                ResolvedCall::Func(f) => {
                    let id = self.func(f);
                    let entries = self.args(&atom.args)?;
                    self.builder
                        .query_table(id, &entries, is_subsumed)
                        .map_err(|error| Error::BackendError(error.to_string()))?;
                }
                ResolvedCall::Primitive(p) => {
                    let ctx = self.query_context();
                    let (id, entries, output) = self.prim(p, &atom.args, ctx)?;
                    self.builder
                        .query_prim(id, &entries, output)
                        .map_err(|error| Error::BackendError(error.to_string()))?;
                }
                ResolvedCall::Values(_) => {
                    unreachable!("`values` is lowered to the underlying function atom before query")
                }
            }
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
                    let value: QueryEntry = match f {
                        ResolvedCall::Func(f) => {
                            let id = self.func(f);
                            let name = f.name.clone();
                            let args = self.args(args)?;
                            let span = span.clone();
                            self.builder
                                .lookup(id, &args, move || {
                                    format!("{span}: lookup of function {name} failed")
                                })
                                .into()
                        }
                        ResolvedCall::Primitive(p) => {
                            let ctx = self.action_context();
                            let (id, args, output) = self.prim(p, args, ctx)?;
                            let name = p.name().to_owned();
                            let span = span.clone();
                            self.builder
                                .call_external_func(id, &args, output, move || {
                                    format!("{span}: call of primitive {name} failed")
                                })
                                .into()
                        }
                        ResolvedCall::Values(_) => {
                            panic!("`values` cannot be bound as a single value")
                        }
                    };
                    self.entries
                        .insert(core::GenericAtomTerm::Var(span.clone(), v.clone()), value);
                }
                core::GenericCoreAction::LetAtomTerm(span, v, x) => {
                    let value = self.entry(x)?;
                    self.entries
                        .insert(core::GenericAtomTerm::Var(span.clone(), v.clone()), value);
                }
                core::GenericCoreAction::Set(_span, f, xs, ys) => match f {
                    ResolvedCall::Primitive(..) => {
                        return Err(Error::BackendError("cannot set a primitive".into()));
                    }
                    ResolvedCall::Values(..) => {
                        return Err(Error::BackendError(
                            "`values` is not a settable function".into(),
                        ));
                    }
                    ResolvedCall::Func(f) => {
                        let id = self.func(f);
                        let entries = self.args(xs.iter().chain(ys))?;
                        self.builder.set(id, &entries);
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
                        let id = self.func(f);
                        let arguments = self.args(args)?;
                        match change {
                            Change::Delete => self.builder.remove(id, &arguments),
                            Change::Subsume => self.builder.subsume(id, &arguments),
                        }
                    }
                },
                core::GenericCoreAction::Union(_span, x, y) => {
                    let x = self.entry(x)?;
                    let y = self.entry(y)?;
                    self.builder.union(x, y);
                }
                core::GenericCoreAction::Panic(_span, message) => {
                    self.builder.panic(message.clone());
                }
            }
        }
        Ok(())
    }

    fn query_table(
        &mut self,
        table: egglog_bridge::FunctionId,
        entries: &[QueryEntry],
        is_subsumed: Option<bool>,
    ) -> Result<(), Error> {
        self.builder
            .query_table(table, entries, is_subsumed)
            .map(|_| ())
            .map_err(|error| Error::BackendError(error.to_string()))
    }

    fn call_external_func(
        &mut self,
        id: ExternalFunctionId,
        name: &str,
        arguments: &[QueryEntry],
        output: ColumnTy,
    ) -> QueryEntry {
        self.builder
            .call_external_func(id, arguments, output, {
                let name = name.to_owned();
                move || format!("call of primitive {name} failed")
            })
            .into()
    }

    fn remove(&mut self, table: egglog_bridge::FunctionId, arguments: &[QueryEntry]) {
        self.builder.remove(table, arguments);
    }

    fn build(mut self, no_decomp: bool) -> egglog_bridge::RuleId {
        self.builder.set_no_decomp(no_decomp);
        self.builder.build()
    }
}

fn literal_to_entry(egraph: &egglog_bridge::EGraph, l: &Literal) -> QueryEntry {
    match l {
        Literal::Int(x) => egraph.base_value_constant::<i64>(*x),
        Literal::Float(x) => egraph.base_value_constant::<sort::F>(x.into()),
        Literal::String(x) => egraph.base_value_constant::<sort::S>(sort::S::new(x.clone())),
        Literal::Bool(x) => egraph.base_value_constant::<bool>(*x),
        Literal::Unit => egraph.base_value_constant::<()>(()),
    }
}

fn literal_to_value(egraph: &egglog_bridge::EGraph, l: &Literal) -> Value {
    match l {
        Literal::Int(x) => egraph.base_values().get::<i64>(*x),
        Literal::Float(x) => egraph.base_values().get::<sort::F>(x.into()),
        Literal::String(x) => egraph.base_values().get::<sort::S>(sort::S::new(x.clone())),
        Literal::Bool(x) => egraph.base_values().get::<bool>(*x),
        Literal::Unit => egraph.base_values().get::<()>(()),
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
    #[error("{1}\nCombined ruleset {0} mixes program and equality-maintenance rulesets")]
    MixedRulesetResponsibilities(String, Span),
    #[error(
        "{1}\nAttempted to add a rule to combined ruleset {0}. Combined rulesets may only depend on other rulesets."
    )]
    CombinedRulesetError(String, Span),
    #[error("{0}")]
    BackendError(String),
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
    #[error("{1}\nRule already exists: {0}")]
    RuleAlreadyExists(String, Span),
    #[error("{1}\nUnsupported type {0} for input")]
    UnsupportedInputType(String, Span),
    #[error("{0}\n{1}")]
    DesugarError(Span, String),
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

    // Force the ordinary route by preserving each singleton's action boundary
    // but giving it block origin. Other commands, including push/pop, are intact.
    fn run_ground_action_oracle(
        graph: &mut EGraph,
        source: &str,
        direct: bool,
    ) -> Result<Vec<String>, Error> {
        if direct {
            return graph
                .parse_and_run_program(None, source)
                .map(|outputs| outputs.iter().map(ToString::to_string).collect());
        }
        let mut outputs = Vec::new();
        for command in graph.parse_program(None, source)? {
            for command in graph.resolve_command(command)?.desugared {
                let command = match command {
                    ResolvedNCommand::CoreAction(action) if !direct => {
                        ResolvedNCommand::CoreActions(ResolvedActions::singleton(action))
                    }
                    command => command,
                };
                outputs.extend(graph.run_command(command)?.iter().map(ToString::to_string));
            }
        }
        Ok(outputs)
    }

    fn assert_action_graphs_equal(left: &EGraph, right: &EGraph) {
        assert_eq!(
            left.functions.keys().collect::<Vec<_>>(),
            right.functions.keys().collect::<Vec<_>>()
        );
        for (name, function) in &left.functions {
            let mut left_rows = Vec::new();
            left.backend.for_each(function.backend_id, |row| {
                left_rows.push((row.vals.to_vec(), row.subsumed))
            });
            let mut right_rows = Vec::new();
            right
                .backend
                .for_each(right.functions[name].backend_id, |row| {
                    right_rows.push((row.vals.to_vec(), row.subsumed))
                });
            left_rows.sort();
            right_rows.sort();
            assert_eq!(left_rows, right_rows, "{name}");
        }
    }

    #[test]
    fn ground_actions_match_compiled_execution() {
        for threads in [1, 4] {
            let mut direct = EGraph::default();
            let mut compiled = EGraph::default();
            for graph in [&mut direct, &mut compiled] {
                graph.backend.set_num_threads(threads);
                graph
                    .parse_and_run_program(
                        None,
                        "(datatype T (A) (B) (N1) (N2) (Pair T T) (Num i64))
                     (relation seen (T))
                     (function missing (T) T :no-merge)
                     (function tuple-result (T) (T T) :merge (values old0 old1))
                     (index Occ missing (any 0 1))
                     (let $global (A))",
                    )
                    .unwrap();
            }
            for (source, succeeds) in [
                ("(Pair (N1) (Pair (N1) (N2)))", true),
                ("(seen (Pair (A) (A)))", true),
                ("(union (A) (A))", true),
                ("(Pair (B) (B))", true),
                ("(union (A) (B))", true),
                ("(union (A) (B))", true),
                ("(check (= (Pair (A) (A)) (Pair (B) (B))))", true),
                ("(push)", true),
                ("(constructor Temporary () T) (Temporary)", true),
                ("(pop)", true),
                ("(Temporary)", false),
                ("(Num (+ 1 2))", true),
                ("(Pair $global (N1))", true),
                ("(begin (Pair (N2) (N2)))", true),
                ("(begin (let local (N2)) (Pair local local))", true),
                ("(missing (Pair (N2) (A)))", false),
                ("(set (missing (N1)) (N2))", true),
                ("(delete (missing (N1)))", true),
                ("(tuple-result (A))", false),
                ("(Occ (A) (A) (B))", false),
                ("(Pair (A) unbound)", false),
                ("(Pair (A))", false),
            ] {
                let actual = run_ground_action_oracle(&mut direct, source, true);
                let expected = run_ground_action_oracle(&mut compiled, source, false);
                assert_eq!(actual.is_ok(), succeeds, "{source}: {actual:?}");
                assert_eq!(expected.is_ok(), succeeds, "{source}: {expected:?}");
                if let (Ok(actual), Ok(expected)) = (actual, expected) {
                    assert_eq!(actual, expected, "{source}");
                }
                assert_action_graphs_equal(&direct, &compiled);
            }
        }
    }

    #[test]
    fn ground_actions_check_eligibility_before_mutation() {
        for mode in 0..3 {
            let mut graph = match mode {
                0 => EGraph::default(),
                1 => EGraph::new_with_term_encoding(),
                _ => EGraph::new_with_proofs(),
            };
            graph
                .parse_and_run_program(
                    None,
                    "(datatype T (A) (N1) (N2) (Pair T T) (Num i64))
                     (let $global (A))",
                )
                .unwrap();
            if mode == 0 {
                graph
                    .parse_and_run_program(
                        None,
                        "(function custom (T) T :no-merge)
                     (index Occ custom (any 0 1))",
                    )
                    .unwrap();
            }
            for (source, admitted) in [
                ("(Pair (N1) (N2))", true),
                ("(Pair (N1) (missing))", false),
                ("(union (N1) (+ 1 2))", false),
                ("(union (A) (Pair (A) (A)))", true),
                ("(Num 1)", false),
                ("(+ 1 2)", false),
                ("(custom (A))", false),
                ("(Pair $global (A))", false),
                ("(set (custom (A)) (N1))", false),
                ("(delete (custom (A)))", false),
                ("(begin (A))", false),
            ] {
                if mode != 0 && !admitted {
                    continue;
                }
                let before = graph.clone();
                let commands = graph.parse_program(None, source).unwrap();
                let accepted = commands.iter().any(|command| match command {
                    Command::Action(action) => graph
                        .prepare_ground_action(
                            typechecking::ClosedAction::from_action(action),
                            &mut GroundActionCache::default(),
                            |_| true,
                        )
                        .is_some(),
                    _ => false,
                });
                assert_eq!(accepted, admitted && mode == 0, "mode {mode}: {source}");
                let form = SexpParser::new(None, source)
                    .next_sexp(|_, range| range)
                    .unwrap()
                    .unwrap();
                assert_eq!(
                    graph
                        .prepare_source_action(&form, &mut GroundActionCache::default())
                        .is_some(),
                    accepted,
                    "source plan mode {mode}: {source}"
                );
                assert_action_graphs_equal(&graph, &before);
                assert!(!graph.backend.flush_updates());
            }
        }
    }

    #[test]
    fn source_actions_share_checked_plans_with_ast_execution() {
        struct Identity;
        impl CommandMacro for Identity {
            fn preserves_closed_constructor_action(&self, _: Option<&str>) -> bool {
                true
            }

            fn transform(
                &self,
                command: Command,
                _: &mut SymbolGen,
                _: &TypeInfo,
            ) -> Result<Vec<Command>, Error> {
                Ok(vec![command])
            }
        }
        let mut source_graph = EGraph::default();
        source_graph
            .parse_and_run_program(
                None,
                "(datatype T (N1) (N2) (N3) (N4) (N5) (f T T) (g T) (h T T T))
                 (relation seen (T))
                 (rule ((= x (f a b))) ((seen x)))",
            )
            .unwrap();
        source_graph.command_macros.register(Arc::new(Identity));
        let source = "(f (N1) (N2))
                      (union (N1) (g (N3)))
                      (union (f (N1) (N2)) (h (N3) (N4) (N5)))
                      (union (N3) (N4))";
        let mut parser = SexpParser::new(None, source);
        let mut calls = GroundActionCache::default();
        while let Some(form) = parser.next_sexp(|_, range| range).unwrap() {
            assert!(
                source_graph
                    .prepare_source_action(&form, &mut calls)
                    .is_some()
            );
        }
        let mut ast_graph = source_graph.clone();
        let commands = ast_graph.parse_program(None, source).unwrap();
        source_graph.parse_and_run_program(None, source).unwrap();
        ast_graph.run_program(commands).unwrap();
        for graph in [&mut source_graph, &mut ast_graph] {
            graph
                .parse_and_run_program(
                    None,
                    "(run 1)
                     (check (seen (h (N4) (N4) (N5))))
                     (check (= (f (g (N4)) (N2)) (h (N3) (N4) (N5))))",
                )
                .unwrap();
        }
        assert_action_graphs_equal(&source_graph, &ast_graph);
    }

    #[test]
    fn source_actions_respect_parser_override_precedence() {
        let mut initial = EGraph::default();
        initial
            .parse_and_run_program(None, "(datatype T (A) (B) (F T))")
            .unwrap();
        for kind in ["expression", "action", "command"] {
            let mut graph = initial.clone();
            match kind {
                "expression" => graph
                    .parser
                    .add_expr_macro(Arc::new(SimpleMacro::new("A", |_, span, _| {
                        Ok(Expr::Call(span, "B".into(), vec![]))
                    }))),
                "action" => {
                    graph
                        .parser
                        .add_action_macro(Arc::new(SimpleMacro::new("A", |_, span, _| {
                            Ok(vec![Action::Expr(
                                span.clone(),
                                Expr::Call(span, "B".into(), vec![]),
                            )])
                        })))
                }
                _ => {
                    graph
                        .parser
                        .add_command_macro(Arc::new(SimpleMacro::new("A", |_, span, _| {
                            Ok(vec![Command::Action(Action::Expr(
                                span.clone(),
                                Expr::Call(span, "B".into(), vec![]),
                            ))])
                        })))
                }
            }
            for (text, admitted) in [("(A)", false), ("(F (A))", kind != "expression")] {
                let form = SexpParser::new(None, text)
                    .next_sexp(|_, range| range)
                    .unwrap()
                    .unwrap();
                assert_eq!(
                    graph
                        .prepare_source_action(&form, &mut GroundActionCache::default())
                        .is_some(),
                    admitted,
                    "{kind}: {text}"
                );
            }
            let mut ordinary = graph.clone();
            let source = "(A) (F (A))";
            let commands = ordinary.parse_program(None, source).unwrap();
            graph.parse_and_run_program(None, source).unwrap();
            ordinary.run_program(commands).unwrap();
            assert_action_graphs_equal(&graph, &ordinary);
            assert_eq!(graph.get_size("B"), 1);
            assert_eq!(graph.get_size("A"), usize::from(kind != "expression"));
        }
    }

    #[test]
    fn source_actions_recheck_parser_overrides_after_empty_or_ground_expansion() {
        for emit_action in [false, true] {
            let mut graph = EGraph::default();
            graph
                .parse_and_run_program(None, "(datatype T (A) (B) (F T))")
                .unwrap();
            graph.parser.add_command_macro(Arc::new(SimpleMacro::new(
                "install",
                move |_, span, parser| {
                    parser.add_expr_macro(Arc::new(SimpleMacro::new("A", |_, span, _| {
                        Ok(Expr::Call(span, "B".into(), vec![]))
                    })));
                    Ok(if emit_action {
                        vec![Command::Action(Action::Expr(
                            span.clone(),
                            Expr::Call(
                                span.clone(),
                                "F".into(),
                                vec![Expr::Call(span, "A".into(), vec![])],
                            ),
                        ))]
                    } else {
                        vec![]
                    })
                },
            )));
            let mut ordinary = graph.clone();
            let source = "(F (A)) (install) (F (A))";
            let commands = ordinary.parse_program(None, source).unwrap();
            graph.parse_and_run_program(None, source).unwrap();
            ordinary.run_program(commands).unwrap();
            assert_action_graphs_equal(&graph, &ordinary);
            assert_eq!(graph.get_size("F"), 2);
            assert_eq!(graph.get_size("A"), 1);
            assert_eq!(graph.get_size("B"), 1);
        }
    }

    #[test]
    fn source_actions_require_command_macro_opt_in_and_keep_error_prefix() {
        struct RejectA;
        impl CommandMacro for RejectA {
            fn transform(
                &self,
                command: Command,
                _: &mut SymbolGen,
                _: &TypeInfo,
            ) -> Result<Vec<Command>, Error> {
                if matches!(&command, Command::Action(Action::Expr(_, Expr::Call(_, head, _))) if head == "A")
                {
                    Err(Error::BackendError("A rejected by macro".into()))
                } else {
                    Ok(vec![command])
                }
            }
        }
        let mut graph = EGraph::default();
        graph
            .parse_and_run_program(None, "(datatype T (A) (B) (F T))")
            .unwrap();
        graph.command_macros.register(Arc::new(RejectA));
        let form = SexpParser::new(None, "(F (B))")
            .next_sexp(|_, range| range)
            .unwrap()
            .unwrap();
        assert!(
            graph
                .prepare_source_action(&form, &mut GroundActionCache::default())
                .is_none()
        );
        let mut ordinary = graph.clone();
        let source = "(F (B)) (A)";
        let commands = ordinary.parse_program(None, source).unwrap();
        let source_error = graph.parse_and_run_program(None, source).unwrap_err();
        let ast_error = ordinary.run_program(commands).unwrap_err();
        assert_eq!(source_error.to_string(), ast_error.to_string());
        assert_action_graphs_equal(&graph, &ordinary);
        assert_eq!(graph.get_size("F"), 1);
        assert_eq!(graph.get_size("A"), 0);
    }

    #[test]
    fn ground_action_cache_keeps_call_validation_and_command_scope() {
        let mut initial = EGraph::default();
        initial
            .parse_and_run_program(None, "(datatype T (A) (F T)) (datatype U (B))")
            .unwrap();
        for source in ["(F (A)) (F (A) (A))", "(F (A)) (F (B))"] {
            let mut graph = initial.clone();
            assert!(graph.parse_and_run_program(None, source).is_err());
            assert_eq!(graph.get_size("F"), 1);
            assert_eq!(graph.get_size("B"), 0);
        }

        let mut graph = initial;
        assert!(
            graph
                .parse_and_run_program(
                    None,
                    "(push) (constructor Temporary () T) (Temporary) (pop) (Temporary)",
                )
                .is_err()
        );
        assert!(!graph.functions.contains_key("Temporary"));
        graph
            .parse_and_run_program(
                None,
                "
            (push)
            (constructor Reused () T)
            (Reused)
            (pop)
            (constructor Padding () T)
            (constructor Reused () T)
            (Reused)
            (check (= (Reused) (Reused)))
        ",
            )
            .unwrap();
        assert_eq!(graph.get_size("Padding"), 0);
        assert_eq!(graph.get_size("Reused"), 1);
    }

    #[test]
    fn ground_actions_batch_restores_congruence_and_rule_visibility() {
        for threads in [1, 4] {
            let mut graph = EGraph::default();
            graph.backend.set_num_threads(threads);
            graph
                .parse_and_run_program(
                    None,
                    "
                (datatype T (A) (B) (F T) (G T))
                (relation seen (T))
                (rule ((= x (G (F (A))))) ((seen x)))
                ",
                )
                .unwrap();
            assert!(graph.backend.can_batch_actions());
            graph
                .parse_and_run_program(
                    None,
                    &format!(
                        "
                (G (F (A)))
                (union (A) (B))
                (G (F (B)))
                {}
                (check (= (G (F (A))) (G (F (B)))))
                (run 1)
                (check (seen (G (F (B)))))
            ",
                        "(G (F (B)))\n".repeat(2_050)
                    ),
                )
                .unwrap();
            assert_eq!(graph.get_size("F"), 1);
            assert_eq!(graph.get_size("G"), 1);
        }
    }

    #[test]
    fn ground_actions_batch_flushes_before_errors_and_rollback() {
        let mut graph = EGraph::default();
        graph
            .parse_and_run_program(None, "(datatype T (A) (B) (F T))")
            .unwrap();
        assert!(
            graph
                .parse_and_run_program(None, "(F (A)) (missing)")
                .is_err()
        );
        assert_eq!(graph.get_size("F"), 1);
        graph
            .parse_and_run_program(
                None,
                "
            (push)
            (union (A) (B))
            (check (= (A) (B)))
            (pop)
            (fail (check (= (A) (B))))
            (fail (union (A) (B)) (panic \"expected\"))
            (fail (check (= (A) (B))))
        ",
            )
            .unwrap();
    }

    #[test]
    fn ground_actions_batch_flushes_before_macro_errors() {
        struct RejectCheck;
        impl CommandMacro for RejectCheck {
            fn transform(
                &self,
                command: Command,
                _: &mut SymbolGen,
                _: &TypeInfo,
            ) -> Result<Vec<Command>, Error> {
                if matches!(command, Command::Check(..)) {
                    Err(Error::BackendError("expected macro error".into()))
                } else {
                    Ok(vec![command])
                }
            }
        }
        let mut graph = EGraph::default();
        graph
            .parse_and_run_program(None, "(datatype T (A) (F T))")
            .unwrap();
        graph.command_macros.register(Arc::new(RejectCheck));
        assert!(
            graph
                .parse_and_run_program(None, "(F (A)) (check (= (A) (A)))")
                .is_err()
        );
        assert_eq!(graph.get_size("F"), 1);
    }

    #[test]
    fn ground_actions_batch_keeps_failing_merge_boundary() {
        let mut graph = EGraph::default();
        graph
            .parse_and_run_program(
                None,
                "
            (datatype T (A) (B) (C))
            (function value (T) i64 :no-merge)
            (set (value (A)) 0)
            (set (value (B)) 1)
        ",
            )
            .unwrap();
        assert!(!graph.backend.can_batch_actions());
        assert!(
            graph
                .parse_and_run_program(None, "(union (A) (B)) (C)")
                .is_err()
        );
        assert_eq!(graph.get_size("C"), 0);
    }

    #[test]
    fn ground_actions_batch_preserves_subsumed_rows() {
        for direct in [true, false] {
            let mut graph = EGraph::default();
            run_ground_action_oracle(
                &mut graph,
                "
                (datatype T (A) (B) (F T))
                (F (A))
                (subsume (F (A)))
                (union (A) (B))
                (F (B))
            ",
                direct,
            )
            .unwrap();
            let mut rows = Vec::new();
            graph
                .backend
                .for_each(graph.functions["F"].backend_id, |row| {
                    rows.push(row.subsumed);
                });
            assert_eq!(rows, vec![true]);
        }
    }

    #[test]
    fn ground_actions_keep_numeric_constructor_names_distinct() {
        let source = "(datatype T (A) (A1))
                      (begin (A) (A) (A) (A) (A))
                      (union (A) (A1))
                      (check (= (A) (A1)))";
        for direct in [true, false] {
            run_ground_action_oracle(&mut EGraph::default(), source, direct).unwrap();
        }
    }

    #[test]
    fn execution_drops_resolved_commands_but_keeps_proof_history() {
        let source = "(datatype T (A) (B)) (union (A) (B)) (check (= (A) (B)))";
        for proofs in [false, true] {
            let mut graph = EGraph::default();
            if proofs {
                graph = graph.with_proofs_enabled().with_proof_testing();
            }
            let program = graph.parse_program(None, source).unwrap();
            let result = graph
                .process_program_internal(ProgramSource::Commands(program.into_iter()), true)
                .unwrap();
            assert!(result.resolved.is_empty());
            assert!(result.resolved_before_proofs.is_empty());
            assert_eq!(!graph.proof_check_program.is_empty(), proofs);

            // Resolution still returns both representations for desugaring and
            // the proof checker, without registering execution history.
            let mut graph = EGraph::default();
            if proofs {
                graph = graph.with_proofs_enabled();
            }
            let program = graph.parse_program(None, source).unwrap();
            let result = graph
                .process_program_internal(ProgramSource::Commands(program.into_iter()), false)
                .unwrap();
            assert!(!result.resolved.is_empty());
            assert_eq!(!result.resolved_before_proofs.is_empty(), proofs);
            assert!(graph.proof_check_program.is_empty());
        }
    }

    #[test]
    fn encoded_source_typecheck_is_charged_to_the_outer_egraph() {
        let mut egraph = EGraph::new_with_term_encoding();

        egraph
            .parse_and_run_program(None, "(datatype Math (Num i64)) (let value (Num 1))")
            .unwrap();

        assert!(egraph.overall_report.frontend_parse > std::time::Duration::ZERO);
        assert!(egraph.overall_report.typecheck > std::time::Duration::ZERO);
        assert!(egraph.overall_report.frontend_other > std::time::Duration::ZERO);
        let source_checker = egraph.proof_state.original_typechecking.as_ref().unwrap();
        assert_eq!(
            source_checker.overall_report.typecheck,
            std::time::Duration::ZERO,
            "the child checker must not retain time omitted from the outer summary"
        );
    }

    #[test]
    fn query_is_recorded_as_command_work_without_persistent_ruleset_rows() {
        let mut egraph = EGraph::default();
        egraph
            .parse_and_run_program(None, "(relation R (i64)) (R 1) (R 2)")
            .unwrap();
        let iterations_before = egraph.overall_report.run.iterations.len();
        let check_time_before = egraph.overall_report.commands_check;

        for _ in 0..2 {
            let matches = egraph
                .query(crate::vars![x: i64], crate::facts![(R x)])
                .unwrap();
            assert_eq!(matches.len(), 2);
        }

        assert_eq!(
            egraph.overall_report.run.iterations.len(),
            iterations_before
        );
        assert!(egraph.overall_report.commands_check > check_time_before);
        assert!(
            egraph
                .timing_summary()
                .unwrap()
                .rulesets
                .iter()
                .all(|ruleset| !ruleset.name.contains("query_ruleset"))
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
    fn proof_support_adds_no_fail_specific_term_read_restrictions() {
        for source in [
            "(datatype N (A)) (let $a (A)) (fail (extract $a -1))",
            "(datatype N (A)) (relation R (N)) (let $a (A)) \
             (R $a) (fail (delete (R $a)) (panic \"stop\"))",
        ] {
            let mut egraph = EGraph::default();
            let resolved = egraph.resolve_program(None, source).unwrap();
            assert!(
                program_supports_proofs(&resolved, &egraph.type_info),
                "{source}"
            );
        }

        let source = "(datatype N (A)) (let $a (A)) \
                      (fail (output \"term.txt\" $a) (panic \"stop\"))";
        let mut egraph = EGraph::default();
        let resolved = egraph.resolve_program(None, source).unwrap();
        assert!(!program_supports_proofs(&resolved, &egraph.type_info));
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

    #[test]
    fn test_combined_ruleset_with_undefined_member_errors() {
        let err = EGraph::default()
            .parse_and_run_program(None, "(unstable-combined-ruleset combined missing)")
            .unwrap_err();
        assert!(matches!(err, Error::NoSuchRuleset(name, _) if name == "missing"));
    }

    #[test]
    fn test_rule_rejects_combined_and_unbound_rulesets() {
        let mut egraph = EGraph::default();
        egraph
            .parse_and_run_program(
                None,
                "(relation number (i64)) (ruleset base) \
                 (unstable-combined-ruleset rules1and2 base)",
            )
            .unwrap();

        let err = egraph
            .parse_and_run_program(None, "(rule () ((number 1)) :ruleset rules1and2)")
            .unwrap_err();
        assert!(matches!(err, Error::CombinedRulesetError(name, _) if name == "rules1and2"));

        let err = egraph
            .parse_and_run_program(None, "(rule () ((number 2)) :ruleset unboundruleset)")
            .unwrap_err();
        assert!(matches!(err, Error::NoSuchRuleset(name, _) if name == "unboundruleset"));
    }

    #[test]
    fn test_combined_ruleset_with_mixed_responsibilities_errors() {
        let mut egraph = EGraph::default();
        let maintenance = egraph
            .proof_state
            .proof_names
            .rebuilding_ruleset_name
            .clone();
        egraph.add_ruleset("program".into());
        egraph.add_ruleset(maintenance.clone());

        let err = egraph
            .add_combined_ruleset(
                &span!(),
                "mixed".into(),
                vec!["program".into(), maintenance],
            )
            .unwrap_err();

        assert!(matches!(err, Error::MixedRulesetResponsibilities(name, _) if name == "mixed"));
    }

    #[test]
    fn test_duplicate_rule_name_errors() {
        let err = EGraph::default()
            .parse_and_run_program(
                None,
                "(relation foo (i64))
                 (rule ((foo x)) ((foo (+ x 1))) :name \"r\")
                 (rule ((foo x)) ((foo (+ x 2))) :name \"r\")",
            )
            .unwrap_err();
        assert!(matches!(err, Error::RuleAlreadyExists(..)));
    }

    #[test]
    fn test_extract_negative_variants_errors() {
        let err = EGraph::default()
            .parse_and_run_program(
                None,
                "(sort Math)(constructor Num (i64) Math)(let x (Num 5))(extract x -1)",
            )
            .unwrap_err();
        assert!(matches!(err, Error::ExtractError(..)));
    }

    #[test]
    fn test_input_missing_file_errors() {
        let err = EGraph::default()
            .parse_and_run_program(
                None,
                "(function edge (i64) i64 :merge old)(input edge \"/no/such/file_xyz\")",
            )
            .unwrap_err();
        assert!(matches!(err, Error::IoError(..)));
    }

    /// Regression test: `SymbolGen::fresh` minted colliding names for
    /// different hints (e.g. hint "x" at count 11 and hint "x1" at count 1
    /// both produce "@x11"). Two distinct globals sharing one minted name
    /// were then conflated while compiling an action, silently binding a
    /// global to the wrong term.
    #[test]
    fn test_fresh_name_collision_globals() {
        let mut egraph = EGraph::default();
        // Each `(or2 x y)` command consumes one `fresh("x")`. After the ten
        // `t` commands (plus the definition of `x` itself), the minted name
        // for a fresh "x" is "@x11". Global `x1` has only been minted once
        // (by its own definition), so minting for it also produces "@x11".
        // The final command references both globals, conflating them.
        egraph
            .parse_and_run_program(
                None,
                r#"
                (sort B)
                (constructor var (String) B)
                (constructor and2 (B B) B)
                (constructor or2 (B B) B)
                (let x (var "x"))
                (let y (var "y"))
                (let t1 (or2 x y))
                (let t2 (or2 x y))
                (let t3 (or2 x y))
                (let t4 (or2 x y))
                (let t5 (or2 x y))
                (let t6 (or2 x y))
                (let t7 (or2 x y))
                (let t8 (or2 x y))
                (let t9 (or2 x y))
                (let t10 (or2 x y))
                (let x1 (var "x1"))
                (let out (and2 x x1))
                "#,
            )
            .unwrap();

        // `out` must equal the term it was bound to. With the name
        // collision, the last action was miscompiled as
        // `(set (out) (and2 (x1) (x1)))`, so this check failed.
        egraph
            .parse_and_run_program(
                None,
                r#"
                (check (= out (and2 (var "x") x1)))
                "#,
            )
            .unwrap();
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
}

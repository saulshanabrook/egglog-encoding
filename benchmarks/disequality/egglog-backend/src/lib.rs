use egglog_experimental::{
    CommandOutput, DisequalityEncoding, EGraph, Error as EgglogError,
    ast::{Action, Actions, Command, Expr, Literal, Merge, Schema, sanitize_internal_names},
    check_disequalities_command, check_known_disequal_command, disequal_action,
    new_experimental_egraph_with_disequality_encoding,
};
use std::{
    collections::{HashMap, HashSet},
    ffi::{CStr, CString, c_char},
    fmt::Write as _,
    panic::{AssertUnwindSafe, catch_unwind},
    ptr,
    rc::Rc,
    slice,
    sync::{Arc, Mutex},
};
use thiserror::Error;

const GENERIC_LANGUAGE_NOTE: &str =
    "; Generic host language used by the disequality case studies.\n";

pub type TermId = u64;
pub type OperatorId = u32;

const RESERVED_IDENTIFIERS: &[&str] = &[
    "begin",
    "birewrite",
    "check",
    "constructor",
    "datatype",
    "datatype*",
    "delete",
    "extract",
    "fail",
    "function",
    "include",
    "input",
    "let",
    "output",
    "panic",
    "pop",
    "print-function",
    "print-size",
    "print-stats",
    "prove",
    "prove-exists",
    "push",
    "relation",
    "repeat",
    "rewrite",
    "rule",
    "ruleset",
    "run",
    "run-schedule",
    "saturate",
    "seq",
    "set",
    "sort",
    "subsume",
    "union",
    "unstable-combined-ruleset",
    "values",
];

const BUILTIN_SORT_IDENTIFIERS: &[&str] = &[
    "Unit", "String", "bool", "i64", "f64", "BigInt", "BigRat", "Map", "Set", "Vec", "Function",
    "MultiSet",
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TermLanguage {
    Vec,
    Direct,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OperatorSpec {
    pub source_name: String,
    pub preferred_name: Option<String>,
    pub arity: usize,
}

#[derive(Clone, Debug)]
pub struct LanguageSchemaBuilder {
    sort_name: String,
    operators: Vec<OperatorSpec>,
    operator_ids: HashMap<(String, usize), OperatorId>,
}

impl LanguageSchemaBuilder {
    pub fn new(sort_name: impl Into<String>) -> Self {
        Self {
            sort_name: sort_name.into(),
            operators: Vec::new(),
            operator_ids: HashMap::new(),
        }
    }

    pub fn register_operator(
        &mut self,
        source_name: impl Into<String>,
        preferred_name: Option<String>,
        arity: usize,
    ) -> Result<OperatorId, BackendError> {
        let source_name = source_name.into();
        if let Some(&id) = self.operator_ids.get(&(source_name.clone(), arity)) {
            let existing = &self.operators[id as usize];
            if existing.preferred_name != preferred_name {
                return Err(BackendError::Other(format!(
                    "operator {source_name:?}/{arity} was registered with conflicting preferred names"
                )));
            }
            return Ok(id);
        }
        let id = OperatorId::try_from(self.operators.len())
            .map_err(|_| BackendError::Other("too many registered operators".to_owned()))?;
        self.operators.push(OperatorSpec {
            source_name: source_name.clone(),
            preferred_name,
            arity,
        });
        self.operator_ids.insert((source_name, arity), id);
        Ok(id)
    }

    pub fn compile(
        self,
        encoding: DisequalityEncoding,
    ) -> Result<DisequalityGraphTemplate, BackendError> {
        DisequalityGraphTemplate::direct(encoding, self)
    }
}

#[derive(Clone, Debug)]
struct DirectOperator {
    source_name: String,
    egglog_name: String,
    arity: usize,
}

#[derive(Clone, Debug)]
struct DirectLanguage {
    source_notes: String,
    sort_name: String,
    atom_name: String,
    lookup_name: String,
    operators: Vec<DirectOperator>,
}

#[derive(Clone, Debug)]
enum HostLanguage {
    Vec,
    Direct(DirectLanguage),
}

impl HostLanguage {
    fn source_notes(&self) -> &str {
        match self {
            HostLanguage::Vec => GENERIC_LANGUAGE_NOTE,
            HostLanguage::Direct(language) => &language.source_notes,
        }
    }

    fn lookup_name(&self) -> &str {
        match self {
            HostLanguage::Vec => "BenchmarkTermAt",
            HostLanguage::Direct(language) => &language.lookup_name,
        }
    }

    fn declaration_commands(&self) -> Vec<Command> {
        match self {
            HostLanguage::Vec => language_declarations(
                "BenchmarkTerm",
                Some(("BenchmarkTerms", "Vec")),
                "BenchmarkTermAt",
                &[("BenchmarkNode", vec!["String", "BenchmarkTerms"])],
            ),
            HostLanguage::Direct(language) => {
                let mut constructors = Vec::with_capacity(language.operators.len() + 1);
                constructors.push((language.atom_name.as_str(), vec!["String"]));
                constructors.extend(language.operators.iter().map(|operator| {
                    (
                        operator.egglog_name.as_str(),
                        vec![language.sort_name.as_str(); operator.arity],
                    )
                }));
                language_declarations(
                    &language.sort_name,
                    None,
                    &language.lookup_name,
                    &constructors,
                )
            }
        }
    }
}

fn language_declarations(
    sort_name: &str,
    container_sort: Option<(&str, &str)>,
    lookup_name: &str,
    constructors: &[(&str, Vec<&str>)],
) -> Vec<Command> {
    let span = egglog_experimental::span!();
    let mut commands = vec![Command::Sort {
        span: span.clone(),
        name: sort_name.to_owned(),
        presort_and_args: None,
        uf: None,
        container_rebuild: None,
        proof_constructors: None,
        unionable: true,
    }];
    if let Some((container_name, presort)) = container_sort {
        commands.push(Command::Sort {
            span: span.clone(),
            name: container_name.to_owned(),
            presort_and_args: Some((
                presort.to_owned(),
                vec![Expr::Var(span.clone(), sort_name.to_owned())],
            )),
            uf: None,
            container_rebuild: None,
            proof_constructors: None,
            unionable: true,
        });
    }
    commands.extend(
        constructors
            .iter()
            .map(|(name, inputs)| Command::Constructor {
                span: span.clone(),
                name: (*name).to_owned(),
                schema: Schema::new(
                    inputs.iter().map(|input| (*input).to_owned()).collect(),
                    sort_name.to_owned(),
                ),
                cost: None,
                unextractable: false,
                hidden: false,
                let_binding: false,
            }),
    );
    commands.push(Command::Function {
        span: span.clone(),
        name: lookup_name.to_owned(),
        schema: Schema::new(vec!["i64".to_owned()], sort_name.to_owned()),
        merge: Some(Merge::result_only(Expr::Var(span, "old".to_owned()))),
        hidden: false,
        let_binding: false,
        internal_view: None,
        unextractable: false,
        identity_vals: None,
        cost: None,
        term_node: false,
    });
    commands
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GraphStats {
    pub nodes: usize,
    pub classes: usize,
    pub extension_rows: usize,
    pub total_tuples: usize,
}

#[derive(Debug, Error)]
pub enum BackendError {
    #[error(transparent)]
    Egglog(#[from] EgglogError),
    #[error("term handle {0} does not exist")]
    UnknownTerm(TermId),
    #[error("invalid UTF-8 in {0}")]
    InvalidUtf8(&'static str),
    #[error("null {0} pointer")]
    NullPointer(&'static str),
    #[error("interaction recording was not enabled for this graph")]
    RecordingDisabled,
    #[error(transparent)]
    Io(#[from] std::io::Error),
    #[error("{0}")]
    Other(String),
}

/// Structured outcome of one [`EGraph::run_program`] call.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CommandStatus {
    /// The command completed and returned the accompanying outputs.
    Success,
    /// An expected `check` command returned [`EgglogError::CheckError`].
    CheckFailed,
    /// An expected `fail` command returned [`EgglogError::ExpectFail`].
    ExpectFailFailed,
}

/// A command status and every [`CommandOutput`] returned by egglog.
#[derive(Clone, Debug)]
pub struct CommandResult {
    pub status: CommandStatus,
    pub outputs: Vec<CommandOutput>,
}

#[derive(Clone, Debug)]
enum RecordedOutcome {
    Success(Vec<CommandOutput>),
    CheckFailed,
    ExpectFailFailed,
}

#[derive(Clone, Debug)]
enum TraceEvent {
    PendingActions(Command),
    Execution {
        command: Command,
        outcome: RecordedOutcome,
        rendered_action_prefix: usize,
    },
    Rebuild,
    Stats,
    Clone,
}

#[derive(Clone, Debug, Default)]
struct Trace {
    tail: Option<Rc<TraceChunk>>,
}

#[derive(Debug)]
struct TraceChunk {
    previous: Option<Rc<TraceChunk>>,
    event: TraceEvent,
}

impl Trace {
    fn push(&mut self, event: TraceEvent) {
        self.tail = Some(Rc::new(TraceChunk {
            previous: self.tail.take(),
            event,
        }));
    }

    fn events(&self) -> Vec<&TraceEvent> {
        let mut events = Vec::new();
        let mut current = self.tail.as_deref();
        while let Some(chunk) = current {
            events.push(&chunk.event);
            current = chunk.previous.as_deref();
        }
        events.reverse();
        events
    }
}

fn compile_direct_language(
    schema: LanguageSchemaBuilder,
    egraph: &mut EGraph,
) -> Result<DirectLanguage, BackendError> {
    let reserved_names = egraph
        .get_function_names()
        .into_iter()
        .chain(
            BUILTIN_SORT_IDENTIFIERS
                .iter()
                .map(|name| (*name).to_owned()),
        )
        .collect::<HashSet<_>>();
    let mut arities_by_source = HashMap::<&str, HashSet<usize>>::new();
    for operator in &schema.operators {
        arities_by_source
            .entry(&operator.source_name)
            .or_default()
            .insert(operator.arity);
    }

    let mut candidates = schema
        .operators
        .iter()
        .enumerate()
        .map(|(index, operator)| {
            let overloaded = arities_by_source[operator.source_name.as_str()].len() > 1;
            let requested = operator
                .preferred_name
                .as_deref()
                .unwrap_or(&operator.source_name);
            let primitive = egraph.type_info().is_primitive(requested);
            let base = sanitized_identifier(requested, &reserved_names, primitive);
            let candidate = if overloaded {
                format!("{base}{}", operator.arity)
            } else {
                base
            };
            let is_verbatim = !overloaded
                && operator.preferred_name.is_none()
                && candidate == operator.source_name;
            (index, candidate, is_verbatim)
        })
        .collect::<Vec<_>>();
    candidates.sort_by_key(|(index, _, is_verbatim)| (!*is_verbatim, *index));

    let mut used_names = reserved_names;
    let mut allocated = vec![String::new(); schema.operators.len()];
    for (index, candidate, _) in candidates {
        allocated[index] = unique_name(candidate, &mut used_names, egraph);
    }

    let sort_is_primitive = egraph.type_info().is_primitive(&schema.sort_name);
    let requested_sort = sanitized_identifier(&schema.sort_name, &used_names, sort_is_primitive);
    let sort_name = unique_name(requested_sort, &mut used_names, egraph);
    let atom_name = unique_name(
        if used_names.contains("Atom") {
            "HostAtom".to_owned()
        } else {
            "Atom".to_owned()
        },
        &mut used_names,
        egraph,
    );
    let lookup_name = unique_name("HostTermAt".to_owned(), &mut used_names, egraph);

    let operators = schema
        .operators
        .into_iter()
        .zip(allocated)
        .map(|(operator, egglog_name)| DirectOperator {
            source_name: operator.source_name,
            egglog_name,
            arity: operator.arity,
        })
        .collect::<Vec<_>>();

    let mut source_notes =
        String::from("; Direct host language generated from source declarations.\n");
    if sort_name != schema.sort_name {
        writeln!(
            source_notes,
            "; source sort {}",
            serde_json::to_string(&schema.sort_name)
                .map_err(|error| BackendError::Other(error.to_string()))?
        )
        .expect("writing to a String cannot fail");
    }
    for operator in &operators {
        if operator.egglog_name != operator.source_name {
            writeln!(
                source_notes,
                "; source operator {}/{}",
                serde_json::to_string(&operator.source_name)
                    .map_err(|error| BackendError::Other(error.to_string()))?,
                operator.arity
            )
            .expect("writing to a String cannot fail");
        }
    }
    Ok(DirectLanguage {
        source_notes,
        sort_name,
        atom_name,
        lookup_name,
        operators,
    })
}

fn sanitized_identifier(name: &str, reserved_names: &HashSet<String>, primitive: bool) -> String {
    let valid = !name.is_empty()
        && !name.starts_with(['@', ':'])
        && !RESERVED_IDENTIFIERS.contains(&name)
        && !reserved_names.contains(name)
        && !primitive
        && !matches!(name, "_" | "true" | "false")
        && name.parse::<i64>().is_err()
        && name.parse::<f64>().is_err()
        && !name.chars().any(|character| {
            character.is_whitespace() || matches!(character, '(' | ')' | '"' | ';')
        });
    if valid {
        return name.to_owned();
    }

    let mut escaped = String::new();
    for character in name.chars() {
        if character.is_alphanumeric()
            || matches!(
                character,
                '_' | '-' | '.' | '+' | '*' | '/' | '?' | '!' | '<' | '>' | '='
            )
        {
            escaped.push(character);
        } else if !escaped.ends_with('_') {
            escaped.push('_');
        }
    }
    let escaped = escaped.trim_matches('_');
    let escaped = if escaped.is_empty() {
        "Symbol"
    } else {
        escaped
    };
    format!("Escaped_{escaped}")
}

fn unique_name(candidate: String, used_names: &mut HashSet<String>, egraph: &mut EGraph) -> String {
    if !egraph.type_info().is_primitive(&candidate) && used_names.insert(candidate.clone()) {
        return candidate;
    }
    for suffix in 2.. {
        let candidate_with_suffix = format!("{candidate}_{suffix}");
        if !egraph.type_info().is_primitive(&candidate_with_suffix)
            && used_names.insert(candidate_with_suffix.clone())
        {
            return candidate_with_suffix;
        }
    }
    unreachable!("an unbounded numeric suffix must eventually be unique")
}

pub struct DisequalityGraphTemplate {
    encoding: DisequalityEncoding,
    language: Arc<HostLanguage>,
    egraph: EGraph,
    // Cloned EGraphs are logically isolated but retain shared internal state.
    execution_lock: Arc<Mutex<()>>,
}

impl DisequalityGraphTemplate {
    pub fn generic(encoding: DisequalityEncoding) -> Result<Self, BackendError> {
        Self::compile(encoding, HostLanguage::Vec)
    }

    fn direct(
        encoding: DisequalityEncoding,
        schema: LanguageSchemaBuilder,
    ) -> Result<Self, BackendError> {
        let mut egraph = new_experimental_egraph_with_disequality_encoding(encoding);
        let language = HostLanguage::Direct(compile_direct_language(schema, &mut egraph)?);
        Self::compile_with_egraph(encoding, language, egraph)
    }

    fn compile(
        encoding: DisequalityEncoding,
        language: HostLanguage,
    ) -> Result<Self, BackendError> {
        let egraph = new_experimental_egraph_with_disequality_encoding(encoding);
        Self::compile_with_egraph(encoding, language, egraph)
    }

    fn compile_with_egraph(
        encoding: DisequalityEncoding,
        language: HostLanguage,
        mut egraph: EGraph,
    ) -> Result<Self, BackendError> {
        egraph.run_program(language.declaration_commands())?;
        Ok(Self {
            encoding,
            language: Arc::new(language),
            egraph,
            execution_lock: Arc::new(Mutex::new(())),
        })
    }

    pub fn new_graph(&self) -> DisequalityGraph {
        self.new_graph_with_recording(false)
    }

    /// Clone the compiled template and record subsequent host interactions for
    /// executable source export.
    pub fn new_recording_graph(&self) -> DisequalityGraph {
        self.new_graph_with_recording(true)
    }

    fn new_graph_with_recording(&self, record_interactions: bool) -> DisequalityGraph {
        let execution_lock = Arc::clone(&self.execution_lock);
        let _guard = execution_lock
            .lock()
            .expect("template execution lock was poisoned");
        DisequalityGraph {
            encoding: self.encoding,
            language: Arc::clone(&self.language),
            egraph: self.egraph.clone(),
            execution_lock: Arc::clone(&self.execution_lock),
            next_term: 0,
            pending: Vec::new(),
            pending_first_term: None,
            recorded_pending_prefix: 0,
            trace: record_interactions.then(Trace::default),
        }
    }
}

pub struct DisequalityGraph {
    encoding: DisequalityEncoding,
    language: Arc<HostLanguage>,
    egraph: EGraph,
    execution_lock: Arc<Mutex<()>>,
    next_term: TermId,
    pending: Vec<Action>,
    pending_first_term: Option<TermId>,
    recorded_pending_prefix: usize,
    trace: Option<Trace>,
}

impl Clone for DisequalityGraph {
    fn clone(&self) -> Self {
        let execution_lock = Arc::clone(&self.execution_lock);
        let _guard = execution_lock
            .lock()
            .expect("graph execution lock was poisoned");
        let mut trace = self.trace.clone();
        let mut recorded_pending_prefix = self.recorded_pending_prefix;
        if let Some(trace) = &mut trace {
            if recorded_pending_prefix < self.pending.len() {
                trace.push(TraceEvent::PendingActions(Command::Actions(Actions::new(
                    self.pending[recorded_pending_prefix..].to_vec(),
                ))));
                recorded_pending_prefix = self.pending.len();
            }
            trace.push(TraceEvent::Clone);
        }
        Self {
            encoding: self.encoding,
            language: Arc::clone(&self.language),
            egraph: self.egraph.clone(),
            execution_lock: Arc::clone(&self.execution_lock),
            next_term: self.next_term,
            pending: self.pending.clone(),
            pending_first_term: self.pending_first_term,
            recorded_pending_prefix,
            trace,
        }
    }
}

impl DisequalityGraph {
    pub fn new(encoding: DisequalityEncoding) -> Result<Self, BackendError> {
        Self::new_with_recording(encoding, false)
    }

    /// Create a generic graph that records host interactions for executable
    /// source export. Normal benchmark runs should use [`Self::new`].
    pub fn new_recording(encoding: DisequalityEncoding) -> Result<Self, BackendError> {
        Self::new_with_recording(encoding, true)
    }

    fn new_with_recording(
        encoding: DisequalityEncoding,
        record_interactions: bool,
    ) -> Result<Self, BackendError> {
        let mut egraph = new_experimental_egraph_with_disequality_encoding(encoding);
        let language = Arc::new(HostLanguage::Vec);
        egraph.run_program(language.declaration_commands())?;
        Ok(Self {
            encoding,
            language,
            egraph,
            execution_lock: Arc::new(Mutex::new(())),
            next_term: 0,
            pending: Vec::new(),
            pending_first_term: None,
            recorded_pending_prefix: 0,
            trace: record_interactions.then(Trace::default),
        })
    }

    pub fn add(
        &mut self,
        operator: impl Into<String>,
        children: &[TermId],
    ) -> Result<TermId, BackendError> {
        if !matches!(&*self.language, HostLanguage::Vec) {
            return Err(BackendError::Other(
                "generic add is only available for the Vec term language".to_owned(),
            ));
        }
        for &child in children {
            self.validate_term(child)?;
        }
        let span = egglog_experimental::span!();
        let children = children
            .iter()
            .map(|&child| self.pending_term_expr(child))
            .collect::<Result<Vec<_>, _>>()?;
        self.queue_term(Expr::Call(
            span.clone(),
            "BenchmarkNode".to_owned(),
            vec![
                Expr::Lit(span.clone(), Literal::String(operator.into())),
                Expr::Call(span, "vec-of".to_owned(), children),
            ],
        ))
    }

    pub fn add_atom(&mut self, name: impl Into<String>) -> Result<TermId, BackendError> {
        if !matches!(&*self.language, HostLanguage::Direct(_)) {
            return Err(BackendError::Other(
                "atom insertion requires the direct term language".to_owned(),
            ));
        }
        let HostLanguage::Direct(language) = &*self.language else {
            unreachable!("the direct-language guard above must hold")
        };
        let span = egglog_experimental::span!();
        self.queue_term(Expr::Call(
            span.clone(),
            language.atom_name.clone(),
            vec![Expr::Lit(span, Literal::String(name.into()))],
        ))
    }

    pub fn add_registered(
        &mut self,
        operator: OperatorId,
        children: &[TermId],
    ) -> Result<TermId, BackendError> {
        for &child in children {
            self.validate_term(child)?;
        }
        let HostLanguage::Direct(language) = &*self.language else {
            return Err(BackendError::Other(
                "registered insertion requires the direct term language".to_owned(),
            ));
        };
        let declaration = language
            .operators
            .get(operator as usize)
            .ok_or_else(|| BackendError::Other(format!("unknown operator id {operator}")))?;
        if declaration.arity != children.len() {
            return Err(BackendError::Other(format!(
                "operator {:?} expects {} children, received {}",
                declaration.source_name,
                declaration.arity,
                children.len()
            )));
        }
        let operator_name = declaration.egglog_name.clone();
        let children = children
            .iter()
            .map(|&child| self.pending_term_expr(child))
            .collect::<Result<Vec<_>, _>>()?;
        self.queue_term(Expr::Call(
            egglog_experimental::span!(),
            operator_name,
            children,
        ))
    }

    pub fn union(&mut self, lhs: TermId, rhs: TermId) -> Result<(), BackendError> {
        self.validate_pair(lhs, rhs)?;
        self.pending.push(Action::Union(
            egglog_experimental::span!(),
            self.pending_term_expr(lhs)?,
            self.pending_term_expr(rhs)?,
        ));
        Ok(())
    }

    pub fn disequal(&mut self, lhs: TermId, rhs: TermId) -> Result<(), BackendError> {
        self.validate_pair(lhs, rhs)?;
        self.pending.push(disequal_action(
            self.pending_term_expr(lhs)?,
            self.pending_term_expr(rhs)?,
        ));
        Ok(())
    }

    pub fn rebuild(&mut self) -> Result<CommandResult, BackendError> {
        let execution_lock = Arc::clone(&self.execution_lock);
        let _guard = execution_lock
            .lock()
            .expect("graph execution lock was poisoned");
        let result = self.flush_unlocked()?;
        if let Some(trace) = &mut self.trace {
            trace.push(TraceEvent::Rebuild);
        }
        Ok(result)
    }

    pub fn flush(&mut self) -> Result<CommandResult, BackendError> {
        let execution_lock = Arc::clone(&self.execution_lock);
        let _guard = execution_lock
            .lock()
            .expect("graph execution lock was poisoned");
        self.flush_unlocked()
    }

    pub fn check_equal(&mut self, lhs: TermId, rhs: TermId) -> Result<CommandResult, BackendError> {
        self.validate_pair(lhs, rhs)?;
        let span = egglog_experimental::span!();
        self.run_query(
            Command::Check(
                span.clone(),
                vec![egglog_experimental::ast::Fact::Eq(
                    span,
                    self.term_expr(lhs)?,
                    self.term_expr(rhs)?,
                )],
            ),
            CommandStatus::CheckFailed,
        )
    }

    pub fn check_known_disequal(
        &mut self,
        lhs: TermId,
        rhs: TermId,
    ) -> Result<CommandResult, BackendError> {
        self.validate_pair(lhs, rhs)?;
        self.run_query(
            check_known_disequal_command(self.term_expr(lhs)?, self.term_expr(rhs)?),
            CommandStatus::ExpectFailFailed,
        )
    }

    /// Run disequality propagation under `fail`.
    ///
    /// [`CommandStatus::Success`] means propagation found a contradiction;
    /// [`CommandStatus::ExpectFailFailed`] means the graph is consistent.
    pub fn check_consistency(&mut self) -> Result<CommandResult, BackendError> {
        let execution_lock = Arc::clone(&self.execution_lock);
        let _guard = execution_lock
            .lock()
            .expect("graph execution lock was poisoned");
        self.flush_unlocked()?;
        let command = if self
            .egraph
            .get_sort_by_name("@disequality-support")
            .is_some()
        {
            Command::Fail(
                egglog_experimental::span!(),
                vec![check_disequalities_command()],
            )
        } else {
            let span = egglog_experimental::span!();
            Command::Fail(
                span.clone(),
                vec![Command::Check(
                    span.clone(),
                    vec![egglog_experimental::ast::Fact::Eq(
                        span.clone(),
                        Expr::Lit(span.clone(), Literal::Int(0)),
                        Expr::Lit(span, Literal::Int(0)),
                    )],
                )],
            )
        };
        self.execute_command_unlocked(command, Some(CommandStatus::ExpectFailFailed), 0)
    }

    fn run_query(
        &mut self,
        command: Command,
        expected_failure: CommandStatus,
    ) -> Result<CommandResult, BackendError> {
        let execution_lock = Arc::clone(&self.execution_lock);
        let _guard = execution_lock
            .lock()
            .expect("graph execution lock was poisoned");
        self.flush_unlocked()?;
        self.execute_command_unlocked(command, Some(expected_failure), 0)
    }

    pub fn stats(&mut self) -> Result<GraphStats, BackendError> {
        let execution_lock = Arc::clone(&self.execution_lock);
        let _guard = execution_lock
            .lock()
            .expect("graph execution lock was poisoned");
        self.flush_unlocked()?;
        let mut classes = HashSet::new();
        for id in 0..self.next_term {
            let expression = self.term_expr(id)?;
            let (sort, value) = self.egraph.eval_expr(&expression)?;
            classes.insert(self.egraph.value_to_class_id(&sort, value));
        }
        let extension_rows = self
            .egraph
            .get_function_names()
            .into_iter()
            .filter(|name| name.starts_with("@disequality"))
            .map(|name| self.egraph.get_size(&name))
            .sum();
        let nodes = match &*self.language {
            HostLanguage::Vec => self.egraph.get_size("BenchmarkNode"),
            HostLanguage::Direct(language) => {
                self.egraph.get_size(&language.atom_name)
                    + language
                        .operators
                        .iter()
                        .map(|operator| self.egraph.get_size(&operator.egglog_name))
                        .sum::<usize>()
            }
        };
        let stats = GraphStats {
            nodes,
            classes: classes.len(),
            extension_rows,
            total_tuples: self.egraph.num_tuples(),
        };
        if let Some(trace) = &mut self.trace {
            trace.push(TraceEvent::Stats);
        }
        Ok(stats)
    }

    /// Render the recorded host interaction sequence as executable egglog.
    ///
    /// Returns [`BackendError::RecordingDisabled`] unless this graph was
    /// created through a recording constructor.
    pub fn source(&mut self) -> Result<String, BackendError> {
        if self.trace.is_none() {
            return Err(BackendError::RecordingDisabled);
        }
        let execution_lock = Arc::clone(&self.execution_lock);
        let _guard = execution_lock
            .lock()
            .expect("graph execution lock was poisoned");
        self.flush_unlocked()?;
        let mut source = self.language.source_notes().to_owned();
        for command in self
            .language
            .declaration_commands()
            .into_iter()
            .filter(|command| {
                !matches!(command, Command::Function { name, .. } if name == self.language.lookup_name())
            })
        {
            writeln!(source, "{command}").expect("writing to a String cannot fail");
        }
        source.push('\n');
        source.push_str(&render_trace(
            self.trace.as_ref().expect("recording was checked above"),
            &self.language,
        ));
        Ok(source)
    }

    /// Render the recorded source after applying the selected compiler pass.
    pub fn desugared_source(&mut self) -> Result<String, BackendError> {
        let source = self.source()?;
        desugar_source(self.encoding, &source)
    }

    fn validate_term(&self, id: TermId) -> Result<(), BackendError> {
        if id < self.next_term {
            Ok(())
        } else {
            Err(BackendError::UnknownTerm(id))
        }
    }

    fn allocate_term(&mut self) -> Result<TermId, BackendError> {
        let id = self.next_term;
        i64::try_from(id)
            .map_err(|_| BackendError::Other(format!("term handle {id} exceeds egglog i64")))?;
        self.next_term = self
            .next_term
            .checked_add(1)
            .ok_or_else(|| BackendError::Other("term handle space exhausted".to_owned()))?;
        Ok(id)
    }

    fn queue_term(&mut self, expression: Expr) -> Result<TermId, BackendError> {
        let id = self.allocate_term()?;
        self.pending_first_term.get_or_insert(id);
        let span = egglog_experimental::span!();
        let binding = format!("term{id}");
        self.pending
            .push(Action::Let(span.clone(), binding.clone(), expression));
        self.pending.push(Action::Set(
            span.clone(),
            self.language.lookup_name().to_owned(),
            vec![term_id_expr(id)?],
            Expr::Var(span, binding),
        ));
        Ok(id)
    }

    fn validate_pair(&self, lhs: TermId, rhs: TermId) -> Result<(), BackendError> {
        self.validate_term(lhs)?;
        self.validate_term(rhs)
    }

    fn term_expr(&self, id: TermId) -> Result<Expr, BackendError> {
        lookup_expr(&self.language, id)
    }

    fn pending_term_expr(&self, id: TermId) -> Result<Expr, BackendError> {
        if self.pending_first_term.is_some_and(|first| id >= first) {
            Ok(Expr::Var(egglog_experimental::span!(), format!("term{id}")))
        } else {
            self.term_expr(id)
        }
    }

    fn flush_unlocked(&mut self) -> Result<CommandResult, BackendError> {
        if self.pending.is_empty() {
            return Ok(CommandResult {
                status: CommandStatus::Success,
                outputs: Vec::new(),
            });
        }

        let batch = Command::Actions(Actions::new(self.pending.clone()));
        let result = self.execute_command_unlocked(batch, None, self.recorded_pending_prefix)?;
        self.pending.clear();
        self.pending_first_term = None;
        self.recorded_pending_prefix = 0;
        Ok(result)
    }

    fn execute_command_unlocked(
        &mut self,
        command: Command,
        expected_failure: Option<CommandStatus>,
        rendered_action_prefix: usize,
    ) -> Result<CommandResult, BackendError> {
        let execution = self.egraph.run_program(vec![command.clone()]);
        let (result, recorded) = match execution {
            Ok(outputs) => {
                let recorded = RecordedOutcome::Success(outputs.clone());
                (
                    CommandResult {
                        status: CommandStatus::Success,
                        outputs,
                    },
                    recorded,
                )
            }
            Err(EgglogError::CheckError(..))
                if expected_failure == Some(CommandStatus::CheckFailed) =>
            {
                (
                    CommandResult {
                        status: CommandStatus::CheckFailed,
                        outputs: Vec::new(),
                    },
                    RecordedOutcome::CheckFailed,
                )
            }
            Err(EgglogError::ExpectFail(..))
                if expected_failure == Some(CommandStatus::ExpectFailFailed) =>
            {
                (
                    CommandResult {
                        status: CommandStatus::ExpectFailFailed,
                        outputs: Vec::new(),
                    },
                    RecordedOutcome::ExpectFailFailed,
                )
            }
            Err(error) => return Err(error.into()),
        };
        if let Some(trace) = &mut self.trace {
            trace.push(TraceEvent::Execution {
                command,
                outcome: recorded,
                rendered_action_prefix,
            });
        }
        Ok(result)
    }
}

pub fn desugar_source(encoding: DisequalityEncoding, source: &str) -> Result<String, BackendError> {
    let mut compiler = new_experimental_egraph_with_disequality_encoding(encoding);
    let commands = compiler.resolve_program(Some("benchmark-source.egg".to_owned()), source)?;
    Ok(sanitize_internal_names(&commands)
        .into_iter()
        .map(|command| command.to_string() + "\n")
        .collect())
}

fn lookup_expr(language: &HostLanguage, id: TermId) -> Result<Expr, BackendError> {
    let id = i64::try_from(id)
        .map_err(|_| BackendError::Other(format!("term handle {id} exceeds egglog i64")))?;
    let span = egglog_experimental::span!();
    Ok(Expr::Call(
        span.clone(),
        language.lookup_name().to_owned(),
        vec![Expr::Lit(span, Literal::Int(id))],
    ))
}

fn term_id_expr(id: TermId) -> Result<Expr, BackendError> {
    let id = i64::try_from(id)
        .map_err(|_| BackendError::Other(format!("term handle {id} exceeds egglog i64")))?;
    Ok(Expr::Lit(egglog_experimental::span!(), Literal::Int(id)))
}

fn source_expr(language: &HostLanguage, expression: Expr) -> Expr {
    match expression {
        Expr::Call(span, head, arguments)
            if head == language.lookup_name()
                && matches!(arguments.as_slice(), [Expr::Lit(_, Literal::Int(_))]) =>
        {
            let [Expr::Lit(_, Literal::Int(id))] = arguments.as_slice() else {
                unreachable!("the match guard fixes the lookup shape")
            };
            Expr::Var(span, format!("$term{id}"))
        }
        Expr::Var(span, name)
            if name
                .strip_prefix("term")
                .is_some_and(|suffix| suffix.parse::<TermId>().is_ok()) =>
        {
            Expr::Var(span, format!("${name}"))
        }
        Expr::Call(span, head, arguments) if head == "@disequal" => {
            Expr::Call(span, "disequal".to_owned(), arguments)
        }
        expression => expression,
    }
}

fn source_action(language: &HostLanguage, action: Action) -> Option<Action> {
    if matches!(&action, Action::Set(_, head, _, _) if head == language.lookup_name()) {
        return None;
    }
    let Command::Action(action) =
        Command::Action(action).visit_exprs(&mut |expression| source_expr(language, expression))
    else {
        unreachable!("visiting an action command preserves its command variant")
    };
    Some(match action {
        Action::Let(span, name, expression)
            if name
                .strip_prefix("term")
                .is_some_and(|suffix| suffix.parse::<TermId>().is_ok()) =>
        {
            Action::Let(span, format!("${name}"), expression)
        }
        action => action,
    })
}

fn source_command(language: &HostLanguage, command: &Command) -> Command {
    let projected = command
        .clone()
        .visit_exprs(&mut |expression| source_expr(language, expression));
    match &projected {
        Command::Check(span, facts)
            if matches!(
                facts.as_slice(),
                [egglog_experimental::ast::Fact::Fact(Expr::Call(_, head, args))]
                    if head == "@check-known-disequal" && args.len() == 2
            ) =>
        {
            let [egglog_experimental::ast::Fact::Fact(Expr::Call(_, _, args))] = facts.as_slice()
            else {
                unreachable!("the match guard fixes the query shape")
            };
            Command::UserDefined(
                span.clone(),
                "check-known-disequal".to_owned(),
                args.clone(),
            )
        }
        Command::RunSchedule(_) => Command::UserDefined(
            egglog_experimental::span!(),
            "check-disequalities".to_owned(),
            Vec::new(),
        ),
        Command::Fail(span, commands) => Command::Fail(
            span.clone(),
            commands
                .iter()
                .map(|command| source_command(language, command))
                .collect(),
        ),
        Command::Action(action) => source_action(language, action.clone())
            .map(Command::Action)
            .unwrap_or_else(|| Command::Actions(Actions::new(Vec::new()))),
        Command::Actions(actions) => Command::Actions(Actions::new(
            actions
                .0
                .iter()
                .cloned()
                .filter_map(|action| source_action(language, action))
                .collect(),
        )),
        command => command.clone(),
    }
}

fn render_command(
    language: &HostLanguage,
    command: &Command,
    outcome: Option<&RecordedOutcome>,
    rendered_action_prefix: usize,
) -> Option<String> {
    let mut command = command.clone();
    if rendered_action_prefix != 0 {
        let Command::Actions(actions) = command else {
            panic!("only action batches can have an already-rendered prefix")
        };
        if rendered_action_prefix >= actions.0.len() {
            return None;
        }
        command = Command::Actions(Actions::new(actions.0[rendered_action_prefix..].to_vec()));
    }
    command = source_command(language, &command);
    if matches!(&command, Command::Actions(actions) if actions.0.is_empty()) {
        return None;
    }
    if matches!(
        outcome,
        Some(RecordedOutcome::CheckFailed | RecordedOutcome::ExpectFailFailed)
    ) {
        command = Command::Fail(egglog_experimental::span!(), vec![command]);
    }
    if let Command::Actions(actions) = command {
        return Some(
            actions
                .0
                .into_iter()
                .map(|action| Command::Action(action).to_string())
                .collect::<Vec<_>>()
                .join("\n"),
        );
    }
    Some(command.to_string())
}

fn render_trace(trace: &Trace, language: &HostLanguage) -> String {
    let events = trace.events();
    let command_count = events
        .iter()
        .filter(|event| matches!(event, TraceEvent::Execution { .. }))
        .count();
    let rebuilds = events
        .iter()
        .filter(|event| matches!(event, TraceEvent::Rebuild))
        .count();
    let stats_reads = events
        .iter()
        .filter(|event| matches!(event, TraceEvent::Stats))
        .count();
    let clones = events
        .iter()
        .filter(|event| matches!(event, TraceEvent::Clone))
        .count();

    let mut source = String::from("; Outcome-preserving chronological host interaction replay.\n");
    writeln!(
        source,
        "; host trace counts: commands={command_count}, rebuilds={rebuilds}, stats_reads={stats_reads}, clones={clones}."
    )
    .expect("writing to a String cannot fail");
    for event in events {
        source.push('\n');
        match event {
            TraceEvent::PendingActions(command) => {
                source.push_str("; pending host actions captured before clone\n");
                if let Some(command) = render_command(language, command, None, 0) {
                    writeln!(source, "{command}").expect("writing to a String cannot fail");
                }
            }
            TraceEvent::Execution {
                command,
                outcome,
                rendered_action_prefix,
            } => {
                let status = match outcome {
                    RecordedOutcome::Success(_) => "success",
                    RecordedOutcome::CheckFailed => "check_failed",
                    RecordedOutcome::ExpectFailFailed => "expect_fail_failed",
                };
                writeln!(source, "; host command result: {status}")
                    .expect("writing to a String cannot fail");
                if let Some(command) =
                    render_command(language, command, Some(outcome), *rendered_action_prefix)
                {
                    writeln!(source, "{command}").expect("writing to a String cannot fail");
                }
                if let RecordedOutcome::Success(outputs) = outcome {
                    for output in outputs.iter() {
                        let rendered = output.to_string();
                        if !rendered.is_empty() {
                            for line in rendered.lines() {
                                writeln!(source, "; command output: {line}")
                                    .expect("writing to a String cannot fail");
                            }
                        }
                    }
                }
            }
            TraceEvent::Rebuild => {
                source.push_str("; host rebuild (the preceding mutation batch was flushed)\n");
            }
            TraceEvent::Stats => source.push_str(
                "; host stats read (numeric values are backend-specific and not replayable)\n",
            ),
            TraceEvent::Clone => source.push_str("; host graph clone\n"),
        }
    }
    source
}

#[repr(C)]
pub struct EgglogDisequalityGraph {
    graph: DisequalityGraph,
    last_error: CString,
}

#[repr(C)]
pub struct EgglogDisequalityTemplate {
    encoding: DisequalityEncoding,
    builder: Option<LanguageSchemaBuilder>,
    template: Option<DisequalityGraphTemplate>,
    last_error: CString,
}

#[repr(i32)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AbiCommandStatus {
    Success = 0,
    CheckFailed = 1,
    ExpectFailFailed = 2,
    Error = 3,
}

#[repr(i32)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AbiOutputKind {
    PrintFunctionSize = 0,
    PrintAllFunctionsSize = 1,
    ExtractBest = 2,
    ExtractVariants = 3,
    ProveExists = 4,
    OverallStatistics = 5,
    PrintFunction = 6,
    RunSchedule = 7,
    UserDefined = 8,
}

struct AbiCommandOutput {
    kind: AbiOutputKind,
    text: CString,
}

#[repr(C)]
pub struct EgglogCommandResult {
    status: AbiCommandStatus,
    outputs: Vec<AbiCommandOutput>,
    error: CString,
}

#[repr(C)]
pub struct EgglogOwnedString {
    value: CString,
}

impl EgglogCommandResult {
    fn from_execution(execution: Result<CommandResult, BackendError>) -> Self {
        match execution {
            Ok(result) => Self {
                status: match result.status {
                    CommandStatus::Success => AbiCommandStatus::Success,
                    CommandStatus::CheckFailed => AbiCommandStatus::CheckFailed,
                    CommandStatus::ExpectFailFailed => AbiCommandStatus::ExpectFailFailed,
                },
                outputs: result
                    .outputs
                    .into_iter()
                    .map(|output| AbiCommandOutput {
                        kind: match &output {
                            CommandOutput::PrintFunctionSize(_) => AbiOutputKind::PrintFunctionSize,
                            CommandOutput::PrintAllFunctionsSize(_) => {
                                AbiOutputKind::PrintAllFunctionsSize
                            }
                            CommandOutput::ExtractBest(..) => AbiOutputKind::ExtractBest,
                            CommandOutput::ExtractVariants(..) => AbiOutputKind::ExtractVariants,
                            CommandOutput::ProveExists { .. } => AbiOutputKind::ProveExists,
                            CommandOutput::OverallStatistics(_) => AbiOutputKind::OverallStatistics,
                            CommandOutput::PrintFunction(..) => AbiOutputKind::PrintFunction,
                            CommandOutput::RunSchedule(_) => AbiOutputKind::RunSchedule,
                            CommandOutput::UserDefined(_) => AbiOutputKind::UserDefined,
                        },
                        text: ffi_cstring(output.to_string()),
                    })
                    .collect(),
                error: CString::default(),
            },
            Err(error) => Self {
                status: AbiCommandStatus::Error,
                outputs: Vec::new(),
                error: ffi_cstring(error.to_string()),
            },
        }
    }

    fn panic(payload: Box<dyn std::any::Any + Send>) -> Self {
        let message = payload
            .downcast_ref::<&str>()
            .copied()
            .or_else(|| payload.downcast_ref::<String>().map(String::as_str))
            .unwrap_or("Rust panic in egglog disequality command");
        Self {
            status: AbiCommandStatus::Error,
            outputs: Vec::new(),
            error: ffi_cstring(message),
        }
    }
}

fn ffi_cstring(value: impl Into<String>) -> CString {
    CString::new(value.into().replace('\0', "\\0")).expect("NUL bytes were replaced")
}

impl EgglogDisequalityTemplate {
    fn record_error(&mut self, error: impl ToString) {
        let message = error.to_string().replace('\0', "\\0");
        self.last_error = CString::new(message).expect("NUL bytes were replaced");
    }
}

impl EgglogDisequalityGraph {
    fn new(graph: DisequalityGraph) -> Self {
        Self {
            graph,
            last_error: CString::default(),
        }
    }

    fn record_error(&mut self, error: impl ToString) {
        let message = error.to_string().replace('\0', "\\0");
        self.last_error = CString::new(message).expect("NUL bytes were replaced");
    }
}

unsafe fn ffi_template<'a>(
    template: *mut EgglogDisequalityTemplate,
) -> Result<&'a mut EgglogDisequalityTemplate, BackendError> {
    // SAFETY: The caller owns the C ABI pointer and this function rejects null.
    unsafe { template.as_mut() }.ok_or(BackendError::NullPointer("template"))
}

fn ffi_template_call<T>(
    template: *mut EgglogDisequalityTemplate,
    fallback: T,
    operation: impl FnOnce(&mut EgglogDisequalityTemplate) -> Result<T, BackendError>,
) -> T {
    let result = catch_unwind(AssertUnwindSafe(|| {
        // SAFETY: Every exported operation requires a live pointer returned by
        // `egglog_disequality_template_new`.
        let template = unsafe { ffi_template(template) }?;
        match operation(template) {
            Ok(value) => {
                template.last_error = CString::default();
                Ok(value)
            }
            Err(error) => {
                template.record_error(&error);
                Err(error)
            }
        }
    }));
    match result {
        Ok(Ok(value)) => value,
        Ok(Err(_)) => fallback,
        Err(payload) => {
            if let Ok(template) = unsafe { ffi_template(template) } {
                let message = payload
                    .downcast_ref::<&str>()
                    .copied()
                    .or_else(|| payload.downcast_ref::<String>().map(String::as_str))
                    .unwrap_or("Rust panic in egglog disequality template");
                template.record_error(message);
            }
            fallback
        }
    }
}

fn encoding_from_abi(value: u32) -> Result<DisequalityEncoding, BackendError> {
    match value {
        0 => Ok(DisequalityEncoding::EqualityEmbedding),
        1 => Ok(DisequalityEncoding::OptimizedEqualityEmbedding),
        2 => Ok(DisequalityEncoding::NegatedEqualityEmbedding),
        3 => Ok(DisequalityEncoding::DisequalityEdges),
        _ => Err(BackendError::Other(format!(
            "unknown disequality encoding {value}"
        ))),
    }
}

fn term_language_from_abi(value: u32) -> Result<TermLanguage, BackendError> {
    match value {
        0 => Ok(TermLanguage::Vec),
        1 => Ok(TermLanguage::Direct),
        _ => Err(BackendError::Other(format!(
            "unknown term language {value}"
        ))),
    }
}

unsafe fn ffi_text<'a>(value: *const c_char, label: &'static str) -> Result<&'a str, BackendError> {
    if value.is_null() {
        return Err(BackendError::NullPointer(label));
    }
    // SAFETY: The C ABI contract requires a NUL-terminated string.
    unsafe { CStr::from_ptr(value) }
        .to_str()
        .map_err(|_| BackendError::InvalidUtf8(label))
}

unsafe fn ffi_graph<'a>(
    graph: *mut EgglogDisequalityGraph,
) -> Result<&'a mut EgglogDisequalityGraph, BackendError> {
    // SAFETY: The caller owns the C ABI pointer and this function rejects null.
    unsafe { graph.as_mut() }.ok_or(BackendError::NullPointer("graph"))
}

fn ffi_call<T>(
    graph: *mut EgglogDisequalityGraph,
    fallback: T,
    operation: impl FnOnce(&mut DisequalityGraph) -> Result<T, BackendError>,
) -> T {
    let result = catch_unwind(AssertUnwindSafe(|| {
        // SAFETY: Every exported operation requires a live pointer returned by
        // `egglog_disequality_graph_new` or `_clone`.
        let graph = unsafe { ffi_graph(graph) }?;
        match operation(&mut graph.graph) {
            Ok(value) => {
                graph.last_error = CString::default();
                Ok(value)
            }
            Err(error) => {
                graph.record_error(&error);
                Err(error)
            }
        }
    }));
    match result {
        Ok(Ok(value)) => value,
        Ok(Err(_)) => fallback,
        Err(payload) => {
            if let Ok(graph) = unsafe { ffi_graph(graph) } {
                let message = payload
                    .downcast_ref::<&str>()
                    .copied()
                    .or_else(|| payload.downcast_ref::<String>().map(String::as_str))
                    .unwrap_or("Rust panic in egglog disequality backend");
                graph.record_error(message);
            }
            fallback
        }
    }
}

fn ffi_command_call(
    graph: *mut EgglogDisequalityGraph,
    operation: impl FnOnce(&mut DisequalityGraph) -> Result<CommandResult, BackendError>,
) -> *mut EgglogCommandResult {
    let execution = catch_unwind(AssertUnwindSafe(|| {
        // SAFETY: Every exported command requires a live pointer returned by
        // `egglog_disequality_graph_new`, `_new_from_template`, or `_clone`.
        let graph = unsafe { ffi_graph(graph) }?;
        let result = operation(&mut graph.graph);
        match &result {
            Ok(_) => graph.last_error = CString::default(),
            Err(error) => graph.record_error(error),
        }
        result
    }));
    let result = match execution {
        Ok(result) => EgglogCommandResult::from_execution(result),
        Err(payload) => EgglogCommandResult::panic(payload),
    };
    Box::into_raw(Box::new(result))
}

#[unsafe(no_mangle)]
pub extern "C" fn egglog_disequality_graph_new(
    encoding: u32,
    record_interactions: i32,
) -> *mut EgglogDisequalityGraph {
    catch_unwind(AssertUnwindSafe(|| {
        let encoding = encoding_from_abi(encoding).ok()?;
        let graph =
            DisequalityGraph::new_with_recording(encoding, record_interactions != 0).ok()?;
        Some(Box::into_raw(Box::new(EgglogDisequalityGraph::new(graph))))
    }))
    .ok()
    .flatten()
    .unwrap_or(ptr::null_mut())
}

#[unsafe(no_mangle)]
/// Allocate a reusable graph template.
///
/// # Safety
///
/// In direct mode, `sort_name` must point to a NUL-terminated UTF-8 string.
/// It is ignored and may be null in Vec mode.
pub unsafe extern "C" fn egglog_disequality_template_new(
    encoding: u32,
    term_language: u32,
    sort_name: *const c_char,
) -> *mut EgglogDisequalityTemplate {
    catch_unwind(AssertUnwindSafe(|| {
        let encoding = encoding_from_abi(encoding).ok()?;
        let term_language = term_language_from_abi(term_language).ok()?;
        let (builder, template) = match term_language {
            TermLanguage::Vec => (
                None,
                Some(DisequalityGraphTemplate::generic(encoding).ok()?),
            ),
            TermLanguage::Direct => {
                // SAFETY: Direct templates require a valid sort name pointer.
                let sort_name = unsafe { ffi_text(sort_name, "sort name") }.ok()?;
                (Some(LanguageSchemaBuilder::new(sort_name)), None)
            }
        };
        Some(Box::into_raw(Box::new(EgglogDisequalityTemplate {
            encoding,
            builder,
            template,
            last_error: CString::default(),
        })))
    }))
    .ok()
    .flatten()
    .unwrap_or(ptr::null_mut())
}

#[unsafe(no_mangle)]
/// Register one source operator in an unfinished direct-language template.
///
/// # Safety
///
/// `template` must uniquely reference a live template from this API.
/// `source_name` must point to a NUL-terminated UTF-8 string, and
/// `preferred_name` must be null or point to one.
pub unsafe extern "C" fn egglog_disequality_template_register_operator(
    template: *mut EgglogDisequalityTemplate,
    source_name: *const c_char,
    preferred_name: *const c_char,
    arity: usize,
) -> OperatorId {
    ffi_template_call(template, OperatorId::MAX, |template| {
        // SAFETY: The C ABI contract requires a valid source name pointer.
        let source_name = unsafe { ffi_text(source_name, "source operator name") }?;
        let preferred_name = if preferred_name.is_null() {
            None
        } else {
            // SAFETY: A non-null preferred name must be NUL-terminated.
            Some(unsafe { ffi_text(preferred_name, "preferred operator name") }?.to_owned())
        };
        let builder = template.builder.as_mut().ok_or_else(|| {
            BackendError::Other("template is not accepting operator declarations".to_owned())
        })?;
        builder.register_operator(source_name, preferred_name, arity)
    })
}

#[unsafe(no_mangle)]
/// Compile a template's declared language schema.
///
/// # Safety
///
/// `template` must uniquely reference a live template from this API.
pub unsafe extern "C" fn egglog_disequality_template_finish(
    template: *mut EgglogDisequalityTemplate,
) -> i32 {
    ffi_template_call(template, -1, |template| {
        if template.template.is_some() {
            return Ok(0);
        }
        let builder = template
            .builder
            .take()
            .ok_or_else(|| BackendError::Other("template has no language schema".to_owned()))?;
        template.template = Some(builder.compile(template.encoding)?);
        Ok(0)
    })
}

#[unsafe(no_mangle)]
/// Instantiate an empty graph from a compiled template.
///
/// # Safety
///
/// `template` must point to a live, finished template from this API and must
/// not be concurrently mutated or freed. Multiple graph-instantiation calls
/// may read the same finished template concurrently.
pub unsafe extern "C" fn egglog_disequality_graph_new_from_template(
    template: *const EgglogDisequalityTemplate,
    record_interactions: i32,
) -> *mut EgglogDisequalityGraph {
    catch_unwind(AssertUnwindSafe(|| {
        // SAFETY: The caller promises a live, finished template that is not
        // concurrently mutated or freed. Graph creation only reads it.
        let template = unsafe { template.as_ref() }?.template.as_ref()?;
        Some(Box::into_raw(Box::new(EgglogDisequalityGraph::new(
            template.new_graph_with_recording(record_interactions != 0),
        ))))
    }))
    .ok()
    .flatten()
    .unwrap_or(ptr::null_mut())
}

#[unsafe(no_mangle)]
/// Release a template allocated by this library.
///
/// # Safety
///
/// `template` must be null or uniquely own a live template from this API. A
/// non-null pointer must not be used or freed again after this call.
pub unsafe extern "C" fn egglog_disequality_template_free(
    template: *mut EgglogDisequalityTemplate,
) {
    if !template.is_null() {
        // SAFETY: Ownership is transferred back exactly once by the caller.
        drop(unsafe { Box::from_raw(template) });
    }
}

#[unsafe(no_mangle)]
/// Return the most recent template error.
///
/// # Safety
///
/// `template` must be null or point to a live template from this API. The
/// returned pointer remains valid only until the template is mutated or freed.
pub unsafe extern "C" fn egglog_disequality_template_last_error(
    template: *const EgglogDisequalityTemplate,
) -> *const c_char {
    if template.is_null() {
        return c"null template pointer".as_ptr();
    }
    // SAFETY: The caller promises this is a live pointer from this API.
    unsafe { &*template }.last_error.as_ptr()
}

#[unsafe(no_mangle)]
/// Clone a graph allocated by this library.
///
/// # Safety
///
/// `graph` must be null or point to a live graph allocated by this library.
pub unsafe extern "C" fn egglog_disequality_graph_clone(
    graph: *const EgglogDisequalityGraph,
) -> *mut EgglogDisequalityGraph {
    catch_unwind(AssertUnwindSafe(|| {
        // SAFETY: The caller promises this is a live pointer from this API.
        let graph = unsafe { graph.as_ref() }?;
        Some(Box::into_raw(Box::new(EgglogDisequalityGraph::new(
            graph.graph.clone(),
        ))))
    }))
    .ok()
    .flatten()
    .unwrap_or(ptr::null_mut())
}

#[unsafe(no_mangle)]
/// Release a graph allocated by this library.
///
/// # Safety
///
/// `graph` must be null or uniquely own a live graph allocated by this library.
/// A non-null pointer must not be used or freed again after this call.
pub unsafe extern "C" fn egglog_disequality_graph_free(graph: *mut EgglogDisequalityGraph) {
    if !graph.is_null() {
        // SAFETY: Ownership is transferred back exactly once by the caller.
        drop(unsafe { Box::from_raw(graph) });
    }
}

#[unsafe(no_mangle)]
/// Add one host node and return its stable handle.
///
/// # Safety
///
/// `graph` must uniquely reference a live graph. `operator_name` must point to
/// a NUL-terminated string, and `children` must expose `child_count` readable
/// handles when that count is nonzero.
pub unsafe extern "C" fn egglog_disequality_add(
    graph: *mut EgglogDisequalityGraph,
    operator_name: *const c_char,
    children: *const TermId,
    child_count: usize,
) -> TermId {
    ffi_call(graph, TermId::MAX, |graph| {
        if operator_name.is_null() {
            return Err(BackendError::NullPointer("operator name"));
        }
        // SAFETY: The caller provides a NUL-terminated operator string.
        let operator = unsafe { CStr::from_ptr(operator_name) }
            .to_str()
            .map_err(|_| BackendError::InvalidUtf8("operator name"))?;
        let children = if child_count == 0 {
            &[]
        } else {
            if children.is_null() {
                return Err(BackendError::NullPointer("children"));
            }
            // SAFETY: The caller provides `child_count` readable handles.
            unsafe { slice::from_raw_parts(children, child_count) }
        };
        graph.add(operator, children)
    })
}

#[unsafe(no_mangle)]
/// Add one dynamic atom and return its stable handle.
///
/// # Safety
///
/// `graph` must uniquely reference a live direct-language graph and
/// `atom_name` must point to a NUL-terminated UTF-8 string.
pub unsafe extern "C" fn egglog_disequality_add_atom(
    graph: *mut EgglogDisequalityGraph,
    atom_name: *const c_char,
) -> TermId {
    ffi_call(graph, TermId::MAX, |graph| {
        // SAFETY: The C ABI contract requires a NUL-terminated atom string.
        let atom_name = unsafe { ffi_text(atom_name, "atom name") }?;
        graph.add_atom(atom_name)
    })
}

#[unsafe(no_mangle)]
/// Add one registered source constructor and return its stable handle.
///
/// # Safety
///
/// `graph` must uniquely reference a live direct-language graph. `children`
/// must expose `child_count` readable handles when that count is nonzero.
pub unsafe extern "C" fn egglog_disequality_add_registered(
    graph: *mut EgglogDisequalityGraph,
    operator: OperatorId,
    children: *const TermId,
    child_count: usize,
) -> TermId {
    ffi_call(graph, TermId::MAX, |graph| {
        let children = if child_count == 0 {
            &[]
        } else {
            if children.is_null() {
                return Err(BackendError::NullPointer("children"));
            }
            // SAFETY: The caller provides `child_count` readable handles.
            unsafe { slice::from_raw_parts(children, child_count) }
        };
        graph.add_registered(operator, children)
    })
}

#[unsafe(no_mangle)]
/// Queue a union between two handles.
///
/// # Safety
///
/// `graph` must uniquely reference a live graph allocated by this library.
pub unsafe extern "C" fn egglog_disequality_union(
    graph: *mut EgglogDisequalityGraph,
    lhs: TermId,
    rhs: TermId,
) -> i32 {
    ffi_call(graph, -1, |graph| {
        graph.union(lhs, rhs)?;
        Ok(0)
    })
}

#[unsafe(no_mangle)]
/// Queue a disequality between two handles.
///
/// # Safety
///
/// `graph` must uniquely reference a live graph allocated by this library.
pub unsafe extern "C" fn egglog_disequality_disunion(
    graph: *mut EgglogDisequalityGraph,
    lhs: TermId,
    rhs: TermId,
) -> i32 {
    ffi_call(graph, -1, |graph| {
        graph.disequal(lhs, rhs)?;
        Ok(0)
    })
}

#[unsafe(no_mangle)]
/// Flush queued AST actions into egglog.
///
/// # Safety
///
/// `graph` must uniquely reference a live graph allocated by this library.
pub unsafe extern "C" fn egglog_disequality_flush(
    graph: *mut EgglogDisequalityGraph,
) -> *mut EgglogCommandResult {
    ffi_command_call(graph, DisequalityGraph::flush)
}

#[unsafe(no_mangle)]
/// Flush queued AST actions and record a host rebuild boundary.
///
/// # Safety
///
/// `graph` must uniquely reference a live graph allocated by this library.
pub unsafe extern "C" fn egglog_disequality_rebuild(
    graph: *mut EgglogDisequalityGraph,
) -> *mut EgglogCommandResult {
    ffi_command_call(graph, DisequalityGraph::rebuild)
}

#[unsafe(no_mangle)]
/// Execute an equality check between two handles.
///
/// # Safety
///
/// `graph` must uniquely reference a live graph allocated by this library.
pub unsafe extern "C" fn egglog_disequality_check_equal(
    graph: *mut EgglogDisequalityGraph,
    lhs: TermId,
    rhs: TermId,
) -> *mut EgglogCommandResult {
    ffi_command_call(graph, |graph| graph.check_equal(lhs, rhs))
}

#[unsafe(no_mangle)]
/// Execute a pair-only known-disequality check between two handles.
///
/// # Safety
///
/// `graph` must uniquely reference a live graph allocated by this library.
pub unsafe extern "C" fn egglog_disequality_check_known_disequal(
    graph: *mut EgglogDisequalityGraph,
    lhs: TermId,
    rhs: TermId,
) -> *mut EgglogCommandResult {
    ffi_command_call(graph, |graph| graph.check_known_disequal(lhs, rhs))
}

#[unsafe(no_mangle)]
/// Execute the global consistency query.
///
/// # Safety
///
/// `graph` must uniquely reference a live graph allocated by this library.
pub unsafe extern "C" fn egglog_disequality_check_consistency(
    graph: *mut EgglogDisequalityGraph,
) -> *mut EgglogCommandResult {
    ffi_command_call(graph, DisequalityGraph::check_consistency)
}

#[unsafe(no_mangle)]
/// Return a command result's stable status tag.
///
/// # Safety
///
/// `result` must be null or point to a live command result from this library.
pub unsafe extern "C" fn egglog_command_result_status(result: *const EgglogCommandResult) -> i32 {
    unsafe { result.as_ref() }.map_or(AbiCommandStatus::Error as i32, |result| {
        result.status as i32
    })
}

#[unsafe(no_mangle)]
/// Return the number of ordered command outputs.
///
/// # Safety
///
/// `result` must be null or point to a live command result from this library.
pub unsafe extern "C" fn egglog_command_result_output_count(
    result: *const EgglogCommandResult,
) -> usize {
    unsafe { result.as_ref() }.map_or(0, |result| result.outputs.len())
}

#[unsafe(no_mangle)]
/// Return an output's stable kind tag, or -1 for an invalid result or index.
///
/// # Safety
///
/// `result` must be null or point to a live command result from this library.
pub unsafe extern "C" fn egglog_command_result_output_kind(
    result: *const EgglogCommandResult,
    index: usize,
) -> i32 {
    unsafe { result.as_ref() }
        .and_then(|result| result.outputs.get(index))
        .map_or(-1, |output| output.kind as i32)
}

#[unsafe(no_mangle)]
/// Return an output's rendered text, or null for an invalid result or index.
///
/// # Safety
///
/// `result` must be null or point to a live command result from this library.
/// The returned pointer remains valid until `result` is freed.
pub unsafe extern "C" fn egglog_command_result_output_text(
    result: *const EgglogCommandResult,
    index: usize,
) -> *const c_char {
    unsafe { result.as_ref() }
        .and_then(|result| result.outputs.get(index))
        .map_or(ptr::null(), |output| output.text.as_ptr())
}

#[unsafe(no_mangle)]
/// Return an error result's message, or an empty string for non-errors.
///
/// # Safety
///
/// `result` must be null or point to a live command result from this library.
/// The returned pointer remains valid until `result` is freed.
pub unsafe extern "C" fn egglog_command_result_error(
    result: *const EgglogCommandResult,
) -> *const c_char {
    let Some(result) = (unsafe { result.as_ref() }) else {
        return c"null command result pointer".as_ptr();
    };
    result.error.as_ptr()
}

#[unsafe(no_mangle)]
/// Release a command result and all of its outputs.
///
/// # Safety
///
/// `result` must be null or uniquely own a live command result from this library.
pub unsafe extern "C" fn egglog_command_result_free(result: *mut EgglogCommandResult) {
    if !result.is_null() {
        // SAFETY: Ownership is transferred back exactly once by the caller.
        drop(unsafe { Box::from_raw(result) });
    }
}

#[unsafe(no_mangle)]
/// Return the number of generic host nodes.
///
/// # Safety
///
/// `graph` must uniquely reference a live graph allocated by this library.
pub unsafe extern "C" fn egglog_disequality_num_nodes(graph: *mut EgglogDisequalityGraph) -> u64 {
    ffi_call(graph, u64::MAX, |graph| Ok(graph.stats()?.nodes as u64))
}

#[unsafe(no_mangle)]
/// Return the number of generic host e-classes.
///
/// # Safety
///
/// `graph` must uniquely reference a live graph allocated by this library.
pub unsafe extern "C" fn egglog_disequality_num_classes(graph: *mut EgglogDisequalityGraph) -> u64 {
    ffi_call(graph, u64::MAX, |graph| Ok(graph.stats()?.classes as u64))
}

#[unsafe(no_mangle)]
/// Return the number of rows in generated disequality support tables.
///
/// # Safety
///
/// `graph` must uniquely reference a live graph allocated by this library.
pub unsafe extern "C" fn egglog_disequality_num_extension_rows(
    graph: *mut EgglogDisequalityGraph,
) -> u64 {
    ffi_call(graph, u64::MAX, |graph| {
        Ok(graph.stats()?.extension_rows as u64)
    })
}

#[unsafe(no_mangle)]
/// Return the total number of tuples in the egglog database.
///
/// # Safety
///
/// `graph` must uniquely reference a live graph allocated by this library.
pub unsafe extern "C" fn egglog_disequality_num_tuples(graph: *mut EgglogDisequalityGraph) -> u64 {
    ffi_call(graph, u64::MAX, |graph| {
        Ok(graph.stats()?.total_tuples as u64)
    })
}

#[unsafe(no_mangle)]
/// Return replayable source owned by the caller.
///
/// # Safety
///
/// `graph` must uniquely reference a live graph. Free a non-null result with
/// [`egglog_owned_string_free`].
pub unsafe extern "C" fn egglog_disequality_source(
    graph: *mut EgglogDisequalityGraph,
) -> *mut EgglogOwnedString {
    ffi_call(graph, ptr::null_mut(), |graph| {
        Ok(Box::into_raw(Box::new(EgglogOwnedString {
            value: ffi_cstring(graph.source()?),
        })))
    })
}

#[unsafe(no_mangle)]
/// Return fully desugared replayable source owned by the caller.
///
/// # Safety
///
/// `graph` must uniquely reference a live graph. Free a non-null result with
/// [`egglog_owned_string_free`].
pub unsafe extern "C" fn egglog_disequality_desugared_source(
    graph: *mut EgglogDisequalityGraph,
) -> *mut EgglogOwnedString {
    ffi_call(graph, ptr::null_mut(), |graph| {
        Ok(Box::into_raw(Box::new(EgglogOwnedString {
            value: ffi_cstring(graph.desugared_source()?),
        })))
    })
}

#[unsafe(no_mangle)]
/// Return a borrowed pointer to an owned UTF-8 string's bytes.
///
/// # Safety
///
/// `value` must be null or point to a live string returned by this library.
/// The pointer remains valid until the string is freed.
pub unsafe extern "C" fn egglog_owned_string_data(
    value: *const EgglogOwnedString,
) -> *const c_char {
    let Some(value) = (unsafe { value.as_ref() }) else {
        return ptr::null();
    };
    value.value.as_ptr()
}

#[unsafe(no_mangle)]
/// Return an owned UTF-8 string's byte length, excluding its trailing NUL.
///
/// # Safety
///
/// `value` must be null or point to a live string returned by this library.
pub unsafe extern "C" fn egglog_owned_string_len(value: *const EgglogOwnedString) -> usize {
    unsafe { value.as_ref() }.map_or(0, |value| value.value.as_bytes().len())
}

#[unsafe(no_mangle)]
/// Release an owned UTF-8 string.
///
/// # Safety
///
/// `value` must be null or uniquely own a live string returned by this library.
pub unsafe extern "C" fn egglog_owned_string_free(value: *mut EgglogOwnedString) {
    if !value.is_null() {
        // SAFETY: Ownership is transferred back exactly once by the caller.
        drop(unsafe { Box::from_raw(value) });
    }
}

#[unsafe(no_mangle)]
/// Return the most recent error message for a graph.
///
/// # Safety
///
/// `graph` must be null or point to a live graph allocated by this library.
/// The returned pointer remains valid only until the graph is mutated or freed.
pub unsafe extern "C" fn egglog_disequality_last_error(
    graph: *const EgglogDisequalityGraph,
) -> *const c_char {
    if graph.is_null() {
        return c"null graph pointer".as_ptr();
    }
    // SAFETY: The caller promises this is a live pointer from this API.
    unsafe { &*graph }.last_error.as_ptr()
}

#[cfg(test)]
mod tests {
    use super::*;

    const ENCODINGS: [DisequalityEncoding; 4] = [
        DisequalityEncoding::EqualityEmbedding,
        DisequalityEncoding::OptimizedEqualityEmbedding,
        DisequalityEncoding::NegatedEqualityEmbedding,
        DisequalityEncoding::DisequalityEdges,
    ];

    #[derive(Debug, PartialEq, Eq)]
    enum TestRelation {
        Equal,
        Unequal,
        Indeterminate,
    }

    fn query_relation(graph: &mut DisequalityGraph, lhs: TermId, rhs: TermId) -> TestRelation {
        match graph.check_equal(lhs, rhs).unwrap().status {
            CommandStatus::Success => TestRelation::Equal,
            CommandStatus::CheckFailed => {
                match graph.check_known_disequal(lhs, rhs).unwrap().status {
                    CommandStatus::Success => TestRelation::Unequal,
                    CommandStatus::ExpectFailFailed => TestRelation::Indeterminate,
                    status => panic!("unexpected pair-disequality status: {status:?}"),
                }
            }
            status => panic!("unexpected equality status: {status:?}"),
        }
    }

    fn graph_is_consistent(graph: &mut DisequalityGraph) -> bool {
        match graph.check_consistency().unwrap().status {
            CommandStatus::Success => false,
            CommandStatus::ExpectFailFailed => true,
            status => panic!("unexpected consistency status: {status:?}"),
        }
    }

    #[test]
    fn all_encodings_support_batched_host_operations() {
        for encoding in ENCODINGS {
            let mut graph = DisequalityGraph::new_recording(encoding).unwrap();
            let a = graph.add("a", &[]).unwrap();
            let b = graph.add("b", &[]).unwrap();
            let fa = graph.add("f", &[a]).unwrap();
            let fb = graph.add("f", &[b]).unwrap();
            graph.disequal(fa, fb).unwrap();

            assert_eq!(query_relation(&mut graph, fa, fb), TestRelation::Unequal);
            assert_eq!(
                query_relation(&mut graph, a, b),
                TestRelation::Indeterminate
            );
            assert!(graph_is_consistent(&mut graph));
            assert_eq!(graph.stats().unwrap().nodes, 4);

            let c = graph.add("c", &[]).unwrap();
            let d = graph.add("d", &[]).unwrap();
            graph.union(a, b).unwrap();
            assert!(!graph_is_consistent(&mut graph));
            assert_eq!(
                query_relation(&mut graph, c, d),
                TestRelation::Indeterminate,
                "pair queries must remain independent of an unrelated contradiction"
            );

            let source = graph.source().unwrap();
            assert!(source.contains("(fail (check-known-disequal"));
            let mut replay = new_experimental_egraph_with_disequality_encoding(encoding);
            replay.parse_and_run_program(None, &source).unwrap();
        }
    }

    #[test]
    fn first_consistency_check_observes_pending_contradictions() {
        for encoding in ENCODINGS {
            let mut graph = DisequalityGraph::new(encoding).unwrap();
            let a = graph.add("a", &[]).unwrap();
            graph.disequal(a, a).unwrap();

            assert_eq!(
                graph.check_consistency().unwrap().status,
                CommandStatus::Success,
                "{encoding:?} skipped disequality support created by the pending batch"
            );
        }
    }

    #[test]
    fn pending_actions_are_ast_and_record_the_submitted_batch() {
        let mut graph =
            DisequalityGraph::new_recording(DisequalityEncoding::NegatedEqualityEmbedding).unwrap();
        let a = graph.add("a", &[]).unwrap();
        let b = graph.add("b", &[]).unwrap();
        graph.disequal(a, b).unwrap();

        assert!(matches!(graph.pending[0], Action::Let(..)));
        assert!(matches!(graph.pending[1], Action::Set(..)));
        assert!(matches!(graph.pending.last(), Some(Action::Expr(..))));
        let expected = Command::Actions(Actions::new(graph.pending.clone())).to_string();
        let result = graph.flush().unwrap();
        assert_eq!(result.status, CommandStatus::Success);

        let events = graph.trace.as_ref().unwrap().events();
        let TraceEvent::Execution { command, .. } = events.last().unwrap() else {
            panic!("the submitted batch was not recorded as an execution")
        };
        assert_eq!(command.to_string(), expected);
    }

    #[test]
    fn unexpected_execution_errors_are_not_recorded() {
        let mut graph =
            DisequalityGraph::new_recording(DisequalityEncoding::NegatedEqualityEmbedding).unwrap();
        let before = graph.trace.as_ref().unwrap().events().len();
        let error = graph
            .execute_command_unlocked(
                Command::Action(Action::Panic(
                    egglog_experimental::span!(),
                    "injected AST failure".to_owned(),
                )),
                None,
                0,
            )
            .unwrap_err();
        assert!(error.to_string().contains("injected AST failure"));
        assert_eq!(graph.trace.as_ref().unwrap().events().len(), before);
    }

    #[test]
    fn successful_command_outputs_are_retained_in_history() {
        let mut graph =
            DisequalityGraph::new_recording(DisequalityEncoding::NegatedEqualityEmbedding).unwrap();
        graph.add("a", &[]).unwrap();
        graph.flush().unwrap();
        let result = graph
            .execute_command_unlocked(
                Command::PrintSize(
                    egglog_experimental::span!(),
                    Some("BenchmarkNode".to_owned()),
                ),
                None,
                0,
            )
            .unwrap();
        assert!(matches!(
            result.outputs.as_slice(),
            [CommandOutput::PrintFunctionSize(1)]
        ));

        let source = graph.source().unwrap();
        assert!(source.contains("(print-size BenchmarkNode)"));
        assert!(source.contains("; command output: 1"));
    }

    #[test]
    fn queries_accept_only_the_expected_failure_kind() {
        let mut graph =
            DisequalityGraph::new_recording(DisequalityEncoding::NegatedEqualityEmbedding).unwrap();
        let span = egglog_experimental::span!();
        let unequal_ints = Command::Check(
            span.clone(),
            vec![egglog_experimental::ast::Fact::Eq(
                span.clone(),
                Expr::Lit(span.clone(), Literal::Int(0)),
                Expr::Lit(span.clone(), Literal::Int(1)),
            )],
        );
        let before = graph.trace.as_ref().unwrap().events().len();
        let error = graph
            .execute_command_unlocked(unequal_ints, Some(CommandStatus::ExpectFailFailed), 0)
            .unwrap_err();
        assert!(matches!(
            error,
            BackendError::Egglog(EgglogError::CheckError(..))
        ));
        assert_eq!(graph.trace.as_ref().unwrap().events().len(), before);

        let successful_check_under_fail = Command::Fail(
            span.clone(),
            vec![Command::Check(
                span.clone(),
                vec![egglog_experimental::ast::Fact::Eq(
                    span.clone(),
                    Expr::Lit(span.clone(), Literal::Int(0)),
                    Expr::Lit(span, Literal::Int(0)),
                )],
            )],
        );
        let error = graph
            .execute_command_unlocked(
                successful_check_under_fail,
                Some(CommandStatus::CheckFailed),
                0,
            )
            .unwrap_err();
        assert!(matches!(
            error,
            BackendError::Egglog(EgglogError::ExpectFail(..))
        ));
        assert_eq!(graph.trace.as_ref().unwrap().events().len(), before);
    }

    #[test]
    fn clones_share_trace_prefix_and_keep_graph_state_isolated() {
        let mut original =
            DisequalityGraph::new_recording(DisequalityEncoding::DisequalityEdges).unwrap();
        let a = original.add("a", &[]).unwrap();
        let b = original.add("b", &[]).unwrap();
        original.disequal(a, b).unwrap();
        original.rebuild().unwrap();

        let mut clone = original.clone();
        let original_tail = original.trace.as_ref().unwrap().tail.as_ref().unwrap();
        let clone_prefix = clone
            .trace
            .as_ref()
            .unwrap()
            .tail
            .as_ref()
            .unwrap()
            .previous
            .as_ref()
            .unwrap();
        assert!(Rc::ptr_eq(original_tail, clone_prefix));
        clone.union(a, b).unwrap();
        assert!(!graph_is_consistent(&mut clone));
        assert!(graph_is_consistent(&mut original));
    }

    #[test]
    fn source_and_desugared_source_replay() {
        for encoding in ENCODINGS {
            let mut graph = DisequalityGraph::new_recording(encoding).unwrap();
            let a = graph.add("quoted \"name\"", &[]).unwrap();
            let b = graph.add("b", &[]).unwrap();
            let c = graph.add("c", &[]).unwrap();
            graph.union(a, c).unwrap();
            graph.disequal(a, b).unwrap();
            assert_eq!(query_relation(&mut graph, a, c), TestRelation::Equal);
            assert_eq!(query_relation(&mut graph, a, b), TestRelation::Unequal);
            assert!(graph_is_consistent(&mut graph));

            let source = graph.source().unwrap();
            assert!(source.contains("chronological host interaction replay"));
            assert!(source.contains("(check (="));
            assert!(source.contains("(check-known-disequal"));
            assert!(!source.contains("HostWitness"));
            let mut replay = new_experimental_egraph_with_disequality_encoding(encoding);
            replay.parse_and_run_program(None, &source).unwrap();
            if encoding != DisequalityEncoding::DisequalityEdges {
                let mut proof_replay = egglog_experimental::new_experimental_egraph_for_proofs_with_disequality_encoding(encoding)
                    .with_proofs_enabled()
                    .with_proof_testing();
                proof_replay.parse_and_run_program(None, &source).unwrap();
            }

            let desugared = graph.desugared_source().unwrap();
            assert!(!desugared.contains("@disequal "));
            assert!(!desugared.contains("(disequal "));
            let mut replay = EGraph::default();
            replay.parse_and_run_program(None, &desugared).unwrap();
            if encoding != DisequalityEncoding::DisequalityEdges {
                let mut proof_replay = egglog_experimental::new_experimental_egraph_for_proofs_with_disequality_encoding(encoding)
                    .with_proofs_enabled()
                    .with_proof_testing();
                proof_replay
                    .parse_and_run_program(None, &desugared)
                    .unwrap();
            }
        }
    }

    #[test]
    fn expected_failures_render_as_runnable_replays() {
        for encoding in ENCODINGS {
            let mut graph = DisequalityGraph::new_recording(encoding).unwrap();
            let a = graph.add("a", &[]).unwrap();
            let b = graph.add("b", &[]).unwrap();
            assert_eq!(
                query_relation(&mut graph, a, b),
                TestRelation::Indeterminate
            );
            graph.disequal(a, a).unwrap();
            assert!(!graph_is_consistent(&mut graph));

            let source = graph.source().unwrap();
            assert!(source.contains("; host command result: check_failed"));
            assert!(source.contains("; host command result: expect_fail_failed"));
            assert!(source.contains("(fail (check (="));
            assert!(source.contains("(fail (check-known-disequal"));
            let mut replay = new_experimental_egraph_with_disequality_encoding(encoding);
            replay.parse_and_run_program(None, &source).unwrap();

            let desugared = graph.desugared_source().unwrap();
            let mut replay = EGraph::default();
            replay.parse_and_run_program(None, &desugared).unwrap();
        }
    }

    #[test]
    fn direct_language_uses_registered_constructors_and_atoms() {
        for encoding in ENCODINGS {
            let mut schema = LanguageSchemaBuilder::new("TestTerm");
            let x = schema.register_operator("x", None, 0).unwrap();
            let y = schema.register_operator("y", None, 0).unwrap();
            let f = schema.register_operator("f", None, 2).unwrap();
            let template = schema.compile(encoding).unwrap();
            let mut graph = template.new_recording_graph();

            let x_term = graph.add_registered(x, &[]).unwrap();
            let y_term = graph.add_registered(y, &[]).unwrap();
            let fxy = graph.add_registered(f, &[x_term, y_term]).unwrap();
            let fyx = graph.add_registered(f, &[y_term, x_term]).unwrap();
            let fresh = graph.add_atom("@generated.1").unwrap();
            graph.disequal(fxy, fyx).unwrap();
            graph.union(x_term, fresh).unwrap();

            assert!(graph_is_consistent(&mut graph));
            assert_eq!(graph.stats().unwrap().nodes, 5);
            let source = graph.source().unwrap();
            assert!(source.contains("(constructor x () TestTerm)"));
            assert!(source.contains("(constructor f (TestTerm TestTerm) TestTerm)"));
            assert!(source.contains("(let $term4 (Atom \"@generated.1\"))"));
            assert!(source.contains("(let $term2 (f $term0 $term1))"));
            assert!(!source.contains("HostTermAt"));
            assert!(!source.contains("BenchmarkNode"));
            assert!(!source.contains("vec-of"));

            let mut replay = new_experimental_egraph_with_disequality_encoding(encoding);
            replay.parse_and_run_program(None, &source).unwrap();
        }
    }

    #[test]
    fn direct_language_names_overloads_and_escapes_only_when_needed() {
        let mut schema = LanguageSchemaBuilder::new("PropelTerm");
        schema.register_operator("Atom", None, 0).unwrap();
        schema
            .register_operator("@match", Some("Match".to_owned()), 2)
            .unwrap();
        schema
            .register_operator("@match", Some("Match".to_owned()), 3)
            .unwrap();
        schema.register_operator("union", None, 1).unwrap();
        schema.register_operator("+", None, 2).unwrap();
        schema.register_operator("Unit", None, 0).unwrap();
        let template = schema
            .compile(DisequalityEncoding::DisequalityEdges)
            .unwrap();
        let source = template.new_recording_graph().source().unwrap();

        assert!(source.contains("(constructor Atom () PropelTerm)"));
        assert!(source.contains("(constructor HostAtom (String) PropelTerm)"));
        assert!(source.contains("(constructor Match2 (PropelTerm PropelTerm) PropelTerm)"));
        assert!(
            source.contains("(constructor Match3 (PropelTerm PropelTerm PropelTerm) PropelTerm)")
        );
        assert!(source.contains("; source operator \"@match\"/2"));
        assert!(source.contains("(constructor Escaped_union (PropelTerm) PropelTerm)"));
        assert!(source.contains("(constructor Escaped_+ (PropelTerm PropelTerm) PropelTerm)"));
        assert!(source.contains("(constructor Escaped_Unit () PropelTerm)"));
    }

    #[test]
    fn direct_template_clones_are_isolated() {
        let mut schema = LanguageSchemaBuilder::new("Term");
        let x = schema.register_operator("x", None, 0).unwrap();
        let template = schema
            .compile(DisequalityEncoding::DisequalityEdges)
            .unwrap();
        let mut left = template.new_graph();
        let mut right = template.new_graph();
        left.add_registered(x, &[]).unwrap();

        assert_eq!(left.stats().unwrap().nodes, 1);
        assert_eq!(right.stats().unwrap().nodes, 0);
    }

    #[test]
    fn direct_template_supports_concurrent_instantiation() {
        let mut schema = LanguageSchemaBuilder::new("Term");
        let x = schema.register_operator("x", None, 0).unwrap();
        let template = Arc::new(
            schema
                .compile(DisequalityEncoding::DisequalityEdges)
                .unwrap(),
        );
        let workers = (0..4)
            .map(|_| {
                let template = Arc::clone(&template);
                std::thread::spawn(move || {
                    let mut graph = template.new_graph();
                    graph.add_registered(x, &[]).unwrap();
                    assert_eq!(graph.stats().unwrap().nodes, 1);
                })
            })
            .collect::<Vec<_>>();

        for worker in workers {
            worker.join().unwrap();
        }
    }

    #[test]
    fn recording_is_explicit_and_preserves_pending_clone_order() {
        let mut unrecorded = DisequalityGraph::new(DisequalityEncoding::DisequalityEdges).unwrap();
        assert!(matches!(
            unrecorded.source(),
            Err(BackendError::RecordingDisabled)
        ));

        let mut original =
            DisequalityGraph::new_recording(DisequalityEncoding::DisequalityEdges).unwrap();
        let a = original.add("a", &[]).unwrap();
        let b = original.add("b", &[]).unwrap();
        let mut clone = original.clone();
        clone.disequal(a, b).unwrap();
        assert_eq!(query_relation(&mut clone, a, b), TestRelation::Unequal);

        let source = clone.source().unwrap();
        let first_batch = source.find("(let $term0").unwrap();
        let clone_event = source.find("; host graph clone").unwrap();
        let disequality = source.find("(disequal $term0 $term1)").unwrap();
        assert!(first_batch < clone_event && clone_event < disequality);

        let mut replay = new_experimental_egraph_with_disequality_encoding(
            DisequalityEncoding::DisequalityEdges,
        );
        replay.parse_and_run_program(None, &source).unwrap();
    }

    #[test]
    fn recorded_shared_dags_render_in_linear_space() {
        let mut graph =
            DisequalityGraph::new_recording(DisequalityEncoding::NegatedEqualityEmbedding).unwrap();
        let root = graph.add("leaf", &[]).unwrap();
        let mut term = root;
        for _ in 0..128 {
            term = graph.add("dup", &[term, term]).unwrap();
        }
        graph.disequal(root, term).unwrap();

        let source = graph.source().unwrap();
        assert_eq!(source.matches("(let $term").count(), 129);
        assert!(source.contains("(vec-of $term127 $term127)"));
        assert!(
            source.len() < 20_000,
            "recorded source was {} bytes",
            source.len()
        );
    }

    #[test]
    fn c_abi_exposes_structured_query_statuses_and_owned_source() {
        // SAFETY: Every pointer in this test is created and freed exactly once
        // through this module's C ABI.
        unsafe {
            let graph = egglog_disequality_graph_new(2, 1);
            assert!(!graph.is_null());
            let a_name = CString::new("a").unwrap();
            let b_name = CString::new("b").unwrap();
            let a = egglog_disequality_add(graph, a_name.as_ptr(), ptr::null(), 0);
            let b = egglog_disequality_add(graph, b_name.as_ptr(), ptr::null(), 0);

            let equality = egglog_disequality_check_equal(graph, a, b);
            assert_eq!(
                egglog_command_result_status(equality),
                AbiCommandStatus::CheckFailed as i32
            );
            assert_eq!(egglog_command_result_output_count(equality), 0);
            egglog_command_result_free(equality);

            let unknown = egglog_disequality_check_known_disequal(graph, a, b);
            assert_eq!(
                egglog_command_result_status(unknown),
                AbiCommandStatus::ExpectFailFailed as i32
            );
            egglog_command_result_free(unknown);

            assert_eq!(egglog_disequality_disunion(graph, a, b), 0);
            let unequal = egglog_disequality_check_known_disequal(graph, a, b);
            assert_eq!(
                egglog_command_result_status(unequal),
                AbiCommandStatus::Success as i32
            );
            egglog_command_result_free(unequal);

            let consistent = egglog_disequality_check_consistency(graph);
            assert_eq!(
                egglog_command_result_status(consistent),
                AbiCommandStatus::ExpectFailFailed as i32
            );
            egglog_command_result_free(consistent);

            let source = egglog_disequality_source(graph);
            assert!(!source.is_null());
            let data = egglog_owned_string_data(source);
            assert!(!data.is_null());
            let rendered = CStr::from_ptr(data).to_str().unwrap();
            assert_eq!(egglog_owned_string_len(source), rendered.len());
            assert!(rendered.contains("check-known-disequal"));
            egglog_owned_string_free(source);
            egglog_disequality_graph_free(graph);
        }
    }

    #[test]
    fn c_abi_preserves_output_order_and_contains_errors_and_panics() {
        // SAFETY: Every pointer in this test is created and freed exactly once
        // through this module's C ABI.
        unsafe {
            let graph = egglog_disequality_graph_new(0, 0);
            assert!(!graph.is_null());
            let outputs = ffi_command_call(graph, |_| {
                Ok(CommandResult {
                    status: CommandStatus::Success,
                    outputs: vec![
                        CommandOutput::PrintFunctionSize(7),
                        CommandOutput::PrintAllFunctionsSize(vec![("f".to_owned(), 3)]),
                    ],
                })
            });
            assert_eq!(egglog_command_result_output_count(outputs), 2);
            assert_eq!(
                egglog_command_result_output_kind(outputs, 0),
                AbiOutputKind::PrintFunctionSize as i32
            );
            assert_eq!(
                egglog_command_result_output_kind(outputs, 1),
                AbiOutputKind::PrintAllFunctionsSize as i32
            );
            assert!(!egglog_command_result_output_text(outputs, 0).is_null());
            assert!(!egglog_command_result_output_text(outputs, 1).is_null());
            egglog_command_result_free(outputs);

            let invalid = egglog_disequality_check_equal(graph, 0, 1);
            assert_eq!(
                egglog_command_result_status(invalid),
                AbiCommandStatus::Error as i32
            );
            assert!(
                CStr::from_ptr(egglog_command_result_error(invalid))
                    .to_str()
                    .unwrap()
                    .contains("does not exist")
            );
            egglog_command_result_free(invalid);

            let panicked = ffi_command_call(graph, |_| panic!("injected FFI panic"));
            assert_eq!(
                egglog_command_result_status(panicked),
                AbiCommandStatus::Error as i32
            );
            assert!(
                CStr::from_ptr(egglog_command_result_error(panicked))
                    .to_str()
                    .unwrap()
                    .contains("injected FFI panic")
            );
            egglog_command_result_free(panicked);
            egglog_disequality_graph_free(graph);

            assert_eq!(
                egglog_command_result_status(ptr::null()),
                AbiCommandStatus::Error as i32
            );
            assert_eq!(egglog_command_result_output_count(ptr::null()), 0);
            assert_eq!(egglog_command_result_output_kind(ptr::null(), 0), -1);
            assert!(egglog_command_result_output_text(ptr::null(), 0).is_null());
            assert_eq!(egglog_owned_string_len(ptr::null()), 0);
            assert!(egglog_owned_string_data(ptr::null()).is_null());
            egglog_command_result_free(ptr::null_mut());
            egglog_owned_string_free(ptr::null_mut());
        }
    }
}

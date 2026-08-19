use egglog_experimental::{
    DisequalityComparison, DisequalityEncoding, EGraph, Error as EgglogError,
    ast::{Expr, sanitize_internal_names},
    compare_disequality, disequalities_are_consistent,
    new_experimental_egraph_with_disequality_encoding,
};
use std::{
    collections::{HashMap, HashSet},
    ffi::{CStr, CString, c_char},
    fmt::Write as _,
    fs,
    panic::{AssertUnwindSafe, catch_unwind},
    path::Path,
    ptr, slice,
    sync::{Arc, Mutex},
};
use thiserror::Error;

const LANGUAGE_PRELUDE: &str = r#"; Generic host language used by the disequality case studies.
(sort BenchmarkTerm)
(sort BenchmarkTerms (Vec BenchmarkTerm))
(constructor BenchmarkNode (String BenchmarkTerms) BenchmarkTerm)
(constructor BenchmarkWitness (i64) BenchmarkTerm)
"#;

const TERM_LOOKUP_DECLARATION: &str = "(function BenchmarkTermAt (i64) BenchmarkTerm :merge old)\n";

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
    source_prelude: String,
    runtime_prelude: String,
    atom_name: String,
    witness_name: String,
    lookup_name: String,
    operators: Vec<DirectOperator>,
}

#[derive(Clone, Debug)]
enum HostLanguage {
    Vec,
    Direct(DirectLanguage),
}

impl HostLanguage {
    fn source_prelude(&self) -> &str {
        match self {
            HostLanguage::Vec => LANGUAGE_PRELUDE,
            HostLanguage::Direct(language) => &language.source_prelude,
        }
    }

    fn runtime_prelude(&self) -> String {
        match self {
            HostLanguage::Vec => format!("{LANGUAGE_PRELUDE}{TERM_LOOKUP_DECLARATION}"),
            HostLanguage::Direct(language) => language.runtime_prelude.clone(),
        }
    }

    fn lookup_name(&self) -> &str {
        match self {
            HostLanguage::Vec => "BenchmarkTermAt",
            HostLanguage::Direct(language) => &language.lookup_name,
        }
    }

    fn witness_name(&self) -> &str {
        match self {
            HostLanguage::Vec => "BenchmarkWitness",
            HostLanguage::Direct(language) => &language.witness_name,
        }
    }
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
    #[error(transparent)]
    Io(#[from] std::io::Error),
    #[error("{0}")]
    Other(String),
}

#[derive(Clone, Debug)]
enum Operation {
    AddGeneric {
        id: TermId,
        operator: String,
        children: Vec<TermId>,
    },
    AddAtom {
        id: TermId,
        name: String,
    },
    AddRegistered {
        id: TermId,
        operator: OperatorId,
        children: Vec<TermId>,
    },
    Union(TermId, TermId),
    Disequal(TermId, TermId),
}

#[derive(Clone, Copy)]
enum RenderMode {
    Runtime {
        first_pending_id: Option<TermId>,
    },
    Replay {
        equality_witness: Option<(TermId, TermId)>,
    },
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
    let witness_name = unique_name("HostWitness".to_owned(), &mut used_names, egraph);
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

    let mut source_prelude =
        String::from("; Direct host language generated from source declarations.\n");
    if sort_name != schema.sort_name {
        writeln!(
            source_prelude,
            "; source sort {}",
            serde_json::to_string(&schema.sort_name)
                .map_err(|error| BackendError::Other(error.to_string()))?
        )
        .expect("writing to a String cannot fail");
    }
    writeln!(source_prelude, "(sort {sort_name})").expect("writing to a String cannot fail");
    writeln!(
        source_prelude,
        "(constructor {atom_name} (String) {sort_name})"
    )
    .expect("writing to a String cannot fail");
    for operator in &operators {
        if operator.egglog_name != operator.source_name {
            writeln!(
                source_prelude,
                "; source operator {}/{}",
                serde_json::to_string(&operator.source_name)
                    .map_err(|error| BackendError::Other(error.to_string()))?,
                operator.arity
            )
            .expect("writing to a String cannot fail");
        }
        let inputs = std::iter::repeat_n(sort_name.as_str(), operator.arity)
            .collect::<Vec<_>>()
            .join(" ");
        writeln!(
            source_prelude,
            "(constructor {} ({inputs}) {sort_name})",
            operator.egglog_name
        )
        .expect("writing to a String cannot fail");
    }
    writeln!(
        source_prelude,
        "(constructor {witness_name} (i64) {sort_name})"
    )
    .expect("writing to a String cannot fail");

    let runtime_prelude =
        format!("{source_prelude}(function {lookup_name} (i64) {sort_name} :merge old)\n");
    Ok(DirectLanguage {
        source_prelude,
        runtime_prelude,
        atom_name,
        witness_name,
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
        egraph.parse_and_run_program(
            Some("benchmark-prelude.egg".to_owned()),
            &language.runtime_prelude(),
        )?;
        Ok(Self {
            encoding,
            language: Arc::new(language),
            egraph,
            execution_lock: Arc::new(Mutex::new(())),
        })
    }

    pub fn new_graph(&self) -> DisequalityGraph {
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
            committed: Vec::new(),
        }
    }
}

pub struct DisequalityGraph {
    encoding: DisequalityEncoding,
    language: Arc<HostLanguage>,
    egraph: EGraph,
    execution_lock: Arc<Mutex<()>>,
    next_term: TermId,
    pending: Vec<Operation>,
    committed: Vec<Arc<[Operation]>>,
}

impl Clone for DisequalityGraph {
    fn clone(&self) -> Self {
        let execution_lock = Arc::clone(&self.execution_lock);
        let _guard = execution_lock
            .lock()
            .expect("graph execution lock was poisoned");
        Self {
            encoding: self.encoding,
            language: Arc::clone(&self.language),
            egraph: self.egraph.clone(),
            execution_lock: Arc::clone(&self.execution_lock),
            next_term: self.next_term,
            pending: self.pending.clone(),
            committed: self.committed.clone(),
        }
    }
}

impl DisequalityGraph {
    pub fn new(encoding: DisequalityEncoding) -> Result<Self, BackendError> {
        let mut egraph = new_experimental_egraph_with_disequality_encoding(encoding);
        let language = Arc::new(HostLanguage::Vec);
        let runtime_prelude = language.runtime_prelude();
        egraph.parse_and_run_program(Some("benchmark-prelude.egg".to_owned()), &runtime_prelude)?;
        Ok(Self {
            encoding,
            language,
            egraph,
            execution_lock: Arc::new(Mutex::new(())),
            next_term: 0,
            pending: Vec::new(),
            committed: Vec::new(),
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
        let id = self.allocate_term()?;
        self.pending.push(Operation::AddGeneric {
            id,
            operator: operator.into(),
            children: children.to_vec(),
        });
        Ok(id)
    }

    pub fn add_atom(&mut self, name: impl Into<String>) -> Result<TermId, BackendError> {
        if !matches!(&*self.language, HostLanguage::Direct(_)) {
            return Err(BackendError::Other(
                "atom insertion requires the direct term language".to_owned(),
            ));
        }
        let id = self.allocate_term()?;
        self.pending.push(Operation::AddAtom {
            id,
            name: name.into(),
        });
        Ok(id)
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
        let id = self.allocate_term()?;
        self.pending.push(Operation::AddRegistered {
            id,
            operator,
            children: children.to_vec(),
        });
        Ok(id)
    }

    pub fn union(&mut self, lhs: TermId, rhs: TermId) -> Result<(), BackendError> {
        self.validate_pair(lhs, rhs)?;
        self.pending.push(Operation::Union(lhs, rhs));
        Ok(())
    }

    pub fn disequal(&mut self, lhs: TermId, rhs: TermId) -> Result<(), BackendError> {
        self.validate_pair(lhs, rhs)?;
        self.pending.push(Operation::Disequal(lhs, rhs));
        Ok(())
    }

    pub fn rebuild(&mut self) -> Result<(), BackendError> {
        let execution_lock = Arc::clone(&self.execution_lock);
        let _guard = execution_lock
            .lock()
            .expect("graph execution lock was poisoned");
        self.flush_unlocked()
    }

    pub fn compare(
        &mut self,
        lhs: TermId,
        rhs: TermId,
    ) -> Result<DisequalityComparison, BackendError> {
        self.validate_pair(lhs, rhs)?;
        let execution_lock = Arc::clone(&self.execution_lock);
        let _guard = execution_lock
            .lock()
            .expect("graph execution lock was poisoned");
        self.flush_unlocked()?;
        let lhs = self.term_expr(lhs)?;
        let rhs = self.term_expr(rhs)?;
        Ok(compare_disequality(
            &mut self.egraph,
            self.encoding,
            lhs,
            rhs,
        )?)
    }

    pub fn is_consistent(&mut self) -> Result<bool, BackendError> {
        let execution_lock = Arc::clone(&self.execution_lock);
        let _guard = execution_lock
            .lock()
            .expect("graph execution lock was poisoned");
        self.flush_unlocked()?;
        Ok(disequalities_are_consistent(&mut self.egraph)?)
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
        Ok(GraphStats {
            nodes,
            classes: classes.len(),
            extension_rows,
            total_tuples: self.egraph.num_tuples(),
        })
    }

    pub fn source(&mut self) -> Result<String, BackendError> {
        let execution_lock = Arc::clone(&self.execution_lock);
        let _guard = execution_lock
            .lock()
            .expect("graph execution lock was poisoned");
        self.flush_unlocked()?;
        let mut source = self.language.source_prelude().to_owned();
        let operations = self
            .committed
            .iter()
            .flat_map(|batch| batch.iter())
            .collect::<Vec<_>>();
        if !operations.is_empty() {
            source.push('\n');
            let equality_witness = operations.iter().find_map(|operation| match operation {
                Operation::Union(lhs, rhs) => Some((*lhs, *rhs)),
                Operation::AddGeneric { .. }
                | Operation::AddAtom { .. }
                | Operation::AddRegistered { .. }
                | Operation::Disequal(_, _) => None,
            });
            source.push_str(&render_operations(
                &self.language,
                operations.iter().copied(),
                RenderMode::Replay { equality_witness },
            )?);
            if equality_witness.is_some() {
                writeln!(
                    source,
                    "\n; Recheck one explicit host union as an equality proof witness.\n(check (= ({} 0) ({} 1)))",
                    self.language.witness_name(),
                    self.language.witness_name()
                )
                .expect("writing to a String cannot fail");
            }
        }
        Ok(source)
    }

    pub fn desugared_source(&mut self) -> Result<String, BackendError> {
        let source = self.source()?;
        desugar_source(self.encoding, &source)
    }

    pub fn write_source(&mut self, path: impl AsRef<Path>) -> Result<(), BackendError> {
        fs::write(path, self.source()?)?;
        Ok(())
    }

    pub fn write_desugared_source(&mut self, path: impl AsRef<Path>) -> Result<(), BackendError> {
        fs::write(path, self.desugared_source()?)?;
        Ok(())
    }

    pub fn write_snapshot(
        &mut self,
        source_path: impl AsRef<Path>,
        desugared_path: impl AsRef<Path>,
    ) -> Result<(), BackendError> {
        let consistent = self.is_consistent()?;
        let mut source = self.source()?;
        source.push_str("\n; The command below records the expected graph consistency.\n");
        if consistent {
            source.push_str("(check-disequalities)\n");
        } else {
            source.push_str("(fail (check-disequalities))\n");
        }
        fs::write(source_path, &source)?;
        fs::write(desugared_path, desugar_source(self.encoding, &source)?)?;
        Ok(())
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
        self.next_term = self
            .next_term
            .checked_add(1)
            .ok_or_else(|| BackendError::Other("term handle space exhausted".to_owned()))?;
        Ok(id)
    }

    fn validate_pair(&self, lhs: TermId, rhs: TermId) -> Result<(), BackendError> {
        self.validate_term(lhs)?;
        self.validate_term(rhs)
    }

    fn term_expr(&mut self, id: TermId) -> Result<Expr, BackendError> {
        let lookup_name = self.language.lookup_name();
        Ok(self
            .egraph
            .parser
            .get_expr_from_string(None, &format!("({lookup_name} {id})"))
            .map_err(EgglogError::from)?)
    }

    fn flush_unlocked(&mut self) -> Result<(), BackendError> {
        if self.pending.is_empty() {
            return Ok(());
        }

        let first_pending_id = self.pending.iter().find_map(|operation| match operation {
            Operation::AddGeneric { id, .. }
            | Operation::AddAtom { id, .. }
            | Operation::AddRegistered { id, .. } => Some(*id),
            Operation::Union(_, _) | Operation::Disequal(_, _) => None,
        });
        let batch = render_operations(
            &self.language,
            self.pending.iter(),
            RenderMode::Runtime { first_pending_id },
        )?;
        self.egraph
            .parse_and_run_program(Some("benchmark-batch.egg".to_owned()), &batch)?;
        self.committed
            .push(std::mem::take(&mut self.pending).into());
        Ok(())
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

fn render_operations<'a>(
    language: &HostLanguage,
    operations: impl IntoIterator<Item = &'a Operation>,
    mode: RenderMode,
) -> Result<String, BackendError> {
    let term_reference = |id: TermId| match mode {
        RenderMode::Runtime { first_pending_id }
            if first_pending_id.is_none_or(|first| id < first) =>
        {
            format!("({} {id})", language.lookup_name())
        }
        RenderMode::Runtime { .. } | RenderMode::Replay { .. } => format!("term{id}"),
    };
    let render_runtime_lookup = |batch: &mut String, id: TermId| {
        if matches!(mode, RenderMode::Runtime { .. }) {
            writeln!(batch, "  (set ({} {id}) term{id})", language.lookup_name())
                .expect("writing to a String cannot fail");
        }
    };
    let mut batch = String::from("(begin\n");
    for operation in operations {
        match operation {
            Operation::AddGeneric {
                id,
                operator,
                children,
            } => {
                let operator = serde_json::to_string(operator)
                    .map_err(|error| BackendError::Other(error.to_string()))?;
                let children = children
                    .iter()
                    .map(|&child| term_reference(child))
                    .collect::<Vec<_>>()
                    .join(" ");
                writeln!(
                    batch,
                    "  (let term{id} (BenchmarkNode {operator} (vec-of{separator}{children})))",
                    separator = if children.is_empty() { "" } else { " " },
                )
                .expect("writing to a String cannot fail");
                render_runtime_lookup(&mut batch, *id);
            }
            Operation::AddAtom { id, name } => {
                let HostLanguage::Direct(language) = language else {
                    return Err(BackendError::Other(
                        "direct atom appeared in a Vec operation stream".to_owned(),
                    ));
                };
                let name = serde_json::to_string(name)
                    .map_err(|error| BackendError::Other(error.to_string()))?;
                writeln!(batch, "  (let term{id} ({} {name}))", language.atom_name)
                    .expect("writing to a String cannot fail");
                render_runtime_lookup(&mut batch, *id);
            }
            Operation::AddRegistered {
                id,
                operator,
                children,
            } => {
                let HostLanguage::Direct(language) = language else {
                    return Err(BackendError::Other(
                        "registered constructor appeared in a Vec operation stream".to_owned(),
                    ));
                };
                let declaration = language.operators.get(*operator as usize).ok_or_else(|| {
                    BackendError::Other(format!("unknown operator id {operator}"))
                })?;
                let children = children
                    .iter()
                    .map(|&child| term_reference(child))
                    .collect::<Vec<_>>()
                    .join(" ");
                writeln!(
                    batch,
                    "  (let term{id} ({}{separator}{children}))",
                    declaration.egglog_name,
                    separator = if children.is_empty() { "" } else { " " },
                )
                .expect("writing to a String cannot fail");
                render_runtime_lookup(&mut batch, *id);
            }
            Operation::Union(lhs, rhs) => {
                writeln!(
                    batch,
                    "  (union {} {})",
                    term_reference(*lhs),
                    term_reference(*rhs)
                )
                .expect("writing to a String cannot fail");
            }
            Operation::Disequal(lhs, rhs) => {
                writeln!(
                    batch,
                    "  (disequal {} {})",
                    term_reference(*lhs),
                    term_reference(*rhs)
                )
                .expect("writing to a String cannot fail");
            }
        }
    }
    if let RenderMode::Replay {
        equality_witness: Some((lhs, rhs)),
    } = mode
    {
        writeln!(batch, "  (union term{lhs} ({} 0))", language.witness_name())
            .expect("writing to a String cannot fail");
        writeln!(batch, "  (union term{rhs} ({} 1))", language.witness_name())
            .expect("writing to a String cannot fail");
    }
    batch.push_str(")\n");
    Ok(batch)
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

#[unsafe(no_mangle)]
pub extern "C" fn egglog_disequality_graph_new(encoding: u32) -> *mut EgglogDisequalityGraph {
    catch_unwind(AssertUnwindSafe(|| {
        let encoding = encoding_from_abi(encoding).ok()?;
        let graph = DisequalityGraph::new(encoding).ok()?;
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
) -> *mut EgglogDisequalityGraph {
    catch_unwind(AssertUnwindSafe(|| {
        // SAFETY: The caller promises a live, finished template that is not
        // concurrently mutated or freed. Graph creation only reads it.
        let template = unsafe { template.as_ref() }?.template.as_ref()?;
        Some(Box::into_raw(Box::new(EgglogDisequalityGraph::new(
            template.new_graph(),
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
/// Flush queued operations into egglog.
///
/// # Safety
///
/// `graph` must uniquely reference a live graph allocated by this library.
pub unsafe extern "C" fn egglog_disequality_rebuild(graph: *mut EgglogDisequalityGraph) -> i32 {
    ffi_call(graph, -1, |graph| {
        graph.rebuild()?;
        Ok(0)
    })
}

#[unsafe(no_mangle)]
/// Query the known relationship between two handles.
///
/// # Safety
///
/// `graph` must uniquely reference a live graph allocated by this library.
pub unsafe extern "C" fn egglog_disequality_compare(
    graph: *mut EgglogDisequalityGraph,
    lhs: TermId,
    rhs: TermId,
) -> i32 {
    ffi_call(graph, -1, |graph| {
        Ok(match graph.compare(lhs, rhs)? {
            DisequalityComparison::Equal => 0,
            DisequalityComparison::Unequal => 1,
            DisequalityComparison::Indeterminate => 2,
        })
    })
}

#[unsafe(no_mangle)]
/// Check whether the graph's accumulated constraints are consistent.
///
/// # Safety
///
/// `graph` must uniquely reference a live graph allocated by this library.
pub unsafe extern "C" fn egglog_disequality_is_consistent(
    graph: *mut EgglogDisequalityGraph,
) -> i32 {
    ffi_call(graph, -1, |graph| Ok(i32::from(graph.is_consistent()?)))
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

unsafe fn ffi_path(path: *const c_char) -> Result<String, BackendError> {
    if path.is_null() {
        return Err(BackendError::NullPointer("path"));
    }
    // SAFETY: The caller provides a NUL-terminated path string.
    Ok(unsafe { CStr::from_ptr(path) }
        .to_str()
        .map_err(|_| BackendError::InvalidUtf8("path"))?
        .to_owned())
}

#[unsafe(no_mangle)]
/// Write replayable source for a graph.
///
/// # Safety
///
/// `graph` must uniquely reference a live graph and `path` must point to a
/// NUL-terminated UTF-8 string.
pub unsafe extern "C" fn egglog_disequality_write_source(
    graph: *mut EgglogDisequalityGraph,
    path: *const c_char,
) -> i32 {
    ffi_call(graph, -1, |graph| {
        // SAFETY: The C ABI contract requires a valid path pointer.
        graph.write_source(unsafe { ffi_path(path) }?)?;
        Ok(0)
    })
}

#[unsafe(no_mangle)]
/// Write fully desugared replayable source for a graph.
///
/// # Safety
///
/// `graph` must uniquely reference a live graph and `path` must point to a
/// NUL-terminated UTF-8 string.
pub unsafe extern "C" fn egglog_disequality_write_desugared(
    graph: *mut EgglogDisequalityGraph,
    path: *const c_char,
) -> i32 {
    ffi_call(graph, -1, |graph| {
        // SAFETY: The C ABI contract requires a valid path pointer.
        graph.write_desugared_source(unsafe { ffi_path(path) }?)?;
        Ok(0)
    })
}

#[unsafe(no_mangle)]
/// Write raw and fully desugared consistency-annotated snapshots.
///
/// # Safety
///
/// `graph` must uniquely reference a live graph. Both paths must point to
/// NUL-terminated UTF-8 strings.
pub unsafe extern "C" fn egglog_disequality_write_snapshot(
    graph: *mut EgglogDisequalityGraph,
    source_path: *const c_char,
    desugared_path: *const c_char,
) -> i32 {
    ffi_call(graph, -1, |graph| {
        // SAFETY: The C ABI contract requires valid path pointers.
        let source_path = unsafe { ffi_path(source_path) }?;
        let desugared_path = unsafe { ffi_path(desugared_path) }?;
        graph.write_snapshot(source_path, desugared_path)?;
        Ok(0)
    })
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

    #[test]
    fn all_encodings_support_batched_host_operations() {
        for encoding in ENCODINGS {
            let mut graph = DisequalityGraph::new(encoding).unwrap();
            let a = graph.add("a", &[]).unwrap();
            let b = graph.add("b", &[]).unwrap();
            let fa = graph.add("f", &[a]).unwrap();
            let fb = graph.add("f", &[b]).unwrap();
            graph.disequal(fa, fb).unwrap();

            assert_eq!(
                graph.compare(fa, fb).unwrap(),
                DisequalityComparison::Unequal
            );
            assert_eq!(
                graph.compare(a, b).unwrap(),
                DisequalityComparison::Indeterminate
            );
            assert!(graph.is_consistent().unwrap());
            assert_eq!(graph.stats().unwrap().nodes, 4);

            let c = graph.add("c", &[]).unwrap();
            let d = graph.add("d", &[]).unwrap();
            graph.union(a, b).unwrap();
            assert!(!graph.is_consistent().unwrap());
            assert_eq!(
                graph.compare(c, d).unwrap(),
                DisequalityComparison::Indeterminate,
                "pair queries must remain independent of an unrelated contradiction"
            );
        }
    }

    #[test]
    fn clones_keep_pending_and_committed_state_isolated() {
        let mut original = DisequalityGraph::new(DisequalityEncoding::DisequalityEdges).unwrap();
        let a = original.add("a", &[]).unwrap();
        let b = original.add("b", &[]).unwrap();
        original.disequal(a, b).unwrap();
        original.rebuild().unwrap();

        let mut clone = original.clone();
        assert!(Arc::ptr_eq(&original.committed[0], &clone.committed[0]));
        clone.union(a, b).unwrap();
        assert!(!clone.is_consistent().unwrap());
        assert!(original.is_consistent().unwrap());
    }

    #[test]
    fn source_and_desugared_source_replay() {
        for encoding in ENCODINGS {
            let mut graph = DisequalityGraph::new(encoding).unwrap();
            let a = graph.add("quoted \"name\"", &[]).unwrap();
            let b = graph.add("b", &[]).unwrap();
            let c = graph.add("c", &[]).unwrap();
            graph.union(a, c).unwrap();
            graph.disequal(a, b).unwrap();

            let source = graph.source().unwrap();
            assert!(source.contains("Recheck one explicit host union"));
            assert!(source.contains("(check (="));
            let mut replay = new_experimental_egraph_with_disequality_encoding(encoding);
            replay.parse_and_run_program(None, &source).unwrap();

            let desugared = graph.desugared_source().unwrap();
            assert!(!desugared.contains("@disequal "));
            assert!(!desugared.contains("(disequal "));
            let mut replay = new_experimental_egraph_with_disequality_encoding(encoding);
            replay.parse_and_run_program(None, &desugared).unwrap();
        }
    }

    #[test]
    fn consistency_annotated_snapshots_replay() {
        for encoding in ENCODINGS {
            let directory = tempfile::tempdir().unwrap();
            let source_path = directory.path().join("graph.egg");
            let desugared_path = directory.path().join("graph.desugared.egg");
            let mut graph = DisequalityGraph::new(encoding).unwrap();
            let a = graph.add("a", &[]).unwrap();
            graph.disequal(a, a).unwrap();
            graph.write_snapshot(&source_path, &desugared_path).unwrap();

            for path in [source_path, desugared_path] {
                let source = fs::read_to_string(&path).unwrap();
                let mut replay = new_experimental_egraph_with_disequality_encoding(encoding);
                replay.parse_and_run_program(None, &source).unwrap();
            }
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
            let mut graph = template.new_graph();

            let x_term = graph.add_registered(x, &[]).unwrap();
            let y_term = graph.add_registered(y, &[]).unwrap();
            let fxy = graph.add_registered(f, &[x_term, y_term]).unwrap();
            let fyx = graph.add_registered(f, &[y_term, x_term]).unwrap();
            let fresh = graph.add_atom("@generated.1").unwrap();
            graph.disequal(fxy, fyx).unwrap();
            graph.union(x_term, fresh).unwrap();

            assert!(graph.is_consistent().unwrap());
            assert_eq!(graph.stats().unwrap().nodes, 5);
            let source = graph.source().unwrap();
            assert!(source.contains("(constructor x () TestTerm)"));
            assert!(source.contains("(constructor f (TestTerm TestTerm) TestTerm)"));
            assert!(source.contains("(let term4 (Atom \"@generated.1\"))"));
            assert!(source.contains("(let term2 (f term0 term1))"));
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
        let source = template.new_graph().source().unwrap();

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
}

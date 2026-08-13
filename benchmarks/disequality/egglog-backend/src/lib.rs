use egglog_experimental::{
    DisequalityComparison, DisequalityEncoding, EGraph, Error as EgglogError,
    ast::{Expr, sanitize_internal_names},
    compare_disequality, disequalities_are_consistent,
    new_experimental_egraph_with_disequality_encoding,
};
use std::{
    collections::HashSet,
    ffi::{CStr, CString, c_char},
    fmt::Write as _,
    fs,
    panic::{AssertUnwindSafe, catch_unwind},
    path::Path,
    ptr, slice,
};
use thiserror::Error;

const PRELUDE: &str = r#"; Generic host language used by the disequality case studies.
(sort BenchmarkTerm)
(sort BenchmarkTerms (Vec BenchmarkTerm))
(constructor BenchmarkNode (String BenchmarkTerms) BenchmarkTerm)
(function BenchmarkTermAt (i64) BenchmarkTerm :no-merge)
"#;

pub type TermId = u64;

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
    #[error("operator name contains a NUL byte")]
    OperatorContainsNul,
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
    Add {
        id: TermId,
        operator: String,
        children: Vec<TermId>,
    },
    Union(TermId, TermId),
    Disequal(TermId, TermId),
}

#[derive(Clone)]
pub struct DisequalityGraph {
    encoding: DisequalityEncoding,
    egraph: EGraph,
    next_term: TermId,
    pending: Vec<Operation>,
    batches: Vec<String>,
}

impl DisequalityGraph {
    pub fn new(encoding: DisequalityEncoding) -> Result<Self, BackendError> {
        let mut egraph = new_experimental_egraph_with_disequality_encoding(encoding);
        egraph.parse_and_run_program(Some("benchmark-prelude.egg".to_owned()), PRELUDE)?;
        Ok(Self {
            encoding,
            egraph,
            next_term: 0,
            pending: Vec::new(),
            batches: Vec::new(),
        })
    }

    pub fn add(
        &mut self,
        operator: impl Into<String>,
        children: &[TermId],
    ) -> Result<TermId, BackendError> {
        for &child in children {
            self.validate_term(child)?;
        }
        let id = self.next_term;
        self.next_term = self
            .next_term
            .checked_add(1)
            .ok_or_else(|| BackendError::Other("term handle space exhausted".to_owned()))?;
        self.pending.push(Operation::Add {
            id,
            operator: operator.into(),
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
        self.flush()
    }

    pub fn compare(
        &mut self,
        lhs: TermId,
        rhs: TermId,
    ) -> Result<DisequalityComparison, BackendError> {
        self.validate_pair(lhs, rhs)?;
        self.flush()?;
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
        self.flush()?;
        Ok(disequalities_are_consistent(&mut self.egraph)?)
    }

    pub fn stats(&mut self) -> Result<GraphStats, BackendError> {
        self.flush()?;
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
        Ok(GraphStats {
            nodes: self.egraph.get_size("BenchmarkNode"),
            classes: classes.len(),
            extension_rows,
            total_tuples: self.egraph.num_tuples(),
        })
    }

    pub fn source(&mut self) -> Result<String, BackendError> {
        self.flush()?;
        let mut source = String::from(PRELUDE);
        for batch in &self.batches {
            source.push('\n');
            source.push_str(batch);
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

    fn validate_pair(&self, lhs: TermId, rhs: TermId) -> Result<(), BackendError> {
        self.validate_term(lhs)?;
        self.validate_term(rhs)
    }

    fn term_expr(&mut self, id: TermId) -> Result<Expr, BackendError> {
        Ok(self
            .egraph
            .parser
            .get_expr_from_string(None, &format!("(BenchmarkTermAt {id})"))
            .map_err(EgglogError::from)?)
    }

    fn flush(&mut self) -> Result<(), BackendError> {
        if self.pending.is_empty() {
            return Ok(());
        }

        let first_pending_id = self.pending.iter().find_map(|operation| match operation {
            Operation::Add { id, .. } => Some(*id),
            Operation::Union(_, _) | Operation::Disequal(_, _) => None,
        });
        let mut batch = String::from("(begin\n");
        for operation in &self.pending {
            match operation {
                Operation::Add {
                    id,
                    operator,
                    children,
                } => {
                    let operator = serde_json::to_string(operator)
                        .map_err(|error| BackendError::Other(error.to_string()))?;
                    let children = children
                        .iter()
                        .map(|&child| term_reference(child, first_pending_id))
                        .collect::<Vec<_>>()
                        .join(" ");
                    writeln!(
                        batch,
                        "  (let term{id} (BenchmarkNode {operator} (vec-of{separator}{children})))",
                        separator = if children.is_empty() { "" } else { " " },
                    )
                    .expect("writing to a String cannot fail");
                    writeln!(batch, "  (set (BenchmarkTermAt {id}) term{id})")
                        .expect("writing to a String cannot fail");
                }
                Operation::Union(lhs, rhs) => {
                    writeln!(
                        batch,
                        "  (union {} {})",
                        term_reference(*lhs, first_pending_id),
                        term_reference(*rhs, first_pending_id)
                    )
                    .expect("writing to a String cannot fail");
                }
                Operation::Disequal(lhs, rhs) => {
                    writeln!(
                        batch,
                        "  (disequal {} {})",
                        term_reference(*lhs, first_pending_id),
                        term_reference(*rhs, first_pending_id)
                    )
                    .expect("writing to a String cannot fail");
                }
            }
        }
        batch.push_str(")\n");
        self.egraph
            .parse_and_run_program(Some("benchmark-batch.egg".to_owned()), &batch)?;
        self.pending.clear();
        self.batches.push(batch);
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

fn term_reference(id: TermId, first_pending_id: Option<TermId>) -> String {
    if first_pending_id.is_some_and(|first| id >= first) {
        format!("term{id}")
    } else {
        format!("(BenchmarkTermAt {id})")
    }
}

#[repr(C)]
pub struct EgglogDisequalityGraph {
    graph: DisequalityGraph,
    last_error: CString,
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
/// Return the number of rows in generated disequality support relations.
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

            graph.union(a, b).unwrap();
            assert!(!graph.is_consistent().unwrap());
        }
    }

    #[test]
    fn clones_keep_pending_and_committed_state_isolated() {
        let mut original = DisequalityGraph::new(DisequalityEncoding::DisequalityEdges).unwrap();
        let a = original.add("a", &[]).unwrap();
        let b = original.add("b", &[]).unwrap();
        original.disequal(a, b).unwrap();

        let mut clone = original.clone();
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
            graph.disequal(a, b).unwrap();

            let source = graph.source().unwrap();
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
}

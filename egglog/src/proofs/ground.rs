//! Construct raw extraction certificates from typed ground terms.
//!
//! Lookup finds view and union-find evidence. The ordinary lifter decodes that
//! evidence before construction, so container witnesses can be identified.
//! A memoized traversal resolves deferred containers and produces raw proofs;
//! the ordinary lifter then reconstructs the completed equality proofs.

use std::iter::once;

use super::ground_evidence::{Proofs, RawEquality};
use super::proof_checker::{gather_global_actions, gather_globals};
use super::proof_container_rebuild::rebuild_container_value_rec;
use super::proof_format::{ProofId, ProofStore, RawProof};
use crate::extract::find_canonical;
use crate::*;

#[derive(Clone, Copy)]
pub(super) enum RowKind {
    /// The row proves `representative = constructor(canonical children)`.
    Constructor,
    /// The row connects a global to its source definition.
    Global,
    /// Project this column from a custom function's row proof.
    Output(usize),
}

/// Existing row evidence and its optional connection to the current leader.
/// `P` is a stored proof value before import and a raw equality afterwards.
#[derive(Clone, Copy)]
pub(super) struct Row<P = Value> {
    pub(super) kind: RowKind,
    /// Proof of this view row's equality.
    pub(super) proof: P,
    /// Existing proof from the view representative to its current leader.
    pub(super) to_leader: Option<P>,
}

/// The lookup result for one node of the input typed DAG.
/// Its position in the returned vector is that node's `TermId`.
pub(super) struct Node<P = Value> {
    /// Canonical at the input node's sort, including nested container elements.
    pub(super) value: Value,
    /// Absent for literals, primitives, and globals without a proof-bearing view.
    /// Having a value alone does not establish a container's existence.
    pub(super) row: Option<Row<P>>,
}

pub(super) fn fail(message: impl Into<String>) -> Error {
    Error::ExtractError(message.into())
}

/// Reject container roots, including containers whose values have stored evidence.
fn require_non_container_root(sort: &ArcSort) -> Result<(), Error> {
    if sort.is_container_sort() {
        Err(fail(format!(
            "proof extraction does not support container roots (sort {})",
            sort.name()
        )))
    } else {
        Ok(())
    }
}

/// Append an expression to `dag`, representing globals as zero-argument calls.
/// Errors if the expression contains a local variable.
fn ground_expr(dag: &mut TermDag, root: &ResolvedExpr) -> Result<TermId, Error> {
    let mut pending = vec![(root, false)];
    let mut values = Vec::new();
    while let Some((expr, visited)) = pending.pop() {
        match expr {
            ResolvedExpr::Lit(_, literal) => values.push(dag.lit(literal.clone())),
            ResolvedExpr::Var(_, var) if var.is_global_ref => {
                values.push(dag.app(var.name.clone(), vec![]));
            }
            ResolvedExpr::Var(_, var) => {
                return Err(fail(format!("unbound ground variable {}", var.name)));
            }
            ResolvedExpr::Call(_, call, children) if visited => {
                let children = values.split_off(values.len() - children.len());
                values.push(dag.app(call.name().to_owned(), children));
            }
            ResolvedExpr::Call(_, _, children) => {
                pending.push((expr, true));
                pending.extend(children.iter().rev().map(|child| (child, false)));
            }
        }
    }
    Ok(values[0])
}

impl EGraph {
    /// Look up `expr`, extract representatives, and certify each equality.
    /// Returns the extraction output followed by its proofs; adds no e-graph rows.
    pub(crate) fn run_prove_extract(
        &self,
        expr: &ResolvedExpr,
        variants: &ResolvedExpr,
    ) -> Result<Vec<CommandOutput>, Error> {
        let sort = expr.output_type();
        require_non_container_root(&sort)?;
        let value = self.lookup_ground_expr(expr)?;
        let count = self.lookup_ground_expr(variants)?;
        let count: i64 = self.backend.base_values().unwrap(count);
        if count < 0 {
            return Err(fail("cannot extract a negative number of variants"));
        }
        let extraction = self.extract_command(sort.clone(), value, count as usize)?;
        let (mut terms, outputs) = match &extraction {
            CommandOutput::ExtractBest(dag, _, term) => (dag.clone(), vec![*term]),
            CommandOutput::ExtractVariants(dag, terms) => (dag.clone(), terms.clone()),
            _ => unreachable!(),
        };
        let input = ground_expr(&mut terms, expr)?;
        let (proof_store, proof_ids) = self.prove_extracted_terms(&terms, input, &outputs, sort)?;
        Ok(vec![
            extraction,
            CommandOutput::ProveExtract {
                proof_store,
                proof_ids,
            },
        ])
    }

    /// Resolve a ground expression to its canonical runtime value without
    /// inserting rows. Container existence is checked later during certification.
    fn lookup_ground_expr(&self, expr: &ResolvedExpr) -> Result<Value, Error> {
        let mut terms = TermDag::default();
        let root = ground_expr(&mut terms, expr)?;
        let (typed, roots) = self
            .typecheck_term_dag(&terms, &[(root, Some(expr.output_type()))], Context::Read)
            .map_err(|error| fail(error.to_string()))?;
        let values = lookup(self, &typed, &roots)?;
        Ok(values[roots[0]].value)
    }
    /// Prove equality of two existing ground terms without inserting them.
    /// See [`Self::prove_extracted_terms`] for input requirements and errors.
    pub fn prove_equal_terms(
        &self,
        terms: &TermDag,
        left: TermId,
        right: TermId,
        sort: ArcSort,
    ) -> Result<(ProofStore, ProofId), Error> {
        let (store, ids) = self.prove_extracted_terms(terms, left, &[right], sort)?;
        Ok((store, ids[0]))
    }

    /// Prove equality of `input` to each term in `outputs`, in that order.
    /// Root IDs refer to `terms`, and every root must have the supplied `sort`.
    /// Globals are zero-argument calls. Proof endpoints use their source definitions
    /// and the evaluated forms of primitive expressions.
    /// Primitives must support read-only evaluation and proof validation.
    ///
    /// Errors on container roots, invalid or ambiguous typings, unavailable terms
    /// or proof evidence, or unequal roots. Containers may occur below a root.
    /// Performs no extraction and writes no e-graph rows.
    /// An empty `outputs` slice still validates and proves `input` to its leader,
    /// but returns no equality proofs. Duplicate outputs retain their positions.
    ///
    /// # Example
    ///
    /// An extractor may return `F(B)` even though the source only inserted `F(A)`.
    /// Existing evidence for `A = B` and `F(A)` suffices to certify that result.
    ///
    /// ```
    /// use egglog::{EGraph, Error, TermDag};
    ///
    /// let mut graph = EGraph::new_with_proofs();
    /// graph.parse_and_run_program(None, "
    ///     (datatype E (A) (B) (F E))
    ///     (F (A)) (B) (union (A) (B)) (run 1)
    /// ")?;
    /// let mut terms = TermDag::default();
    /// let a = terms.app("A".into(), vec![]);
    /// let b = terms.app("B".into(), vec![]);
    /// let input = terms.app("F".into(), vec![a]);
    /// let output = terms.app("F".into(), vec![b]);
    /// let sort = graph.type_info().get_sort_by_name("E").unwrap().clone();
    /// let (store, proofs) = graph.prove_extracted_terms(&terms, input, &[output], sort)?;
    /// let equality = store.get(proofs[0]);
    /// assert_eq!(store.term_dag().to_string(equality.lhs()), "(F (A))");
    /// assert_eq!(store.term_dag().to_string(equality.rhs()), "(F (B))");
    /// # Ok::<(), Error>(())
    /// ```
    pub fn prove_extracted_terms(
        &self,
        terms: &TermDag,
        input: TermId,
        outputs: &[TermId],
        sort: ArcSort,
    ) -> Result<(ProofStore, Vec<ProofId>), Error> {
        require_non_container_root(&sort)?;
        let roots = once(input)
            .chain(outputs.iter().copied())
            .map(|root| (root, Some(sort.clone())))
            .collect::<Vec<_>>();
        let (typed, roots) = self
            .typecheck_term_dag(terms, &roots, Context::Read)
            .map_err(|error| fail(error.to_string()))?;
        let values = lookup(self, &typed, &roots)?;
        let (mut proofs, nodes) = Proofs::import(self, values)?;
        let globals = gather_globals(&self.proof_check_program, &mut proofs.raw.term_dag)
            .map_err(|error| fail(error.to_string()))?;
        let mut builder = GroundProofs {
            terms: &typed,
            nodes: &nodes,
            proofs,
            globals,
            memo: vec![None; typed.size()],
        };
        let input = builder.finish(roots[0], None)?;
        let mut raw_proofs = vec![input.proof];
        for &id in &roots[1..] {
            let right = builder.finish(id, None)?;
            let back = builder.proofs.sym(right);
            raw_proofs.push(builder.proofs.trans(input, back).proof);
        }
        let (mut store, mut proof_ids) =
            builder.proofs.lift(&self.proof_check_program, &raw_proofs);
        proof_ids.remove(0);
        let mut proofs = Vec::with_capacity(outputs.len());
        let mut simplified = Default::default();
        for proof in proof_ids {
            let expected = store.get(proof).proposition().clone();
            if self.proof_state.verify_proofs {
                store
                    .check_proof(proof, &self.proof_check_program)
                    .map_err(|error| fail(format!("invalid ground-term proof: {error}")))?;
            }
            let proof = store.simplify_with_cache(proof, &mut simplified);
            if store.get(proof).proposition() != &expected {
                return Err(fail("proof simplification changed the requested equality"));
            }
            if self.proof_state.verify_proofs {
                store
                    .check_proof(proof, &self.proof_check_program)
                    .map_err(|error| {
                        fail(format!("invalid simplified ground-term proof: {error}"))
                    })?;
            }
            proofs.push(proof);
        }
        Ok((store, proofs))
    }
}

/// Look up canonical values and available view evidence for every node in `terms`.
/// The result has `terms.size()` entries: entry `id` describes `terms.get(id)`,
/// including non-root children. [`Proofs::import`] resolves its proof references.
///
/// `terms` must have children before parents. `roots` must be nonempty, contain
/// valid IDs from this DAG, and refer to terms of the same sort. On success,
/// every root has the same canonical value. No e-graph rows are inserted.
///
/// Errors on missing rows or proof columns, unsupported or failed primitive
/// evaluation, or unequal root values. Container values may still lack an
/// existence witness; this is checked when their certificates are completed.
fn lookup(egraph: &EGraph, terms: &TypedTermDag, roots: &[TermId]) -> Result<Vec<Node>, Error> {
    if egraph
        .get_sort_by_name(&egraph.proof_state.proof_names.proof_datatype)
        .is_none()
    {
        return Err(fail("ground-term certification requires proof evidence"));
    }
    let mut nodes: Vec<Node> = Vec::with_capacity(terms.size());
    for (id, node) in terms.nodes() {
        let sort = node.sort();
        let (value, row) = match node {
            TypedTerm::Var(never) => match *never {},
            TypedTerm::Lit(literal) => {
                let value = egraph
                    .read(|mut state| {
                        state.eval_resolved_expr(
                            &ResolvedExpr::Lit(Span::Panic, literal.clone()),
                            &[],
                        )
                    })
                    .ok_or_else(|| fail("could not evaluate literal"))?;
                (value, None)
            }
            TypedTerm::App(ResolvedCall::Primitive(primitive), children) => {
                if primitive.validator().is_none() {
                    return Err(fail(format!(
                        "primitive {} has no proof validator",
                        primitive.name()
                    )));
                }
                let signature = primitive
                    .input()
                    .iter()
                    .cloned()
                    .chain(once(sort.clone()))
                    .collect::<Vec<_>>();
                let ResolvedCall::Primitive(runtime) = ResolvedCall::from_resolution(
                    primitive.name(),
                    &signature,
                    &egraph.type_info,
                    Context::Read,
                    &Span::Panic,
                )?
                else {
                    return Err(fail("expected a primitive registration"));
                };
                let inputs = children
                    .iter()
                    .map(|child| nodes[*child].value)
                    .collect::<Vec<_>>();
                let value = egraph
                    .read(|mut state| state.apply_primitive(&runtime, &inputs))
                    .ok_or_else(|| fail(format!("primitive {} failed", primitive.name())))?;
                (canonical(egraph, value, &sort)?, None)
            }
            TypedTerm::App(ResolvedCall::Func(function), children) => {
                let mut key = children
                    .iter()
                    .map(|child| nodes[*child].value)
                    .collect::<Vec<_>>();
                // A source alias `(let y x)` has the same written term as
                // x. Its value-only binding can carry a reflexive proof, so
                // read the original binding's connector as the evidence.
                let table = if function.role.is_global() {
                    let origin = global_origin(egraph, global_name(terms, children)?);
                    key = vec![egraph.backend.base_values().get::<S>(origin.clone().into())];
                    egraph.global_table(&origin)
                } else {
                    egraph.functions.get(&function.name)
                }
                .ok_or_else(|| fail(format!("missing view {}", function.name)))?;
                let row = egraph
                    .backend
                    .lookup_row(table.backend_id, &key)
                    .ok_or_else(|| {
                        fail(format!(
                            "Could not find term {} in the e-graph",
                            terms.to_string(id)
                        ))
                    })?;
                let raw = row[key.len()];
                let value = canonical(egraph, raw, &sort)?;
                let proof_row = if table.decl.role.is_view() && table.func_type.outputs.len() == 2 {
                    let kind = if function.role.is_global() {
                        RowKind::Global
                    } else if table.decl.role == FunctionRole::FunctionView {
                        RowKind::Output(key.len())
                    } else {
                        RowKind::Constructor
                    };
                    let proof = row[key.len() + 1];
                    let to_leader = to_leader(egraph, raw, value, &sort)?;
                    Some(Row {
                        kind,
                        proof,
                        to_leader,
                    })
                } else if function.role.is_global() && !sort.is_eq_sort() {
                    None
                } else {
                    return Err(fail(format!("{} has no proof column", function.name)));
                };
                (value, proof_row)
            }
            TypedTerm::App(ResolvedCall::Values(_), _) => {
                return Err(fail("tuple terms cannot be certified"));
            }
        };
        nodes.push(Node { value, row });
    }
    let input = nodes[roots[0]].value;
    if roots[1..].iter().any(|root| nodes[*root].value != input) {
        return Err(fail("requested terms have different leaders"));
    }
    Ok(nodes)
}

/// Read the source binding name from a shared global table call.
/// The call must have one literal string argument.
fn global_name<'a>(terms: &'a TypedTermDag, children: &[TermId]) -> Result<&'a str, Error> {
    if let [key] = children
        && let TypedTerm::Lit(Literal::String(name)) = terms.get(*key)
    {
        Ok(name)
    } else {
        Err(fail("global reference requires a literal binding name"))
    }
}

/// Follow source global aliases to the binding that supplies their evidence.
/// A name with no source alias is returned unchanged.
fn global_origin(egraph: &EGraph, name: &str) -> String {
    let mut origin = name.to_owned();
    let mut seen = HashSet::default();
    while seen.insert(origin.clone()) {
        // Popped actions remain in the proof program, so only the latest
        // binding can determine whether the current name is an alias.
        let binding = gather_global_actions(&egraph.proof_check_program)
            .filter_map(|action| match action {
                ResolvedAction::Let(_, var, expr) if var.name == origin => Some(expr),
                _ => None,
            })
            .last();
        let Some(ResolvedExpr::Var(_, var)) = binding else {
            break;
        };
        if !var.is_global_ref {
            break;
        }
        origin = var.name.clone();
    }
    origin
}

/// Return `value` with equality-sort elements replaced by their leaders,
/// including inside nested containers. Errors if a container cannot be rebuilt.
/// The value must belong to `sort`; no e-graph rows are inserted.
fn canonical(egraph: &EGraph, value: Value, sort: &ArcSort) -> Result<Value, Error> {
    if sort.is_eq_container_sort() {
        egraph
            .read(|mut state| {
                rebuild_container_value_rec(
                    &mut state,
                    sort,
                    value,
                    &egraph.proof_state.uf_parent,
                    true,
                )
            })
            .ok_or_else(|| fail("could not canonicalize container value"))
    } else {
        Ok(find_canonical(egraph, value, sort))
    }
}

/// Read the union-find proof connecting a view's output to `leader`.
/// Returns `None` when the values already agree or `sort` is not an equality sort.
/// Otherwise errors if the stored edge is missing or ends at a different value.
fn to_leader(
    egraph: &EGraph,
    raw: Value,
    leader: Value,
    sort: &ArcSort,
) -> Result<Option<Value>, Error> {
    if raw == leader || !sort.is_eq_sort() {
        return Ok(None);
    }
    let name = egraph
        .proof_state
        .uf_parent
        .get(sort.name())
        .ok_or_else(|| fail("missing union-find proof table"))?;
    let table = &egraph.functions[name];
    let row = egraph
        .backend
        .lookup_row(table.backend_id, &[raw])
        .ok_or_else(|| fail("missing equality to the leader"))?;
    if row[1] != leader {
        return Err(fail("union proof does not reach the leader"));
    }
    Ok(Some(row[2]))
}

/// Evidence for a typed node. Only containers may wait for a parent's witness.
#[derive(Clone)]
enum GroundProof {
    Proof(RawEquality),
    Container {
        lhs: TermId,
        rhs: TermId,
        arguments: Vec<RawEquality>,
        /// Retains a completed certificate when the DAG shares this container.
        proof: Option<RawEquality>,
    },
}

impl GroundProof {
    /// The evaluated source term and its leader term.
    fn endpoints(&self) -> (TermId, TermId) {
        match self {
            Self::Proof(proof) => (proof.lhs, proof.rhs),
            Self::Container { lhs, rhs, .. } => (*lhs, *rhs),
        }
    }

    /// Ordinary certificates available to a primitive consuming this node.
    /// A temporary container contributes element evidence without claiming existence.
    fn arguments(&self) -> &[RawEquality] {
        match self {
            Self::Proof(proof) => std::slice::from_ref(proof),
            Self::Container { arguments, .. } => arguments,
        }
    }
}

/// Memoized construction over the typed DAG and decoded row evidence.
struct GroundProofs<'a> {
    terms: &'a TypedTermDag,
    nodes: &'a [Node<RawEquality>],
    proofs: Proofs,
    globals: HashMap<String, TermId>,
    memo: Vec<Option<GroundProof>>,
}

impl GroundProofs<'_> {
    /// Return a node's raw proof or a container recipe awaiting enclosing evidence.
    fn build(&mut self, id: TermId) -> Result<GroundProof, Error> {
        if let Some(proof) = &self.memo[id] {
            return Ok(proof.clone());
        }
        let term = self.terms.get(id).clone();
        let mut result = match term {
            TypedTerm::Lit(literal) => {
                let term = self.proofs.raw.term_dag.lit(literal);
                GroundProof::Proof(self.proofs.add(RawProof::Fiat(term, term), term, term))
            }
            TypedTerm::App(ResolvedCall::Primitive(primitive), children) => {
                let children = children
                    .into_iter()
                    .map(|id| self.build(id))
                    .collect::<Result<Vec<_>, _>>()?;
                let left = children
                    .iter()
                    .map(|proof| proof.endpoints().0)
                    .collect::<Vec<_>>();
                let right = children
                    .iter()
                    .map(|proof| proof.endpoints().1)
                    .collect::<Vec<_>>();
                let validate = primitive.validator().expect("lookup requires validators");
                let lhs = validate(&mut self.proofs.raw.term_dag, &left).ok_or_else(|| {
                    fail(format!("primitive {} failed validation", primitive.name()))
                })?;
                let rhs = validate(&mut self.proofs.raw.term_dag, &right).ok_or_else(|| {
                    fail(format!(
                        "primitive {} failed validation at leaders",
                        primitive.name()
                    ))
                })?;
                let arguments = children
                    .iter()
                    .flat_map(GroundProof::arguments)
                    .copied()
                    .collect::<Vec<_>>();
                if primitive.output().is_container_sort() {
                    GroundProof::Container {
                        lhs,
                        rhs,
                        arguments,
                        proof: None,
                    }
                } else {
                    let evidence = self.proofs.dependencies(&arguments);
                    GroundProof::Proof(self.proofs.certificate(lhs, rhs, &arguments, &evidence)?)
                }
            }
            TypedTerm::App(ResolvedCall::Func(_), children) => {
                let proof = if let Some(row) = self.nodes[id].row {
                    match row.kind {
                        RowKind::Constructor => {
                            let mut proof = row.proof;
                            for (index, child) in children.into_iter().enumerate() {
                                let witness = self.proofs.project(row.proof, index);
                                let child = self.finish(child, Some(witness))?;
                                let back = self.proofs.sym(child);
                                proof = self.proofs.congr(proof, index, back);
                            }
                            self.proofs.sym(proof)
                        }
                        RowKind::Output(column) => self.proofs.project(row.proof, column),
                        RowKind::Global => {
                            let source = self.globals[global_name(self.terms, &children)?];
                            if row.proof.rhs == source {
                                self.proofs.sym(row.proof)
                            } else if row.proof.lhs == source {
                                let back = self.proofs.sym(row.proof);
                                self.proofs.trans(row.proof, back)
                            } else {
                                let evidence = self.proofs.dependencies(&[row.proof]);
                                self.proofs
                                    .equality(source, row.proof.lhs, &evidence)
                                    .ok_or_else(|| fail("global view has no source connector"))?
                            }
                        }
                    }
                } else {
                    let term = self.globals[global_name(self.terms, &children)?];
                    self.proofs.add(RawProof::Fiat(term, term), term, term)
                };
                GroundProof::Proof(proof)
            }
            _ => return Err(fail("unsupported ground term")),
        };
        if let Some(edge) = self.nodes[id].row.and_then(|row| row.to_leader) {
            let GroundProof::Proof(proof) = result else {
                unreachable!("only view rows carry union-find edges")
            };
            result = GroundProof::Proof(self.proofs.trans(proof, edge));
        }
        self.memo[id] = Some(result.clone());
        Ok(result)
    }

    /// Complete a node's certificate. Deferred containers require an enclosing
    /// witness; successful certificates are shared by later uses of that node.
    fn finish(&mut self, id: TermId, witness: Option<RawEquality>) -> Result<RawEquality, Error> {
        match self.build(id)? {
            GroundProof::Proof(proof)
            | GroundProof::Container {
                proof: Some(proof), ..
            } => Ok(proof),
            GroundProof::Container {
                lhs,
                rhs,
                arguments,
                ..
            } => {
                let witness =
                    witness.ok_or_else(|| fail("container proof requires enclosing evidence"))?;
                let mut roots = vec![witness];
                roots.extend_from_slice(&arguments);
                let evidence = self.proofs.dependencies(&roots);
                let proof = self.proofs.certificate(lhs, rhs, &arguments, &evidence)?;
                let Some(GroundProof::Container { proof: saved, .. }) = &mut self.memo[id] else {
                    unreachable!()
                };
                *saved = Some(proof);
                Ok(proof)
            }
        }
    }
}

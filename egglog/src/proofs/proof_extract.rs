//! Certify the terms a command extractor actually returned, without unfolding
//! their DAG into a query. Table reads are fully keyed; proof composition stays
//! in a shared DAG until all roots have been materialized.

use super::proof_checker::gather_globals;
use super::proof_container_rebuild::rebuild_container_value_rec;
use super::proof_extractor::RootExtractor;
use super::proof_format::{
    Justification, Proof, ProofId, ProofStore, Proposition, SynthKey, proof_store_from_terms,
};
use super::proof_head::ProofAlgebra;
use crate::core::GenericExprExt;
use crate::extract::{SelectedNode, find_canonical};
use crate::*;

/// The source scope needed to certify a lowered extraction. Keeping just its
/// typed input and type environment also preserves popped/redeclared sorts in
/// replay; the runtime never restores or executes an encoding pipeline.
pub(crate) struct ExtractionSource {
    pub input: ResolvedExpr,
    pub types: TypeInfo,
    /// Final lowered input/count, filled after generated globals are removed.
    pub request: Option<(String, String)>,
}

type NodeKey = (TermId, String);

struct InputEvidence<'a> {
    egraph: &'a EGraph,
    source_types: &'a TypeInfo,
    dag: TermDag,
    extractor: RootExtractor,
    nodes: HashMap<NodeKey, SelectedNode>,
    /// Source globals retain evidence after their definition's rows disappear.
    globals: HashMap<NodeKey, String>,
    global_witnesses: HashSet<NodeKey>,
}

struct Certificates {
    store: ProofStore,
    nodes: HashMap<NodeKey, SelectedNode>,
    proofs: HashMap<NodeKey, ProofId>,
    /// Row proofs and their right endpoints, shared across selected roots.
    rows: HashMap<NodeKey, (ProofId, TermId)>,
    edges: HashMap<NodeKey, ProofId>,
    canonical_terms: HashMap<NodeKey, TermId>,
}

impl InputEvidence<'_> {
    /// Read an existing value's term with one shared proof/term extraction
    /// cache. This never asks the ordinary extractor to choose another result.
    fn materialize(&mut self, value: Value, sort: &ArcSort) -> Result<TermId, Error> {
        self.extractor
            .extract(self.egraph, &mut self.dag, value, sort)
            .ok_or_else(|| {
                Error::ExtractError(format!(
                    "cannot reconstruct extraction proof evidence at sort {}",
                    sort.name()
                ))
            })
    }

    fn canonical(&self, value: Value, sort: &ArcSort) -> Result<Value, Error> {
        if sort.is_eq_container_sort() {
            self.egraph
                .read(|mut state| {
                    rebuild_container_value_rec(
                        &mut state,
                        sort,
                        value,
                        &self.egraph.proof_state.uf_parent,
                        true,
                    )
                })
                .ok_or_else(|| {
                    Error::ExtractError("cannot canonicalize extracted container".into())
                })
        } else {
            Ok(find_canonical(self.egraph, value, sort))
        }
    }

    /// Resolve one shallow call with a known output sort. Children are variables,
    /// so typing does not copy the selected program; the key includes the sort
    /// because an empty polymorphic container can occur at several sorts.
    fn resolve_call(
        &self,
        head: &str,
        children: &[TermId],
        sort: &ArcSort,
    ) -> Result<ResolvedCall, Error> {
        let source = self.source_types;
        if let Some(func) = source.get_func_type(head) {
            if func.output().name() != sort.name() || func.input.len() != children.len() {
                return Err(Error::ExtractError(format!(
                    "extracted call {head} has the wrong type"
                )));
            }
            return Ok(ResolvedCall::Func(func.clone()));
        }
        let mut symbols = SymbolGen::new("@extract-proof-type-".into());
        let expr = Expr::Call(
            Span::Panic,
            head.to_owned(),
            children
                .iter()
                .enumerate()
                .map(|(i, &child)| match self.dag.get(child) {
                    Term::Lit(lit) => Expr::Lit(Span::Panic, lit.clone()),
                    _ => Expr::Var(Span::Panic, format!("@extract-proof-arg-{i}")),
                })
                .collect(),
        );
        let (atoms, mapped) = expr.to_query(source, &mut symbols);
        let query = crate::core::Query { atoms };
        let mut problem = Problem::default();
        problem.add_query(&query, source, Context::Read)?;
        problem.add_binding(mapped.get_corresponding_var_or_lit(source), sort.clone());
        let assignment = problem
            .solve(|sort: &ArcSort| sort.name())
            .map_err(|e| e.to_type_error())?;
        let facts = assignment.annotate_facts(
            &[egglog_ast::generic_ast::GenericFact::Fact(mapped)],
            source,
            Context::Read,
        )?;
        let ResolvedFact::Fact(ResolvedExpr::Call(_, call, _)) = &facts[0] else {
            unreachable!()
        };
        let ResolvedCall::Primitive(primitive) = call else {
            return Err(Error::ExtractError(format!(
                "unsupported extracted call {head}"
            )));
        };
        let types = primitive
            .input()
            .iter()
            .cloned()
            .chain(std::iter::once(sort.clone()))
            .collect::<Vec<_>>();
        // Source typing and encoded replay may have different native primitive
        // ids. Dispatch the registration from the graph being read.
        Ok(ResolvedCall::from_resolution(
            head,
            &types,
            &self.egraph.type_info,
            Context::Read,
            &Span::Panic,
        )?)
    }

    /// Read source syntax by exact view lookups and read-context primitives.
    /// Missing rows propagate to a containing global's retained evidence;
    /// typing and primitive-validation failures are never hidden by that fallback.
    fn read_node(&mut self, term: TermId, sort: ArcSort) -> Result<Option<NodeKey>, Error> {
        let key = (term, sort.name().to_owned());
        if self.nodes.contains_key(&key) {
            return Ok(Some(key));
        }
        let result = (|| -> Result<_, Error> {
            Ok(Some(match self.dag.get(term).clone() {
                Term::Lit(lit) => {
                    if literal_sort(&lit).name() != sort.name() {
                        return Err(Error::ExtractError(
                            "extraction input literal has the wrong type".into(),
                        ));
                    }
                    let value = self
                        .egraph
                        .read(|mut state| {
                            state.eval_resolved_expr(&ResolvedExpr::Lit(Span::Panic, lit), &[])
                        })
                        .unwrap();
                    (value, vec![], None)
                }
                Term::Var(name) => {
                    return Err(Error::ExtractError(format!(
                        "extraction input contains a free variable {name}"
                    )));
                }
                Term::App(head, terms) => {
                    let call = self.resolve_call(&head, &terms, &sort)?;
                    let inputs = match &call {
                        ResolvedCall::Func(func) => &func.input,
                        ResolvedCall::Primitive(primitive) => primitive.input(),
                        ResolvedCall::Values(_) => {
                            return Err(Error::ExtractError(
                                "tuple extraction is unsupported".into(),
                            ));
                        }
                    };
                    let mut children = Vec::with_capacity(terms.len());
                    for (term, input) in terms.iter().zip(inputs) {
                        let Some(child) = self.read_node(*term, input.clone())? else {
                            return Ok(None);
                        };
                        children.push(child);
                    }
                    let values = children
                        .iter()
                        .map(|key| self.nodes[key].value)
                        .collect::<Vec<_>>();
                    match call {
                        ResolvedCall::Func(func) => {
                            let source = self.source_types;
                            if func.subtype != FunctionSubtype::Constructor
                                && !source.is_global(&head)
                            {
                                return Err(Error::ExtractError(format!(
                                    "extracted custom function {head} is not a constructor"
                                )));
                            }
                            let Some(row) = self.egraph.read(|state| {
                                state.lookup_proof_values(&head, RawValues(values))
                            })?
                            else {
                                return Ok(None);
                            };
                            (
                                self.canonical(row[0], &sort)?,
                                children,
                                Some((row[0], row[1])),
                            )
                        }
                        ResolvedCall::Primitive(primitive) => {
                            let validator = primitive.validator().ok_or_else(|| {
                                Error::ExtractError(format!(
                                    "extracted primitive {} has no proof validator",
                                    primitive.name()
                                ))
                            })?;
                            if validator(&mut self.dag, &terms) != Some(term) {
                                return Err(Error::ExtractError(format!(
                                    "extraction input has a noncanonical primitive value: {}",
                                    primitive.name()
                                )));
                            }
                            let value = self
                                .egraph
                                .read(|mut state| state.apply_primitive(&primitive, &values))
                                .ok_or_else(|| {
                                    Error::ExtractError(format!(
                                        "extracted primitive {} failed",
                                        primitive.name()
                                    ))
                                })?;
                            (self.canonical(value, &sort)?, children, None)
                        }
                        ResolvedCall::Values(_) => unreachable!(),
                    }
                }
            }))
        })()?;
        let (value, children, row, global_witness) = match result {
            Some((value, children, row)) => (value, children, row, false),
            None => {
                // Prefer the actual syntax's view rows: a global defined after
                // a union can carry a reflexive proof of another representative.
                // Only fall back to its stored evidence when the original rows
                // have disappeared; endpoint checks still require the source.
                if let Some(name) = self.globals.get(&key)
                    && let Some(row) = self
                        .egraph
                        .read(|state| state.lookup_proof_values(name, RawValues(vec![])))?
                {
                    (
                        self.canonical(row[0], &sort)?,
                        vec![],
                        Some((row[0], row[1])),
                        true,
                    )
                } else {
                    return Ok(None);
                }
            }
        };
        if global_witness {
            self.global_witnesses.insert(key.clone());
        }
        self.nodes.insert(
            key.clone(),
            SelectedNode {
                sort,
                value,
                children,
                row,
            },
        );
        Ok(Some(key))
    }
}

impl Certificates {
    /// Composition checks belong at this boundary: malformed input/evidence
    /// must return an extraction error before the proof algebra's assertions.
    fn trans(&mut self, left: ProofId, right: ProofId) -> Result<ProofId, Error> {
        if self.store.get(left).rhs() != self.store.get(right).lhs() {
            return Err(Error::ExtractError(
                "extraction proof has mismatched transitivity endpoints".into(),
            ));
        }
        Ok(self.store.trans(left, right))
    }

    fn congr(&mut self, base: ProofId, index: usize, step: ProofId) -> Result<ProofId, Error> {
        let rhs = self.store.get(base).rhs();
        if !matches!(self.store.term_dag.get(rhs), Term::App(_, children)
            if children.get(index) == Some(&self.store.get(step).lhs()))
        {
            return Err(Error::ExtractError(
                "extraction proof does not start at the rewritten child".into(),
            ));
        }
        Ok(self.store.congr(base, index, step))
    }

    fn project(&mut self, proof: ProofId, index: usize) -> Result<ProofId, Error> {
        let rhs = self.store.get(proof).rhs();
        if !matches!(self.store.term_dag.get(rhs), Term::App(_, children) if index < children.len())
        {
            return Err(Error::ExtractError(
                "extraction proof has an invalid child projection".into(),
            ));
        }
        Ok(self.store.push_projection(proof, index))
    }

    /// Reconstruct canonical witnesses from row/union endpoints. Container
    /// witnesses use the same normalizer as the proof checker.
    fn canonical_term(&mut self, key: &NodeKey) -> Result<TermId, Error> {
        if let Some(&term) = self.canonical_terms.get(key) {
            return Ok(term);
        }
        let node = self.nodes[key].clone();
        let term = if node.sort.is_container_sort() {
            let children = node
                .children
                .iter()
                .map(|child| self.canonical_term(child))
                .collect::<Result<Vec<_>, _>>()?;
            node.sort
                .rebuild_container_normalizer()
                .and_then(|(_, normalize)| normalize(&mut self.store.term_dag, &children))
                .ok_or_else(|| {
                    Error::ExtractError("cannot normalize canonical container witness".into())
                })?
        } else {
            key.0
        };
        self.canonical_terms.insert(key.clone(), term);
        Ok(term)
    }

    /// Produce `canonical value = selected term`. Containers are anchored by
    /// their parent's canonical child or the evaluated source input.
    fn certify(
        &mut self,
        key: &NodeKey,
        anchor: Option<(ProofId, TermId)>,
        input_anchor: bool,
    ) -> Result<ProofId, Error> {
        if let Some(&proof) = self.proofs.get(key) {
            return Ok(proof);
        }
        let node = self.nodes[key].clone();
        let proof = if node.row.is_some() {
            let (mut proof, row_term) = self.rows[key];
            if !node.children.is_empty() {
                let canonical_children = node
                    .children
                    .iter()
                    .map(|child| self.canonical_term(child))
                    .collect::<Result<Vec<_>, _>>()?;
                if !matches!(self.store.term_dag.get(row_term), Term::App(_, children)
                    if *children == canonical_children)
                {
                    return Err(Error::ExtractError(
                        "constructor evidence does not match its canonical children".into(),
                    ));
                }
            }
            if input_anchor && !node.children.is_empty() {
                // Rewrite the actual source forward to canonical children: a
                // collapsing set/map cannot be reconstructed in reverse.
                let (mut source, _) = anchor.ok_or_else(|| {
                    Error::ExtractError("the extraction input has no existence anchor".into())
                })?;
                for (index, child) in node.children.iter().enumerate() {
                    let child_anchor = self.project(source, index)?;
                    let child_proof = self.certify(child, Some((child_anchor, child.0)), true)?;
                    let back = self.store.sym(child_proof);
                    source = self.congr(source, index, back)?;
                }
                let back = self.store.sym(source);
                proof = self.trans(proof, back)?;
            } else {
                for (index, child) in node.children.iter().enumerate() {
                    let child_anchor = self.project(proof, index)?;
                    let child_term = self.store.get(child_anchor).rhs();
                    let child_proof =
                        self.certify(child, Some((child_anchor, child_term)), false)?;
                    proof = self.congr(proof, index, child_proof)?;
                }
            }
            if let Some(&edge) = self.edges.get(key) {
                let back = self.store.sym(edge);
                proof = self.trans(back, proof)?;
            }
            proof
        } else if node.sort.is_container_sort() {
            let (mut proof, canonical) = anchor.ok_or_else(|| {
                Error::ExtractError("extracted container has no existence proof".into())
            })?;
            if input_anchor {
                for (index, child) in node.children.iter().enumerate() {
                    let child_anchor = self.project(proof, index)?;
                    let child_proof = self.certify(child, Some((child_anchor, child.0)), true)?;
                    let back = self.store.sym(child_proof);
                    proof = self.congr(proof, index, back)?;
                }
                proof = self.store.normalize_step(proof);
                self.store.sym(proof)
            } else {
                // Selected Set/Map elements are retained in storage order;
                // match them to the canonical term's normalized order.
                let Term::App(head, current_children) = self.store.term_dag.get(canonical).clone()
                else {
                    return Err(Error::ExtractError(
                        "container did not reconstruct as an application".into(),
                    ));
                };
                if !matches!(self.store.term_dag.get(key.0), Term::App(target_head, _) if &head == target_head)
                {
                    return Err(Error::ExtractError(
                        "extracted container uses a different value constructor".into(),
                    ));
                }
                let candidates = node
                    .children
                    .iter()
                    .map(|child| self.canonical_term(child))
                    .collect::<Result<Vec<_>, _>>()?;
                for (index, old) in current_children.into_iter().enumerate() {
                    let selected = if candidates.get(index) == Some(&old) {
                        Some(index)
                    } else {
                        candidates.iter().position(|term| *term == old)
                    }
                    .ok_or_else(|| {
                        Error::ExtractError(
                            "extracted container elements do not match its value".into(),
                        )
                    })?;
                    let child_anchor = self.project(proof, index)?;
                    let child_proof =
                        self.certify(&node.children[selected], Some((child_anchor, old)), false)?;
                    proof = self.congr(proof, index, child_proof)?;
                }
                self.store.normalize_step(proof)
            }
        } else if node.sort.is_eq_sort() {
            return Err(Error::ExtractError(
                "an extracted eq-sort value needs a constructor witness".into(),
            ));
        } else if let Some((anchor, _)) = anchor {
            anchor
        } else {
            // Only primitive value leaves are self-evident.
            self.store.push_shared_proof(
                SynthKey::Fiat(key.0, key.0),
                Proof {
                    proposition: Proposition::new(key.0, key.0),
                    justification: Justification::Fiat,
                },
            )
        };
        self.proofs.insert(key.clone(), proof);
        Ok(proof)
    }
}

/// Preserve the source expression's semantics as a DAG. Global definitions are
/// already shared terms from the proof checker, never unfolded into Exprs.
fn source_term(
    expr: &ResolvedExpr,
    dag: &mut TermDag,
    globals: &HashMap<String, TermId>,
) -> Result<TermId, Error> {
    match expr {
        ResolvedExpr::Lit(_, lit) => Ok(dag.lit(lit.clone())),
        ResolvedExpr::Var(_, var) => globals
            .get(&var.name)
            .copied()
            .ok_or_else(|| Error::ExtractError(format!("missing input global {}", var.name))),
        ResolvedExpr::Call(_, ResolvedCall::Func(func), args)
            if args.is_empty() && globals.contains_key(&func.name) =>
        {
            Ok(globals[&func.name])
        }
        ResolvedExpr::Call(_, call, args) => {
            let args = args
                .iter()
                .map(|arg| source_term(arg, dag, globals))
                .collect::<Result<Vec<_>, _>>()?;
            match call {
                ResolvedCall::Func(func) => Ok(dag.app(func.name.clone(), args)),
                ResolvedCall::Primitive(primitive) => primitive
                    .validator()
                    .and_then(|validator| validator(dag, &args))
                    .ok_or_else(|| {
                        Error::ExtractError(format!(
                            "cannot validate extraction input primitive {}",
                            primitive.name()
                        ))
                    }),
                ResolvedCall::Values(_) => Err(Error::ExtractError(
                    "tuple extraction is unsupported".into(),
                )),
            }
        }
    }
}

pub(crate) fn prove_extracted(
    egraph: &EGraph,
    source: &ExtractionSource,
    input_action: usize,
    input_value: Value,
    output_dag: &TermDag,
    output_roots: &[TermId],
    selected: HashMap<NodeKey, SelectedNode>,
) -> Result<Vec<CommandOutput>, Error> {
    if output_roots.is_empty() {
        return Ok(vec![]);
    }
    if output_roots.iter().any(|&root| root >= output_dag.size()) {
        return Err(Error::ExtractError(
            "extractor returned an invalid term id".into(),
        ));
    }
    let source_input = &source.input;
    let sort = source_input.output_type();
    // Start from the extractor's arena so all selected roots retain their ids.
    let mut dag = output_dag.clone();
    let globals = gather_globals(&egraph.proof_check_program, &mut dag).map_err(|error| {
        Error::ExtractError(format!("cannot resolve extraction input globals: {error}"))
    })?;
    let input_term = source_term(source_input, &mut dag, &globals)?;
    let input_global = match source_input {
        ResolvedExpr::Var(_, var) => Some(var.name.as_str()),
        ResolvedExpr::Call(_, ResolvedCall::Func(func), args)
            if args.is_empty() && globals.contains_key(&func.name) =>
        {
            Some(func.name.as_str())
        }
        _ => None,
    };
    let mut witnesses = HashMap::<NodeKey, String>::default();
    for (name, &term) in &globals {
        if let Some(sort) = source.types.get_global_sort(name) {
            witnesses
                .entry((term, sort.name().to_owned()))
                .and_modify(|old| {
                    if name < old {
                        *old = name.clone();
                    }
                })
                .or_insert_with(|| name.clone());
        }
    }
    if let Some(name) = input_global {
        // The actual input's carried evidence takes priority over an unrelated
        // alias with the same historical definition.
        witnesses.insert((input_term, sort.name().to_owned()), name.to_owned());
    }
    let normalizers: HashMap<_, _> = egraph
        .type_info
        .sorts
        .values()
        .filter_map(|sort| sort.rebuild_container_normalizer())
        .collect();
    let mut value_constructors = HashSet::default();
    for sort in egraph.type_info.sorts.values() {
        if let Some(head) = sort.prim_value_constructor() {
            if egraph.type_info.get_prims(&head).map_or(0, <[_]>::len) != 1 {
                return Err(Error::ExtractError(format!(
                    "ambiguous primitive value constructor {head}"
                )));
            }
            value_constructors.insert(head);
        }
    }
    let mut session = InputEvidence {
        egraph,
        source_types: &source.types,
        dag,
        extractor: RootExtractor::new(),
        nodes: HashMap::default(),
        globals: witnesses,
        global_witnesses: HashSet::default(),
    };
    let input = session
        .read_node(input_term, sort.clone())?
        .ok_or_else(|| {
            Error::ExtractError("extraction input constructor evidence is missing".into())
        })?;
    if session.nodes[&input].value != session.canonical(input_value, &sort)? {
        return Err(Error::ExtractError(
            "the extraction input's proof semantics do not match its evaluated value".into(),
        ));
    }
    // Input certificates project by source syntax position. Container output
    // evidence follows storage order and is matched by canonical element below;
    // do not let an identical selected term replace those source positions.
    for (key, node) in selected {
        session.nodes.entry(key).or_insert(node);
    }
    let mut outputs = Vec::with_capacity(output_roots.len());
    for &term in output_roots {
        let key = (term, sort.name().to_owned());
        if session.nodes[&key].value != session.nodes[&input].value {
            return Err(Error::ExtractError(
                "extractor returned a term from a different equivalence class".into(),
            ));
        }
        outputs.push(key);
    }
    let mut output_nodes = HashSet::default();
    let mut pending = outputs.clone();
    while let Some(key) = pending.pop() {
        if output_nodes.insert(key.clone()) {
            pending.extend(session.nodes[&key].children.iter().cloned());
        }
    }
    let mut reachable = output_nodes.clone();
    pending.push(input.clone());
    while let Some(key) = pending.pop() {
        if reachable.insert(key.clone()) {
            pending.extend(session.nodes[&key].children.iter().cloned());
        }
    }
    // Materialize and convert each existing row/union proof in one batch.
    // Their endpoints supply canonical term witnesses without recreating
    // deleted syntax or adding term tables to the source-view encoding.
    let proof_sort = egraph
        .get_sort_by_name(&egraph.proof_state.proof_names.proof_datatype)
        .ok_or_else(|| {
            Error::ExtractError(
                "missing extraction proof sort; replay the complete encoded program".into(),
            )
        })?
        .clone();
    let rows = session
        .nodes
        .iter()
        .filter_map(|(key, node)| node.row.map(|row| (key.clone(), node.clone(), row)))
        .collect::<Vec<_>>();
    // The only non-value Fiat introduced here names the evaluated input's
    // source action. Selected output terms are never assumed.
    let names = &egraph.proof_state.proof_names;
    let action = session.dag.lit(Literal::Int(input_action as i64));
    let root = session.dag.lit(Literal::Int(0));
    let input_anchor = session
        .dag
        .app(names.fiat_term_constructor.clone(), vec![action, root]);
    let mut evidence_roots = vec![input_anchor];
    let mut evidence_keys = vec![];
    for (key, node, (value, row_proof)) in rows {
        let raw = session.materialize(row_proof, &proof_sort)?;
        evidence_roots.push(raw);
        evidence_keys.push((key.clone(), false));
        if value != node.value {
            let uf = &egraph.proof_state.uf_parent[node.sort.name()];
            let row = egraph
                .read(|state| state.lookup_proof_values(uf, RawValues(vec![value])))?
                .ok_or_else(|| Error::ExtractError("missing extraction union proof".into()))?;
            let raw = session.materialize(row[1], &proof_sort)?;
            evidence_roots.push(raw);
            evidence_keys.push((key, true));
        }
    }
    let (mut store, ids) = proof_store_from_terms(
        names,
        session.dag,
        &evidence_roots,
        &egraph.proof_check_program,
        normalizers,
        value_constructors,
    );
    store
        .remove_globals(&egraph.proof_check_program)
        .map_err(|error| {
            Error::ExtractError(format!(
                "cannot resolve extraction evidence globals: {error}"
            ))
        })?;
    let mut ids = ids.into_iter();
    let input_anchor = ids.next().unwrap();
    let mut certificates = Certificates {
        store,
        nodes: session.nodes,
        proofs: HashMap::default(),
        rows: HashMap::default(),
        edges: HashMap::default(),
        canonical_terms: HashMap::default(),
    };
    let mut expected_input = input_term;
    for ((key, edge), id) in evidence_keys.into_iter().zip(ids) {
        let proof = certificates.store.get(id);
        if edge {
            certificates.edges.insert(key.clone(), id);
            certificates.canonical_terms.insert(key, proof.rhs());
        } else {
            // A late global may retain B = B after its historical A row was
            // deleted. Only the input global may use that carried endpoint;
            // nested or output evidence must still match the requested term.
            if session.global_witnesses.contains(&key)
                && reachable.contains(&key)
                && proof.rhs() != key.0
            {
                if key == input && input_global.is_some() && !output_nodes.contains(&key) {
                    expected_input = proof.rhs();
                } else {
                    return Err(Error::ExtractError(
                        "retained global evidence does not match the requested extraction term"
                            .into(),
                    ));
                }
            }
            certificates.rows.insert(key.clone(), (id, proof.rhs()));
            certificates.canonical_terms.insert(key, proof.lhs());
        }
    }
    let input_proof = certificates.certify(&input, Some((input_anchor, input_term)), true)?;
    let back = certificates.store.sym(input_proof);
    let canonical_anchor = certificates.trans(input_proof, back)?;
    let canonical_input = certificates.canonical_term(&input)?;
    let mut ids = Vec::with_capacity(output_roots.len());
    for key in outputs {
        let result =
            certificates.certify(&key, Some((canonical_anchor, canonical_input)), false)?;
        ids.push(certificates.trans(back, result)?);
    }
    let mut store = certificates.store;
    let mut results = Vec::with_capacity(ids.len());
    let mut simplified = Default::default();
    for (id, &term) in ids.into_iter().zip(output_roots) {
        if store.get(id).lhs() != expected_input || store.get(id).rhs() != term {
            return Err(Error::ExtractError(
                "extraction proof does not match the requested input and extracted result".into(),
            ));
        }
        if egraph.proof_state.verify_proofs {
            store
                .check_proof(id, &egraph.proof_check_program)
                .map_err(|error| {
                    Error::ExtractError(format!("invalid extraction proof: {error}"))
                })?;
        }
        let proof_id = store.simplify_with_cache(id, &mut simplified);
        if egraph.proof_state.verify_proofs {
            store
                .check_proof(proof_id, &egraph.proof_check_program)
                .map_err(|error| {
                    Error::ExtractError(format!("invalid simplified extraction proof: {error}"))
                })?;
        }
        results.push(CommandOutput::ProveExists {
            proof_store: store.clone(),
            proof_id,
        });
    }
    Ok(results)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prove_extract_reports_composition_mismatch() {
        let mut dag = TermDag::default();
        let one = dag.lit(Literal::Int(1));
        let two = dag.lit(Literal::Int(2));
        let parent = dag.app("Container".into(), vec![one]);
        let mut store = ProofStore::new(dag, HashMap::default(), HashSet::default());
        let [one, two, parent] = [one, two, parent].map(|term| {
            store.id_to_proof.push(Proof {
                proposition: Proposition::new(term, term),
                justification: Justification::Fiat,
            })
        });
        let mut certificates = Certificates {
            store,
            nodes: HashMap::default(),
            proofs: HashMap::default(),
            rows: HashMap::default(),
            edges: HashMap::default(),
            canonical_terms: HashMap::default(),
        };
        assert!(matches!(
            certificates.trans(one, two),
            Err(Error::ExtractError(_))
        ));
        assert!(matches!(
            certificates.congr(parent, 0, two),
            Err(Error::ExtractError(_))
        ));
        assert!(matches!(
            certificates.project(parent, 1),
            Err(Error::ExtractError(_))
        ));
    }
}

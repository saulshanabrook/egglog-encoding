//! Certify the terms a command extractor actually returned, without unfolding
//! their DAG into a query. Table reads are fully keyed; proof composition stays
//! in a shared DAG until all roots have been materialized.

use super::proof_checker::gather_globals;
use super::proof_container_rebuild::rebuild_container_value_rec;
use super::proof_extractor::RootExtractor;
use super::proof_format::proof_store_from_terms;
use crate::core::GenericExprExt;
use crate::extract::find_canonical;
use crate::*;

type NodeKey = (TermId, String);

#[derive(Clone)]
struct Node {
    sort: ArcSort,
    value: Value,
    children: Vec<NodeKey>,
    /// Constructor/global view row: its value and its carried proof.
    row: Option<(Value, Value)>,
    /// The original syntax's row is gone, so this proof comes from a global.
    global_witness: bool,
}

struct Certificates<'a> {
    egraph: &'a EGraph,
    dag: TermDag,
    extractor: RootExtractor,
    nodes: HashMap<NodeKey, Node>,
    proofs: HashMap<NodeKey, TermId>,
    /// A source global's carried proof can still justify its original term
    /// after constructor rows or container elements have disappeared.
    globals: HashMap<NodeKey, String>,
    /// Materialized row proofs and their right endpoints, shared across roots.
    rows: HashMap<NodeKey, (TermId, TermId)>,
    edges: HashMap<NodeKey, TermId>,
    canonical_terms: HashMap<NodeKey, TermId>,
}

impl Certificates<'_> {
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
        let source = self
            .egraph
            .proof_state
            .original_typechecking
            .as_ref()
            .ok_or_else(|| Error::ExtractError("missing extraction source types".into()))?;
        if let Some(func) = source.type_info.get_func_type(head) {
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
        let (atoms, mapped) = expr.to_query(&source.type_info, &mut symbols);
        let query = crate::core::Query { atoms };
        let mut problem = Problem::default();
        problem.add_query(&query, &source.type_info, Context::Read)?;
        problem.add_binding(
            mapped.get_corresponding_var_or_lit(&source.type_info),
            sort.clone(),
        );
        let assignment = problem
            .solve(|sort: &ArcSort| sort.name())
            .map_err(|e| e.to_type_error())?;
        let facts = assignment.annotate_facts(
            &[egglog_ast::generic_ast::GenericFact::Fact(mapped)],
            &source.type_info,
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

    /// Evaluate a typed selected DAG by exact view lookups and read-context
    /// primitives. No constructor is inserted, even for custom extractors.
    fn read_node(&mut self, term: TermId, sort: ArcSort) -> Result<NodeKey, Error> {
        let key = (term, sort.name().to_owned());
        if self.nodes.contains_key(&key) {
            return Ok(key);
        }
        let result = (|| {
            Ok(match self.dag.get(term).clone() {
                Term::Lit(lit) => {
                    if literal_sort(&lit).name() != sort.name() {
                        return Err(Error::ExtractError(
                            "extracted literal has the wrong type".into(),
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
                        "extractor returned a free variable {name}"
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
                        children.push(self.read_node(*term, input.clone())?);
                    }
                    let values = children
                        .iter()
                        .map(|key| self.nodes[key].value)
                        .collect::<Vec<_>>();
                    match call {
                        ResolvedCall::Func(func) => {
                            let source = self
                                .egraph
                                .proof_state
                                .original_typechecking
                                .as_ref()
                                .unwrap();
                            if func.subtype != FunctionSubtype::Constructor
                                && !source.type_info.is_global(&head)
                            {
                                return Err(Error::ExtractError(format!(
                                    "extracted custom function {head} is not a constructor"
                                )));
                            }
                            let row = self
                                .egraph
                                .read(|state| state.lookup_proof_values(&head, RawValues(values)))?
                                .ok_or_else(|| {
                                    Error::ExtractError(format!(
                                        "extracted term does not exist: {head}"
                                    ))
                                })?;
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
                                    "extractor returned a noncanonical primitive value: {}",
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
            })
        })();
        let (value, children, row, global_witness) = match result {
            Ok((value, children, row)) => (value, children, row, false),
            Err(error) => {
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
                    return Err(error);
                }
            }
        };
        self.nodes.insert(
            key.clone(),
            Node {
                sort,
                value,
                children,
                row,
                global_witness,
            },
        );
        Ok(key)
    }

    /// Reconstruct canonical witnesses from proof endpoints. E-class values
    /// themselves have no term tables in the source-view encoding.
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
                .and_then(|(_, normalize)| normalize(&mut self.dag, &children))
                .ok_or_else(|| {
                    Error::ExtractError("cannot normalize canonical container witness".into())
                })?
        } else {
            key.0
        };
        self.canonical_terms.insert(key.clone(), term);
        Ok(term)
    }

    /// Produce `canonical value = selected term`. A container's existence must
    /// be anchored: normally at the parent's canonical child, or at the original
    /// evaluated input itself (`input_anchor`).
    fn certify(
        &mut self,
        key: &NodeKey,
        anchor: Option<(TermId, TermId)>,
        input_anchor: bool,
    ) -> Result<TermId, Error> {
        if let Some(&proof) = self.proofs.get(key) {
            return Ok(proof);
        }
        let node = self.nodes[key].clone();
        let names = &self.egraph.proof_state.proof_names;
        let proof = if node.row.is_some() {
            let (mut proof, row_term) = self.rows[key];
            if !node.children.is_empty() {
                let canonical_children = node
                    .children
                    .iter()
                    .map(|child| self.canonical_term(child))
                    .collect::<Result<Vec<_>, _>>()?;
                if !matches!(self.dag.get(row_term), Term::App(_, children) if *children == canonical_children)
                {
                    return Err(Error::ExtractError(
                        "constructor evidence does not match its canonical children".into(),
                    ));
                }
            }
            if input_anchor && !node.children.is_empty() {
                // The input was actually evaluated. Rewrite its children toward
                // the view key, then reverse that certificate. In particular,
                // this can collapse a source set/map; reconstructing the source
                // backwards from its collapsed runtime value cannot do that.
                let (mut source, _) = anchor.expect("the input has an existence anchor");
                for (index, child) in node.children.iter().enumerate() {
                    let index_term = self.dag.lit(Literal::Int(index as i64));
                    let child_anchor = self
                        .dag
                        .app(names.proj_constructor.clone(), vec![source, index_term]);
                    let child_proof = self.certify(child, Some((child_anchor, child.0)), true)?;
                    let back = self
                        .dag
                        .app(names.eq_sym_constructor.clone(), vec![child_proof]);
                    source = self.dag.app(
                        names.congr_constructor.clone(),
                        vec![source, index_term, back],
                    );
                }
                let back = self.dag.app(names.eq_sym_constructor.clone(), vec![source]);
                proof = self
                    .dag
                    .app(names.eq_trans_constructor.clone(), vec![proof, back]);
            } else {
                let row_children = match self.dag.get(row_term) {
                    Term::App(_, children) => children.clone(),
                    _ => vec![],
                };
                for (index, child) in node.children.iter().enumerate() {
                    let index_term = self.dag.lit(Literal::Int(index as i64));
                    let child_anchor = self
                        .dag
                        .app(names.proj_constructor.clone(), vec![proof, index_term]);
                    let child_proof =
                        self.certify(child, Some((child_anchor, row_children[index])), false)?;
                    proof = self.dag.app(
                        names.congr_constructor.clone(),
                        vec![proof, index_term, child_proof],
                    );
                }
            }
            if let Some(&edge) = self.edges.get(key) {
                let back = self.dag.app(names.eq_sym_constructor.clone(), vec![edge]);
                proof = self
                    .dag
                    .app(names.eq_trans_constructor.clone(), vec![back, proof]);
            }
            proof
        } else if node.sort.is_container_sort() {
            let (mut proof, canonical) = anchor.ok_or_else(|| {
                Error::ExtractError("extracted container has no existence proof".into())
            })?;
            if input_anchor {
                // Here the anchor is the source input, which may use a different
                // term for each child than the runtime representative does.
                for (index, child) in node.children.iter().enumerate() {
                    let index_term = self.dag.lit(Literal::Int(index as i64));
                    let child_anchor = self
                        .dag
                        .app(names.proj_constructor.clone(), vec![proof, index_term]);
                    let child_proof = self.certify(child, Some((child_anchor, child.0)), true)?;
                    let back = self
                        .dag
                        .app(names.eq_sym_constructor.clone(), vec![child_proof]);
                    proof = self.dag.app(
                        names.congr_constructor.clone(),
                        vec![proof, index_term, back],
                    );
                }
                proof = self
                    .dag
                    .app(names.container_normalize_constructor.clone(), vec![proof]);
                self.dag.app(names.eq_sym_constructor.clone(), vec![proof])
            } else {
                // Container term order is not storage order (notably Set and
                // Map). Locate each canonical element in the actual term, then
                // normalize after replacing its selected representative.
                let Term::App(head, current_children) = self.dag.get(canonical).clone() else {
                    return Err(Error::ExtractError(
                        "container did not reconstruct as an application".into(),
                    ));
                };
                let Term::App(target_head, _) = self.dag.get(key.0) else {
                    unreachable!()
                };
                if &head != target_head {
                    return Err(Error::ExtractError(
                        "extracted container uses a different value constructor".into(),
                    ));
                }
                let mut candidates = Vec::with_capacity(node.children.len());
                for child in &node.children {
                    candidates.push(self.canonical_term(child)?);
                }
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
                    let index_term = self.dag.lit(Literal::Int(index as i64));
                    let child_anchor = self
                        .dag
                        .app(names.proj_constructor.clone(), vec![proof, index_term]);
                    let child_proof =
                        self.certify(&node.children[selected], Some((child_anchor, old)), false)?;
                    proof = self.dag.app(
                        names.congr_constructor.clone(),
                        vec![proof, index_term, child_proof],
                    );
                }
                self.dag
                    .app(names.container_normalize_constructor.clone(), vec![proof])
            }
        } else if node.sort.is_eq_sort() {
            return Err(Error::ExtractError(
                "an extracted eq-sort value needs a constructor witness".into(),
            ));
        } else if let Some((anchor, _)) = anchor {
            anchor
        } else {
            // Only primitive value leaves are self-evident. Constructor and
            // container branches above always require existing evidence.
            self.dag
                .app(names.fiat(node.sort.name()), vec![key.0, key.0])
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
    source_input: &ResolvedExpr,
    input_action: usize,
    input_value: Value,
    output_dag: &TermDag,
    output_roots: &[TermId],
) -> Result<Vec<CommandOutput>, Error> {
    if output_roots.is_empty() {
        return Ok(vec![]);
    }
    if output_roots.iter().any(|&root| root >= output_dag.size()) {
        return Err(Error::ExtractError(
            "extractor returned an invalid term id".into(),
        ));
    }
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
    let source = egraph
        .proof_state
        .original_typechecking
        .as_ref()
        .ok_or_else(|| Error::ExtractError("missing extraction source types".into()))?;
    let mut witnesses = HashMap::<NodeKey, String>::default();
    for (name, &term) in &globals {
        if let Some(sort) = source.type_info.get_global_sort(name) {
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
    let mut session = Certificates {
        egraph,
        dag,
        extractor: RootExtractor::new(),
        nodes: HashMap::default(),
        proofs: HashMap::default(),
        globals: witnesses,
        rows: HashMap::default(),
        edges: HashMap::default(),
        canonical_terms: HashMap::default(),
    };
    let input = session.read_node(input_term, sort.clone())?;
    if session.nodes[&input].value != session.canonical(input_value, &sort)? {
        return Err(Error::ExtractError(
            "the extraction input's proof semantics do not match its evaluated value".into(),
        ));
    }
    let mut outputs = Vec::with_capacity(output_roots.len());
    for &term in output_roots {
        let key = session.read_node(term, sort.clone())?;
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
    let mut expected_input = input_term;
    let witnesses = session
        .nodes
        .iter()
        .filter(|(key, node)| node.global_witness && reachable.contains(*key))
        .map(|(key, node)| (key.clone(), node.row.unwrap().1))
        .collect::<Vec<_>>();
    if !witnesses.is_empty() {
        // A global bound after a union can prove B = B although its historical
        // definition was A. Inspect all fallback witnesses before composing
        // parent congruences; an endpoint mismatch must not reach their asserts.
        let names = &egraph.proof_state.proof_names;
        let proof_sort = egraph
            .get_sort_by_name(&names.proof_datatype)
            .unwrap()
            .clone();
        let terms = witnesses
            .iter()
            .map(|(_, value)| session.materialize(*value, &proof_sort))
            .collect::<Result<Vec<_>, _>>()?;
        let (mut evidence, ids) = proof_store_from_terms(
            names,
            session.dag.clone(),
            &terms,
            &egraph.proof_check_program,
            normalizers.clone(),
            value_constructors.clone(),
        );
        evidence
            .remove_globals(&egraph.proof_check_program)
            .map_err(|error| {
                Error::ExtractError(format!("cannot resolve extraction input evidence: {error}"))
            })?;
        for ((key, _), id) in witnesses.iter().zip(ids) {
            let endpoint = evidence.get(id).rhs();
            if endpoint == key.0 {
                continue;
            }
            if key == &input && input_global.is_some() && !output_nodes.contains(key) {
                // Match the existing evaluated-global semantics, retaining its
                // carried endpoint rather than inventing an A = B certificate.
                expected_input = endpoint;
            } else {
                return Err(Error::ExtractError(
                    "retained global evidence does not match the requested extraction term".into(),
                ));
            }
        }
        session.dag = evidence.term_dag;
    }
    // Materialize and convert each existing row/union proof in one batch.
    // Their endpoints supply canonical term witnesses without recreating
    // deleted syntax or adding term tables to the source-view encoding.
    let proof_sort = egraph
        .get_sort_by_name(&egraph.proof_state.proof_names.proof_datatype)
        .unwrap()
        .clone();
    let rows = session
        .nodes
        .iter()
        .filter_map(|(key, node)| node.row.map(|row| (key.clone(), node.clone(), row)))
        .collect::<Vec<_>>();
    let mut evidence_roots = vec![];
    let mut evidence_keys = vec![];
    for (key, node, (value, row_proof)) in rows {
        let raw = session.materialize(row_proof, &proof_sort)?;
        evidence_roots.push(raw);
        evidence_keys.push((key.clone(), false, raw));
        if value != node.value {
            let uf = &egraph.proof_state.uf_parent[node.sort.name()];
            let row = egraph
                .read(|state| state.lookup_proof_values(uf, RawValues(vec![value])))?
                .ok_or_else(|| Error::ExtractError("missing extraction union proof".into()))?;
            let raw = session.materialize(row[1], &proof_sort)?;
            evidence_roots.push(raw);
            evidence_keys.push((key, true, raw));
        }
    }
    let (mut evidence, ids) = proof_store_from_terms(
        &egraph.proof_state.proof_names,
        session.dag,
        &evidence_roots,
        &egraph.proof_check_program,
        normalizers.clone(),
        value_constructors.clone(),
    );
    evidence
        .remove_globals(&egraph.proof_check_program)
        .map_err(|error| {
            Error::ExtractError(format!("cannot resolve extraction row evidence: {error}"))
        })?;
    for ((key, edge, raw), id) in evidence_keys.into_iter().zip(ids) {
        let proof = evidence.get(id);
        if edge {
            session.edges.insert(key.clone(), raw);
            session.canonical_terms.insert(key, proof.rhs());
        } else {
            session.rows.insert(key.clone(), (raw, proof.rhs()));
            session.canonical_terms.insert(key, proof.lhs());
        }
    }
    session.dag = evidence.term_dag;

    // lower_inputs recorded this expression's evaluation as a source action.
    // This is the only non-value Fiat introduced here; output terms never are.
    let names = &egraph.proof_state.proof_names;
    let action = session.dag.lit(Literal::Int(input_action as i64));
    let root = session.dag.lit(Literal::Int(0));
    let input_anchor = session
        .dag
        .app(names.fiat_term_constructor.clone(), vec![action, root]);
    let input_proof = session.certify(&input, Some((input_anchor, input_term)), true)?;
    let back = session
        .dag
        .app(names.eq_sym_constructor.clone(), vec![input_proof]);
    let canonical_anchor = session
        .dag
        .app(names.eq_trans_constructor.clone(), vec![input_proof, back]);
    let canonical_input = session.canonical_term(&input)?;
    let mut proof_roots = Vec::with_capacity(output_roots.len());
    for key in outputs {
        let result = session.certify(&key, Some((canonical_anchor, canonical_input)), false)?;
        proof_roots.push(
            session
                .dag
                .app(names.eq_trans_constructor.clone(), vec![back, result]),
        );
    }
    let (mut store, ids) = proof_store_from_terms(
        names,
        session.dag,
        &proof_roots,
        &egraph.proof_check_program,
        normalizers,
        value_constructors,
    );
    store
        .remove_globals(&egraph.proof_check_program)
        .map_err(|error| {
            Error::ExtractError(format!("cannot remove extraction proof globals: {error}"))
        })?;
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

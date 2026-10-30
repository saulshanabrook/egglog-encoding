//! Ground-term typechecking with contextual overload resolution.
//!
//! Shared syntax such as `(vec-empty)` may have different sorts in different
//! contexts. Each selected typing has its own node in the [`TypedTermDag`].

use std::iter::once;
use std::sync::Arc;

use crate::constraint::{Problem, assign};
use crate::core::StringOrEq;
use crate::sort::literal_sort;
use crate::util::{HashMap, HashSet, IndexMap};
use crate::{
    ArcSort, Atom, AtomTerm, Context, EGraph, FuncType, ResolvedCall, Term, TermDag, TermId,
    TypeError, TypeInfo, TypeInfoView, TypedTerm, TypedTermDag,
};
use egglog_ast::generic_ast::Literal;
use egglog_ast::span::Span;

impl EGraph {
    /// Typecheck ground terms against source signatures, resolving zero-argument
    /// global calls to their binding tables. Works with or without proof encoding.
    /// Global bindings must exist; other terms need not exist in the e-graph.
    /// Does not evaluate terms or insert rows.
    ///
    /// See [`TypeInfoView::typecheck_term_dag`] for root ordering, expected sorts,
    /// and errors. Error IDs refer to `terms`; returned IDs belong to the typed DAG.
    pub fn typecheck_term_dag(
        &self,
        terms: &TermDag,
        roots: &[(TermId, Option<ArcSort>)],
        context: Context,
    ) -> Result<(TypedTermDag, Vec<TermId>), GroundTypeError> {
        let types = self.type_info.source_types();
        types.typecheck_with_globals(terms, roots, context, &|name| {
            types.get_func_type(self.global_table(name)?.name())
        })
    }
}

impl TypeInfo {
    /// Typecheck ground terms against table signatures.
    /// See [`TypeInfoView::typecheck_term_dag`] for root typing and errors, and
    /// [`Self::source_types`] to interpret encoded views as source operations.
    ///
    /// # Example
    ///
    /// One unresolved `(vec-empty)` node can be used at two different sorts.
    /// The returned root IDs refer to separate nodes in the typed DAG.
    ///
    /// ```
    /// use egglog::{Context, EGraph, TermDag};
    ///
    /// let mut graph = EGraph::default();
    /// graph.parse_and_run_program(None, "
    ///     (sort Ints (Vec i64))
    ///     (sort Strings (Vec String))
    /// ").unwrap();
    /// let types = graph.type_info();
    /// let mut terms = TermDag::default();
    /// let empty = terms.app("vec-empty".into(), vec![]);
    /// let roots = ["Ints", "Strings"].map(|name| {
    ///     (empty, Some(types.get_sort_by_name(name).unwrap().clone()))
    /// });
    /// let (typed, roots) = types.typecheck_term_dag(&terms, &roots, Context::Read).unwrap();
    /// assert_ne!(roots[0], roots[1]);
    /// assert_eq!(typed.get(roots[0]).sort().name(), "Ints");
    /// assert_eq!(typed.get(roots[1]).sort().name(), "Strings");
    /// ```
    pub fn typecheck_term_dag(
        &self,
        terms: &TermDag,
        roots: &[(TermId, Option<ArcSort>)],
        context: Context,
    ) -> Result<(TypedTermDag, Vec<TermId>), GroundTypeError> {
        TypeInfoView::from(self).typecheck_term_dag(terms, roots, context)
    }
}

impl TypeInfoView<'_> {
    /// Typecheck the reachable ground terms, optionally constraining each
    /// root's sort. The same syntax may be requested at several root sorts.
    /// Returns the typed DAG and its root IDs in the requested order.
    /// Returned IDs belong to the new DAG, which contains only selected typings.
    /// Each child ID must precede its parent in the input DAG. Empty roots produce
    /// an empty DAG and root list; duplicate roots are preserved.
    ///
    /// Unreachable terms are ignored. Errors on variables, invalid references,
    /// type mismatches, ambiguous typings, or primitives unavailable in `context`.
    /// Does not evaluate primitives or read or write function tables.
    pub fn typecheck_term_dag(
        self,
        terms: &TermDag,
        roots: &[(TermId, Option<ArcSort>)],
        context: Context,
    ) -> Result<(TypedTermDag, Vec<TermId>), GroundTypeError> {
        self.typecheck_with_globals(terms, roots, context, &|_| None)
    }

    /// Typecheck roots with a resolver for zero-argument global calls.
    /// Each resolved signature must take a string binding name and return one value.
    fn typecheck_with_globals(
        self,
        terms: &TermDag,
        roots: &[(TermId, Option<ArcSort>)],
        context: Context,
        resolve_global: &dyn Fn(&str) -> Option<Arc<FuncType>>,
    ) -> Result<(TypedTermDag, Vec<TermId>), GroundTypeError> {
        let order = reachable_terms(terms, roots.iter().map(|(term, _)| *term))?;
        let mut inference = Inference {
            types: self,
            terms,
            context,
            resolve_global,
            candidates: HashMap::default(),
            dag: TypedTermDag::default(),
        };
        for term in order {
            let candidates = inference.infer(term)?;
            inference.candidates.insert(term, candidates);
        }
        let mut selected = Vec::with_capacity(roots.len());
        for (term, expected) in roots {
            let candidates = &inference.candidates[term];
            let candidate = match expected {
                Some(sort) => {
                    candidates
                        .get(sort.name())
                        .ok_or_else(|| GroundTypeError::WrongSort {
                            term: *term,
                            expected: sort.name().to_owned(),
                            inferred: candidates.keys().cloned().collect(),
                        })?
                }
                None if candidates.len() == 1 => candidates.values().next().unwrap(),
                None => {
                    return Err(GroundTypeError::Ambiguous {
                        term: *term,
                        sorts: candidates.keys().cloned().collect(),
                    });
                }
            };
            selected.push(candidate.node.clone()?);
        }

        // Inference may have explored unused overloads. Retain only typings
        // selected by the roots, preserving sharing and topological order.
        let mut reachable = HashSet::default();
        let mut pending = selected.clone();
        while let Some(id) = pending.pop() {
            if reachable.insert(id)
                && let TypedTerm::App(_, children) = inference.dag.get(id)
            {
                pending.extend(children.iter().copied());
            }
        }
        let mut remap = HashMap::default();
        let mut dag = TypedTermDag::default();
        for (old, expression) in inference.dag.nodes() {
            if !reachable.contains(&old) {
                continue;
            }
            let mut expression = expression.clone();
            if let TypedTerm::App(_, children) = &mut expression {
                for child in children {
                    *child = remap[child];
                }
            }
            remap.insert(old, dag.add_node(&expression));
        }
        Ok((dag, selected.into_iter().map(|id| remap[&id]).collect()))
    }
}

/// A failure to typecheck ground DAG syntax. Term IDs refer to the input DAG.
#[derive(Clone, Debug, thiserror::Error)]
pub enum GroundTypeError {
    #[error("term {term} is outside the term DAG")]
    InvalidTerm { term: TermId },
    #[error("term {term} contains the variable {name}; expected a ground term")]
    Variable { term: TermId, name: String },
    #[error("term {term} has no valid typing")]
    NoTyping { term: TermId },
    #[error("term {term} has ambiguous typings at sorts {sorts:?}")]
    Ambiguous { term: TermId, sorts: Vec<String> },
    #[error("term {term} must have sort {expected}, but has possible sorts {inferred:?}")]
    WrongSort {
        term: TermId,
        expected: String,
        inferred: Vec<String>,
    },
    #[error("cannot typecheck term {term}: {source}")]
    Type { term: TermId, source: TypeError },
}

/// One possible result sort and its resolved node, or the error for that typing.
struct Candidate {
    sort: ArcSort,
    node: Result<TermId, GroundTypeError>,
}

struct Inference<'a> {
    types: TypeInfoView<'a>,
    terms: &'a TermDag,
    context: Context,
    resolve_global: &'a dyn Fn(&str) -> Option<Arc<FuncType>>,
    /// Input node ID, then result sort name. Candidate node IDs belong to `dag`.
    candidates: HashMap<TermId, IndexMap<String, Candidate>>,
    dag: TypedTermDag,
}

impl Inference<'_> {
    fn infer(&mut self, term: TermId) -> Result<IndexMap<String, Candidate>, GroundTypeError> {
        let mut result = IndexMap::default();
        let (head, children) = match self.terms.get(term) {
            Term::Lit(lit) => {
                let sort = literal_sort(lit);
                let node = self.dag.lit(lit.clone());
                result.insert(
                    sort.name().to_owned(),
                    Candidate {
                        sort,
                        node: Ok(node),
                    },
                );
                return Ok(result);
            }
            Term::Var(name) => {
                return Err(GroundTypeError::Variable {
                    term,
                    name: name.clone(),
                });
            }
            Term::App(head, children) => (head, children),
        };
        if children.is_empty()
            && self.types.get_func_type(head).is_none()
            && self.types.get_prims(head).is_none()
            && let Some(function) = (self.resolve_global)(head)
        {
            let sort = function.output().clone();
            let key = self.dag.lit(Literal::String(head.clone()));
            let node = self.dag.app(ResolvedCall::Func(function), vec![key]);
            result.insert(
                sort.name().to_owned(),
                Candidate {
                    sort,
                    node: Ok(node),
                },
            );
            return Ok(result);
        }
        if self
            .types
            .get_func_type(head)
            .is_some_and(|f| f.is_tuple_output())
        {
            return Err(GroundTypeError::Type {
                term,
                source: TypeError::CannotExtractTupleOutput(head.clone(), Span::Panic),
            });
        }

        // Each argument position has its own variable, even when two positions
        // contain the same TermId. Syntactic sharing does not equate their types.
        let args: Vec<_> = children
            .iter()
            .enumerate()
            .map(|(i, child)| match self.terms.get(*child) {
                Term::Lit(lit) => AtomTerm::Literal(Span::Panic, lit.clone()),
                _ => AtomTerm::Var(Span::Panic, format!("arg-{i}")),
            })
            .chain(once(AtomTerm::Var(Span::Panic, "result".into())))
            .collect();
        let atom = Atom {
            span: Span::Panic,
            head: StringOrEq::Head(head.clone()),
            args,
        };
        let constraints = atom
            .get_constraints(self.types, self.context)
            .map_err(|source| GroundTypeError::Type { term, source })?;
        let mut domains: Vec<Vec<ArcSort>> = children
            .iter()
            .map(|child| {
                self.candidates[child]
                    .values()
                    .map(|c| c.sort.clone())
                    .collect()
            })
            .collect();
        let mut outputs: Vec<_> = self.types.type_info().sorts.values().cloned().collect();
        outputs.sort_by(|a, b| a.name().cmp(b.name()));
        domains.push(outputs);

        // Propagate constraints before enumerating unconstrained sorts.
        let mut pending = vec![constraints];
        let mut signatures = HashSet::default();
        let mut last_error = None;
        while let Some(constraints) = pending.pop() {
            let assignment = match (Problem {
                constraints: constraints.clone(),
                range: HashSet::default(),
            })
            .solve(|sort: &ArcSort| sort.name())
            {
                Ok(assignment) => assignment,
                Err(error) => {
                    last_error = Some(error.to_type_error());
                    continue;
                }
            };
            if atom.args.iter().zip(&domains).any(|(arg, domain)| {
                assignment
                    .get(arg)
                    .is_some_and(|sort| !domain.iter().any(|s| s.name() == sort.name()))
            }) {
                continue;
            }
            if let Some((arg, domain)) = atom
                .args
                .iter()
                .zip(&domains)
                .filter(|(arg, _)| assignment.get(arg).is_none())
                .min_by_key(|(_, domain)| domain.len())
            {
                for sort in domain.iter().rev() {
                    let mut branch = constraints.clone();
                    branch.push(assign(arg.clone(), sort.clone()));
                    pending.push(branch);
                }
                continue;
            }
            let signature: Vec<_> = atom
                .args
                .iter()
                .map(|arg| assignment.get(arg).unwrap().clone())
                .collect();
            if !signatures.insert(
                signature
                    .iter()
                    .map(|s| s.name().to_owned())
                    .collect::<Vec<_>>(),
            ) {
                continue;
            }
            let sort = signature.last().unwrap().clone();
            if let Some(previous) = result.get_mut(sort.name()) {
                previous.node = Err(GroundTypeError::Ambiguous {
                    term,
                    sorts: vec![sort.name().to_owned()],
                });
                continue;
            }
            let node = ResolvedCall::from_resolution(
                head,
                &signature,
                self.types,
                self.context,
                &Span::Panic,
            )
            .map_err(|source| GroundTypeError::Type { term, source })
            .and_then(|call| {
                let children = children
                    .iter()
                    .zip(&signature)
                    .map(|(child, sort)| self.candidates[child][sort.name()].node.clone())
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.dag.app(call, children))
            });
            result.insert(sort.name().to_owned(), Candidate { sort, node });
        }
        if result.is_empty() {
            return Err(match last_error {
                Some(source) => GroundTypeError::Type { term, source },
                None => GroundTypeError::NoTyping { term },
            });
        }
        Ok(result)
    }
}

/// Return reachable IDs in child-before-parent order.
/// Errors on invalid IDs, forward references, or cycles; ignores unreachable nodes.
fn reachable_terms(
    terms: &TermDag,
    roots: impl Iterator<Item = TermId>,
) -> Result<Vec<TermId>, GroundTypeError> {
    let mut seen = HashSet::default();
    let mut pending: Vec<_> = roots.collect();
    while let Some(term) = pending.pop() {
        if term >= terms.size() {
            return Err(GroundTypeError::InvalidTerm { term });
        }
        if seen.insert(term)
            && let Term::App(_, children) = terms.get(term)
        {
            // Reject forward references and cycles before bottom-up inference.
            for &child in children {
                if child >= term {
                    return Err(GroundTypeError::InvalidTerm { term: child });
                }
                pending.push(child);
            }
        }
    }
    let mut order: Vec<_> = seen.into_iter().collect();
    order.sort_unstable();
    Ok(order)
}

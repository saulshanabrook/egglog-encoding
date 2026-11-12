use crate::ast::FunctionSubtype;
use crate::extract::find_canonical;
use crate::termdag::{TermDag, TermId};
use crate::util::{HashMap, HashSet};
use crate::{ArcSort, EGraph, Value};
use std::vec::IntoIter;

/// A node of the search: a value together with the sort it is reconstructed at.
type Key = (Value, String);

/// Root-directed extraction for proof terms.
///
/// Unlike the public extractor, this does not compute globally optimal costs
/// for the whole e-graph. It searches for any reconstructable term for the
/// requested root, ignoring `:unextractable` and hidden constructor flags, and
/// skips view tables so proof terms use their original constructor names. A term
/// of any depth extracts without overflowing the stack.
pub(super) struct RootExtractor {
    cache: HashMap<Key, Option<TermId>>,
    active: HashSet<Key>,
}

/// What the frame on top of the stack needs from the driver.
enum Step {
    /// This child's term, before the frame can continue.
    Need(Value, ArcSort),
    /// Nothing more; the frame's answer is `None` when its node has no term.
    Done(Option<TermId>),
}

/// How to start resolving a node.
enum Begin {
    /// Nothing is known yet; push this frame.
    Push(Frame),
    /// The cache, or a cycle back to a frame already on the stack, settles it.
    Settled(Option<TermId>),
}

/// One suspended node of the search.
struct Frame {
    key: Key,
    value: Value,
    sort: ArcSort,
    stage: Stage,
}

/// How far a frame has got through the ways to reconstruct its node: the exact
/// reconstruction first, then the canonical representative's term.
enum Stage {
    /// Nothing tried yet.
    Start,
    /// Reconstructing a container from its elements, in order.
    Container {
        elements: Vec<(ArcSort, Value)>,
        children: Vec<TermId>,
    },
    /// Reconstructing an e-class from a table row.
    Eq(EqStage),
    /// Waiting on the canonical representative's term, which is the answer.
    Canonical,
}

/// The eq-sort search: functions in declaration order, and within a function its
/// matching rows in lexicographic order.
struct EqStage {
    /// Index into `egraph.functions` of the first function not yet scanned.
    unscanned: usize,
    /// The function `rows` and `row` come from.
    func: usize,
    /// Matching rows of this function in lexicographic order, still to try.
    rows: IntoIter<Vec<Value>>,
    /// The row being reconstructed, with the child terms resolved so far.
    row: Option<(Vec<Value>, Vec<TermId>)>,
}

impl EqStage {
    fn new() -> Self {
        Self {
            unscanned: 0,
            func: 0,
            rows: Vec::new().into_iter(),
            row: None,
        }
    }

    /// The next row to try for `value` at `sort`, moving on to further functions
    /// once the current one's matching rows run out.
    ///
    /// Rows come back lexicographically smallest first.
    fn next_row(&mut self, egraph: &EGraph, value: Value, sort: &ArcSort) -> Option<Vec<Value>> {
        loop {
            if let Some(row) = self.rows.next() {
                return Some(row);
            }

            let (_, func) = egraph.functions.get_index(self.unscanned)?;
            self.func = self.unscanned;
            self.unscanned += 1;
            // Term/proof relations (function-to-Unit, id in the last input) and
            // ordinary constructors both reconstruct here; views and the
            // subsumption markers (`is_proof_node_relation` is false for markers) are
            // skipped.
            if (func.decl.subtype != FunctionSubtype::Constructor && !func.is_proof_node_relation())
                || func.extraction_layout().0.name() != sort.name()
                || func.decl.role.is_view()
            {
                continue;
            }

            let mut rows = Vec::new();
            egraph.backend.for_each_matching_col(
                func.backend_id,
                func.extraction_layout().1,
                value,
                |row| {
                    if !row.subsumed {
                        rows.push(row.vals.to_vec());
                    }
                },
            );
            // Sorting makes the chosen row independent of storage and index order.
            rows.sort_unstable();
            self.rows = rows.into_iter();
        }
    }
}

impl Frame {
    /// Take this node as far as it can go, given the term its last requested
    /// child produced (`None` on the frame's first turn).
    fn advance(
        &mut self,
        egraph: &EGraph,
        termdag: &mut TermDag,
        resumed: Option<Option<TermId>>,
    ) -> Step {
        let mut child = resumed;
        loop {
            match &mut self.stage {
                Stage::Start => {
                    if self.sort.is_container_sort() {
                        self.stage = Stage::Container {
                            elements: self
                                .sort
                                .inner_values(egraph.backend.container_values(), self.value),
                            children: Vec::new(),
                        };
                    } else if self.sort.is_eq_sort() {
                        self.stage = Stage::Eq(EqStage::new());
                    } else {
                        return Step::Done(Some(self.sort.reconstruct_termdag_base(
                            egraph.backend.base_values(),
                            self.value,
                            termdag,
                        )));
                    }
                }
                // An element with no term sinks the whole container.
                Stage::Container { .. } if matches!(child, Some(None)) => {
                    return self.fall_back(egraph);
                }
                Stage::Container { elements, children } => {
                    if let Some(Some(term)) = child.take() {
                        children.push(term);
                    }
                    return match elements.get(children.len()) {
                        Some((sort, value)) => Step::Need(*value, sort.clone()),
                        None => Step::Done(Some(self.sort.reconstruct_termdag_container(
                            egraph.backend.container_values(),
                            self.value,
                            termdag,
                            std::mem::take(children),
                        ))),
                    };
                }
                Stage::Eq(eq) => {
                    match child.take() {
                        // A child with no term rules the row out; try the next.
                        Some(None) => eq.row = None,
                        Some(Some(term)) => {
                            eq.row
                                .as_mut()
                                .expect("a resolved child belongs to the pending row")
                                .1
                                .push(term);
                        }
                        None => {}
                    }
                    match &mut eq.row {
                        Some((row, children)) => {
                            let (_, func) = egraph
                                .functions
                                .get_index(eq.func)
                                .expect("the pending row's function");
                            return if children.len() == func.extraction_layout().1 {
                                Step::Done(Some(
                                    termdag.app(func.name().to_string(), std::mem::take(children)),
                                ))
                            } else {
                                let index = children.len();
                                Step::Need(row[index], func.func_type.input[index].clone())
                            };
                        }
                        None => match eq.next_row(egraph, self.value, &self.sort) {
                            Some(row) => eq.row = Some((row, Vec::new())),
                            None => return self.fall_back(egraph),
                        },
                    }
                }
                Stage::Canonical => {
                    return Step::Done(
                        child
                            .take()
                            .expect("the canonical representative was resolved"),
                    );
                }
            }
        }
    }

    /// Give up on reconstructing this node exactly and wait on the canonical
    /// representative's term instead, or report no term when the node already is
    /// the representative.
    fn fall_back(&mut self, egraph: &EGraph) -> Step {
        let canonical = find_canonical(egraph, self.value, &self.sort);
        if canonical == self.value {
            return Step::Done(None);
        }
        self.stage = Stage::Canonical;
        Step::Need(canonical, self.sort.clone())
    }
}

impl RootExtractor {
    pub(super) fn new() -> Self {
        Self {
            cache: Default::default(),
            active: Default::default(),
        }
    }

    /// Open a node, marking it in progress so a cycle back to it resolves to
    /// `None` instead of spinning.
    fn begin(&mut self, value: Value, sort: ArcSort) -> Begin {
        let key = (value, sort.name().to_owned());
        if let Some(term) = self.cache.get(&key) {
            return Begin::Settled(*term);
        }
        if !self.active.insert(key.clone()) {
            return Begin::Settled(None);
        }
        Begin::Push(Frame {
            key,
            value,
            sort,
            stage: Stage::Start,
        })
    }

    pub(super) fn extract(
        &mut self,
        egraph: &EGraph,
        termdag: &mut TermDag,
        value: Value,
        sort: &ArcSort,
    ) -> Option<TermId> {
        let mut stack = match self.begin(value, sort.clone()) {
            Begin::Push(frame) => vec![frame],
            Begin::Settled(term) => return term,
        };
        // The term the frame on top of the stack asked for, once it is known.
        let mut resumed = None;

        loop {
            let step = stack
                .last_mut()
                .expect("the loop returns as soon as the stack empties")
                .advance(egraph, termdag, resumed.take());
            match step {
                Step::Need(value, sort) => match self.begin(value, sort) {
                    Begin::Push(frame) => stack.push(frame),
                    Begin::Settled(term) => resumed = Some(term),
                },
                Step::Done(term) => {
                    let frame = stack.pop().expect("the frame that just advanced");
                    self.active.remove(&frame.key);
                    self.cache.insert(frame.key, term);
                    if stack.is_empty() {
                        return term;
                    }
                    resumed = Some(term);
                }
            }
        }
    }
}

pub(crate) fn extract_root(
    egraph: &EGraph,
    termdag: &mut TermDag,
    value: Value,
    sort: ArcSort,
) -> Option<TermId> {
    RootExtractor::new().extract(egraph, termdag, value, &sort)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn first_output(egraph: &EGraph, function_name: &str) -> Value {
        let func = egraph
            .functions
            .get(function_name)
            .unwrap_or_else(|| panic!("function `{function_name}` was not declared"));
        let mut value = None;
        egraph.backend.for_each_while(func.backend_id, |row| {
            value = Some(row.vals[func.extraction_layout().1]);
            false
        });
        value.unwrap_or_else(|| panic!("function `{function_name}` has no rows"))
    }

    fn first_input(egraph: &EGraph, function_name: &str, input: usize) -> Value {
        let func = egraph
            .functions
            .get(function_name)
            .unwrap_or_else(|| panic!("function `{function_name}` was not declared"));
        let mut value = None;
        egraph.backend.for_each_while(func.backend_id, |row| {
            value = Some(row.vals[input]);
            false
        });
        value.unwrap_or_else(|| panic!("function `{function_name}` has no rows"))
    }

    fn extract_to_string(egraph: &EGraph, value: Value, sort_name: &str) -> String {
        let mut termdag = TermDag::default();
        let term = extract_root(
            egraph,
            &mut termdag,
            value,
            egraph.get_sort_by_name(sort_name).unwrap().clone(),
        )
        .unwrap();
        termdag.to_string(term)
    }

    #[test]
    fn extracts_direct_constructor_root() {
        let mut egraph = EGraph::default();
        egraph
            .parse_and_run_program(
                None,
                r#"
                (sort Expr)
                (constructor Target () Expr)
                (Target)
                "#,
            )
            .unwrap();

        assert_eq!(
            extract_to_string(&egraph, first_output(&egraph, "Target"), "Expr"),
            "(Target)"
        );
    }

    #[test]
    fn canonicalizes_when_exact_root_is_subsumed() {
        let mut egraph = EGraph::default();
        egraph
            .parse_and_run_program(
                None,
                r#"
                (sort Expr :internal-uf UF_Expr)
                (function UF_Expr (Expr Expr) Unit :merge old :internal-hidden)
                (constructor Alias () Expr)
                (constructor Target () Expr)

                (let $alias (Alias))
                (let $target (Target))
                (set (UF_Expr $alias $target) ())
                (subsume (Alias))
                "#,
            )
            .unwrap();

        assert_eq!(
            extract_to_string(&egraph, first_output(&egraph, "Alias"), "Expr"),
            "(Target)"
        );
    }

    #[test]
    fn extracts_container_root() {
        let mut egraph = EGraph::default();
        egraph
            .parse_and_run_program(
                None,
                r#"
                (sort Expr)
                (sort ExprPair (Pair Expr Expr))
                (constructor Leaf () Expr)
                (constructor Box (ExprPair) Expr)
                (Box (pair (Leaf) (Leaf)))
                "#,
            )
            .unwrap();

        assert_eq!(
            extract_to_string(&egraph, first_input(&egraph, "Box", 0), "ExprPair"),
            "(pair (Leaf) (Leaf))"
        );
    }

    #[test]
    fn preserves_pending_rows_when_child_groups_are_loaded() {
        let mut egraph = EGraph::default();
        egraph
            .parse_and_run_program(
                None,
                r#"
                (sort Expr)
                (constructor Node (Expr) Expr)
                (constructor Leaf (i64) Expr)
                "#,
            )
            .unwrap();
        let node = egraph.functions["Node"].backend_id;
        let leaf = egraph.functions["Leaf"].backend_id;
        let root = egraph.backend.fresh_id();
        let cycle = egraph.backend.fresh_id();
        let branch = egraph.backend.fresh_id();
        let first_leaf = egraph.backend.fresh_id();
        let second_leaf = egraph.backend.fresh_id();
        let seven = egraph.backend.base_values().get(7i64);
        let nine = egraph.backend.base_values().get(9i64);
        // Root candidates sort as cycle, branch, second_leaf. The first fails
        // after loading another group; the second must remain next even though
        // the last was inserted first and also has a reconstructable term.
        egraph.backend.add_values([
            (node, vec![second_leaf, root]),
            (node, vec![cycle, root]),
            (node, vec![first_leaf, branch]),
            (node, vec![root, cycle]),
            (node, vec![branch, root]),
            (leaf, vec![seven, first_leaf]),
            (leaf, vec![nine, second_leaf]),
        ]);
        let sort = egraph.get_sort_by_name("Expr").unwrap().clone();
        let mut termdag = TermDag::default();
        let mut extractor = RootExtractor::new();
        let term = extractor
            .extract(&egraph, &mut termdag, root, &sort)
            .unwrap();
        assert_eq!(termdag.to_string(term), "(Node (Node (Leaf 7)))");
        let other = extractor
            .extract(&egraph, &mut termdag, second_leaf, &sort)
            .unwrap();
        assert_eq!(termdag.to_string(other), "(Leaf 9)");
        assert_eq!(
            extractor.extract(&egraph, &mut termdag, root, &sort),
            Some(term)
        );
    }

    #[test]
    fn active_roots_break_cycles() {
        let mut egraph = EGraph::default();
        egraph
            .parse_and_run_program(
                None,
                r#"
                (sort Expr)
                (constructor Target () Expr)
                (Target)
                "#,
            )
            .unwrap();

        let value = first_output(&egraph, "Target");
        let sort = egraph.get_sort_by_name("Expr").unwrap().clone();
        let mut extractor = RootExtractor::new();
        let mut termdag = TermDag::default();
        extractor.active.insert((value, sort.name().to_owned()));

        assert_eq!(extractor.extract(&egraph, &mut termdag, value, &sort), None);
    }
}

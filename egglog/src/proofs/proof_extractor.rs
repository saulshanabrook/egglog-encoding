use crate::ast::FunctionSubtype;
use crate::extract::find_canonical;
use crate::termdag::{TermDag, TermId};
use crate::util::{HashMap, HashSet};
use crate::{ArcSort, EGraph, Function, Value};
use egglog_backend_trait::BackendExt;
use std::ops::Range;

/// A node of the search: a value together with the sort it is reconstructed at.
type Key = (Value, String);

/// Root-directed extraction for proof terms.
///
/// Unlike the public extractor, this does not compute globally optimal costs
/// for the whole e-graph. It searches for any reconstructable term for the
/// requested root, ignoring `:unextractable` and hidden constructor flags, and
/// skips view tables and globals' rows so proof terms use their original
/// constructor names. A term
/// of any depth extracts without overflowing the stack.
struct RootExtractor {
    cache: HashMap<Key, Option<TermId>>,
    active: HashSet<Key>,
    /// Every function the search has read so far, keyed by its index in
    /// `EGraph::functions`. Scoped to one extraction run.
    scanned: HashMap<usize, FunctionRows>,
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
    /// Positions in that function's [`FunctionRows`] ordering, holding the rows
    /// that match the node's value and have not been tried yet.
    rows: Range<usize>,
    /// The row being reconstructed, with the child terms resolved so far.
    row: Option<(Vec<Value>, Vec<TermId>)>,
}

/// The non-subsumed rows of one function, grouped by the value in its
/// extraction output column.
///
/// A group's rows are in lexicographic order, so which row a search picks does
/// not depend on the backend's row iteration order — see `prove_exists`.
struct FunctionRows {
    /// Row width; zero when the function has no rows.
    arity: usize,
    /// The rows, concatenated in the order the backend yielded them.
    vals: Vec<Value>,
    /// Row numbers into `vals`, ordered by output value and then by row
    /// contents, so each group is a contiguous run.
    order: Vec<u32>,
    /// Where each output value's group sits in `order`.
    groups: HashMap<Value, Range<usize>>,
}

impl FunctionRows {
    fn build(egraph: &EGraph, func: &Function) -> Self {
        let output_idx = func.extraction_output_index();
        let mut arity = 0;
        let mut vals = Vec::new();
        egraph
            .backend
            .for_each(func.backend_id, |row: egglog_bridge::ScanEntry| {
                if !row.subsumed {
                    arity = row.vals.len();
                    vals.extend_from_slice(row.vals);
                }
            });
        vals.shrink_to_fit();

        let count = if arity == 0 { 0 } else { vals.len() / arity };
        let mut order: Vec<u32> = (0..count as u32).collect();
        order.sort_unstable_by(|&a, &b| {
            let a = &vals[a as usize * arity..][..arity];
            let b = &vals[b as usize * arity..][..arity];
            // Group by output value; order a group lexicographically by whole row.
            a[output_idx].cmp(&b[output_idx]).then_with(|| a.cmp(b))
        });

        let mut groups: HashMap<Value, Range<usize>> = HashMap::default();
        let mut start = 0;
        while start < order.len() {
            let value = vals[order[start] as usize * arity + output_idx];
            let mut end = start + 1;
            while end < order.len() && vals[order[end] as usize * arity + output_idx] == value {
                end += 1;
            }
            groups.insert(value, start..end);
            start = end;
        }

        Self {
            arity,
            vals,
            order,
            groups,
        }
    }

    /// The row at `position` in the ordering.
    fn row(&self, position: usize) -> &[Value] {
        let start = self.order[position] as usize * self.arity;
        &self.vals[start..start + self.arity]
    }

    /// Where the rows holding `value` in the output column sit in the ordering.
    fn group(&self, value: Value) -> Range<usize> {
        self.groups.get(&value).cloned().unwrap_or(0..0)
    }
}

impl EqStage {
    fn new() -> Self {
        Self {
            unscanned: 0,
            func: 0,
            rows: 0..0,
            row: None,
        }
    }

    /// The next row to try for `value` at `sort`, moving on to further functions
    /// once the current one's matching rows run out.
    ///
    /// Rows come back lexicographically smallest first (see [`FunctionRows`]).
    fn next_row(
        &mut self,
        egraph: &EGraph,
        scanned: &mut HashMap<usize, FunctionRows>,
        value: Value,
        sort: &ArcSort,
    ) -> Option<Vec<Value>> {
        loop {
            if let Some(position) = self.rows.next() {
                let rows = scanned
                    .get(&self.func)
                    .expect("the function whose rows are being tried was scanned");
                return Some(rows.row(position).to_vec());
            }

            let (_, func) = egraph.functions.get_index(self.unscanned)?;
            self.func = self.unscanned;
            self.unscanned += 1;
            // Term/proof relations (function-to-Unit, id in the last input) and
            // ordinary constructors both reconstruct here; views and the
            // subsumption markers (`is_relation_term` is false for markers) are
            // skipped. So is a global's row: it only aliases the term it was bound
            // to, so a proof stated over the alias would not line up at a
            // congruence step.
            let aliases_a_term = func.decl.internal_let;
            if (func.decl.subtype != FunctionSubtype::Constructor && !func.is_relation_term())
                || func.extraction_output_sort().name() != sort.name()
                || func.decl.term_constructor.is_some()
                || aliases_a_term
            {
                continue;
            }

            self.rows = scanned
                .entry(self.func)
                .or_insert_with(|| FunctionRows::build(egraph, func))
                .group(value);
        }
    }
}

impl Frame {
    /// Take this node as far as it can go, given the term its last requested
    /// child produced (`None` on the frame's first turn).
    fn advance(
        &mut self,
        egraph: &EGraph,
        scanned: &mut HashMap<usize, FunctionRows>,
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
                            return if children.len() == func.extraction_num_children() {
                                Step::Done(Some(termdag.app(
                                    func.extraction_term_name().to_string(),
                                    std::mem::take(children),
                                )))
                            } else {
                                let index = children.len();
                                Step::Need(row[index], func.schema.input[index].clone())
                            };
                        }
                        None => match eq.next_row(egraph, scanned, self.value, &self.sort) {
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
    fn new() -> Self {
        Self {
            cache: Default::default(),
            active: Default::default(),
            scanned: Default::default(),
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

    fn extract(
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
                .advance(egraph, &mut self.scanned, termdag, resumed.take());
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
            value = Some(row.vals[func.extraction_output_index()]);
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

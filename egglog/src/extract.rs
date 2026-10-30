//! Cost models used by extraction.
//!
//! [`Cost`] is the minimum requirement for ranking extracted terms.
//! [`TreeCostModel`] computes a node annotation and then folds it with selected
//! child costs. The annotation can carry context that should not be part of the
//! final cost, so tree extraction does not require costs to support addition.
//!
//! [`MonoidCost`] adds the associative and commutative combination operation
//! needed to charge shared dependencies once. [`DagCostModel`] computes the
//! marginal costs consumed by DAG extractors. [`TreeCostModelFromDag`] adapts
//! such a model to tree extraction by combining each node's marginal cost with
//! its selected child costs. [`DEFAULT_COST_MODEL`] is the default additive
//! tree model.

use crate::termdag::{TermDag, TermId};
use crate::util::{HashMap, HashSet};
use crate::*;
use numeric_id::NumericId;
use std::collections::VecDeque;

/// A value that can be used to rank extraction candidates.
pub trait Cost: Clone + Ord {}

impl<T: Clone + Ord> Cost for T {}

/// An extraction cost with an identity and a combination operation.
///
/// Implementations must make `identity` a two-sided identity and `combine`
/// associative, commutative, deterministic, non-panicking, and monotone with
/// respect to [`Cost`]'s ordering. Rust cannot enforce these laws.
pub trait MonoidCost: Cost {
    /// The identity cost, usually zero.
    fn identity() -> Self;

    /// Combines two costs without overflowing or panicking.
    fn combine(self, other: &Self) -> Self;
}

macro_rules! monoid_unsigned_cost {
    ($($cost:ty),* $(,)?) => {$(
        impl MonoidCost for $cost {
            fn identity() -> Self {
                0
            }

            fn combine(self, other: &Self) -> Self {
                self.saturating_add(*other)
            }
        }
    )*};
}

monoid_unsigned_cost!(u8, u16, u32, u64, u128, usize);

macro_rules! monoid_exact_cost {
    ($($cost:ty),* $(,)?) => {$(
        impl MonoidCost for $cost {
            fn identity() -> Self {
                use num::Zero;
                Self::zero()
            }

            fn combine(self, other: &Self) -> Self {
                self + other
            }
        }
    )*};
}

monoid_exact_cost!(num::BigInt, num::BigRational);

/// Computes marginal costs for extraction that charges shared dependencies once.
///
/// The returned costs exclude selected child and container-element costs.
/// Implementations must return equal costs for equivalent arguments during one
/// extraction.
pub trait DagCostModel<C: MonoidCost> {
    /// Computes the cost of a non-container primitive value.
    fn base_value_cost(&self, egraph: &EGraph, sort: &ArcSort, value: Value) -> C;
    /// Computes an enode's cost, excluding its children.
    fn enode_cost(&self, egraph: &EGraph, func: &Function, enode: &Enode<'_>) -> C;

    /// Computes a container's cost, excluding its elements.
    fn container_cost(&self, egraph: &EGraph, sort: &ArcSort, value: Value) -> C {
        let _ = (egraph, sort, value);
        C::identity()
    }
}

/// Computes tree-extraction costs from node annotations and selected child costs.
///
/// Models used by [`TreeExtractor`] must be deterministic and satisfy optimal
/// substructure: replacing a child with a lower-cost extraction must not make
/// its parent more expensive. They must also avoid making cyclic terms improve
/// indefinitely. Otherwise extraction may be non-optimal, fail to converge, or
/// fail during reconstruction. The annotation types let the first stage retain
/// context, such as the constructor kind, without encoding it in `C`.
pub trait TreeCostModel<C: Cost> {
    /// Context retained between [`TreeCostModel::enode_cost`] and its fold.
    type EnodeCost;
    /// Context retained between [`TreeCostModel::container_cost`] and its fold.
    type ContainerCost;

    /// Computes the cost of a non-container primitive value.
    fn base_value_cost(&self, egraph: &EGraph, sort: &ArcSort, value: Value) -> C;

    /// Computes the annotation folded with an enode's selected child costs.
    fn enode_cost(&self, egraph: &EGraph, func: &Function, enode: &Enode<'_>) -> Self::EnodeCost;

    /// Computes the annotation folded with a container's selected element costs.
    fn container_cost(&self, egraph: &EGraph, sort: &ArcSort, value: Value) -> Self::ContainerCost;

    /// Produces an enode's total cost from its annotation and child costs.
    fn fold_enode_cost(&self, enode_cost: Self::EnodeCost, child_costs: &[C]) -> C;

    /// Produces a container's total cost from its annotation and element costs.
    fn fold_container_cost(&self, container_cost: Self::ContainerCost, element_costs: &[C]) -> C;
}

trait TreeExtractorCostModel<C: Cost> {
    fn base_value_cost(&self, egraph: &EGraph, sort: &ArcSort, value: Value) -> C;
    fn total_enode_cost(
        &self,
        egraph: &EGraph,
        func: &Function,
        enode: &Enode<'_>,
        child_costs: &[C],
    ) -> C;
    fn total_container_cost(
        &self,
        egraph: &EGraph,
        sort: &ArcSort,
        value: Value,
        element_costs: &[C],
    ) -> C;
}

impl<C: Cost, M: TreeCostModel<C>> TreeExtractorCostModel<C> for M {
    fn base_value_cost(&self, egraph: &EGraph, sort: &ArcSort, value: Value) -> C {
        TreeCostModel::base_value_cost(self, egraph, sort, value)
    }

    fn total_enode_cost(
        &self,
        egraph: &EGraph,
        func: &Function,
        enode: &Enode<'_>,
        child_costs: &[C],
    ) -> C {
        self.fold_enode_cost(self.enode_cost(egraph, func, enode), child_costs)
    }

    fn total_container_cost(
        &self,
        egraph: &EGraph,
        sort: &ArcSort,
        value: Value,
        element_costs: &[C],
    ) -> C {
        self.fold_container_cost(self.container_cost(egraph, sort, value), element_costs)
    }
}

/// Adapts a [`DagCostModel`] to tree extraction by combining marginal costs.
#[derive(Clone, Debug)]
pub struct TreeCostModelFromDag<M>(pub M);

impl<C: MonoidCost, M: DagCostModel<C>> TreeCostModel<C> for TreeCostModelFromDag<M> {
    type EnodeCost = C;
    type ContainerCost = C;

    fn base_value_cost(&self, egraph: &EGraph, sort: &ArcSort, value: Value) -> C {
        self.0.base_value_cost(egraph, sort, value)
    }

    fn enode_cost(&self, egraph: &EGraph, func: &Function, enode: &Enode<'_>) -> C {
        self.0.enode_cost(egraph, func, enode)
    }

    fn container_cost(&self, egraph: &EGraph, sort: &ArcSort, value: Value) -> C {
        self.0.container_cost(egraph, sort, value)
    }

    fn fold_enode_cost(&self, enode_cost: C, child_costs: &[C]) -> C {
        child_costs
            .iter()
            .fold(enode_cost, |cost, child| cost.combine(child))
    }

    fn fold_container_cost(&self, container_cost: C, element_costs: &[C]) -> C {
        element_costs
            .iter()
            .fold(container_cost, |cost, element| cost.combine(element))
    }
}

/// The default extraction cost type.
pub type DefaultCost = u64;

/// The marginal-cost model underlying default tree and DAG extraction.
///
/// With [`DefaultCost`], constructor `:cost` declarations override `node_cost`
/// and selected child costs are combined with each constructor's cost.
#[derive(Clone, Debug)]
pub struct AdditiveCostModel {
    /// The fallback cost for primitive values and constructors without `:cost`.
    pub node_cost: DefaultCost,
}

impl Default for AdditiveCostModel {
    fn default() -> Self {
        Self { node_cost: 1 }
    }
}

/// The default additive model used by tree extraction.
pub const DEFAULT_COST_MODEL: TreeCostModelFromDag<AdditiveCostModel> =
    TreeCostModelFromDag(AdditiveCostModel { node_cost: 1 });

impl DagCostModel<DefaultCost> for AdditiveCostModel {
    fn base_value_cost(&self, _egraph: &EGraph, _sort: &ArcSort, _value: Value) -> DefaultCost {
        self.node_cost
    }

    fn enode_cost(&self, egraph: &EGraph, func: &Function, _enode: &Enode<'_>) -> DefaultCost {
        func.extraction_head_cost(egraph).unwrap_or(self.node_cost)
    }
}

/// One extracted root or root variant.
///
/// The cost is the objective value assigned by the selected extractor. Tree
/// extraction reports tree cost; DAG extractors may instead report a per-root
/// or per-variant DAG cost. `term` indexes the enclosing result's shared
/// [`TermDag`].
#[derive(Clone, Debug)]
pub struct ExtractedTerm<C> {
    /// The selected extractor's cost for this result.
    pub cost: C,
    /// The extracted root in the enclosing result's [`TermDag`].
    pub term: TermId,
}

/// Best-extraction results for a batch of requested roots.
///
/// All returned term ids index the shared [`ExtractedTerms::termdag`].
#[derive(Clone, Debug)]
pub struct ExtractedTerms<C> {
    /// Shared term storage for every extracted root.
    pub termdag: TermDag,
    /// One extraction result per requested root, in request order.
    ///
    /// `None` means that root is unextractable with the selected cost model and
    /// available constructors.
    pub terms: Vec<Option<ExtractedTerm<C>>>,
}

/// Root-variant extraction results for a batch of requested roots.
///
/// All returned term ids index the shared [`ExtractedTermVariants::termdag`].
#[derive(Clone, Debug)]
pub struct ExtractedTermVariants<C> {
    /// Shared term storage for every extracted variant.
    pub termdag: TermDag,
    /// Outer vector follows requested-root order; each inner vector contains that root's variants.
    pub variants: Vec<Vec<ExtractedTerm<C>>>,
}

struct CommandCostModel;

impl DagCostModel<DefaultCost> for CommandCostModel {
    fn base_value_cost(&self, _: &EGraph, _: &ArcSort, _: Value) -> DefaultCost {
        1
    }

    fn enode_cost(&self, egraph: &EGraph, func: &Function, enode: &Enode<'_>) -> DefaultCost {
        (egraph.extraction_cost)(egraph, func, enode)
    }
}

/// Bellman-Ford-like tree extraction with reusable cost preparation.
///
/// The prepared state borrows the e-graph because reconstruction still needs
/// its sort storage and constructor metadata. This prevents prepared costs from
/// being used after the e-graph is mutated.
pub struct TreeExtractor<'g, C: Cost> {
    egraph: &'g EGraph,
    funcs: Vec<String>,
    cost_model: Box<dyn TreeExtractorCostModel<C> + 'g>,
    /// Dense id assigned to each eq sort that some extractable function outputs;
    /// indexes into `costs` and `parent_edge`.
    sort_ids: HashMap<String, usize>,
    costs: Vec<HashMap<Value, RankedCost<C>>>,
    parent_edge: Vec<HashMap<Value, (usize, Vec<Value>)>>,
}

/// Every successful relaxation updates the cost and chronological rank together.
struct RankedCost<C> {
    cost: C,
    rank: usize,
}

/// How extraction treats one child column of a function, resolved once so the
/// per-row cost loops avoid repeated sort dispatch and name-keyed lookups.
enum ChildKind {
    /// An eq-sort column; `Some` holds the sort's dense id, `None` means no
    /// extractable function outputs this sort (its terms have no cost).
    EqSort(Option<usize>),
    Container(ArcSort),
    Base(ArcSort),
}

/// Per-function data for [`TreeExtractor::bellman_ford`]: resolved schema facts
/// plus a flat materialized copy of the table's non-subsumed rows, so each
/// relaxation pass iterates memory instead of re-scanning the table.
struct FuncData<'a> {
    func: &'a Function,
    /// Row width in `rows`: the function's inputs plus its output columns.
    arity: usize,
    output_idx: usize,
    output_sort_id: usize,
    child_kinds: Vec<ChildKind>,
    rows: Vec<Value>,
}

/// The rows reading each eq value as a child, directly or inside a container.
///
/// Eq-sort ids come from one backend counter, so a value alone names its class.
struct ChildIndex {
    /// Each read value's local id, an index into `offsets`.
    ids: HashMap<Value, u32>,
    /// `offsets[l]..offsets[l + 1]` is the run in `readers` for local id `l`.
    offsets: Vec<u32>,
    /// `(function, row)` pairs, one run per value.
    readers: Vec<(u32, u32)>,
}

impl ChildIndex {
    /// Indexes the `(value, function, row)` triples that `reads` yields. Each
    /// call to `reads` must yield the same triples in the same order. Panics
    /// past 2^32 triples.
    fn new<I: Iterator<Item = (Value, u32, u32)>>(reads: impl Fn() -> I) -> Self {
        // `locals` holds each read's value, then its local id. A value's offset
        // counts its reads, then holds its run's end; the fill pass moves it back
        // to the run's start.
        let mut ids: HashMap<Value, u32> = HashMap::default();
        let mut offsets: Vec<u32> = Vec::new();
        let mut locals: Vec<u32> = Vec::new();
        reads().for_each(|(value, _, _)| locals.push(value.rep()));
        for read in &mut locals {
            let local = *ids.entry(Value::new(*read)).or_insert_with(|| {
                offsets.push(0);
                (offsets.len() - 1) as u32
            });
            offsets[local as usize] += 1;
            *read = local;
        }
        assert!(
            u32::try_from(locals.len()).is_ok(),
            "extraction index exceeds 2^32 child reads"
        );
        let mut end = 0;
        for offset in offsets.iter_mut() {
            end += *offset;
            *offset = end;
        }
        offsets.reserve_exact(1);
        offsets.push(end);
        let mut readers = vec![(0, 0); locals.len()];
        let mut read = 0;
        reads().for_each(|(_, function, row)| {
            let start = &mut offsets[locals[read] as usize];
            read += 1;
            *start -= 1;
            readers[*start as usize] = (function, row);
        });
        ChildIndex {
            ids,
            offsets,
            readers,
        }
    }

    /// The `(function, row)` pairs reading `value`, in no particular order.
    fn readers(&self, value: Value) -> &[(u32, u32)] {
        self.ids.get(&value).map_or(&[], |&local| {
            let local = local as usize;
            &self.readers[self.offsets[local] as usize..self.offsets[local + 1] as usize]
        })
    }
}

/// Dirty rows are visited in sweep order.
struct DirtyRows {
    words: Vec<u64>,
    count: usize,
}

impl DirtyRows {
    fn full(len: usize) -> Self {
        let mut words = vec![u64::MAX; len.div_ceil(64)];
        if let Some(last) = words.last_mut() {
            *last >>= len.div_ceil(64) * 64 - len; // clear the padding bits
        }
        Self { words, count: len }
    }

    fn insert(&mut self, row: usize) {
        let bit = 1 << (row % 64);
        let word = &mut self.words[row / 64];
        if *word & bit == 0 {
            *word |= bit;
            self.count += 1;
        }
    }

    fn pop_from(&mut self, cursor: usize) -> Option<usize> {
        if self.count == 0 {
            return None;
        }
        let mut wi = cursor / 64;
        let mut pending = *self.words.get(wi)? & (u64::MAX << (cursor % 64));
        while pending == 0 {
            wi += 1;
            pending = *self.words.get(wi)?;
        }
        let bit = pending.trailing_zeros() as usize;
        self.words[wi] &= !(1 << bit);
        self.count -= 1;
        Some(wi * 64 + bit)
    }
}

impl<'g, C: Cost> TreeExtractor<'g, C> {
    /// Prepares extraction costs for constructors reachable from `rootsorts`.
    ///
    /// Pass `None` to prepare every extractable root sort. Later calls to
    /// [`TreeExtractor::extract_best_with_sort`] and
    /// [`TreeExtractor::extract_variants_with_sort`] reuse the prepared best
    /// costs and producer choices.
    ///
    /// Primitive and container roots are costed when extracted. Variant
    /// extraction also uses the model to rescore candidate root enodes, so the
    /// model must return stable results for the extractor's lifetime.
    pub fn compute_costs_from_rootsorts(
        rootsorts: Option<Vec<ArcSort>>,
        egraph: &'g EGraph,
        cost_model: impl TreeCostModel<C> + 'g,
    ) -> Self {
        // We filter out tables unreachable from the root sorts
        let extract_all_sorts = rootsorts.is_none();

        let mut rootsorts = rootsorts.unwrap_or_default();

        // Built a reverse index from output sort to function head symbols
        // Only include constructors (not regular functions), and respect the user-facing
        // hidden and unextractable flags.
        let mut rev_index: HashMap<String, Vec<String>> = Default::default();
        for func in egraph.functions.iter() {
            let unextractable = func.1.decl.unextractable;
            let hidden = func.1.decl.internal_hidden;

            // Only extract constructors and view tables, which reconstruct as their
            // their own head. Proof extraction uses its own root-directed extractor
            // and does not need alternate behavior here.
            if !unextractable
                && !hidden
                && (func.1.decl.subtype == FunctionSubtype::Constructor
                    || func.1.decl.role.is_view())
            {
                let func_name = func.0.clone();
                let (output_sort, _) = func.1.extraction_layout();
                let output_sort_name = output_sort.name();
                if let Some(v) = rev_index.get_mut(output_sort_name) {
                    v.push(func_name);
                } else {
                    rev_index.insert(output_sort_name.to_owned(), vec![func_name]);
                    if extract_all_sorts {
                        rootsorts.push(output_sort.clone());
                    }
                }
            }
        }

        // Do a BFS to find reachable tables
        let mut q: VecDeque<ArcSort> = VecDeque::new();
        let mut seen: HashSet<String> = Default::default();
        for rootsort in rootsorts.iter() {
            if seen.insert(rootsort.name().to_owned()) {
                q.push_back(rootsort.clone());
            }
        }

        let mut funcs_set: HashSet<String> = Default::default();
        let mut funcs: Vec<String> = Vec::new();
        while !q.is_empty() {
            let sort = q.pop_front().unwrap();
            if sort.is_container_sort() {
                let inner_sorts = sort.inner_sorts();
                for s in inner_sorts {
                    if !seen.contains(s.name()) {
                        q.push_back(s.clone());
                        seen.insert(s.name().to_owned());
                    }
                }
            } else if sort.is_eq_sort()
                && let Some(head_symbols) = rev_index.get(sort.name())
            {
                for h in head_symbols {
                    if !funcs_set.contains(h) {
                        let func = egraph.functions.get(h).unwrap();
                        let num_children = func.extraction_layout().1;
                        for ch in func.func_type.input.iter().take(num_children) {
                            let ch_name = ch.name();
                            if !seen.contains(ch_name) {
                                q.push_back(ch.clone());
                                seen.insert(ch_name.to_owned());
                            }
                        }
                        funcs_set.insert(h.clone());
                        funcs.push(h.clone());
                    }
                }
            }
        }

        // Initialize the tables to have the reachable entries
        let mut sort_ids: HashMap<String, usize> = Default::default();
        for func_name in funcs.iter() {
            let func = egraph.functions.get(func_name).unwrap();
            let output_sort_name = func.extraction_layout().0.name();
            let next_id = sort_ids.len();
            sort_ids
                .entry(output_sort_name.to_owned())
                .or_insert(next_id);
        }
        let n_sorts = sort_ids.len();

        let mut extractor = TreeExtractor {
            egraph,
            funcs,
            cost_model: Box::new(cost_model),
            sort_ids,
            costs: (0..n_sorts).map(|_| Default::default()).collect(),
            parent_edge: (0..n_sorts).map(|_| Default::default()).collect(),
        };

        extractor.bellman_ford(egraph);

        extractor
    }

    /// Compute the cost of a single enode
    /// Recurse if container
    /// Returns None if contains an undefined eqsort term (potentially after unfolding)
    fn compute_cost_node(&self, egraph: &EGraph, value: Value, sort: &ArcSort) -> Option<C> {
        if sort.is_container_sort() {
            let elements = sort.inner_values(egraph.backend.container_values(), value);
            let mut ch_costs: Vec<C> = Vec::new();
            for ch in elements.iter() {
                ch_costs.push(self.compute_cost_node(egraph, ch.1, &ch.0)?);
            }
            Some(
                self.cost_model
                    .total_container_cost(egraph, sort, value, &ch_costs),
            )
        } else if sort.is_eq_sort() {
            self.costs[*self.sort_ids.get(sort.name())?]
                .get(&value)
                .map(|entry| entry.cost.clone())
        } else {
            // Primitive
            Some(self.cost_model.base_value_cost(egraph, sort, value))
        }
    }

    /// A row in a constructor table is a hyperedge from the set of input terms to the constructed output term.
    fn compute_cost_hyperedge(
        &self,
        egraph: &EGraph,
        row: &egglog_bridge::ScanEntry,
        func: &Function,
    ) -> Option<C> {
        let mut ch_costs: Vec<C> = Vec::new();
        let sorts = &func.func_type.input;
        let output_idx = func.extraction_layout().1;
        for (value, sort) in row.vals.iter().take(output_idx).zip(sorts.iter()) {
            ch_costs.push(self.compute_cost_node(egraph, *value, sort)?);
        }
        let head_name = func.name();
        let enode = Enode {
            name: head_name,
            children: &row.vals[..output_idx],
            eclass: row.vals[output_idx],
            subsumed: row.subsumed,
        };
        let cost_func = func;
        Some(
            self.cost_model
                .total_enode_cost(egraph, cost_func, &enode, &ch_costs),
        )
    }

    fn compute_topo_rnk_node(&self, egraph: &EGraph, value: Value, sort: &ArcSort) -> usize {
        if sort.is_container_sort() {
            sort.inner_values(egraph.backend.container_values(), value)
                .iter()
                .fold(0, |ret, (sort, value)| {
                    usize::max(ret, self.compute_topo_rnk_node(egraph, *value, sort))
                })
        } else if sort.is_eq_sort() {
            if let Some(id) = self.sort_ids.get(sort.name()) {
                self.costs[*id]
                    .get(&value)
                    .map_or(usize::MAX, |entry| entry.rank)
            } else {
                usize::MAX
            }
        } else {
            0
        }
    }

    /// Compute the child costs of one materialized row into `ch_costs`, and fold them
    /// into the row's total cost. Returns `None` if any child is uncomputed so far.
    fn row_cost(
        &self,
        egraph: &EGraph,
        f: &FuncData,
        row: &[Value],
        ch_costs: &mut Vec<C>,
    ) -> Option<C> {
        ch_costs.clear();
        for (kind, value) in f.child_kinds.iter().zip(row) {
            ch_costs.push(match kind {
                ChildKind::EqSort(Some(id)) => self.costs[*id].get(value)?.cost.clone(),
                ChildKind::EqSort(None) => return None,
                ChildKind::Container(sort) => self.compute_cost_node(egraph, *value, sort)?,
                ChildKind::Base(sort) => self.cost_model.base_value_cost(egraph, sort, *value),
            });
        }
        let enode = Enode {
            name: f.func.name(),
            children: &row[..f.output_idx],
            eclass: row[f.output_idx],
            subsumed: false,
        };
        Some(
            self.cost_model
                .total_enode_cost(egraph, f.func, &enode, ch_costs),
        )
    }

    /// The chronological rank of one child; a row's edge rank is its children's maximum.
    fn child_rank(&self, egraph: &EGraph, kind: &ChildKind, value: Value) -> usize {
        match kind {
            ChildKind::EqSort(Some(id)) => self.costs[*id]
                .get(&value)
                .map_or(usize::MAX, |entry| entry.rank),
            ChildKind::EqSort(None) => usize::MAX,
            ChildKind::Container(sort) => self.compute_topo_rnk_node(egraph, value, sort),
            ChildKind::Base(_) => 0,
        }
    }

    /// Report every eq value a container value's cost depends on, found by
    /// recursing through nested container values.
    fn register_container_deps(
        &self,
        egraph: &EGraph,
        sort: &ArcSort,
        value: Value,
        register: &mut impl FnMut(Value),
    ) {
        if sort.is_container_sort() {
            for (inner_sort, inner_value) in
                sort.inner_values(egraph.backend.container_values(), value)
            {
                self.register_container_deps(egraph, &inner_sort, inner_value, register);
            }
        } else if sort.is_eq_sort() && self.sort_ids.contains_key(sort.name()) {
            register(value);
        }
    }

    /// Builds the [`ChildIndex`] of `func_data`.
    fn child_index(&self, egraph: &EGraph, func_data: &[FuncData]) -> ChildIndex {
        // Walking a container allocates, so each is walked once and its reads kept.
        let mut container_reads = Vec::new();
        for (fi, f) in func_data.iter().enumerate() {
            if !f
                .child_kinds
                .iter()
                .any(|k| matches!(k, ChildKind::Container(_)))
            {
                continue;
            }
            for (ri, row) in f.rows.chunks_exact(f.arity).enumerate() {
                for (kind, value) in f.child_kinds.iter().zip(row) {
                    if let ChildKind::Container(sort) = kind {
                        self.register_container_deps(egraph, sort, *value, &mut |v| {
                            container_reads.push((v, fi as u32, ri as u32))
                        });
                    }
                }
            }
        }
        ChildIndex::new(|| {
            func_data
                .iter()
                .enumerate()
                .flat_map(|(fi, f)| {
                    f.rows
                        .chunks_exact(f.arity)
                        .enumerate()
                        .flat_map(move |(ri, row)| {
                            f.child_kinds
                                .iter()
                                .zip(row)
                                .filter_map(move |(kind, value)| {
                                    matches!(kind, ChildKind::EqSort(Some(_)))
                                        .then_some((*value, fi as u32, ri as u32))
                                })
                        })
                })
                .chain(container_reads.iter().copied())
        })
    }

    /// We use Bellman-Ford to compute the costs of the relevant eq sorts' terms
    /// [Bellman-Ford](https://en.wikipedia.org/wiki/Bellman%E2%80%93Ford_algorithm) is a shortest path algorithm.
    /// The version implemented here computes the shortest path from any node in a set of sources to all the reachable nodes.
    /// Computing the minimum cost for terms is treated as a shortest path problem on a hypergraph here.
    /// In this hypergraph, the nodes corresponde to eclasses, the distances are the costs to extract a term of those eclasses,
    /// and each enode is a hyperedge that goes from the set of children eclasses to the enode's eclass.
    /// The sources are the eclasses with known costs from the cost model.
    /// Additionally, to avoid cycles in the extraction even when the cost model can assign an equal cost to a term and its subterm.
    /// It computes a topological rank for each eclass
    /// and only allows each eclass to have children of classes of strictly smaller ranks in the extraction.
    fn bellman_ford(&mut self, egraph: &EGraph) {
        // Materialize each function's non-subsumed rows once, so the relaxation
        // passes below iterate plain memory instead of re-scanning every table.
        let func_data: Vec<FuncData> = self
            .funcs
            .iter()
            .map(|func_name| {
                let func = egraph.functions.get(func_name).unwrap();
                let (target_sort, num_children) = func.extraction_layout();
                let child_kinds = func.func_type.input[..num_children]
                    .iter()
                    .map(|sort| {
                        if sort.is_container_sort() {
                            ChildKind::Container(sort.clone())
                        } else if sort.is_eq_sort() {
                            ChildKind::EqSort(self.sort_ids.get(sort.name()).copied())
                        } else {
                            ChildKind::Base(sort.clone())
                        }
                    })
                    .collect();
                let arity = func.func_type.input.len() + func.func_type.outputs.len();
                // Reserved from the table's size at the first live row, so the copy never
                // regrows and a fully subsumed table allocates nothing.
                let reserve = egraph.backend.table_size(func.backend_id) * arity;
                let mut rows = Vec::new();
                egraph.backend.for_each(func.backend_id, |row| {
                    if !row.subsumed {
                        if rows.is_empty() {
                            rows.reserve_exact(reserve);
                        }
                        rows.extend_from_slice(row.vals);
                    }
                });
                FuncData {
                    func,
                    arity,
                    output_idx: num_children,
                    output_sort_id: self.sort_ids[target_sort.name()],
                    child_kinds,
                    rows,
                }
            })
            .collect();

        let child_index = self.child_index(egraph, &func_data);

        let mut topo_rnk_cnt = 0usize;
        // Semi-naive relaxation: a row recomputes exactly the same cost against a
        // never-increasing target unless one of its child (sort, value) costs
        // changed since the row was last evaluated, so only such "dirty" rows are
        // (re)visited.
        let mut dirty: Vec<DirtyRows> = func_data
            .iter()
            .map(|f| DirtyRows::full(f.rows.len() / f.arity))
            .collect();

        let mut ch_costs: Vec<C> = Vec::new();
        loop {
            let mut any = false;
            for (fi, f) in func_data.iter().enumerate() {
                if dirty[fi].count == 0 {
                    continue;
                }
                any = true;
                // Marks set at or behind the sweep cursor (including a row
                // re-marking itself) stay for the next sweep; marks ahead of it
                // are picked up in this one, matching the naive pass exactly.
                let mut cursor = 0;
                while let Some(ri) = dirty[fi].pop_from(cursor) {
                    cursor = ri + 1;
                    let row = &f.rows[ri * f.arity..(ri + 1) * f.arity];
                    let Some(new_cost) = self.row_cost(egraph, f, row, &mut ch_costs) else {
                        continue;
                    };
                    let target = row[f.output_idx];
                    let entry = self.costs[f.output_sort_id].entry(target);
                    if let HEntry::Occupied(old) = &entry
                        && new_cost >= old.get().cost
                    {
                        continue;
                    }
                    // record the chronological order of the updates
                    // which serves as a topological order that avoids cycles
                    // even when a term has a cost equal to its subterms
                    topo_rnk_cnt += 1;
                    entry.insert(RankedCost {
                        cost: new_cost,
                        rank: topo_rnk_cnt,
                    });
                    for &(dfi, dri) in child_index.readers(target) {
                        dirty[dfi as usize].insert(dri as usize);
                    }
                }
            }
            if !any {
                break;
            }
        }

        // Free the scheduler's state before the parent edges allocate.
        drop((child_index, dirty));

        // Save the edges for reconstruction
        for (parents, costs) in self.parent_edge.iter_mut().zip(&self.costs) {
            parents.reserve(costs.len());
        }
        for (fi, f) in func_data.into_iter().enumerate() {
            for row in f.rows.chunks_exact(f.arity) {
                let target = row[f.output_idx];
                let Some(best) = self.costs[f.output_sort_id].get(&target) else {
                    continue;
                };
                // one of the possible best parent edges
                if self.row_cost(egraph, &f, row, &mut ch_costs).as_ref() != Some(&best.cost) {
                    continue;
                }
                let edge_rank = f
                    .child_kinds
                    .iter()
                    .zip(row)
                    .map(|(kind, value)| self.child_rank(egraph, kind, *value))
                    .max()
                    .unwrap_or(0);
                // one of the parent edges that avoids cycles
                if best.rank > edge_rank
                    && let HEntry::Vacant(e) = self.parent_edge[f.output_sort_id].entry(target)
                {
                    e.insert((fi, row.to_vec()));
                }
            }
        }
    }

    /// This recursively reconstruct the termdag that gives the minimum cost for eclass value.
    fn reconstruct_termdag_node_helper(
        &self,
        egraph: &EGraph,
        termdag: &mut TermDag,
        value: Value,
        sort: &ArcSort,
        cache: &mut HashMap<(Value, String), TermId>,
    ) -> TermId {
        let key = (value, sort.name().to_owned());
        if let Some(term) = cache.get(&key) {
            return *term;
        }

        let term = if sort.is_container_sort() {
            let elements = sort.inner_values(egraph.backend.container_values(), value);
            let mut ch_terms: Vec<TermId> = Vec::new();
            for ch in elements.iter() {
                ch_terms.push(
                    self.reconstruct_termdag_node_helper(egraph, termdag, ch.1, &ch.0, cache),
                );
            }
            sort.reconstruct_termdag_container(
                egraph.backend.container_values(),
                value,
                termdag,
                ch_terms,
            )
        } else if sort.is_eq_sort() {
            let (function, hyperedge) = self.parent_edge[self.sort_ids[sort.name()]]
                .get(&value)
                .unwrap();
            let func = egraph.functions.get(&self.funcs[*function]).unwrap();
            let ch_sorts = &func.func_type.input;

            let num_children = func.extraction_layout().1;
            let output_name = func.name();

            let mut ch_terms: Vec<TermId> = Vec::new();
            for (value, sort) in hyperedge.iter().take(num_children).zip(ch_sorts.iter()) {
                ch_terms.push(
                    self.reconstruct_termdag_node_helper(egraph, termdag, *value, sort, cache),
                );
            }
            termdag.app(output_name.to_string(), ch_terms)
        } else {
            // Base value case
            sort.reconstruct_termdag_base(egraph.backend.base_values(), value, termdag)
        };

        cache.insert(key, term);
        term
    }

    /// Extracts the best term for `value` from a prepared sort.
    ///
    /// `sort` may be a requested root sort, a sort reachable from those roots,
    /// a primitive sort, or a container of prepared sorts.
    pub fn extract_best_with_sort(
        &self,
        termdag: &mut TermDag,
        value: Value,
        sort: ArcSort,
    ) -> Option<ExtractedTerm<C>> {
        self.extract_best_with_sort_cached(termdag, &mut Default::default(), value, sort)
    }

    fn extract_best_with_sort_cached(
        &self,
        termdag: &mut TermDag,
        cache: &mut HashMap<(Value, String), TermId>,
        value: Value,
        sort: ArcSort,
    ) -> Option<ExtractedTerm<C>> {
        let egraph = self.egraph;
        // Canonicalize the value using the union-find if available (for term-encoding mode)
        let canonical_value = find_canonical(egraph, value, &sort);

        let best_cost = self.compute_cost_node(egraph, canonical_value, &sort)?;
        let term =
            self.reconstruct_termdag_node_helper(egraph, termdag, canonical_value, &sort, cache);

        Some(ExtractedTerm {
            cost: best_cost,
            term,
        })
    }

    /// Extract variants of an e-class.
    ///
    /// Variants are selected by first picking the lowest-cost root e-nodes and
    /// then extracting each e-node's children with their best prepared terms.
    pub fn extract_variants_with_sort(
        &self,
        termdag: &mut TermDag,
        value: Value,
        nvariants: usize,
        sort: ArcSort,
    ) -> Vec<ExtractedTerm<C>> {
        if nvariants == 0 {
            return vec![];
        }

        let egraph = self.egraph;
        if sort.is_eq_sort() {
            // Canonicalize the value using the union-find if available
            let canonical_value = find_canonical(egraph, value, &sort);

            let mut root_variants: Vec<(C, String, Vec<Value>)> = Vec::new();

            for func_name in self.funcs.iter().filter(|func_name| {
                sort.name()
                    == egraph
                        .functions
                        .get(*func_name)
                        .unwrap()
                        .extraction_layout()
                        .0
                        .name()
            }) {
                let func = egraph.functions.get(func_name).unwrap();
                let output_idx = func.extraction_layout().1;

                let find_root_variants = |row: egglog_bridge::ScanEntry| {
                    if !row.subsumed {
                        let target = &row.vals[output_idx];
                        // A variant whose cost is `None` has a child e-class with no
                        // finite extraction (e.g. a purely cyclic child); such a variant
                        // can never appear in a minimal extraction, so we skip it. The
                        // target e-class still extracts via its other, costed variants.
                        if *target == canonical_value
                            && let Some(cost) = self.compute_cost_hyperedge(egraph, &row, func)
                        {
                            root_variants.push((cost, func_name.clone(), row.vals.to_vec()));
                        }
                    }
                };

                egraph.backend.for_each(func.backend_id, find_root_variants);
            }

            let mut res: Vec<ExtractedTerm<C>> = Vec::new();
            let mut cache: HashMap<(Value, String), TermId> = Default::default();
            root_variants.sort();
            root_variants.truncate(nvariants);
            for (cost, func_name, hyperedge) in root_variants {
                let mut ch_terms: Vec<TermId> = Vec::new();
                let func = egraph.functions.get(&func_name).unwrap();
                let ch_sorts = &func.func_type.input;
                let num_children = func.extraction_layout().1;
                for (value, sort) in hyperedge.iter().zip(ch_sorts.iter()).take(num_children) {
                    ch_terms.push(self.reconstruct_termdag_node_helper(
                        egraph, termdag, *value, sort, &mut cache,
                    ));
                }
                res.push(ExtractedTerm {
                    cost,
                    term: termdag.app(func.name().to_owned(), ch_terms),
                });
            }

            res
        } else {
            log::warn!(
                "extracting multiple variants for containers or primitives is not implemented, returning a single variant."
            );
            if let Some(res) = self.extract_best_with_sort(termdag, value, sort) {
                vec![res]
            } else {
                vec![]
            }
        }
    }
}

/// Find the canonical representative of a value using the sort's `:internal-uf`
/// union-find, or return the value unchanged if the sort has none.
///
/// The encoding's union-find is a function keyed by the element
/// (`UF_<Sort> : (S) -> (S, {Unit|Proof})`). Rebuild saturates path compression,
/// so `lookup_id` returns the leader in one hop; a miss means the value is its
/// own leader. A two-key union-find is a `(child, parent)` relation (a
/// user-provided `:internal-uf`, see `tests/uf-extraction.egg`), resolved with a
/// one-hop scan.
pub(crate) fn find_canonical(egraph: &EGraph, value: Value, sort: &ArcSort) -> Value {
    let Some(uf_name) = egraph.proof_state.uf_parent.get(sort.name()) else {
        return value;
    };

    let Some(uf_func) = egraph.functions.get(uf_name) else {
        return value;
    };

    if uf_func.func_type.input.len() == 1 {
        return egraph
            .backend
            .lookup_id(uf_func.backend_id, &[value])
            .unwrap_or(value);
    }

    // Two-key `(child, parent)` relation: one-hop lookup.
    let mut canonical = value;
    egraph
        .backend
        .for_each(uf_func.backend_id, |row: egglog_bridge::ScanEntry| {
            if row.vals[0] == value {
                canonical = row.vals[1];
            }
        });

    canonical
}

impl Function {
    /// Returns the extraction head cost for this table, whether from a view
    /// table's `:internal-cost` or an ordinary constructor's `:cost`.
    pub(crate) fn extraction_head_cost(&self, _egraph: &EGraph) -> Option<DefaultCost> {
        self.decl.cost
    }

    /// Whether this table's rows read as e-nodes: a real constructor, or the
    /// view standing in for one. A view for a custom function does not — its
    /// first output is that function's value, not an e-class.
    pub(crate) fn rows_are_enodes(&self) -> bool {
        match self.decl.subtype {
            FunctionSubtype::Constructor => true,
            FunctionSubtype::Custom => self.decl.role.is_constructor_view(),
        }
    }

    /// Whether this is the functional-dependency view `(children) -> (eclass, {Unit|Proof})`,
    /// where the e-class is the first output column rather than the last input column.
    pub(crate) fn is_fd_view(&self) -> bool {
        self.decl.role.is_view() && self.func_type.outputs.len() > 1
    }

    /// Whether this is a term/proof relation with its id in the last input column.
    pub(crate) fn is_proof_node_relation(&self) -> bool {
        self.decl.role.is_term_node()
    }

    /// Whether this term node's id belongs to `proof_sort`.
    #[cfg(test)]
    pub(crate) fn is_proof_node_of(&self, proof_sort: &str) -> bool {
        self.is_proof_node_relation()
            && self
                .func_type
                .input
                .last()
                .is_some_and(|sort| sort.name() == proof_sort)
    }

    /// True when the id is the last input column (old-form views and encoding
    /// relations), rather than a real output column.
    fn id_is_last_input(&self) -> bool {
        (self.decl.role.is_view() && !self.is_fd_view()) || self.is_proof_node_relation()
    }

    /// Returns the extracted output sort and its row index. The index is also
    /// the number of preceding child columns.
    pub(crate) fn extraction_layout(&self) -> (&ArcSort, usize) {
        if self.id_is_last_input() {
            let output_index = self.func_type.input.len() - 1;
            (&self.func_type.input[output_index], output_index)
        } else {
            (self.func_type.output(), self.func_type.input.len())
        }
    }
}

impl EGraph {
    /// Extracts the best tree term for each requested `(sort, value)` root
    /// using [`DEFAULT_COST_MODEL`].
    pub fn extract_best(
        &self,
        roots: Vec<(ArcSort, Value)>,
    ) -> Result<ExtractedTerms<DefaultCost>, Error> {
        self.extract_best_with_cost_model(roots, DEFAULT_COST_MODEL)
    }

    /// Extracts the best tree term for each requested `(sort, value)` root.
    ///
    /// This is the normal user extraction path: it respects `:unextractable`
    /// and hidden internal functions. The cost model must satisfy the
    /// optimal-substructure and convergence requirements on [`TreeExtractor`].
    pub fn extract_best_with_cost_model<C: Cost, M: TreeCostModel<C>>(
        &self,
        roots: Vec<(ArcSort, Value)>,
        cost_model: M,
    ) -> Result<ExtractedTerms<C>, Error> {
        let rootsorts = roots.iter().map(|(sort, _)| sort.clone()).collect();
        let extractor =
            TreeExtractor::compute_costs_from_rootsorts(Some(rootsorts), self, cost_model);
        let mut termdag = TermDag::default();
        let mut cache = Default::default();
        let extracted_roots = roots
            .into_iter()
            .map(|(sort, value)| {
                extractor.extract_best_with_sort_cached(&mut termdag, &mut cache, value, sort)
            })
            .collect();

        Ok(ExtractedTerms {
            termdag,
            terms: extracted_roots,
        })
    }

    /// Extracts up to `nvariants` tree root variants for each requested root
    /// using [`DEFAULT_COST_MODEL`].
    pub fn extract_variants(
        &self,
        roots: Vec<(ArcSort, Value)>,
        nvariants: usize,
    ) -> Result<ExtractedTermVariants<DefaultCost>, Error> {
        self.extract_variants_with_cost_model(roots, nvariants, DEFAULT_COST_MODEL)
    }

    /// Extracts up to `nvariants` tree root variants for each requested root.
    ///
    /// The cost model must satisfy the optimal-substructure and convergence
    /// requirements on [`TreeExtractor`].
    pub fn extract_variants_with_cost_model<C: Cost, M: TreeCostModel<C>>(
        &self,
        roots: Vec<(ArcSort, Value)>,
        nvariants: usize,
        cost_model: M,
    ) -> Result<ExtractedTermVariants<C>, Error> {
        if nvariants == 0 {
            return Ok(ExtractedTermVariants {
                termdag: TermDag::default(),
                variants: roots.iter().map(|_| Vec::new()).collect(),
            });
        }

        let rootsorts = roots.iter().map(|(sort, _)| sort.clone()).collect();
        let extractor =
            TreeExtractor::compute_costs_from_rootsorts(Some(rootsorts), self, cost_model);
        let mut termdag = TermDag::default();
        let variants = roots
            .into_iter()
            .map(|(sort, value)| {
                extractor.extract_variants_with_sort(&mut termdag, value, nvariants, sort)
            })
            .collect();

        Ok(ExtractedTermVariants { termdag, variants })
    }

    /// Extracts the best term for one value using the default additive cost model.
    pub fn extract_value(
        &self,
        sort: &ArcSort,
        value: Value,
    ) -> Result<(TermDag, TermId, DefaultCost), Error> {
        let sort_name = sort.name().to_owned();
        let mut extracted = self.extract_best(vec![(sort.clone(), value)])?;
        let root = extracted
            .terms
            .pop()
            .expect("one requested root produces one result")
            .ok_or_else(|| {
                Error::ExtractError(format!(
                    "Unable to find any valid extraction for sort {sort_name}"
                ))
            })?;
        Ok((extracted.termdag, root.term, root.cost))
    }

    /// Run command tree extraction with the configured constructor costs.
    pub(crate) fn extract_command(
        &self,
        sort: ArcSort,
        value: Value,
        variants: usize,
    ) -> Result<CommandOutput, Error> {
        let extractor = TreeExtractor::compute_costs_from_rootsorts(
            Some(vec![sort.clone()]),
            self,
            TreeCostModelFromDag(CommandCostModel),
        );
        let mut dag = TermDag::default();
        if variants == 0 {
            let extracted = extractor
                .extract_best_with_sort(&mut dag, value, sort.clone())
                .ok_or_else(|| {
                    Error::ExtractError(format!(
                        "Unable to find any valid extraction for sort {}",
                        sort.name()
                    ))
                })?;
            Ok(CommandOutput::ExtractBest(
                dag,
                extracted.cost,
                extracted.term,
            ))
        } else {
            let terms = extractor
                .extract_variants_with_sort(&mut dag, value, variants, sort)
                .into_iter()
                .map(|extracted| extracted.term)
                .collect();
            Ok(CommandOutput::ExtractVariants(dag, terms))
        }
    }

    /// For constructors and relations, the output column can be ignored
    pub fn function_to_dag(
        &self,
        sym: &str,
        n: usize,
        include_output: bool,
    ) -> Result<(Vec<TermId>, Option<Vec<TermId>>, TermDag), Error> {
        let global = (!self.functions.contains_key(sym))
            .then(|| self.backend.base_values().get::<S>(sym.to_owned().into()));
        let func = self
            .functions
            .get(sym)
            .or_else(|| self.global_table(sym))
            .ok_or(TypeError::UnboundFunction(sym.to_owned(), span!()))?;
        let (_, input_arity, output_arity) = func.table_read_projection();
        let input_sorts = &func.func_type.input[usize::from(global.is_some())..input_arity];
        // Logical columns are a prefix of the physical inputs-then-outputs row.
        let output_sorts = if input_arity < func.func_type.input.len() {
            &func.func_type.input[input_arity..input_arity + output_arity]
        } else {
            &func.func_type.outputs[..output_arity]
        };
        let mut rootsorts = input_sorts.to_vec();
        if include_output {
            rootsorts.extend_from_slice(output_sorts);
        }
        let extractor =
            TreeExtractor::compute_costs_from_rootsorts(Some(rootsorts), self, DEFAULT_COST_MODEL);

        let mut termdag = TermDag::default();
        let mut inputs: Vec<TermId> = Vec::new();
        let mut output: Option<Vec<TermId>> = if include_output {
            Some(Vec::new())
        } else {
            None
        };

        let extract_row = |row: egglog_bridge::ScanEntry| {
            if global.is_some_and(|key| row.vals[0] != key) {
                return true;
            }
            if inputs.len() < n {
                // include subsumed rows
                let mut children: Vec<TermId> = Vec::new();
                for (value, sort) in row.vals.iter().zip(input_sorts) {
                    let term_id = extractor
                        .extract_best_with_sort(&mut termdag, *value, sort.clone())
                        .map(|extracted| extracted.term)
                        .unwrap_or_else(|| termdag.var("Unextractable".into()));
                    children.push(term_id);
                }
                inputs.push(termdag.app(sym.to_owned(), children));
                if include_output {
                    // Extract every output (value) column. A tuple-output function has more than
                    // one; we display them wrapped in a `(values ...)` term to mirror the surface
                    // syntax.
                    let mut out_terms = Vec::new();
                    for (i, sort) in output_sorts.iter().enumerate() {
                        let value = row.vals[input_arity + i];
                        let term = extractor
                            .extract_best_with_sort(&mut termdag, value, sort.clone())
                            .map(|extracted| extracted.term)
                            .unwrap_or_else(|| termdag.var("Unextractable".into()));
                        out_terms.push(term);
                    }
                    let term = if out_terms.len() == 1 {
                        out_terms.pop().unwrap()
                    } else {
                        termdag.app("values".to_owned(), out_terms)
                    };
                    output.as_mut().unwrap().push(term);
                }
                true
            } else {
                false
            }
        };

        self.backend.for_each_while(func.backend_id, extract_row);

        Ok((inputs, output, termdag))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn term_encoding_rebuild_makes_canonical_lookup_one_hop() {
        let mut egraph = EGraph::new_with_term_encoding();
        egraph
            .parse_and_run_program(
                None,
                r#"
                (sort E)
                (constructor Mk (i64) E)
                (Mk 0)
                (Mk 1)
                (Mk 2)
                ; Union query-matched variables (existing e-classes), not
                ; freshly-built constructor terms: this takes the general
                ; `UF_<Sort>` edge path (forming a multi-edge chain to compress)
                ; rather than the term-mode construct-into-e-class optimization,
                ; which would fuse the operands with no chain to compress.
                (relation Link (E E))
                (Link (Mk 0) (Mk 1))
                (Link (Mk 1) (Mk 2))
                (rule ((Link x y)) ((union x y)))
                (run 1)
                "#,
            )
            .unwrap();

        let path_compressions: usize = egraph
            .get_overall_run_report()
            .num_matches_per_rule
            .iter()
            .filter(|(rule, _)| rule.as_ref().contains("uf_path_compress"))
            .map(|(_, matches)| *matches)
            .sum();
        assert!(
            path_compressions > 0,
            "test must create a multi-edge UF chain"
        );

        let uf_name = &egraph.proof_state.uf_parent["E"];
        let uf_id = egraph.functions[uf_name].backend_id;
        let mut rows = Vec::new();
        egraph
            .backend
            .for_each(uf_id, |row| rows.push(row.vals.to_vec()));
        assert!(rows.len() >= 2);

        let sort = egraph.get_sort_by_name("E").unwrap();
        for row in rows {
            let child = row[0];
            let parent = row[1];
            assert_eq!(egraph.backend.lookup_id(uf_id, &[parent]), None);
            assert_eq!(find_canonical(&egraph, child, sort), parent);
        }
    }

    #[test]
    fn dirty_rows_have_no_padding_rows() {
        for len in [0, 1, 63, 64, 65, 127, 128, 129] {
            let mut rows = DirtyRows::full(len);
            for row in 0..len {
                assert_eq!(rows.pop_from(row), Some(row));
            }
            assert_eq!(rows.pop_from(len), None);
            assert_eq!(rows.pop_from(0), None);
            assert_eq!(rows.count, 0);
        }
    }

    #[test]
    fn child_index_groups_every_read_under_its_value() {
        // A fixed linear congruential stream, so values repeat across functions.
        let mut state = 12345u64;
        let mut next = |bound: u64| {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            ((state >> 33) % bound) as u32
        };
        let reads: Vec<(Value, u32, u32)> = (0..2000)
            .map(|_| (Value::new_const(next(300)), next(5), next(400)))
            .collect();
        let index = ChildIndex::new(|| reads.iter().copied());
        let mut expected: HashMap<Value, Vec<(u32, u32)>> = HashMap::default();
        for &(value, function, row) in &reads {
            expected.entry(value).or_default().push((function, row));
        }
        for v in 0..310 {
            let value = Value::new_const(v);
            let mut got = index.readers(value).to_vec();
            got.sort_unstable();
            let mut want = expected.remove(&value).unwrap_or_default();
            want.sort_unstable();
            assert_eq!(got, want, "readers of {v}");
        }
        assert!(expected.is_empty());
        assert_eq!(index.readers.len(), reads.len());
        assert!(
            ChildIndex::new(std::iter::empty)
                .readers(Value::new_const(0))
                .is_empty()
        );
    }

    #[test]
    fn dirty_rows_defer_marks_behind_the_cursor() {
        let mut rows = DirtyRows::full(130);
        for row in 0..130 {
            assert_eq!(rows.pop_from(row), Some(row));
        }
        rows.insert(63);
        rows.insert(129);
        rows.insert(129);
        assert_eq!(rows.count, 2);
        assert_eq!(rows.pop_from(0), Some(63));
        rows.insert(0);
        rows.insert(63);
        rows.insert(64);
        assert_eq!(rows.pop_from(64), Some(64));
        assert_eq!(rows.pop_from(65), Some(129));
        assert_eq!(rows.pop_from(130), None);
        assert_eq!(rows.count, 2);
        assert_eq!(rows.pop_from(0), Some(0));
        assert_eq!(rows.pop_from(1), Some(63));
        assert_eq!(rows.count, 0);
    }
}

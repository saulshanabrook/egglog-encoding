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

/// Typed evidence retained while reconstructing a selected term. The row's
/// proof belongs to this exact constructor choice, not a later table lookup.
#[derive(Clone)]
pub(crate) struct SelectedNode {
    pub sort: ArcSort,
    pub value: Value,
    pub children: Vec<(TermId, String)>,
    pub row: Option<(Value, Value)>,
}

pub(crate) type SelectedNodes = HashMap<(TermId, String), SelectedNode>;

#[derive(Default)]
struct Reconstruction {
    cache: HashMap<(Value, String), TermId>,
    evidence: Option<SelectedNodes>,
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
    costs: HashMap<String, HashMap<Value, C>>,
    topo_rnk_cnt: usize,
    topo_rnk: HashMap<String, HashMap<Value, usize>>,
    parent_edge: HashMap<String, HashMap<Value, (String, Vec<Value>)>>,
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
                    || func.1.decl.internal_view.is_some())
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
        let mut costs: HashMap<String, HashMap<Value, C>> = Default::default();
        let mut topo_rnk: HashMap<String, HashMap<Value, usize>> = Default::default();
        let mut parent_edge: HashMap<String, HashMap<Value, (String, Vec<Value>)>> =
            Default::default();

        for func_name in funcs.iter() {
            let func = egraph.functions.get(func_name).unwrap();
            let output_sort_name = func.extraction_layout().0.name();
            if !costs.contains_key(output_sort_name) {
                costs.insert(output_sort_name.to_owned(), Default::default());
                topo_rnk.insert(output_sort_name.to_owned(), Default::default());
                parent_edge.insert(output_sort_name.to_owned(), Default::default());
            }
        }

        let mut extractor = TreeExtractor {
            egraph,
            funcs,
            cost_model: Box::new(cost_model),
            costs,
            topo_rnk_cnt: 0,
            topo_rnk,
            parent_edge,
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
            self.costs.get(sort.name())?.get(&value).cloned()
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
            if let Some(t) = self.topo_rnk.get(sort.name()) {
                *t.get(&value).unwrap_or(&usize::MAX)
            } else {
                usize::MAX
            }
        } else {
            0
        }
    }

    fn compute_topo_rnk_hyperedge(
        &self,
        egraph: &EGraph,
        row: &egglog_bridge::ScanEntry,
        func: &Function,
    ) -> usize {
        let sorts = &func.func_type.input;
        let num_children = func.extraction_layout().1;
        row.vals
            .iter()
            .take(num_children)
            .zip(sorts.iter())
            .fold(0, |ret, (value, sort)| {
                usize::max(ret, self.compute_topo_rnk_node(egraph, *value, sort))
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
        let mut ensure_fixpoint = false;

        let funcs = self.funcs.clone();

        while !ensure_fixpoint {
            ensure_fixpoint = true;

            for func_name in funcs.iter() {
                let func = egraph.functions.get(func_name).unwrap();
                let (target_sort, output_idx) = func.extraction_layout();
                let relax_hyperedge = |row: egglog_bridge::ScanEntry| {
                    if !row.subsumed {
                        let target = &row.vals[output_idx];
                        let mut updated = false;
                        if let Some(new_cost) = self.compute_cost_hyperedge(egraph, &row, func) {
                            match self
                                .costs
                                .get_mut(target_sort.name())
                                .unwrap()
                                .entry(*target)
                            {
                                HEntry::Vacant(e) => {
                                    updated = true;
                                    e.insert(new_cost);
                                }
                                HEntry::Occupied(mut e) => {
                                    if new_cost < *(e.get()) {
                                        updated = true;
                                        e.insert(new_cost);
                                    }
                                }
                            }
                        }
                        // record the chronological order of the updates
                        // which serves as a topological order that avoids cycles
                        // even when a term has a cost equal to its subterms
                        if updated {
                            ensure_fixpoint = false;
                            self.topo_rnk_cnt += 1;
                            self.topo_rnk
                                .get_mut(target_sort.name())
                                .unwrap()
                                .insert(*target, self.topo_rnk_cnt);
                        }
                    }
                };

                egraph.backend.for_each(func.backend_id, relax_hyperedge);
            }
        }

        // Save the edges for reconstruction
        for func_name in funcs.iter() {
            let func = egraph.functions.get(func_name).unwrap();
            let (target_sort, output_idx) = func.extraction_layout();

            let save_best_parent_edge = |row: egglog_bridge::ScanEntry| {
                if !row.subsumed {
                    let target = &row.vals[output_idx];
                    if let Some(best_cost) = self.costs.get(target_sort.name()).unwrap().get(target)
                        && Some(best_cost.clone())
                            == self.compute_cost_hyperedge(egraph, &row, func)
                    {
                        // one of the possible best parent edges
                        let target_topo_rnk = *self
                            .topo_rnk
                            .get(target_sort.name())
                            .unwrap()
                            .get(target)
                            .unwrap();
                        if target_topo_rnk > self.compute_topo_rnk_hyperedge(egraph, &row, func) {
                            // one of the parent edges that avoids cycles
                            if let HEntry::Vacant(e) = self
                                .parent_edge
                                .get_mut(target_sort.name())
                                .unwrap()
                                .entry(*target)
                            {
                                e.insert((func.decl.name.clone(), row.vals.to_vec()));
                            }
                        }
                    }
                }
            };

            egraph
                .backend
                .for_each(func.backend_id, save_best_parent_edge);
        }
    }

    /// Reconstruct the prepared best tree, or a variant's chosen root row.
    /// Variants share best children without replacing their cached best root.
    fn reconstruct_termdag_node_helper(
        &self,
        termdag: &mut TermDag,
        value: Value,
        sort: &ArcSort,
        reconstruction: &mut Reconstruction,
        root_row: Option<(&Function, &[Value])>,
    ) -> TermId {
        let egraph = self.egraph;
        let key = root_row.is_none().then(|| (value, sort.name().to_owned()));
        if let Some(key) = &key
            && let Some(term) = reconstruction.cache.get(key)
        {
            return *term;
        }

        let mut children = vec![];
        let mut row = None;
        let term = if sort.is_container_sort() {
            let elements = sort.inner_values(egraph.backend.container_values(), value);
            let mut ch_terms: Vec<TermId> = Vec::new();
            for ch in elements.iter() {
                let term = self.reconstruct_termdag_node_helper(
                    termdag,
                    ch.1,
                    &ch.0,
                    reconstruction,
                    None,
                );
                if reconstruction.evidence.is_some() {
                    children.push((term, ch.0.name().to_owned()));
                }
                ch_terms.push(term);
            }
            sort.reconstruct_termdag_container(
                egraph.backend.container_values(),
                value,
                termdag,
                ch_terms,
            )
        } else if sort.is_eq_sort() {
            let (func, hyperedge) = root_row.unwrap_or_else(|| {
                let (func_name, hyperedge) = &self.parent_edge[sort.name()][&value];
                (&egraph.functions[func_name], hyperedge.as_slice())
            });
            let ch_sorts = &func.func_type.input;

            let num_children = func.extraction_layout().1;
            let output_name = func.name();

            let mut ch_terms: Vec<TermId> = Vec::new();
            for (value, sort) in hyperedge.iter().take(num_children).zip(ch_sorts.iter()) {
                let term = self.reconstruct_termdag_node_helper(
                    termdag,
                    *value,
                    sort,
                    reconstruction,
                    None,
                );
                if reconstruction.evidence.is_some() {
                    children.push((term, sort.name().to_owned()));
                }
                ch_terms.push(term);
            }
            if func.decl.internal_view.is_some() {
                row = Some((hyperedge[num_children], hyperedge[num_children + 1]));
            }
            termdag.app(output_name.to_string(), ch_terms)
        } else {
            // Base value case
            sort.reconstruct_termdag_base(egraph.backend.base_values(), value, termdag)
        };

        if let Some(key) = key {
            reconstruction.cache.insert(key, term);
        }
        if let Some(evidence) = &mut reconstruction.evidence {
            evidence.insert(
                (term, sort.name().to_owned()),
                SelectedNode {
                    sort: sort.clone(),
                    value,
                    children,
                    row,
                },
            );
        }
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
        reconstruction: &mut Reconstruction,
        value: Value,
        sort: ArcSort,
    ) -> Option<ExtractedTerm<C>> {
        let egraph = self.egraph;
        // Canonicalize the value using the union-find if available (for term-encoding mode)
        let canonical_value = find_canonical(egraph, value, &sort);

        let best_cost = self.compute_cost_node(egraph, canonical_value, &sort)?;
        let term = self.reconstruct_termdag_node_helper(
            termdag,
            canonical_value,
            &sort,
            reconstruction,
            None,
        );

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
        self.extract_variants_with_sort_cached(
            termdag,
            &mut Reconstruction::default(),
            value,
            nvariants,
            sort,
        )
    }

    fn extract_variants_with_sort_cached(
        &self,
        termdag: &mut TermDag,
        reconstruction: &mut Reconstruction,
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
            root_variants.sort();
            root_variants.truncate(nvariants);
            for (cost, func_name, hyperedge) in root_variants {
                let term = self.reconstruct_termdag_node_helper(
                    termdag,
                    canonical_value,
                    &sort,
                    reconstruction,
                    Some((&egraph.functions[&func_name], &hyperedge)),
                );
                res.push(ExtractedTerm { cost, term });
            }

            res
        } else {
            log::warn!(
                "extracting multiple variants for containers or primitives is not implemented, returning a single variant."
            );
            if let Some(res) =
                self.extract_best_with_sort_cached(termdag, reconstruction, value, sort)
            {
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
            FunctionSubtype::Custom => self.decl.internal_view == Some(ViewKind::Constructor),
        }
    }

    /// Whether this is the functional-dependency view `(children) -> (eclass, {Unit|Proof})`,
    /// where the e-class is the first output column rather than the last input column.
    pub(crate) fn is_fd_view(&self) -> bool {
        self.decl.internal_view.is_some() && self.func_type.outputs.len() > 1
    }

    /// A proof-node relation created by the proof encoding, marked
    /// `:internal-term-node`. Its rows are reconstructed during extraction with
    /// the minted id as the last input column and the earlier inputs as the
    /// proof's children. Views and plain bookkeeping relations such as the
    /// subsumption markers are unmarked, so extraction never reads them.
    pub(crate) fn is_proof_node_relation(&self) -> bool {
        self.decl.internal_term_node
    }

    /// Whether this relation's rows are the proof encoding's own, which is what
    /// puts them on append-and-scan storage: a proof node marked
    /// `:internal-term-node` whose minted last input is a `Proof`.
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
        (self.decl.internal_view.is_some() && !self.is_fd_view()) || self.is_proof_node_relation()
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

    /// Run the built-in tree extractor, optionally retaining its typed choices
    /// for proof certification. Dynamic costs change choices, never algorithms.
    pub(crate) fn extract_command(
        &self,
        sort: &ArcSort,
        value: Value,
        variants: usize,
        evidence: bool,
    ) -> Result<(CommandOutput, SelectedNodes), Error> {
        let extractor = TreeExtractor::compute_costs_from_rootsorts(
            Some(vec![sort.clone()]),
            self,
            TreeCostModelFromDag(CommandCostModel),
        );
        let mut dag = TermDag::default();
        let mut reconstruction = Reconstruction {
            evidence: evidence.then(HashMap::default),
            ..Default::default()
        };
        let output = if variants == 0 {
            let extracted = extractor
                .extract_best_with_sort_cached(&mut dag, &mut reconstruction, value, sort.clone())
                .ok_or_else(|| {
                    Error::ExtractError(
                        "Unable to find any valid extraction (likely due to subsume or delete)"
                            .into(),
                    )
                })?;
            CommandOutput::ExtractBest(dag, extracted.cost, extracted.term)
        } else {
            let terms = extractor
                .extract_variants_with_sort_cached(
                    &mut dag,
                    &mut reconstruction,
                    value,
                    variants,
                    sort.clone(),
                )
                .into_iter()
                .map(|extracted| extracted.term)
                .collect();
            CommandOutput::ExtractVariants(dag, terms)
        };
        Ok((output, reconstruction.evidence.unwrap_or_default()))
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

    /// For constructors and relations, the output column can be ignored
    pub fn function_to_dag(
        &self,
        sym: &str,
        n: usize,
        include_output: bool,
    ) -> Result<(Vec<TermId>, Option<Vec<TermId>>, TermDag), Error> {
        let func = self
            .functions
            .get(sym)
            .ok_or(TypeError::UnboundFunction(sym.to_owned(), span!()))?;
        let (_, input_arity, output_arity) = func.table_read_projection();
        let input_sorts = &func.func_type.input[..input_arity];
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
}

//! Support for containers
//!
//! Containers behave a lot like base values. They are implemented differently because
//! their ids share a space with other Ids in the egraph and as a result, their ids need to be
//! sparse.
//!
//! This is a relatively "eagler" implementation of containers, reflecting egglog's current
//! semantics. One could imagine a variant of containers in which they behave more like egglog
//! functions than base values.

use std::{
    any::{Any, TypeId},
    hash::{Hash, Hasher},
    ops::Deref,
};

use crate::numeric_id::{DenseIdMap, IdVec, NumericId, define_id};
use crossbeam_queue::SegQueue;
use dashmap::SharedValue;
use rayon::{
    iter::{ParallelBridge, ParallelIterator},
    prelude::*,
};
use rustc_hash::FxHasher;
use smallvec::SmallVec;

use crate::{
    CausalReceipts, ColumnId, CounterId, ExecutionState, Offset, ReplaySortId, SubsetRef, TableId,
    TaggedRowBuffer, Value, WrappedTable,
    common::{DashMap, HashMap, IndexSet, SubsetTracker},
    parallel_heuristics::{parallelize_inter_container_op, parallelize_intra_container_op},
    receipts::ContainerVersionDependency,
    table_spec::{Rebuilder, ValueRebuilder},
};

#[cfg(test)]
mod tests;

define_id!(pub ContainerValueId, u32, "an identifier for containers");

pub trait MergeFn:
    Fn(&mut ExecutionState, Value, Value) -> Value + dyn_clone::DynClone + Send + Sync
{
}
impl<T: Fn(&mut ExecutionState, Value, Value) -> Value + Clone + Send + Sync> MergeFn for T {}

// Implements `Clone` for `Box<dyn MergeFn>`.
dyn_clone::clone_trait_object!(MergeFn);

#[derive(Clone, Default)]
struct ContainerIds {
    ids: IndexSet<TypeId>,
}

impl ContainerIds {
    fn insert(&mut self, ty: TypeId) -> ContainerValueId {
        if let Some(idx) = self.ids.get_index_of(&ty) {
            ContainerValueId::from_usize(idx)
        } else {
            let idx = self.ids.len();
            self.ids.insert(ty);
            ContainerValueId::from_usize(idx)
        }
    }

    fn get(&self, ty: &TypeId) -> Option<ContainerValueId> {
        self.ids.get_index_of(ty).map(ContainerValueId::from_usize)
    }
}

#[derive(Clone, Default)]
pub struct ContainerValues {
    subset_tracker: SubsetTracker,
    container_ids: ContainerIds,
    data: DenseIdMap<ContainerValueId, Box<dyn DynamicContainerEnv + Send + Sync>>,
}

/// Summary returned by container rebuild.
///
/// `changed` means some container entry changed during rebuild, either because
/// its contents changed or because its outer id canonicalized.
///
/// `dirty_ids` is narrower: it records container ids whose semantics changed
/// while their stored outer id stayed stable. Ordinary table rebuild already
/// handles changed-id cases; these ids need a follow-up parent-row refresh.
/// This includes containers that changed directly and containers whose
/// contained containers changed in place.
///
/// For example, `l(vec-of(w(k(b))))` can rebuild to `l(vec-of(k(b)))` without
/// changing the `Vec` id. The row is now newly matchable, but seminaive will
/// miss it unless the parent row is retimestamped.
#[derive(Clone, Default)]
pub struct ContainerRebuildSummary {
    changed: bool,
    // Container ids whose semantics changed in a way that may not produce a
    // fresh parent-row delta during ordinary table rebuild.
    dirty_ids: IndexSet<Value>,
    dirty_dependencies: HashMap<(ReplaySortId, Value), SmallVec<[ContainerVersionDependency; 1]>>,
}

impl ContainerRebuildSummary {
    /// Returns whether any container entry changed during rebuild.
    pub fn changed(&self) -> bool {
        self.changed
    }

    /// Returns the container ids whose parent rows may need retimestamping.
    pub fn dirty_ids(&self) -> &IndexSet<Value> {
        &self.dirty_ids
    }

    pub(crate) fn dirty_dependency_candidates(
        &self,
        sort: ReplaySortId,
        value: Value,
    ) -> Option<&[ContainerVersionDependency]> {
        self.dirty_dependencies
            .get(&(sort, value))
            .map(SmallVec::as_slice)
    }

    fn note_change(&mut self) {
        self.changed = true;
    }

    pub(crate) fn note_dirty_id(&mut self, value: Value) {
        self.changed = true;
        self.dirty_ids.insert(value);
    }

    pub(crate) fn note_dirty_dependency(&mut self, dependency: ContainerVersionDependency) -> bool {
        self.note_dirty_id(dependency.outer.raw);
        let key = (dependency.outer.sort, dependency.outer.raw);
        match self.dirty_dependencies.entry(key) {
            hashbrown::hash_map::Entry::Vacant(entry) => {
                entry.insert(SmallVec::from_buf([dependency]));
                true
            }
            hashbrown::hash_map::Entry::Occupied(mut entry) => {
                let dependencies = entry.get_mut();
                if let Some(current) = dependencies
                    .iter_mut()
                    .find(|current| current.outer.term == dependency.outer.term)
                {
                    assert_eq!(
                        (
                            current.dependency.wave,
                            current.dependency.equalities.as_of_edges,
                        ),
                        (
                            dependency.dependency.wave,
                            dependency.dependency.equalities.as_of_edges,
                        ),
                        "one container rebuild pass produced incompatible dependency landmarks"
                    );
                    let prior_len = current.dependency.equalities.pairs.len();
                    let mut pairs = current.dependency.equalities.pairs.to_vec();
                    for pair in dependency.dependency.equalities.pairs {
                        if !pairs.contains(&pair) {
                            pairs.push(pair);
                        }
                    }
                    current.dependency.equalities.pairs = pairs.into_boxed_slice();
                    current.dependency.equalities.pairs.len() != prior_len
                } else {
                    dependencies.push(dependency);
                    true
                }
            }
        }
    }

    fn extend(&mut self, other: Self) {
        self.changed |= other.changed;
        self.dirty_ids.extend(other.dirty_ids);
        for (_, dependencies) in other.dirty_dependencies {
            for dependency in dependencies {
                self.note_dirty_dependency(dependency);
            }
        }
    }
}

impl ContainerValues {
    pub fn new() -> Self {
        Default::default()
    }

    fn get<C: ContainerValue>(&self) -> Option<&ContainerEnv<C>> {
        let id = self.container_ids.get(&TypeId::of::<C>())?;
        let res = self.data.get(id)?.as_any();
        Some(res.downcast_ref::<ContainerEnv<C>>().unwrap())
    }

    /// Iterate over the containers of the given type.
    pub fn for_each<C: ContainerValue>(&self, mut f: impl FnMut(&C, Value)) {
        let Some(env) = self.get::<C>() else {
            return;
        };
        for ent in env.to_id.iter() {
            f(ent.key(), *ent.value());
        }
    }

    /// Get the container associated with the value `val` in the database. The caller must know the
    /// type of the container.
    ///
    /// The return type of this function may contain lock guards. Attempts to modify the contents
    /// of the containers database may deadlock if the given guard has not been dropped.
    pub fn get_val<C: ContainerValue>(&self, val: Value) -> Option<impl Deref<Target = C> + '_> {
        self.get::<C>()?.get_container(val)
    }

    pub fn register_val<C: ContainerValue>(
        &self,
        container: C,
        exec_state: &mut ExecutionState,
    ) -> Value {
        let env = self
            .get::<C>()
            .expect("must register container type before registering a value");
        env.get_or_insert(&container, exec_state)
    }

    /// Rebuild a single container value by remapping each contained value
    /// through `remap`, returning the (possibly new) interned value, or `value`
    /// unchanged if it is not a registered container of the type behind
    /// `type_id`.
    ///
    /// Unlike [`ContainerValues::rebuild_all`], which drives rebuilds off the
    /// backend union-find, the caller supplies the remapping explicitly and
    /// identifies the container type dynamically by its [`TypeId`].
    pub fn rebuild_val_with(
        &self,
        type_id: TypeId,
        value: Value,
        exec_state: &mut ExecutionState,
        remap: &(dyn Fn(Value) -> Value + Send + Sync),
    ) -> Value {
        let Some(id) = self.container_ids.get(&type_id) else {
            return value;
        };
        let Some(env) = self.data.get(id) else {
            return value;
        };
        env.rebuild_val_with(value, exec_state, remap)
            .unwrap_or(value)
    }

    /// Apply the given rebuild to the contents of each container.
    pub fn rebuild_all(
        &mut self,
        table_id: TableId,
        table: &WrappedTable,
        exec_state: &mut ExecutionState,
    ) -> ContainerRebuildSummary {
        let Some(rebuilder) = table.rebuilder(&[]) else {
            return Default::default();
        };
        let to_scan = rebuilder.hint_col().map(|_| {
            // We may attempt an incremental rebuild.
            self.subset_tracker.recent_updates(table_id, table)
        });
        let mut summary = if parallelize_inter_container_op(self.data.next_id().index()) {
            self.data
                .iter_mut()
                .zip(std::iter::repeat_with(|| exec_state.clone()))
                .par_bridge()
                .map(|((_, env), mut exec_state)| {
                    env.apply_rebuild(
                        table,
                        &*rebuilder,
                        to_scan.as_ref().map(|x| x.as_ref()),
                        &mut exec_state,
                    )
                })
                .reduce(ContainerRebuildSummary::default, |mut acc, summary| {
                    acc.extend(summary);
                    acc
                })
        } else {
            let mut summary = ContainerRebuildSummary::default();
            for (_, env) in self.data.iter_mut() {
                summary.extend(env.apply_rebuild(
                    table,
                    &*rebuilder,
                    to_scan.as_ref().map(|x| x.as_ref()),
                    exec_state,
                ));
            }
            summary
        };
        self.expand_dirty_id_closure(&mut summary, exec_state.causal_receipts());
        summary
    }

    /// Add ancestor containers to the dirty-id set until it is transitively closed.
    ///
    /// A rebuild can change a container's semantics in place without changing
    /// its id. If that container is itself stored inside another container,
    /// the parent container has also changed semantically even though no direct
    /// rebuild touched its contents. For example, with
    /// `(p (vec-of (vec-of (w (b)))))` and `(rewrite (w x) x)`, the inner
    /// `Vec` rebuilds in place to `vec-of (b)`. Without this closure, only the
    /// inner `Vec` id is dirty; the outer `Vec` row is not retimestamped, so a
    /// later rule like `(rewrite (p (vec-of (vec-of (b)))) (b))` can miss the
    /// newly matchable parent row.
    fn expand_dirty_id_closure(
        &self,
        summary: &mut ContainerRebuildSummary,
        receipts: Option<&CausalReceipts>,
    ) {
        if !summary.dirty_dependencies.is_empty() {
            let receipts =
                receipts.expect("typed dirty-container dependencies require causal receipts");
            let mut frontier = summary
                .dirty_dependencies
                .values()
                .flat_map(|dependencies| dependencies.iter().cloned())
                .collect::<Vec<_>>();
            while !frontier.is_empty() {
                let mut next = Vec::<ContainerVersionDependency>::new();
                for dependency in frontier.drain(..) {
                    let child = dependency.outer;
                    let mut child_set = IndexSet::default();
                    child_set.insert(child.raw);
                    for (_, env) in self.data.iter() {
                        let mut parents = IndexSet::default();
                        env.extend_containers_containing(&child_set, &mut parents);
                        for parent in parents {
                            let mut parent_endpoints = receipts
                                .container_parent_candidates(env.container_type_id(), parent)
                                .into_iter()
                                .filter(|candidate| {
                                    env.contains_typed_child(
                                        parent,
                                        child.raw,
                                        child.sort,
                                        &candidate.child_sorts,
                                    )
                                })
                                .map(|candidate| candidate.endpoint);
                            let Some(parent_endpoint) = parent_endpoints.next() else {
                                // The raw reverse index is only a candidate
                                // generator. A value collision in another
                                // logical sort is not ancestry.
                                continue;
                            };
                            assert!(
                                parent_endpoints.next().is_none(),
                                "container parent has multiple exact logical replay sorts"
                            );
                            if parent_endpoint == child {
                                continue;
                            }
                            if env.causal_receipt_kind().is_none() {
                                panic!(
                                    "causal container rebuild does not support {}",
                                    env.container_type_name()
                                );
                            }
                            let propagated = ContainerVersionDependency {
                                outer: parent_endpoint,
                                dependency: dependency.dependency.clone(),
                            };
                            if summary.note_dirty_dependency(propagated.clone()) {
                                next.push(propagated);
                            }
                        }
                    }
                }
                frontier = next;
            }
            return;
        }

        let mut frontier = summary.dirty_ids.clone();
        let mut seen = frontier.iter().copied().collect::<IndexSet<_>>();

        while !frontier.is_empty() {
            let mut next = IndexSet::default();
            for (_, env) in self.data.iter() {
                env.extend_containers_containing(&frontier, &mut next);
            }
            frontier.clear();
            for value in next {
                if seen.insert(value) {
                    summary.note_dirty_id(value);
                    frontier.insert(value);
                }
            }
        }
    }

    /// Add a new container type to the given [`ContainerValue`] instance.
    ///
    /// Container types need a meaans of generating fresh ids (`id_counter`) along with a means of
    /// merging conflicting ids (`merge_fn`).
    pub fn register_type<C: ContainerValue>(
        &mut self,
        id_counter: CounterId,
        merge_fn: impl MergeFn + 'static,
    ) -> ContainerValueId {
        let id = self.container_ids.insert(TypeId::of::<C>());
        self.data.get_or_insert(id, || {
            Box::new(ContainerEnv::<C>::new(Box::new(merge_fn), id_counter))
        });
        id
    }
}

/// A trait implemented by container types.
///
/// Containers behave a lot like base values, but they include extra trait methods to support
/// rebuilding of container contents and merging containers that become equal after a rebuild pass
/// has taken place.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CausalContainerKind {
    Pair,
    Vec,
    Maybe,
    Either,
}

impl CausalContainerKind {
    fn validate_arity(self, arity: usize) -> Result<(), &'static str> {
        match self {
            Self::Pair if arity != 2 => Err("causal Pair container does not have two children"),
            Self::Maybe if arity > 1 => Err("causal Maybe container has more than one child"),
            Self::Either if arity != 1 => Err("causal Either container does not have one child"),
            Self::Vec | Self::Pair | Self::Maybe | Self::Either => Ok(()),
        }
    }
}

pub trait ContainerValue: Hash + Eq + Clone + Send + Sync + 'static {
    /// The positional container shape supported by exact causal rebuild
    /// capture. Unlisted container semantics fail closed only if rebuild
    /// actually changes the container; ordinary execution is unaffected.
    fn causal_receipt_kind() -> Option<CausalContainerKind> {
        None
    }

    /// Map each value yielded by [`ContainerValue::iter`] to its logical
    /// child-sort slot. Ordered supported containers have a compact default;
    /// variant containers such as Either override it.
    fn causal_child_sort_slots(&self) -> Option<Box<[usize]>> {
        let len = self.iter().count();
        match Self::causal_receipt_kind()? {
            CausalContainerKind::Pair => Some((0..len).collect()),
            CausalContainerKind::Vec | CausalContainerKind::Maybe => {
                Some(std::iter::repeat_n(0, len).collect())
            }
            CausalContainerKind::Either => None,
        }
    }

    /// Rebuild an additional container in place according the the given [`ValueRebuilder`].
    ///
    /// If this method returns `false` then the container must not have been modified (i.e. it must
    /// hash to the same value, and compare equal to a copy of itself before the call).
    fn rebuild_contents(&mut self, rebuilder: &dyn ValueRebuilder) -> bool;

    /// Iterate over the contents of the container.
    ///
    /// Note that containers can be more structured than just a sequence of values. This iterator
    /// is used to populate an index that in turn is used to speed up rebuilds. If a value in the
    /// container is eligible for a rebuild and it is not mentioned by this iterator, the outer
    /// container registry may skip rebuilding this container.
    fn iter(&self) -> impl Iterator<Item = Value> + '_;
}

pub trait DynamicContainerEnv: Any + dyn_clone::DynClone + Send + Sync {
    fn as_any(&self) -> &dyn Any;
    fn container_type_id(&self) -> TypeId;
    fn causal_receipt_kind(&self) -> Option<CausalContainerKind>;
    fn container_type_name(&self) -> &'static str;
    fn contains_typed_child(
        &self,
        parent: Value,
        child: Value,
        child_sort: ReplaySortId,
        child_sorts: &[ReplaySortId],
    ) -> bool;
    fn apply_rebuild(
        &mut self,
        table: &WrappedTable,
        rebuilder: &dyn Rebuilder,
        subset: Option<SubsetRef>,
        exec_state: &mut ExecutionState,
    ) -> ContainerRebuildSummary;
    /// Add ids for containers in this environment that contain any `values`.
    ///
    /// This uses the container content index populated from
    /// [`ContainerValue::iter`] and lets callers climb from dirty child ids to
    /// all directly containing parent container ids.
    fn extend_containers_containing(&self, values: &IndexSet<Value>, out: &mut IndexSet<Value>);
    /// Rebuild the single container `value` by remapping each contained value
    /// through `remap`, returning the (possibly new) interned value, or `None`
    /// if `value` is not registered in this environment.
    fn rebuild_val_with(
        &self,
        value: Value,
        exec_state: &mut ExecutionState,
        remap: &(dyn Fn(Value) -> Value + Send + Sync),
    ) -> Option<Value>;
}

// Implements `Clone` for `Box<dyn DynamicContainerEnv>`.
dyn_clone::clone_trait_object!(DynamicContainerEnv);

fn hash_container(container: &impl ContainerValue) -> u64 {
    let mut hasher = FxHasher::default();
    container.hash(&mut hasher);
    hasher.finish()
}

#[derive(Clone)]
struct ContainerEnv<C: Eq + Hash> {
    merge_fn: Box<dyn MergeFn>,
    counter: CounterId,
    to_id: DashMap<C, Value>,
    to_container: DashMap<Value, (usize /* hash code */, usize /* map */)>,
    /// Map from a Value to the set of ids of containers that contain that value.
    val_index: DashMap<Value, IndexSet<Value>>,
}

impl<C: ContainerValue> DynamicContainerEnv for ContainerEnv<C> {
    fn as_any(&self) -> &dyn Any {
        self
    }

    fn container_type_id(&self) -> TypeId {
        TypeId::of::<C>()
    }

    fn causal_receipt_kind(&self) -> Option<CausalContainerKind> {
        C::causal_receipt_kind()
    }

    fn container_type_name(&self) -> &'static str {
        std::any::type_name::<C>()
    }

    fn contains_typed_child(
        &self,
        parent: Value,
        child: Value,
        child_sort: ReplaySortId,
        child_sorts: &[ReplaySortId],
    ) -> bool {
        let Some(container) = self.get_container(parent) else {
            return false;
        };
        let values = container.iter().collect::<SmallVec<[Value; 4]>>();
        if let Some(slots) = container.causal_child_sort_slots() {
            return values
                .iter()
                .copied()
                .zip(slots)
                .any(|(value, slot)| value == child && child_sorts.get(slot) == Some(&child_sort));
        }
        // Unsupported uniform containers such as Set and MultiSet can still
        // be identified exactly enough to fail closed only when truly reached.
        if let [only_sort] = child_sorts {
            return *only_sort == child_sort && values.contains(&child);
        }
        // For an unsupported heterogeneous container, retaining a raw child
        // whose logical sort occurs anywhere in its schema is conservative
        // and remains an explicit fail-closed boundary.
        values.contains(&child) && child_sorts.contains(&child_sort)
    }

    fn apply_rebuild(
        &mut self,
        table: &WrappedTable,
        rebuilder: &dyn Rebuilder,
        subset: Option<SubsetRef>,
        exec_state: &mut ExecutionState,
    ) -> ContainerRebuildSummary {
        let use_incremental = subset.is_some_and(|subset| {
            incremental_rebuild(
                subset.size(),
                self.to_id.len(),
                parallelize_intra_container_op(self.to_id.len()),
            )
        });
        if exec_state.causal_receipts().is_some() {
            assert_eq!(
                rayon::current_num_threads(),
                1,
                "causal container rebuild requires serial execution"
            );
            if use_incremental {
                return self.apply_rebuild_incremental_receipts(
                    table,
                    rebuilder,
                    exec_state,
                    subset.expect("incremental rebuild requires a recent-update subset"),
                    rebuilder.hint_col().unwrap(),
                );
            }
            return self.apply_rebuild_nonincremental_receipts(rebuilder, exec_state);
        }
        if use_incremental {
            return self.apply_rebuild_incremental(
                table,
                rebuilder,
                exec_state,
                subset.expect("incremental rebuild requires a recent-update subset"),
                rebuilder.hint_col().unwrap(),
            );
        }
        self.apply_rebuild_nonincremental(rebuilder, exec_state)
    }

    fn extend_containers_containing(&self, values: &IndexSet<Value>, out: &mut IndexSet<Value>) {
        for value in values {
            if let Some(containers) = self.val_index.get(value) {
                out.extend(containers.iter().copied());
            }
        }
    }

    fn rebuild_val_with(
        &self,
        value: Value,
        exec_state: &mut ExecutionState,
        remap: &(dyn Fn(Value) -> Value + Send + Sync),
    ) -> Option<Value> {
        // Clone out of the guard before re-interning to avoid deadlocking on
        // the underlying map.
        let mut container = self.get_container(value)?.clone();
        container.rebuild_contents(&ClosureRebuilder { remap });
        Some(self.get_or_insert(&container, exec_state))
    }
}

impl<C: ContainerValue> ContainerEnv<C> {
    pub fn new(merge_fn: Box<dyn MergeFn>, counter: CounterId) -> Self {
        Self {
            merge_fn,
            counter,
            to_id: DashMap::default(),
            to_container: DashMap::default(),
            val_index: DashMap::default(),
        }
    }

    fn get_or_insert(&self, container: &C, exec_state: &mut ExecutionState) -> Value {
        if let Some(value) = self.to_id.get(container) {
            return *value;
        }

        // Time to insert a new mapping. First, insert into `to_container`: the moment that we
        // insert a new value into `to_id`, someone else can return it from another call to
        // `get_or_insert` and then feed that value to `get_container`.

        let value = Value::from_usize(exec_state.inc_counter(self.counter));
        let target_map = self.to_id.determine_map(container);
        // This assertion is here because in parallel rebuilding we use `to_container` to
        // compute the intended shard for to_id, because we have a mutable borrow of
        // `to_container` that means we cannot call `determine_map` on `to_id`.
        debug_assert_eq!(
            target_map,
            self.to_container
                .determine_shard(hash_container(container) as usize)
        );
        self.to_container
            .insert(value, (hash_container(container) as usize, target_map));

        // Now insert into `to_id`, handling the case where a different thread is doing the same
        // thing.
        match self.to_id.entry(container.clone()) {
            dashmap::Entry::Vacant(vac) => {
                // Common case: insert the mapping in to_id and update the index.
                vac.insert(value);
                for val in container.iter() {
                    self.val_index.entry(val).or_default().insert(value);
                }
                value
            }
            dashmap::Entry::Occupied(occ) => {
                // Someone inserted `container` into the mapping since we looked it up. Remove the
                // mapping that we inserted into `to_container` (we won't use it), and instead
                // return the "winning" value.
                let res = *occ.get();
                std::mem::drop(occ); // drop the lock.
                self.to_container.remove(&value);
                res
            }
        }
    }

    fn insert_owned(&self, container: C, value: Value, exec_state: &mut ExecutionState) -> Value {
        let hc = hash_container(&container);
        let target_map = self.to_id.determine_map(&container);
        match self.to_id.entry(container) {
            dashmap::Entry::Occupied(mut occ) => {
                if let Some(receipts) = exec_state.causal_receipts() {
                    assert!(
                        exec_state.active_cause_capability().is_none(),
                        "container rebuild inherited an unrelated active cause"
                    );
                    let cutoff = receipts.equality_edge_count().unwrap_or_else(|error| {
                        panic!("cannot prepare container canonicalization: {error}")
                    });
                    let prepared = receipts
                        .container_canonicalization_cause(
                            exec_state.causal_wave(),
                            *occ.get(),
                            value,
                            cutoff,
                        )
                        .unwrap_or_else(|error| {
                            panic!("cannot record exact container canonicalization: {error}")
                        });
                    exec_state.set_active_container_canonicalization(Some(prepared));
                }
                let result = (self.merge_fn)(exec_state, *occ.get(), value);
                if exec_state.causal_receipts().is_some() {
                    exec_state.set_active_container_canonicalization(None);
                }
                let old_val = *occ.get();
                if result != old_val {
                    self.to_container.remove(&old_val);
                    self.to_container.insert(result, (hc as usize, target_map));
                    *occ.get_mut() = result;
                    for val in occ.key().iter() {
                        let mut index = self.val_index.entry(val).or_default();
                        index.swap_remove(&old_val);
                        index.insert(result);
                    }
                }
                result
            }
            dashmap::Entry::Vacant(vacant_entry) => {
                self.to_container.insert(value, (hc as usize, target_map));
                for val in vacant_entry.key().iter() {
                    self.val_index.entry(val).or_default().insert(value);
                }
                vacant_entry.insert(value);
                value
            }
        }
    }

    fn reinsert_incremental(
        &self,
        container: C,
        old_id: Value,
        rebuilt_id: Value,
        container_changed: bool,
        exec_state: &mut ExecutionState,
        summary: &mut ContainerRebuildSummary,
    ) {
        if container_changed || rebuilt_id != old_id {
            summary.note_change();
        }
        if rebuilt_id != old_id {
            // Parent rows will get a real delta from ordinary table rebuild, so
            // we only need an explicit refresh when the outer id stayed stable.
            self.to_container.remove(&old_id);
        }
        let actual = self.insert_owned(container, rebuilt_id, exec_state);
        if container_changed && rebuilt_id == old_id && actual == old_id {
            summary.note_dirty_id(old_id);
        }
    }

    fn apply_rebuild_nonincremental_receipts(
        &mut self,
        rebuilder: &dyn Rebuilder,
        exec_state: &mut ExecutionState,
    ) -> ContainerRebuildSummary {
        struct Prepared<C> {
            before: C,
            after: C,
            old_id: Value,
            rebuilt_id: Value,
            contents_changed: bool,
            dependency: Option<ContainerVersionDependency>,
        }

        let receipts = exec_state
            .causal_receipts()
            .expect("receipt container rebuild requires the receipt arena");
        let cutoff = receipts
            .equality_edge_count()
            .unwrap_or_else(|error| panic!("cannot start exact container rebuild: {error}"));
        let wave = exec_state.causal_wave();
        let mut prepared = Vec::<Prepared<C>>::new();
        for entry in self.to_id.iter() {
            let before = entry.key().clone();
            let old_id = *entry.value();
            let rebuilt_id = rebuilder.rebuild_val(old_id);
            let mut after = before.clone();
            let contents_changed = after.rebuild_contents(rebuilder);
            if !contents_changed && rebuilt_id == old_id {
                continue;
            }
            let kind = C::causal_receipt_kind().unwrap_or_else(|| {
                panic!(
                    "causal container rebuild does not support {}",
                    std::any::type_name::<C>()
                )
            });
            kind.validate_arity(before.iter().count())
                .unwrap_or_else(|error| panic!("{error}"));
            kind.validate_arity(after.iter().count())
                .unwrap_or_else(|error| panic!("{error}"));
            let dependency = if contents_changed {
                let before_children = before.iter().collect::<SmallVec<[Value; 4]>>();
                let after_children = after.iter().collect::<SmallVec<[Value; 4]>>();
                Some(
                    receipts
                        .container_dependency(
                            TypeId::of::<C>(),
                            old_id,
                            wave,
                            &before_children,
                            &after_children,
                            cutoff,
                        )
                        .unwrap_or_else(|error| {
                            panic!("cannot record exact positional container rebuild: {error}")
                        })
                        .expect(
                            "container reported changed contents without a positional child change",
                        ),
                )
            } else {
                None
            };
            prepared.push(Prepared {
                before,
                after,
                old_id,
                rebuilt_id,
                contents_changed,
                dependency,
            });
        }

        let mut summary = ContainerRebuildSummary::default();
        for change in prepared {
            summary.note_change();
            let hc = hash_container(&change.before);
            let target_map = self.to_id.determine_map(&change.before);
            let shard = self.to_id.shards_mut()[target_map].get_mut();
            let _ = shard
                .remove_entry(hc, |(_, value)| *value.get() == change.old_id)
                .expect("prepared container disappeared before serial publication");
            self.to_container.remove(&change.old_id);
            let actual = self.insert_owned(change.after, change.rebuilt_id, exec_state);
            if change.contents_changed
                && change.rebuilt_id == change.old_id
                && actual == change.old_id
            {
                summary.note_dirty_dependency(
                    change
                        .dependency
                        .expect("stable changed container has no dependency"),
                );
            }
        }
        summary
    }

    fn apply_rebuild_incremental(
        &mut self,
        table: &WrappedTable,
        rebuilder: &dyn Rebuilder,
        exec_state: &mut ExecutionState,
        to_scan: SubsetRef,
        search_col: ColumnId,
    ) -> ContainerRebuildSummary {
        // NB: there is no parallel implementation as of now.
        //
        // Implementing one should be straightforward, but we should wait for a real benchmark that
        // requires it. It's possible that incremental rebuilding will only be profitable when the
        // total number of ids to rebuild is small, in which case the overhead of parallelism may
        // not be worth it in the first place.
        let mut summary = ContainerRebuildSummary::default();
        let mut buf = TaggedRowBuffer::new(1);
        table.scan_project(
            to_scan,
            &[search_col],
            Offset::new(0),
            usize::MAX,
            &[],
            &mut buf,
        );
        // For each value in the buffer, rebuild all containers that mention it.
        let mut to_rebuild = IndexSet::<Value>::default();
        for (_, row) in buf.iter() {
            to_rebuild.insert(row[0]);
            let Some(ids) = self.val_index.get(&row[0]) else {
                continue;
            };
            to_rebuild.extend(&*ids);
        }
        for id in to_rebuild {
            let Some((hc, target_map)) = self.to_container.get(&id).map(|x| *x) else {
                continue;
            };
            let shard_mut = self.to_id.shards_mut()[target_map].get_mut();
            let Some((mut container, _)) =
                shard_mut.remove_entry(hc as u64, |(_, v)| *v.get() == id)
            else {
                continue;
            };
            let rebuilt_id = rebuilder.rebuild_val(id);
            let container_changed = container.rebuild_contents(rebuilder);
            self.reinsert_incremental(
                container,
                id,
                rebuilt_id,
                container_changed,
                exec_state,
                &mut summary,
            );
        }
        summary
    }

    fn apply_rebuild_incremental_receipts(
        &mut self,
        table: &WrappedTable,
        rebuilder: &dyn Rebuilder,
        exec_state: &mut ExecutionState,
        to_scan: SubsetRef,
        search_col: ColumnId,
    ) -> ContainerRebuildSummary {
        struct Prepared<C> {
            before: C,
            after: C,
            old_id: Value,
            rebuilt_id: Value,
            contents_changed: bool,
            dependency: Option<ContainerVersionDependency>,
        }

        // Preserve the ordinary incremental candidate scan and insertion
        // order. Receipt preparation is read-only and validates every selected
        // change before the first registry mutation.
        let mut buf = TaggedRowBuffer::new(1);
        table.scan_project(
            to_scan,
            &[search_col],
            Offset::new(0),
            usize::MAX,
            &[],
            &mut buf,
        );
        let mut to_rebuild = IndexSet::<Value>::default();
        for (_, row) in buf.iter() {
            to_rebuild.insert(row[0]);
            let Some(ids) = self.val_index.get(&row[0]) else {
                continue;
            };
            to_rebuild.extend(&*ids);
        }

        let receipts = exec_state
            .causal_receipts()
            .expect("receipt container rebuild requires the receipt arena");
        let cutoff = receipts
            .equality_edge_count()
            .unwrap_or_else(|error| panic!("cannot start exact container rebuild: {error}"));
        let wave = exec_state.causal_wave();
        let mut prepared = Vec::<Prepared<C>>::new();
        for old_id in to_rebuild {
            let Some(before) = self
                .get_container(old_id)
                .map(|container| container.clone())
            else {
                continue;
            };
            let rebuilt_id = rebuilder.rebuild_val(old_id);
            let mut after = before.clone();
            let contents_changed = after.rebuild_contents(rebuilder);
            if !contents_changed && rebuilt_id == old_id {
                continue;
            }
            let kind = C::causal_receipt_kind().unwrap_or_else(|| {
                panic!(
                    "causal container rebuild does not support {}",
                    std::any::type_name::<C>()
                )
            });
            kind.validate_arity(before.iter().count())
                .unwrap_or_else(|error| panic!("{error}"));
            kind.validate_arity(after.iter().count())
                .unwrap_or_else(|error| panic!("{error}"));
            let dependency = if contents_changed {
                let before_children = before.iter().collect::<SmallVec<[Value; 4]>>();
                let after_children = after.iter().collect::<SmallVec<[Value; 4]>>();
                Some(
                    receipts
                        .container_dependency(
                            TypeId::of::<C>(),
                            old_id,
                            wave,
                            &before_children,
                            &after_children,
                            cutoff,
                        )
                        .unwrap_or_else(|error| {
                            panic!("cannot record exact positional container rebuild: {error}")
                        })
                        .expect(
                            "container reported changed contents without a positional child change",
                        ),
                )
            } else {
                None
            };
            prepared.push(Prepared {
                before,
                after,
                old_id,
                rebuilt_id,
                contents_changed,
                dependency,
            });
        }

        let mut summary = ContainerRebuildSummary::default();
        for change in prepared {
            // An earlier incremental collision can retire a later selected id;
            // the ordinary path observes the same absence and skips it.
            let Some((hc, target_map)) = self.to_container.get(&change.old_id).map(|entry| *entry)
            else {
                continue;
            };
            let shard = self.to_id.shards_mut()[target_map].get_mut();
            let Some((before, _)) =
                shard.remove_entry(hc as u64, |(_, value)| *value.get() == change.old_id)
            else {
                continue;
            };
            assert!(
                before == change.before,
                "incremental container changed after receipt preflight"
            );
            self.to_container.remove(&change.old_id);
            summary.note_change();
            let actual = self.insert_owned(change.after, change.rebuilt_id, exec_state);
            if change.contents_changed
                && change.rebuilt_id == change.old_id
                && actual == change.old_id
            {
                summary.note_dirty_dependency(
                    change
                        .dependency
                        .expect("stable changed container has no dependency"),
                );
            }
        }
        summary
    }

    fn apply_rebuild_nonincremental(
        &mut self,
        rebuilder: &dyn Rebuilder,
        exec_state: &mut ExecutionState,
    ) -> ContainerRebuildSummary {
        if parallelize_inter_container_op(self.to_id.len()) {
            return self.apply_rebuild_nonincremental_parallel(rebuilder, exec_state);
        }
        let mut summary = ContainerRebuildSummary::default();
        let mut to_reinsert = Vec::new();
        let shards = self.to_id.shards_mut();
        for shard in shards.iter_mut() {
            let shard = shard.get_mut();
            // SAFETY: the iterator does not outlive `shard`.
            for bucket in unsafe { shard.iter() } {
                // SAFETY: the bucket is valid; we just got it from the iterator.
                let (container, val) = unsafe { bucket.as_mut() };
                let old_val = *val.get();
                let new_val = rebuilder.rebuild_val(old_val);
                let container_changed = container.rebuild_contents(rebuilder);
                if !container_changed && new_val == old_val {
                    // Nothing changed about this entry. Leave it in place.
                    continue;
                }
                summary.note_change();
                if container_changed {
                    // The container changed. Remove both map entries then reinsert.
                    // SAFETY: This is a valid bucket. Furthermore, iterators remain valid if
                    // buckets they have already yielded have been removed.
                    let ((container, _), _) = unsafe { shard.remove(bucket) };
                    self.to_container.remove(&old_val);
                    to_reinsert.push((container, new_val, new_val == old_val));
                } else {
                    // Just the value changed. Leave the container in place.
                    *val.get_mut() = new_val;
                    let prev = self.to_container.remove(&old_val).unwrap().1;
                    self.to_container.insert(new_val, prev);
                }
            }
        }
        for (container, val, stable_id) in to_reinsert {
            let actual = self.insert_owned(container, val, exec_state);
            // Refresh only when rebuild changed container semantics in place.
            // If the outer id changed, ordinary table rebuild already creates a
            // fresh parent-row delta for seminaive to follow.
            if stable_id && actual == val {
                summary.note_dirty_id(val);
            }
        }
        summary
    }

    fn apply_rebuild_nonincremental_parallel(
        &mut self,
        rebuilder: &dyn Rebuilder,
        exec_state: &mut ExecutionState,
    ) -> ContainerRebuildSummary {
        // This is very similar to the serial variant. The main difference is that
        // `to_reinsert` isn't a flat vector. It's instead a vector of queues - one per
        // destination map shard. This lets us do a bulk insertion in parallel without having
        // to grab a lock per container.
        let mut to_reinsert =
            IdVec::<usize /* to_id shard */, SegQueue<(C, Value, bool)>>::default();
        to_reinsert.resize_with(self.to_id.shards().len(), Default::default);

        let shards = self.to_id.shards_mut();
        let changed = shards
            .par_iter_mut()
            .map(|shard| {
                let mut changed = false;
                let shard = shard.get_mut();
                // SAFETY: the iterator does not outlive `shard`.
                for bucket in unsafe { shard.iter() } {
                    // SAFETY: the bucket is valid; we just got it from the iterator.
                    let (container, val) = unsafe { bucket.as_mut() };
                    let old_val = *val.get();
                    let new_val = rebuilder.rebuild_val(old_val);
                    let container_changed = container.rebuild_contents(rebuilder);
                    if !container_changed && new_val == old_val {
                        // Nothing changed about this entry. Leave it in place.
                        continue;
                    }
                    changed = true;
                    if container_changed {
                        // The container changed. Remove both map entries then reinsert.
                        // SAFETY: This is a valid bucket. Furthermore, iterators remain valid if
                        // buckets they have already yielded have been removed.
                        let ((container, _), _) = unsafe { shard.remove(bucket) };
                        self.to_container.remove(&old_val);
                        // Spooky: we're using `to_container` to determine the shard for
                        // `to_id`. We are assuming that the # shards determination is
                        // deterministic here. There is a debug assertion in `get_or_insert`
                        // that attempts to verify this.
                        let shard = self
                            .to_container
                            .determine_shard(hash_container(&container) as usize);
                        to_reinsert[shard].push((container, new_val, new_val == old_val));
                    } else {
                        // Just the value changed. Leave the container in place.
                        *val.get_mut() = new_val;
                        let prev = self.to_container.remove(&old_val).unwrap().1;
                        self.to_container.insert(new_val, prev);
                    }
                }
                changed
            })
            .max()
            .unwrap_or(false);

        let dirty_ids = SegQueue::new();
        shards
            .iter_mut()
            .enumerate()
            .map(|(i, shard)| (i, shard, exec_state.clone()))
            .par_bridge()
            .for_each(|(shard_id, shard, mut exec_state)| {
                // This bit is a real slog. Once Dashmap updates from RawTable to HashTable for
                // the underlying shard, this will get a little better.
                //
                // NB: We are probably leaving some paralellism on the floor with these calls
                // to `to_container` and `val_index`.
                let shard = shard.get_mut();
                let queue = &to_reinsert[shard_id];
                while let Some((container, val, stable_id)) = queue.pop() {
                    let hc = hash_container(&container);
                    let target_map = self.to_container.determine_shard(hc as usize);
                    match shard.find_or_find_insert_slot(
                        hc,
                        |(c, _)| c == &container,
                        |(c, _)| hash_container(c),
                    ) {
                        Ok(bucket) => {
                            // SAFETY: the bucket is valid; we just got it from the shard and
                            // we have not done any operations that can invalidate the bucket.
                            let (container, val_slot) = unsafe { bucket.as_mut() };
                            let old_val = *val_slot.get();
                            let result = (self.merge_fn)(&mut exec_state, old_val, val);
                            if result != old_val {
                                self.to_container.remove(&old_val);
                                self.to_container.insert(result, (hc as usize, target_map));
                                *val_slot.get_mut() = result;
                                for val in container.iter() {
                                    let mut index = self.val_index.entry(val).or_default();
                                    index.swap_remove(&old_val);
                                    index.insert(result);
                                }
                            }
                            // As in the serial path, only same-id semantic
                            // changes need an explicit parent-row refresh.
                            if stable_id && result == val {
                                dirty_ids.push(val);
                            }
                        }
                        Err(slot) => {
                            self.to_container.insert(val, (hc as usize, target_map));
                            for v in container.iter() {
                                self.val_index.entry(v).or_default().insert(val);
                            }
                            // SAFETY: We just got this slot from `find_or_find_insert_slot`
                            // and we have not mutated the map at all since then.
                            unsafe {
                                shard.insert_in_slot(hc, slot, (container, SharedValue::new(val)));
                            }
                            if stable_id {
                                dirty_ids.push(val);
                            }
                        }
                    }
                }
            });
        let mut summary = ContainerRebuildSummary::default();
        if changed {
            summary.note_change();
        }
        while let Some(value) = dirty_ids.pop() {
            summary.note_dirty_id(value);
        }
        summary
    }

    fn get_container(&self, value: Value) -> Option<impl Deref<Target = C> + '_> {
        let (hc, target_map) = *self.to_container.get(&value)?;
        let shard = &self.to_id.shards()[target_map];
        let read_guard = shard.read();
        let val_ptr: *const (C, _) = shard
            .read()
            .find(hc as u64, |(_, v)| *v.get() == value)?
            .as_ptr();
        struct ValueDeref<'a, T, Guard> {
            _guard: Guard,
            data: &'a T,
        }

        impl<T, Guard> Deref for ValueDeref<'_, T, Guard> {
            type Target = T;

            fn deref(&self) -> &T {
                self.data
            }
        }

        Some(ValueDeref {
            _guard: read_guard,
            // SAFETY: the value will remain valid for as long as `read_guard` is in scope.
            data: unsafe {
                let unwrapped: &(C, _) = &*val_ptr;
                &unwrapped.0
            },
        })
    }
}

fn incremental_rebuild(uf_size: usize, table_size: usize, parallel: bool) -> bool {
    if parallel {
        table_size > 1000 && uf_size * 512 <= table_size
    } else {
        table_size > 1000 && uf_size * 8 <= table_size
    }
}

/// A [`ValueRebuilder`] that remaps individual values through a caller-supplied
/// closure. Used by [`ContainerValues::rebuild_val_with`] to rebuild a single
/// container against an explicit value mapping rather than a backend union-find.
struct ClosureRebuilder<'a> {
    remap: &'a (dyn Fn(Value) -> Value + Send + Sync),
}

impl ValueRebuilder for ClosureRebuilder<'_> {
    fn rebuild_val(&self, val: Value) -> Value {
        (self.remap)(val)
    }
}

//! Bounded residual-key lookahead for mixed/fused plans. It only changes
//! the next stage, never filters answers or replaces the executor. Missing
//! indexes and exhausted budgets leave conservative candidate supersets.
use super::super::join_tail::for_each_stage_atom;
use super::super::packed_cache::RootProjectionSlot;
use super::super::probe::intersect_with_dense_ref;
use super::*;
use crate::row_buffer::RowSink;

// Empirical limits on tiny input scans, key probes, candidate stages, and
// the required ordering margin keep speculative work bounded. They are cost
// heuristics, not join-size or runtime guarantees.
// Small positive bounds can still produce an unhelpful order: unlike a
// zero bound, they do not establish selectivity. Demand a large estimated
// margin before displacing the incumbent; exact execution remains unchanged.
const POSITIVE_PROMOTION_MARGIN: usize = 128;

fn row_limit() -> usize {
    16
}

#[derive(Default)]
struct Keys(SmallVec<[Value; 16]>);
impl RowSink for Keys {
    fn add_row(&mut self, _: RowId, values: &[Value]) {
        self.0.push(values[0]);
    }
}

fn may_overlap(a: SubsetRef<'_>, b: SubsetRef<'_>, budget: &mut usize) -> bool {
    match (a, b) {
        (SubsetRef::Dense(r), s) | (s, SubsetRef::Dense(r)) => {
            intersect_with_dense_ref(s, r).is_some()
        }
        (SubsetRef::Sparse(a), SubsetRef::Sparse(b)) => {
            let (a, b) = if a.inner().len() <= b.inner().len() {
                (a, b)
            } else {
                (b, a)
            };
            for row in a.inner() {
                if *budget == 0 {
                    return true;
                }
                *budget -= 1;
                if b.inner().binary_search(row).is_ok() {
                    return true;
                }
            }
            false
        }
    }
}

impl<'a, 'state, 'exec> JoinState<'a, 'state, 'exec> {
    fn cached_projection(
        &self,
        source: &AtomRows<'_, '_>,
        col: ColumnId,
        cs: &[Constraint],
    ) -> Option<RootProjectionSlot> {
        let AtomRows::Root(root) = source else {
            return None;
        };
        root.cached_projection(col, cs)
    }

    fn small_keys(
        &self,
        atom: &Atom,
        source: &AtomRows<'_, '_>,
        col: ColumnId,
        cs: &[Constraint],
        budget: &mut usize,
    ) -> Option<Keys> {
        if let Some(slot) = self.cached_projection(source, col, cs)
            && let Some(index) = slot.get()
            && index.len() <= row_limit()
            && index.len() <= *budget
        {
            *budget -= index.len();
            return Some(Keys((0..index.len()).map(|i| index.value_at(i)).collect()));
        }
        let rows = source.subset();
        if rows.size() > row_limit() || rows.size() > *budget {
            return None;
        }
        *budget -= rows.size();
        let mut keys = Keys::default();
        self.db.tables[atom.table].table.scan_project(
            rows,
            &[col],
            Offset::new(0),
            rows.size(),
            cs,
            &mut keys,
        );
        keys.0.sort_unstable();
        keys.0.dedup();
        Some(keys)
    }

    fn probe_scan(
        &self,
        atom: &Atom,
        source: &AtomRows<'_, '_>,
        col: ColumnId,
        cs: &[Constraint],
        keys: &mut Keys,
        budget: &mut usize,
    ) {
        if let Some(other) = self.small_keys(atom, source, col, cs, budget) {
            keys.0.retain(|v| other.0.binary_search(v).is_ok());
            return;
        }
        if let Some(slot) = self.cached_projection(source, col, cs)
            && let Some(index) = slot.get()
        {
            keys.0.retain(|v| {
                if *budget == 0 {
                    return true;
                }
                *budget -= 1;
                index.find(*v).is_some()
            });
            return;
        }
        let rows = source.subset();
        let info = &self.db.tables[atom.table];
        let handle = info.column_indexes.get_if_present(&col);
        if let Some(handle) = handle
            && let Some(index) = handle.get()
        {
            keys.0.retain(|v| {
                if *budget == 0 {
                    return true;
                }
                *budget -= 1;
                index
                    .get_subset(v)
                    .is_some_and(|s| may_overlap(s, rows, budget))
            });
        }
    }

    pub(super) fn extension_bound(
        &self,
        stage: &JoinStage,
        atoms: &DenseIdMap<AtomId, Atom>,
        bindings: &BindingInfo<'_, '_>,
        budget: &mut usize,
    ) -> Option<usize> {
        match stage {
            JoinStage::Intersect { scans, .. } => {
                if scans.iter().any(|s| s.occurrence_cols.is_some()) {
                    return None;
                }
                let seed = scans
                    .iter()
                    .enumerate()
                    .min_by_key(|(_, s)| bindings.subsets[s.atom].size())?
                    .0;
                let s = &scans[seed];
                let mut keys = self.small_keys(
                    &atoms[s.atom],
                    &bindings.subsets[s.atom],
                    s.column,
                    &s.cs,
                    budget,
                )?;
                for (i, s) in scans.iter().enumerate() {
                    if i != seed {
                        self.probe_scan(
                            &atoms[s.atom],
                            &bindings.subsets[s.atom],
                            s.column,
                            &s.cs,
                            &mut keys,
                            budget,
                        );
                    }
                }
                Some(keys.0.len())
            }
            JoinStage::FusedIntersect {
                cover,
                bind,
                to_intersect,
            } => {
                if cover.occurrence_cols.is_some()
                    || to_intersect
                        .iter()
                        .any(|(s, _)| s.occurrence_cols.is_some())
                {
                    return None;
                }
                // Count physical cover rows, retaining duplicate projected keys.
                // Fused filtering checks every projected component. It can
                // overestimate tuple matches but cannot invent a rejection.
                let rows = bindings.subsets[cover.to_index.atom].subset();
                if rows.size() > row_limit() || rows.size() > *budget {
                    return None;
                }
                *budget -= rows.size();
                let mut buffer = TaggedRowBuffer::new(bind.len());
                let proj: SmallVec<[ColumnId; 4]> = bind.iter().map(|(col, _)| *col).collect();
                self.db.tables[atoms[cover.to_index.atom].table]
                    .table
                    .scan_project(
                        rows,
                        &proj,
                        Offset::new(0),
                        rows.size(),
                        &cover.constraints,
                        &mut buffer,
                    );
                let mut count = 0;
                'row: for (_, values) in buffer.iter() {
                    for (filter, positions) in to_intersect {
                        for (col, position) in filter.to_index.vars.iter().zip(positions) {
                            let mut key = Keys(smallvec::smallvec![values[position.index()]]);
                            self.probe_scan(
                                &atoms[filter.to_index.atom],
                                &bindings.subsets[filter.to_index.atom],
                                *col,
                                &filter.constraints,
                                &mut key,
                                budget,
                            );
                            if key.0.is_empty() {
                                continue 'row;
                            }
                        }
                    }
                    count += 1;
                }
                Some(count)
            }
            _ => None,
        }
    }

    // Swapping an independent leaf forward also moves the incumbent back.
    // Allow that indirect deferral only if the incumbent is a projection that
    // thereby passes its last join dependency and becomes factorized in the
    // new order. A later DVO sort may change that order again.
    fn swap_factorizes_incumbent(
        stages: &[JoinStage],
        order: &InstrOrder,
        cur: usize,
        position: usize,
    ) -> bool {
        let JoinStage::FusedIntersect {
            cover,
            to_intersect,
            ..
        } = &stages[order.get(cur)]
        else {
            return false;
        };
        if !to_intersect.is_empty() {
            return false;
        }
        let atom = cover.to_index.atom;
        let uses_atom = |p| {
            let mut touches = false;
            for_each_stage_atom(&stages[order.get(p)], |a| touches |= a == atom);
            touches
        };
        (cur + 1..position).any(uses_atom) && !(position + 1..order.len()).any(uses_atom)
    }

    // Ordinary Intersect stages recurse once per distinct shared key, not
    // once per physical row. Existing root projections and current catalog
    // indexes supply conservative key-count bounds without building an index.
    // A whole-table catalog overestimates any constrained residual, which is
    // sufficient for this ordering score. Reset/missing handles are unknown.
    fn incumbent_bound(
        &self,
        stage: &JoinStage,
        atoms: &DenseIdMap<AtomId, Atom>,
        bindings: &BindingInfo<'_, '_>,
    ) -> usize {
        let mut bound = estimate_size(stage, bindings);
        if let JoinStage::Intersect { scans, .. } = stage {
            for scan in scans {
                // An occurrence scan unions keys from several columns; one
                // ordinary column's distinct count does not bound that union.
                if scan.occurrence_cols.is_some() {
                    continue;
                }
                let atom = &atoms[scan.atom];
                if let Some(slot) =
                    self.cached_projection(&bindings.subsets[scan.atom], scan.column, &scan.cs)
                    && let Some(index) = slot.get()
                {
                    bound = bound.min(index.len());
                    // A constrained root's domain is already no larger than
                    // the global column domain, so its catalog cannot help.
                    continue;
                }
                if let Some(handle) = self.db.tables[atom.table]
                    .column_indexes
                    .get_if_present(&scan.column)
                    && let Some(index) = handle.get()
                {
                    bound = bound.min(index.len());
                }
            }
        }
        bound
    }

    pub(super) fn mixed_probe_order(
        &self,
        stages: &JoinStages,
        atoms: &DenseIdMap<AtomId, Atom>,
        order: &mut InstrOrder,
        cur: usize,
        bindings: &BindingInfo<'_, '_>,
    ) -> bool {
        if !stages.supports_lookahead {
            return false;
        }
        let stages = &stages.instrs;
        let mut budget = 256;
        let mut best = None;
        let mut incumbent = self.incumbent_bound(&stages[order.get(cur)], atoms, bindings);
        let remaining = order.len() - cur;
        for k in 0..remaining.min(64) {
            let position = cur + k;
            let stage = &stages[order.get(position)];
            if let Some(mut count) = self.extension_bound(stage, atoms, bindings, &mut budget) {
                if position == cur {
                    // Compare conservative extension bounds on both sides,
                    // rather than a candidate's keys against incumbent rows.
                    incumbent = incumbent.min(count);
                }
                if count == 0 {
                    best = Some((position, 0));
                    break;
                }
                let mut factorized = false;
                if let JoinStage::FusedIntersect {
                    cover,
                    to_intersect,
                    ..
                } = stage
                    && to_intersect.is_empty()
                    && !(cur..order.len()).any(|p| {
                        let mut touched = false;
                        if p != position {
                            for_each_stage_atom(&stages[order.get(p)], |a| {
                                touched |= a == cover.to_index.atom
                            });
                        }
                        touched
                    })
                {
                    count = 1;
                    factorized = true;
                }
                if count <= 4
                    && count.saturating_mul(POSITIVE_PROMOTION_MARGIN) < incumbent
                    && best.is_none_or(|(_, b)| count < b)
                    && (position == cur
                        || !factorized
                        || Self::swap_factorizes_incumbent(stages, order, cur, position))
                {
                    best = Some((position, count));
                }
            }
            if budget == 0 {
                break;
            }
        }
        if let Some((position, _)) = best
            && position != cur
        {
            order.data.swap(cur, position);
            return true;
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::offsets::SortedOffsetSlice;

    #[test]
    fn bounded_overlap_never_loses_a_witness() {
        for a in 0u32..128 {
            for b in 0u32..128 {
                let left: Vec<_> = (0..7)
                    .filter(|i| a & (1 << i) != 0)
                    .map(RowId::new)
                    .collect();
                let right: Vec<_> = (0..7)
                    .filter(|i| b & (1 << i) != 0)
                    .map(RowId::new)
                    .collect();
                // SAFETY: both vectors are strictly increasing.
                let left = SubsetRef::Sparse(unsafe { SortedOffsetSlice::new_unchecked(&left) });
                let right = SubsetRef::Sparse(unsafe { SortedOffsetSlice::new_unchecked(&right) });
                for limit in [0, 1, 3, 16] {
                    let mut budget = limit;
                    let answer = may_overlap(left, right, &mut budget);
                    assert!(a & b == 0 || answer);
                    if limit == 16 {
                        assert_eq!(answer, a & b != 0);
                    }
                    assert!(budget <= limit);
                }
            }
        }
    }
}

#[cfg(test)]
#[path = "lookahead_tests.rs"]
mod probe_tests;
